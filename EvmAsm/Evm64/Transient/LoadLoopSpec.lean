/-
  EvmAsm.Evm64.Transient.LoadSpec

  Stack-level `cpsTripleWithin` specification for the EVM `TLOAD` opcode
  (0x5c, EIP-1153 transient storage; see `EvmAsm/Evm64/Transient/LoadProgram.lean`).

  TLOAD scans the transient-storage exec-log from the END for the most-recent
  entry keyed by the executing frame's `env.ADDRESS` and the slot key at the
  stack top, replacing the stack top IN PLACE with that entry's `current`
  (or 0 when no entry matches). The pure model is `transientLookup`.

  Proof layout (bottom-up):
  - `evm_tload_cmp_*`: the 25-instruction compare block, one lemma per exit —
    eight mismatch exits (merged into `evm_tload_cmp_mismatch_spec_within` by
    limb `by_cases`) and the all-limbs-equal pass-through
    (`evm_tload_cmp_pass_spec_within`). Proven over `evm_tload_cmp_code b2`
    (variable entry) and extended to the loop slice.
  - `evm_tload_copy_spec_within` / `evm_tload_tail_{continue,exit}_spec_within`:
    the match-copy arm and the decrement/zero tail, each `∀ base` over its own
    slice code (runBlock needs a variable entry) and instantiated at the
    in-situ offsets (+100 / +136 of the loop slice).
  - `evm_tload_iter_{match,nomatch_continue,nomatch_exit}_spec_within`: one
    full loop iteration over `evm_tload_loop_code b2`.
  - `evm_tload_loop_spec_within`: snoc induction (`List.reverseRecOn`) over the
    unscanned prefix; the loop invariant at entry with `m` entries left is
    `x15 = m`, `x14 = TRANSIENT_STORAGE_LOG_BASE + 128*m`, and the final stack
    top is `transientLookup` over those `m` entries.
  - `evm_tload_spec_within` (head + loop / empty-log path) and the public
    witness `evm_tload_stack_spec_within`.
-/

import EvmAsm.Evm64.Transient.LoadProgram
import EvmAsm.Evm64.Transient.StoreSpec
import EvmAsm.Evm64.StorageAssertions
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Transient

open EvmAsm.Rv64
open EvmAsm.Evm64

/-! ## The pure reverse-scan model -/

/-- Scan a transient-log suffix (given most-recent-first) for the first entry
    keyed by `(addrHash, slotKey)`; 0 when none matches. -/
def transientLookupRev (addrHash slotKey : EvmWord) :
    List StorageLogEntry → EvmWord
  | [] => 0
  | e :: es =>
      if e.addrHash = addrHash ∧ e.slotKey = slotKey then e.current
      else transientLookupRev addrHash slotKey es

/-- The EIP-1153 TLOAD value: the `current` of the LAST entry of `entries`
    matching `(addrHash, slotKey)` (the log is append-only, so the last match
    is the most-recent write), or 0 when no entry matches. -/
def transientLookup (addrHash slotKey : EvmWord)
    (entries : List StorageLogEntry) : EvmWord :=
  transientLookupRev addrHash slotKey entries.reverse

@[simp] theorem transientLookup_nil {addrHash slotKey : EvmWord} :
    transientLookup addrHash slotKey [] = 0 := rfl

/-- The snoc unfold driving the reverse-scan induction: the entry appended
    LAST is scanned FIRST. -/
theorem transientLookup_snoc {addrHash slotKey : EvmWord}
    {es : List StorageLogEntry} {e : StorageLogEntry} :
    transientLookup addrHash slotKey (es ++ [e]) =
      if e.addrHash = addrHash ∧ e.slotKey = slotKey then e.current
      else transientLookup addrHash slotKey es := by
  simp [transientLookup, List.reverse_append, transientLookupRev]

/-! ## Limb ↔ word bridging -/

/-- Two `EvmWord`s with equal limbs are equal (via the `fromLimbs` round
    trip). Bridges the guest's 4-limb dword compares to word equality. -/
theorem evmWord_eq_of_limbs_eq {v w : EvmWord}
    (h0 : v.getLimbN 0 = w.getLimbN 0) (h1 : v.getLimbN 1 = w.getLimbN 1)
    (h2 : v.getLimbN 2 = w.getLimbN 2) (h3 : v.getLimbN 3 = w.getLimbN 3) :
    v = w := by
  have hf : v.getLimb = w.getLimb := by
    funext i
    match i with
    | ⟨0, _⟩ =>
      rw [EvmWord.getLimb_eq_getLimbN, EvmWord.getLimb_eq_getLimbN]; exact h0
    | ⟨1, _⟩ =>
      rw [EvmWord.getLimb_eq_getLimbN, EvmWord.getLimb_eq_getLimbN]; exact h1
    | ⟨2, _⟩ =>
      rw [EvmWord.getLimb_eq_getLimbN, EvmWord.getLimb_eq_getLimbN]; exact h2
    | ⟨3, _⟩ =>
      rw [EvmWord.getLimb_eq_getLimbN, EvmWord.getLimb_eq_getLimbN]; exact h3
  calc v = EvmWord.fromLimbs v.getLimb := (EvmWord.fromLimbs_getLimb v).symm
    _ = EvmWord.fromLimbs w.getLimb := by rw [hf]
    _ = w := EvmWord.fromLimbs_getLimb w

/-! ## Address / counter arithmetic -/

/-- Base address of transient-log entry `L`. -/
def tloadEnt (L : Nat) : Word :=
  TRANSIENT_STORAGE_LOG_BASE + BitVec.ofNat 64 (L * 128)

theorem tloadEnt_zero : tloadEnt 0 = TRANSIENT_STORAGE_LOG_BASE := by
  simp [tloadEnt]

theorem tloadEnt_succ (L : Nat) : tloadEnt (L + 1) = tloadEnt L + 128 := by
  unfold tloadEnt
  rw [show (L + 1) * 128 = L * 128 + 128 from by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc,
      show (BitVec.ofNat 64 128 : Word) = 128 from by decide]

/-- `x + 128` stepped back by the `ADDI x14, x14, -128` immediate is `x`. -/
theorem add128_addi_neg128 (x : Word) :
    (x + 128) + signExtend12 (-128 : BitVec 12) = x := by
  rw [show signExtend12 (-128 : BitVec 12) = (18446744073709551488 : Word)
        from by decide,
      BitVec.add_assoc,
      show (128 : Word) + 18446744073709551488 = 0 from by decide]
  simp

/-- The `ADDI x15, x15, -1` decrement: `v + sext(-1) = v - 1`. -/
theorem addi_neg1_eq_sub_one (v : Word) :
    v + signExtend12 (-1 : BitVec 12) = v - 1 := by
  rw [show signExtend12 (-1 : BitVec 12) = (18446744073709551615 : Word)
        from by decide]
  bv_omega

theorem ofNat_succ_sub_one (L : Nat) :
    BitVec.ofNat 64 (L + 1) - 1 = BitVec.ofNat 64 L := by
  rw [BitVec.ofNat_add, show (BitVec.ofNat 64 1 : Word) = 1 from by decide,
      BitVec.add_sub_cancel]

theorem ofNat64_ne_zero {L : Nat} (h0 : L ≠ 0) (hlt : L < 2 ^ 64) :
    BitVec.ofNat 64 L ≠ 0 := by
  intro h
  have h2 : (BitVec.ofNat 64 L).toNat = 0 := by rw [h]; rfl
  rw [BitVec.toNat_ofNat] at h2
  omega

/-! ## Pre-existential helper -/

/-- Lift a family of concrete-scratch-register triples to a `regOwn` pre:
    the loop invariant owns `x16`/`x17` without pinning their values. -/
theorem cpsTripleWithin_regOwn2_pre {nSteps : Nat} {entry exit_ : Word}
    {cr : CodeReq} {r1 r2 : Reg} {P Q : Assertion}
    (h : ∀ v1 v2 : Word, cpsTripleWithin nSteps entry exit_ cr
      ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** P) Q) :
    cpsTripleWithin nSteps entry exit_ cr (regOwn r1 ** regOwn r2 ** P) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hA, hRest, hdA, huA, ⟨v1, hv1⟩, hB, hP2, hdB, huB, ⟨v2, hv2⟩, hpP2⟩ := hpP
  exact h v1 v2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hdisj, hunion,
     ⟨hA, hRest, hdA, huA, hv1, hB, hP2, hdB, huB, hv2, hpP2⟩, hpR⟩ hpc

/-- Weaken four leading concrete register atoms to `regOwn` (the scratch
    registers the merged posts clobber). -/
theorem sepConj_own4 {r1 r2 r3 r4 : Reg} {v1 v2 v3 v4 : Word}
    {Q : Assertion} :
    ∀ h, ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) ** Q) h →
      (regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** Q) h :=
  fun h hp =>
    sepConj_mono (regIs_implies_regOwn r1)
      (sepConj_mono (regIs_implies_regOwn r2)
        (sepConj_mono (regIs_implies_regOwn r3)
          (sepConj_mono_left (regIs_implies_regOwn r4)))) h hp

/-- Weaken two concrete register atoms (positions 4–5) to `regOwn`. -/
theorem sepConj_own2_after3 {r1 r2 : Reg} {v1 v2 : Word}
    {A B C Q : Assertion} :
    ∀ h, (A ** B ** C ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Q) h →
      (A ** B ** C ** regOwn r1 ** regOwn r2 ** Q) h :=
  fun h hp =>
    sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (regIs_implies_regOwn r1)
        (sepConj_mono_left (regIs_implies_regOwn r2))))) h hp

/-! ## Compare-block lemmas (the 25-instruction slice `evm_tload_cmp`)

All nine share one footprint: five registers (`x20`, `x12`, `x14`, `x16`,
`x17` — `x15` and `x0` are untouched here) plus 16 memory cells: the four
`env.ADDRESS` limbs `a0..a3`, the four stack-top key limbs `k0..k3`, and the
scanned entry's eight compare limbs `e0..e7` (addrHash then slotKey) at
`ent .. ent+56`. Pre has `x14 = ent + 128`; the leading ADDI steps it to
`ent`. -/

/- `signExtend12` constant folds shared by the block lemmas. -/
theorem sE0 : signExtend12 (BitVec.ofNat 12 0) = (0 : Word) := by decide
theorem sE8 : signExtend12 (BitVec.ofNat 12 8) = (8 : Word) := by decide
theorem sE16 : signExtend12 (BitVec.ofNat 12 16) = (16 : Word) := by decide
theorem sE24 : signExtend12 (BitVec.ofNat 12 24) = (24 : Word) := by decide
theorem sE32 : signExtend12 (BitVec.ofNat 12 32) = (32 : Word) := by decide
theorem sE40 : signExtend12 (BitVec.ofNat 12 40) = (40 : Word) := by decide
theorem sE48 : signExtend12 (BitVec.ofNat 12 48) = (48 : Word) := by decide
theorem sE56 : signExtend12 (BitVec.ofNat 12 56) = (56 : Word) := by decide
theorem sE96 : signExtend12 (BitVec.ofNat 12 96) = (96 : Word) := by decide
theorem sE104 : signExtend12 (BitVec.ofNat 12 104) = (104 : Word) := by decide
theorem sE112 : signExtend12 (BitVec.ofNat 12 112) = (112 : Word) := by decide
theorem sE120 : signExtend12 (BitVec.ofNat 12 120) = (120 : Word) := by decide

/-- Mismatch at compare pair 0 (`addrHash` limb 0 differs): ADDI, LD, LD, then
    the first BNE exits to the decrement block. -/
theorem evm_tload_cmp_exit0_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (hne0 : e0 ≠ a0) :
    cpsTripleWithin 4 b2 (b2 + 136) (evm_tload_cmp_code b2)
      (((.x20) ↦ᵣ envAddr) ** ((.x12) ↦ᵣ sp) ** ((.x14) ↦ᵣ (ent + 128)) **
       ((.x16) ↦ᵣ x16old) ** ((.x17) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) ** ((ent + 16) ↦ₘ e2) **
       ((ent + 24) ↦ₘ e3) ** ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7))
      (((.x20) ↦ᵣ envAddr) ** ((.x12) ↦ᵣ sp) ** ((.x14) ↦ᵣ ent) **
       ((.x16) ↦ᵣ e0) ** ((.x17) ↦ᵣ a0) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) ** ((ent + 16) ↦ₘ e2) **
       ((ent + 24) ↦ₘ e3) ** ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  have haddi := addi_spec_gen_same_within .x14 (ent + 128) (-128 : BitVec 12)
    b2 (by decide)
  rw [add128_addi_neg128] at haddi
  have hLDe0 := ld_spec_gen_within .x16 .x14 ent x16old e0
    (BitVec.ofNat 12 0) (b2 + 4) (by decide)
  have hLDc0 := ld_spec_gen_within .x17 .x20 envAddr x17old a0
    (BitVec.ofNat 12 0) (b2 + 8) (by decide)
  simp only [sE0] at hLDe0 hLDc0
  have hbne0_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 124)
    e0 a0 (b2 + 12)
  rw [show signExtend13 (BitVec.ofNat 13 124) = BitVec.ofNat 64 124 from by decide,
      show (b2 + 12 : Word) + BitVec.ofNat 64 124 = b2 + 136 from by bv_omega]
    at hbne0_raw
  have hbne0 := cpsBranchWithin_takenStripPure2 hbne0_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hne0 ((sepConj_pure_right _).mp h_rest).2)
  runBlock haddi hLDe0 hLDc0 hbne0

/-- Mismatch at compare pair 1. -/
theorem evm_tload_cmp_exit1_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (heq0 : e0 = a0)
    (hne1 : e1 ≠ a1) :
    cpsTripleWithin 7 b2 (b2 + 136) (evm_tload_cmp_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
       (((.x16)) ↦ᵣ e1) ** (((.x17)) ↦ᵣ a1) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  have haddi := addi_spec_gen_same_within .x14 (ent + 128) (-128 : BitVec 12)
    b2 (by decide)
  rw [add128_addi_neg128] at haddi
  have hLDe0 := ld_spec_gen_within .x16 .x14 ent x16old e0
    (BitVec.ofNat 12 0) (b2 + 4) (by decide)
  have hLDc0 := ld_spec_gen_within .x17 .x20 envAddr x17old a0
    (BitVec.ofNat 12 0) (b2 + 8) (by decide)
  simp only [sE0] at hLDe0 hLDc0
  have hbne0_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 124)
    e0 a0 (b2 + 12)
  rw [show (b2 + 12 : Word) + 4 = b2 + 16 from by bv_omega] at hbne0_raw
  have hbne0 := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq0)
  have hLDe1 := ld_spec_gen_within .x16 .x14 ent e0 e1
    (BitVec.ofNat 12 8) (b2 + 16) (by decide)
  have hLDc1 := ld_spec_gen_within .x17 .x20 envAddr a0 a1
    (BitVec.ofNat 12 8) (b2 + 20) (by decide)
  simp only [sE8] at hLDe1 hLDc1
  have hbne1_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 112)
    e1 a1 (b2 + 24)
  rw [show signExtend13 (BitVec.ofNat 13 112) = BitVec.ofNat 64 112 from by decide,
      show (b2 + 24 : Word) + BitVec.ofNat 64 112 = b2 + 136 from by bv_omega]
    at hbne1_raw
  have hbne1 := cpsBranchWithin_takenStripPure2 hbne1_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hne1 ((sepConj_pure_right _).mp h_rest).2)
  runBlock haddi hLDe0 hLDc0 hbne0 hLDe1 hLDc1 hbne1

/-- Mismatch at compare pair 2. -/
theorem evm_tload_cmp_exit2_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (heq0 : e0 = a0) (heq1 : e1 = a1)
    (hne2 : e2 ≠ a2) :
    cpsTripleWithin 10 b2 (b2 + 136) (evm_tload_cmp_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
       (((.x16)) ↦ᵣ e2) ** (((.x17)) ↦ᵣ a2) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  have haddi := addi_spec_gen_same_within .x14 (ent + 128) (-128 : BitVec 12)
    b2 (by decide)
  rw [add128_addi_neg128] at haddi
  have hLDe0 := ld_spec_gen_within .x16 .x14 ent x16old e0
    (BitVec.ofNat 12 0) (b2 + 4) (by decide)
  have hLDc0 := ld_spec_gen_within .x17 .x20 envAddr x17old a0
    (BitVec.ofNat 12 0) (b2 + 8) (by decide)
  simp only [sE0] at hLDe0 hLDc0
  have hbne0_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 124)
    e0 a0 (b2 + 12)
  rw [show (b2 + 12 : Word) + 4 = b2 + 16 from by bv_omega] at hbne0_raw
  have hbne0 := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq0)
  have hLDe1 := ld_spec_gen_within .x16 .x14 ent e0 e1
    (BitVec.ofNat 12 8) (b2 + 16) (by decide)
  have hLDc1 := ld_spec_gen_within .x17 .x20 envAddr a0 a1
    (BitVec.ofNat 12 8) (b2 + 20) (by decide)
  simp only [sE8] at hLDe1 hLDc1
  have hbne1_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 112)
    e1 a1 (b2 + 24)
  rw [show (b2 + 24 : Word) + 4 = b2 + 28 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq1)
  have hLDe2 := ld_spec_gen_within .x16 .x14 ent e1 e2
    (BitVec.ofNat 12 16) (b2 + 28) (by decide)
  have hLDc2 := ld_spec_gen_within .x17 .x20 envAddr a1 a2
    (BitVec.ofNat 12 16) (b2 + 32) (by decide)
  simp only [sE16] at hLDe2 hLDc2
  have hbne2_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 100)
    e2 a2 (b2 + 36)
  rw [show signExtend13 (BitVec.ofNat 13 100) = BitVec.ofNat 64 100 from by decide,
      show (b2 + 36 : Word) + BitVec.ofNat 64 100 = b2 + 136 from by bv_omega]
    at hbne2_raw
  have hbne2 := cpsBranchWithin_takenStripPure2 hbne2_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hne2 ((sepConj_pure_right _).mp h_rest).2)
  runBlock haddi hLDe0 hLDc0 hbne0 hLDe1 hLDc1 hbne1 hLDe2 hLDc2 hbne2

/-- Mismatch at compare pair 3. -/
theorem evm_tload_cmp_exit3_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (heq0 : e0 = a0) (heq1 : e1 = a1) (heq2 : e2 = a2)
    (hne3 : e3 ≠ a3) :
    cpsTripleWithin 13 b2 (b2 + 136) (evm_tload_cmp_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
       (((.x16)) ↦ᵣ e3) ** (((.x17)) ↦ᵣ a3) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  have haddi := addi_spec_gen_same_within .x14 (ent + 128) (-128 : BitVec 12)
    b2 (by decide)
  rw [add128_addi_neg128] at haddi
  have hLDe0 := ld_spec_gen_within .x16 .x14 ent x16old e0
    (BitVec.ofNat 12 0) (b2 + 4) (by decide)
  have hLDc0 := ld_spec_gen_within .x17 .x20 envAddr x17old a0
    (BitVec.ofNat 12 0) (b2 + 8) (by decide)
  simp only [sE0] at hLDe0 hLDc0
  have hbne0_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 124)
    e0 a0 (b2 + 12)
  rw [show (b2 + 12 : Word) + 4 = b2 + 16 from by bv_omega] at hbne0_raw
  have hbne0 := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq0)
  have hLDe1 := ld_spec_gen_within .x16 .x14 ent e0 e1
    (BitVec.ofNat 12 8) (b2 + 16) (by decide)
  have hLDc1 := ld_spec_gen_within .x17 .x20 envAddr a0 a1
    (BitVec.ofNat 12 8) (b2 + 20) (by decide)
  simp only [sE8] at hLDe1 hLDc1
  have hbne1_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 112)
    e1 a1 (b2 + 24)
  rw [show (b2 + 24 : Word) + 4 = b2 + 28 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq1)
  have hLDe2 := ld_spec_gen_within .x16 .x14 ent e1 e2
    (BitVec.ofNat 12 16) (b2 + 28) (by decide)
  have hLDc2 := ld_spec_gen_within .x17 .x20 envAddr a1 a2
    (BitVec.ofNat 12 16) (b2 + 32) (by decide)
  simp only [sE16] at hLDe2 hLDc2
  have hbne2_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 100)
    e2 a2 (b2 + 36)
  rw [show (b2 + 36 : Word) + 4 = b2 + 40 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq2)
  have hLDe3 := ld_spec_gen_within .x16 .x14 ent e2 e3
    (BitVec.ofNat 12 24) (b2 + 40) (by decide)
  have hLDc3 := ld_spec_gen_within .x17 .x20 envAddr a2 a3
    (BitVec.ofNat 12 24) (b2 + 44) (by decide)
  simp only [sE24] at hLDe3 hLDc3
  have hbne3_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 88)
    e3 a3 (b2 + 48)
  rw [show signExtend13 (BitVec.ofNat 13 88) = BitVec.ofNat 64 88 from by decide,
      show (b2 + 48 : Word) + BitVec.ofNat 64 88 = b2 + 136 from by bv_omega]
    at hbne3_raw
  have hbne3 := cpsBranchWithin_takenStripPure2 hbne3_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hne3 ((sepConj_pure_right _).mp h_rest).2)
  runBlock haddi hLDe0 hLDc0 hbne0 hLDe1 hLDc1 hbne1 hLDe2 hLDc2 hbne2 hLDe3 hLDc3 hbne3

/-- Mismatch at compare pair 4. -/
theorem evm_tload_cmp_exit4_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (heq0 : e0 = a0) (heq1 : e1 = a1) (heq2 : e2 = a2) (heq3 : e3 = a3)
    (hne4 : e4 ≠ k0) :
    cpsTripleWithin 16 b2 (b2 + 136) (evm_tload_cmp_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
       (((.x16)) ↦ᵣ e4) ** (((.x17)) ↦ᵣ k0) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  have haddi := addi_spec_gen_same_within .x14 (ent + 128) (-128 : BitVec 12)
    b2 (by decide)
  rw [add128_addi_neg128] at haddi
  have hLDe0 := ld_spec_gen_within .x16 .x14 ent x16old e0
    (BitVec.ofNat 12 0) (b2 + 4) (by decide)
  have hLDc0 := ld_spec_gen_within .x17 .x20 envAddr x17old a0
    (BitVec.ofNat 12 0) (b2 + 8) (by decide)
  simp only [sE0] at hLDe0 hLDc0
  have hbne0_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 124)
    e0 a0 (b2 + 12)
  rw [show (b2 + 12 : Word) + 4 = b2 + 16 from by bv_omega] at hbne0_raw
  have hbne0 := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq0)
  have hLDe1 := ld_spec_gen_within .x16 .x14 ent e0 e1
    (BitVec.ofNat 12 8) (b2 + 16) (by decide)
  have hLDc1 := ld_spec_gen_within .x17 .x20 envAddr a0 a1
    (BitVec.ofNat 12 8) (b2 + 20) (by decide)
  simp only [sE8] at hLDe1 hLDc1
  have hbne1_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 112)
    e1 a1 (b2 + 24)
  rw [show (b2 + 24 : Word) + 4 = b2 + 28 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq1)
  have hLDe2 := ld_spec_gen_within .x16 .x14 ent e1 e2
    (BitVec.ofNat 12 16) (b2 + 28) (by decide)
  have hLDc2 := ld_spec_gen_within .x17 .x20 envAddr a1 a2
    (BitVec.ofNat 12 16) (b2 + 32) (by decide)
  simp only [sE16] at hLDe2 hLDc2
  have hbne2_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 100)
    e2 a2 (b2 + 36)
  rw [show (b2 + 36 : Word) + 4 = b2 + 40 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq2)
  have hLDe3 := ld_spec_gen_within .x16 .x14 ent e2 e3
    (BitVec.ofNat 12 24) (b2 + 40) (by decide)
  have hLDc3 := ld_spec_gen_within .x17 .x20 envAddr a2 a3
    (BitVec.ofNat 12 24) (b2 + 44) (by decide)
  simp only [sE24] at hLDe3 hLDc3
  have hbne3_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 88)
    e3 a3 (b2 + 48)
  rw [show (b2 + 48 : Word) + 4 = b2 + 52 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_ntakenStripPure2 hbne3_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq3)
  have hLDe4 := ld_spec_gen_within .x16 .x14 ent e3 e4
    (BitVec.ofNat 12 32) (b2 + 52) (by decide)
  have hLDc4 := ld_spec_gen_within .x17 .x12 sp a3 k0
    (BitVec.ofNat 12 0) (b2 + 56) (by decide)
  simp only [sE32, sE0] at hLDe4 hLDc4
  have hbne4_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 76)
    e4 k0 (b2 + 60)
  rw [show signExtend13 (BitVec.ofNat 13 76) = BitVec.ofNat 64 76 from by decide,
      show (b2 + 60 : Word) + BitVec.ofNat 64 76 = b2 + 136 from by bv_omega]
    at hbne4_raw
  have hbne4 := cpsBranchWithin_takenStripPure2 hbne4_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hne4 ((sepConj_pure_right _).mp h_rest).2)
  runBlock haddi hLDe0 hLDc0 hbne0 hLDe1 hLDc1 hbne1 hLDe2 hLDc2 hbne2 hLDe3 hLDc3 hbne3 hLDe4 hLDc4 hbne4

/-- Mismatch at compare pair 5. -/
theorem evm_tload_cmp_exit5_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (heq0 : e0 = a0) (heq1 : e1 = a1) (heq2 : e2 = a2) (heq3 : e3 = a3) (heq4 : e4 = k0)
    (hne5 : e5 ≠ k1) :
    cpsTripleWithin 19 b2 (b2 + 136) (evm_tload_cmp_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
       (((.x16)) ↦ᵣ e5) ** (((.x17)) ↦ᵣ k1) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  have haddi := addi_spec_gen_same_within .x14 (ent + 128) (-128 : BitVec 12)
    b2 (by decide)
  rw [add128_addi_neg128] at haddi
  have hLDe0 := ld_spec_gen_within .x16 .x14 ent x16old e0
    (BitVec.ofNat 12 0) (b2 + 4) (by decide)
  have hLDc0 := ld_spec_gen_within .x17 .x20 envAddr x17old a0
    (BitVec.ofNat 12 0) (b2 + 8) (by decide)
  simp only [sE0] at hLDe0 hLDc0
  have hbne0_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 124)
    e0 a0 (b2 + 12)
  rw [show (b2 + 12 : Word) + 4 = b2 + 16 from by bv_omega] at hbne0_raw
  have hbne0 := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq0)
  have hLDe1 := ld_spec_gen_within .x16 .x14 ent e0 e1
    (BitVec.ofNat 12 8) (b2 + 16) (by decide)
  have hLDc1 := ld_spec_gen_within .x17 .x20 envAddr a0 a1
    (BitVec.ofNat 12 8) (b2 + 20) (by decide)
  simp only [sE8] at hLDe1 hLDc1
  have hbne1_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 112)
    e1 a1 (b2 + 24)
  rw [show (b2 + 24 : Word) + 4 = b2 + 28 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq1)
  have hLDe2 := ld_spec_gen_within .x16 .x14 ent e1 e2
    (BitVec.ofNat 12 16) (b2 + 28) (by decide)
  have hLDc2 := ld_spec_gen_within .x17 .x20 envAddr a1 a2
    (BitVec.ofNat 12 16) (b2 + 32) (by decide)
  simp only [sE16] at hLDe2 hLDc2
  have hbne2_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 100)
    e2 a2 (b2 + 36)
  rw [show (b2 + 36 : Word) + 4 = b2 + 40 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq2)
  have hLDe3 := ld_spec_gen_within .x16 .x14 ent e2 e3
    (BitVec.ofNat 12 24) (b2 + 40) (by decide)
  have hLDc3 := ld_spec_gen_within .x17 .x20 envAddr a2 a3
    (BitVec.ofNat 12 24) (b2 + 44) (by decide)
  simp only [sE24] at hLDe3 hLDc3
  have hbne3_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 88)
    e3 a3 (b2 + 48)
  rw [show (b2 + 48 : Word) + 4 = b2 + 52 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_ntakenStripPure2 hbne3_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq3)
  have hLDe4 := ld_spec_gen_within .x16 .x14 ent e3 e4
    (BitVec.ofNat 12 32) (b2 + 52) (by decide)
  have hLDc4 := ld_spec_gen_within .x17 .x12 sp a3 k0
    (BitVec.ofNat 12 0) (b2 + 56) (by decide)
  simp only [sE32, sE0] at hLDe4 hLDc4
  have hbne4_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 76)
    e4 k0 (b2 + 60)
  rw [show (b2 + 60 : Word) + 4 = b2 + 64 from by bv_omega] at hbne4_raw
  have hbne4 := cpsBranchWithin_ntakenStripPure2 hbne4_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq4)
  have hLDe5 := ld_spec_gen_within .x16 .x14 ent e4 e5
    (BitVec.ofNat 12 40) (b2 + 64) (by decide)
  have hLDc5 := ld_spec_gen_within .x17 .x12 sp k0 k1
    (BitVec.ofNat 12 8) (b2 + 68) (by decide)
  simp only [sE40, sE8] at hLDe5 hLDc5
  have hbne5_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 64)
    e5 k1 (b2 + 72)
  rw [show signExtend13 (BitVec.ofNat 13 64) = BitVec.ofNat 64 64 from by decide,
      show (b2 + 72 : Word) + BitVec.ofNat 64 64 = b2 + 136 from by bv_omega]
    at hbne5_raw
  have hbne5 := cpsBranchWithin_takenStripPure2 hbne5_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hne5 ((sepConj_pure_right _).mp h_rest).2)
  runBlock haddi hLDe0 hLDc0 hbne0 hLDe1 hLDc1 hbne1 hLDe2 hLDc2 hbne2 hLDe3 hLDc3 hbne3 hLDe4 hLDc4 hbne4 hLDe5 hLDc5 hbne5

/-- Mismatch at compare pair 6. -/
theorem evm_tload_cmp_exit6_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (heq0 : e0 = a0) (heq1 : e1 = a1) (heq2 : e2 = a2) (heq3 : e3 = a3) (heq4 : e4 = k0) (heq5 : e5 = k1)
    (hne6 : e6 ≠ k2) :
    cpsTripleWithin 22 b2 (b2 + 136) (evm_tload_cmp_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
       (((.x16)) ↦ᵣ e6) ** (((.x17)) ↦ᵣ k2) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  have haddi := addi_spec_gen_same_within .x14 (ent + 128) (-128 : BitVec 12)
    b2 (by decide)
  rw [add128_addi_neg128] at haddi
  have hLDe0 := ld_spec_gen_within .x16 .x14 ent x16old e0
    (BitVec.ofNat 12 0) (b2 + 4) (by decide)
  have hLDc0 := ld_spec_gen_within .x17 .x20 envAddr x17old a0
    (BitVec.ofNat 12 0) (b2 + 8) (by decide)
  simp only [sE0] at hLDe0 hLDc0
  have hbne0_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 124)
    e0 a0 (b2 + 12)
  rw [show (b2 + 12 : Word) + 4 = b2 + 16 from by bv_omega] at hbne0_raw
  have hbne0 := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq0)
  have hLDe1 := ld_spec_gen_within .x16 .x14 ent e0 e1
    (BitVec.ofNat 12 8) (b2 + 16) (by decide)
  have hLDc1 := ld_spec_gen_within .x17 .x20 envAddr a0 a1
    (BitVec.ofNat 12 8) (b2 + 20) (by decide)
  simp only [sE8] at hLDe1 hLDc1
  have hbne1_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 112)
    e1 a1 (b2 + 24)
  rw [show (b2 + 24 : Word) + 4 = b2 + 28 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq1)
  have hLDe2 := ld_spec_gen_within .x16 .x14 ent e1 e2
    (BitVec.ofNat 12 16) (b2 + 28) (by decide)
  have hLDc2 := ld_spec_gen_within .x17 .x20 envAddr a1 a2
    (BitVec.ofNat 12 16) (b2 + 32) (by decide)
  simp only [sE16] at hLDe2 hLDc2
  have hbne2_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 100)
    e2 a2 (b2 + 36)
  rw [show (b2 + 36 : Word) + 4 = b2 + 40 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq2)
  have hLDe3 := ld_spec_gen_within .x16 .x14 ent e2 e3
    (BitVec.ofNat 12 24) (b2 + 40) (by decide)
  have hLDc3 := ld_spec_gen_within .x17 .x20 envAddr a2 a3
    (BitVec.ofNat 12 24) (b2 + 44) (by decide)
  simp only [sE24] at hLDe3 hLDc3
  have hbne3_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 88)
    e3 a3 (b2 + 48)
  rw [show (b2 + 48 : Word) + 4 = b2 + 52 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_ntakenStripPure2 hbne3_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq3)
  have hLDe4 := ld_spec_gen_within .x16 .x14 ent e3 e4
    (BitVec.ofNat 12 32) (b2 + 52) (by decide)
  have hLDc4 := ld_spec_gen_within .x17 .x12 sp a3 k0
    (BitVec.ofNat 12 0) (b2 + 56) (by decide)
  simp only [sE32, sE0] at hLDe4 hLDc4
  have hbne4_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 76)
    e4 k0 (b2 + 60)
  rw [show (b2 + 60 : Word) + 4 = b2 + 64 from by bv_omega] at hbne4_raw
  have hbne4 := cpsBranchWithin_ntakenStripPure2 hbne4_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq4)
  have hLDe5 := ld_spec_gen_within .x16 .x14 ent e4 e5
    (BitVec.ofNat 12 40) (b2 + 64) (by decide)
  have hLDc5 := ld_spec_gen_within .x17 .x12 sp k0 k1
    (BitVec.ofNat 12 8) (b2 + 68) (by decide)
  simp only [sE40, sE8] at hLDe5 hLDc5
  have hbne5_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 64)
    e5 k1 (b2 + 72)
  rw [show (b2 + 72 : Word) + 4 = b2 + 76 from by bv_omega] at hbne5_raw
  have hbne5 := cpsBranchWithin_ntakenStripPure2 hbne5_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq5)
  have hLDe6 := ld_spec_gen_within .x16 .x14 ent e5 e6
    (BitVec.ofNat 12 48) (b2 + 76) (by decide)
  have hLDc6 := ld_spec_gen_within .x17 .x12 sp k1 k2
    (BitVec.ofNat 12 16) (b2 + 80) (by decide)
  simp only [sE48, sE16] at hLDe6 hLDc6
  have hbne6_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 52)
    e6 k2 (b2 + 84)
  rw [show signExtend13 (BitVec.ofNat 13 52) = BitVec.ofNat 64 52 from by decide,
      show (b2 + 84 : Word) + BitVec.ofNat 64 52 = b2 + 136 from by bv_omega]
    at hbne6_raw
  have hbne6 := cpsBranchWithin_takenStripPure2 hbne6_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hne6 ((sepConj_pure_right _).mp h_rest).2)
  runBlock haddi hLDe0 hLDc0 hbne0 hLDe1 hLDc1 hbne1 hLDe2 hLDc2 hbne2 hLDe3 hLDc3 hbne3 hLDe4 hLDc4 hbne4 hLDe5 hLDc5 hbne5 hLDe6 hLDc6 hbne6

/-- Mismatch at compare pair 7. -/
theorem evm_tload_cmp_exit7_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (heq0 : e0 = a0) (heq1 : e1 = a1) (heq2 : e2 = a2) (heq3 : e3 = a3) (heq4 : e4 = k0) (heq5 : e5 = k1) (heq6 : e6 = k2)
    (hne7 : e7 ≠ k3) :
    cpsTripleWithin 25 b2 (b2 + 136) (evm_tload_cmp_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
       (((.x16)) ↦ᵣ e7) ** (((.x17)) ↦ᵣ k3) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  have haddi := addi_spec_gen_same_within .x14 (ent + 128) (-128 : BitVec 12)
    b2 (by decide)
  rw [add128_addi_neg128] at haddi
  have hLDe0 := ld_spec_gen_within .x16 .x14 ent x16old e0
    (BitVec.ofNat 12 0) (b2 + 4) (by decide)
  have hLDc0 := ld_spec_gen_within .x17 .x20 envAddr x17old a0
    (BitVec.ofNat 12 0) (b2 + 8) (by decide)
  simp only [sE0] at hLDe0 hLDc0
  have hbne0_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 124)
    e0 a0 (b2 + 12)
  rw [show (b2 + 12 : Word) + 4 = b2 + 16 from by bv_omega] at hbne0_raw
  have hbne0 := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq0)
  have hLDe1 := ld_spec_gen_within .x16 .x14 ent e0 e1
    (BitVec.ofNat 12 8) (b2 + 16) (by decide)
  have hLDc1 := ld_spec_gen_within .x17 .x20 envAddr a0 a1
    (BitVec.ofNat 12 8) (b2 + 20) (by decide)
  simp only [sE8] at hLDe1 hLDc1
  have hbne1_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 112)
    e1 a1 (b2 + 24)
  rw [show (b2 + 24 : Word) + 4 = b2 + 28 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq1)
  have hLDe2 := ld_spec_gen_within .x16 .x14 ent e1 e2
    (BitVec.ofNat 12 16) (b2 + 28) (by decide)
  have hLDc2 := ld_spec_gen_within .x17 .x20 envAddr a1 a2
    (BitVec.ofNat 12 16) (b2 + 32) (by decide)
  simp only [sE16] at hLDe2 hLDc2
  have hbne2_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 100)
    e2 a2 (b2 + 36)
  rw [show (b2 + 36 : Word) + 4 = b2 + 40 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq2)
  have hLDe3 := ld_spec_gen_within .x16 .x14 ent e2 e3
    (BitVec.ofNat 12 24) (b2 + 40) (by decide)
  have hLDc3 := ld_spec_gen_within .x17 .x20 envAddr a2 a3
    (BitVec.ofNat 12 24) (b2 + 44) (by decide)
  simp only [sE24] at hLDe3 hLDc3
  have hbne3_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 88)
    e3 a3 (b2 + 48)
  rw [show (b2 + 48 : Word) + 4 = b2 + 52 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_ntakenStripPure2 hbne3_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq3)
  have hLDe4 := ld_spec_gen_within .x16 .x14 ent e3 e4
    (BitVec.ofNat 12 32) (b2 + 52) (by decide)
  have hLDc4 := ld_spec_gen_within .x17 .x12 sp a3 k0
    (BitVec.ofNat 12 0) (b2 + 56) (by decide)
  simp only [sE32, sE0] at hLDe4 hLDc4
  have hbne4_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 76)
    e4 k0 (b2 + 60)
  rw [show (b2 + 60 : Word) + 4 = b2 + 64 from by bv_omega] at hbne4_raw
  have hbne4 := cpsBranchWithin_ntakenStripPure2 hbne4_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq4)
  have hLDe5 := ld_spec_gen_within .x16 .x14 ent e4 e5
    (BitVec.ofNat 12 40) (b2 + 64) (by decide)
  have hLDc5 := ld_spec_gen_within .x17 .x12 sp k0 k1
    (BitVec.ofNat 12 8) (b2 + 68) (by decide)
  simp only [sE40, sE8] at hLDe5 hLDc5
  have hbne5_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 64)
    e5 k1 (b2 + 72)
  rw [show (b2 + 72 : Word) + 4 = b2 + 76 from by bv_omega] at hbne5_raw
  have hbne5 := cpsBranchWithin_ntakenStripPure2 hbne5_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq5)
  have hLDe6 := ld_spec_gen_within .x16 .x14 ent e5 e6
    (BitVec.ofNat 12 48) (b2 + 76) (by decide)
  have hLDc6 := ld_spec_gen_within .x17 .x12 sp k1 k2
    (BitVec.ofNat 12 16) (b2 + 80) (by decide)
  simp only [sE48, sE16] at hLDe6 hLDc6
  have hbne6_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 52)
    e6 k2 (b2 + 84)
  rw [show (b2 + 84 : Word) + 4 = b2 + 88 from by bv_omega] at hbne6_raw
  have hbne6 := cpsBranchWithin_ntakenStripPure2 hbne6_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 heq6)
  have hLDe7 := ld_spec_gen_within .x16 .x14 ent e6 e7
    (BitVec.ofNat 12 56) (b2 + 88) (by decide)
  have hLDc7 := ld_spec_gen_within .x17 .x12 sp k2 k3
    (BitVec.ofNat 12 24) (b2 + 92) (by decide)
  simp only [sE56, sE24] at hLDe7 hLDc7
  have hbne7_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 40)
    e7 k3 (b2 + 96)
  rw [show signExtend13 (BitVec.ofNat 13 40) = BitVec.ofNat 64 40 from by decide,
      show (b2 + 96 : Word) + BitVec.ofNat 64 40 = b2 + 136 from by bv_omega]
    at hbne7_raw
  have hbne7 := cpsBranchWithin_takenStripPure2 hbne7_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hne7 ((sepConj_pure_right _).mp h_rest).2)
  runBlock haddi hLDe0 hLDc0 hbne0 hLDe1 hLDc1 hbne1 hLDe2 hLDc2 hbne2 hLDe3 hLDc3 hbne3 hLDe4 hLDc4 hbne4 hLDe5 hLDc5 hbne5 hLDe6 hLDc6 hbne6 hLDe7 hLDc7 hbne7

/-- All eight compare pairs equal: the block falls through to the copy arm
    (loop-slice offset +100) with `x14` on the matched entry. -/
theorem evm_tload_cmp_pass_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 : Word) :
    cpsTripleWithin 25 b2 (b2 + 100) (evm_tload_cmp_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ a0) ** ((ent + 8) ↦ₘ a1) **
       ((ent + 16) ↦ₘ a2) ** ((ent + 24) ↦ₘ a3) **
       ((ent + 32) ↦ₘ k0) ** ((ent + 40) ↦ₘ k1) **
       ((ent + 48) ↦ₘ k2) ** ((ent + 56) ↦ₘ k3))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
       (((.x16)) ↦ᵣ k3) ** (((.x17)) ↦ᵣ k3) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ a0) ** ((ent + 8) ↦ₘ a1) **
       ((ent + 16) ↦ₘ a2) ** ((ent + 24) ↦ₘ a3) **
       ((ent + 32) ↦ₘ k0) ** ((ent + 40) ↦ₘ k1) **
       ((ent + 48) ↦ₘ k2) ** ((ent + 56) ↦ₘ k3)) := by
  have haddi := addi_spec_gen_same_within .x14 (ent + 128) (-128 : BitVec 12)
    b2 (by decide)
  rw [add128_addi_neg128] at haddi
  have hLDe0 := ld_spec_gen_within .x16 .x14 ent x16old a0
    (BitVec.ofNat 12 0) (b2 + 4) (by decide)
  have hLDc0 := ld_spec_gen_within .x17 .x20 envAddr x17old a0
    (BitVec.ofNat 12 0) (b2 + 8) (by decide)
  simp only [sE0] at hLDe0 hLDc0
  have hbne0_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 124)
    a0 a0 (b2 + 12)
  rw [show (b2 + 12 : Word) + 4 = b2 + 16 from by bv_omega] at hbne0_raw
  have hbne0 := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 rfl)
  have hLDe1 := ld_spec_gen_within .x16 .x14 ent a0 a1
    (BitVec.ofNat 12 8) (b2 + 16) (by decide)
  have hLDc1 := ld_spec_gen_within .x17 .x20 envAddr a0 a1
    (BitVec.ofNat 12 8) (b2 + 20) (by decide)
  simp only [sE8] at hLDe1 hLDc1
  have hbne1_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 112)
    a1 a1 (b2 + 24)
  rw [show (b2 + 24 : Word) + 4 = b2 + 28 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 rfl)
  have hLDe2 := ld_spec_gen_within .x16 .x14 ent a1 a2
    (BitVec.ofNat 12 16) (b2 + 28) (by decide)
  have hLDc2 := ld_spec_gen_within .x17 .x20 envAddr a1 a2
    (BitVec.ofNat 12 16) (b2 + 32) (by decide)
  simp only [sE16] at hLDe2 hLDc2
  have hbne2_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 100)
    a2 a2 (b2 + 36)
  rw [show (b2 + 36 : Word) + 4 = b2 + 40 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 rfl)
  have hLDe3 := ld_spec_gen_within .x16 .x14 ent a2 a3
    (BitVec.ofNat 12 24) (b2 + 40) (by decide)
  have hLDc3 := ld_spec_gen_within .x17 .x20 envAddr a2 a3
    (BitVec.ofNat 12 24) (b2 + 44) (by decide)
  simp only [sE24] at hLDe3 hLDc3
  have hbne3_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 88)
    a3 a3 (b2 + 48)
  rw [show (b2 + 48 : Word) + 4 = b2 + 52 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_ntakenStripPure2 hbne3_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 rfl)
  have hLDe4 := ld_spec_gen_within .x16 .x14 ent a3 k0
    (BitVec.ofNat 12 32) (b2 + 52) (by decide)
  have hLDc4 := ld_spec_gen_within .x17 .x12 sp a3 k0
    (BitVec.ofNat 12 0) (b2 + 56) (by decide)
  simp only [sE32, sE0] at hLDe4 hLDc4
  have hbne4_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 76)
    k0 k0 (b2 + 60)
  rw [show (b2 + 60 : Word) + 4 = b2 + 64 from by bv_omega] at hbne4_raw
  have hbne4 := cpsBranchWithin_ntakenStripPure2 hbne4_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 rfl)
  have hLDe5 := ld_spec_gen_within .x16 .x14 ent k0 k1
    (BitVec.ofNat 12 40) (b2 + 64) (by decide)
  have hLDc5 := ld_spec_gen_within .x17 .x12 sp k0 k1
    (BitVec.ofNat 12 8) (b2 + 68) (by decide)
  simp only [sE40, sE8] at hLDe5 hLDc5
  have hbne5_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 64)
    k1 k1 (b2 + 72)
  rw [show (b2 + 72 : Word) + 4 = b2 + 76 from by bv_omega] at hbne5_raw
  have hbne5 := cpsBranchWithin_ntakenStripPure2 hbne5_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 rfl)
  have hLDe6 := ld_spec_gen_within .x16 .x14 ent k1 k2
    (BitVec.ofNat 12 48) (b2 + 76) (by decide)
  have hLDc6 := ld_spec_gen_within .x17 .x12 sp k1 k2
    (BitVec.ofNat 12 16) (b2 + 80) (by decide)
  simp only [sE48, sE16] at hLDe6 hLDc6
  have hbne6_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 52)
    k2 k2 (b2 + 84)
  rw [show (b2 + 84 : Word) + 4 = b2 + 88 from by bv_omega] at hbne6_raw
  have hbne6 := cpsBranchWithin_ntakenStripPure2 hbne6_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 rfl)
  have hLDe7 := ld_spec_gen_within .x16 .x14 ent k2 k3
    (BitVec.ofNat 12 56) (b2 + 88) (by decide)
  have hLDc7 := ld_spec_gen_within .x17 .x12 sp k2 k3
    (BitVec.ofNat 12 24) (b2 + 92) (by decide)
  simp only [sE56, sE24] at hLDe7 hLDc7
  have hbne7_raw := bne_spec_gen_within .x16 .x17 (BitVec.ofNat 13 40)
    k3 k3 (b2 + 96)
  rw [show (b2 + 96 : Word) + 4 = b2 + 100 from by bv_omega] at hbne7_raw
  have hbne7 := cpsBranchWithin_ntakenStripPure2 hbne7_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 rfl)
  runBlock haddi hLDe0 hLDc0 hbne0 hLDe1 hLDc1 hbne1 hLDe2 hLDc2 hbne2 hLDe3 hLDc3 hbne3 hLDe4 hLDc4 hbne4 hLDe5 hLDc5 hbne5 hLDe6 hLDc6 hbne6 hLDe7 hLDc7 hbne7


/-- Merged mismatch exit of the compare block: SOME compare pair differs
    (word-level `(addrHash, slotKey)` inequality bridged to limbs by the
    caller). Exits to the decrement block with `x14` on the entry, `x15`
    untouched, scratch `x16`/`x17` clobbered, memory unchanged. -/
theorem evm_tload_cmp_mismatch_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (hne : ¬(e0 = a0 ∧ e1 = a1 ∧ e2 = a2 ∧ e3 = a3 ∧
             e4 = k0 ∧ e5 = k1 ∧ e6 = k2 ∧ e7 = k3)) :
    cpsTripleWithin 25 b2 (b2 + 136) (evm_tload_cmp_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
       regOwn .x16 ** regOwn .x17 **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  by_cases h0 : e0 = a0
  case neg =>
    exact cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => hp) sepConj_own2_after3
        (evm_tload_cmp_exit0_spec_within b2 ent envAddr sp x16old x17old
          a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 h0))
  case pos =>
    by_cases h1 : e1 = a1
    case neg =>
      exact cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => hp) sepConj_own2_after3
          (evm_tload_cmp_exit1_spec_within b2 ent envAddr sp x16old x17old
            a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 h0 h1))
    case pos =>
      by_cases h2 : e2 = a2
      case neg =>
        exact cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun h hp => hp) sepConj_own2_after3
            (evm_tload_cmp_exit2_spec_within b2 ent envAddr sp x16old x17old
              a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 h0 h1 h2))
      case pos =>
        by_cases h3 : e3 = a3
        case neg =>
          exact cpsTripleWithin_mono_nSteps (by omega)
            (cpsTripleWithin_weaken (fun h hp => hp) sepConj_own2_after3
              (evm_tload_cmp_exit3_spec_within b2 ent envAddr sp x16old x17old
                a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 h0 h1 h2 h3))
        case pos =>
          by_cases h4 : e4 = k0
          case neg =>
            exact cpsTripleWithin_mono_nSteps (by omega)
              (cpsTripleWithin_weaken (fun h hp => hp) sepConj_own2_after3
                (evm_tload_cmp_exit4_spec_within b2 ent envAddr sp x16old x17old
                  a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 h0 h1 h2 h3 h4))
          case pos =>
            by_cases h5 : e5 = k1
            case neg =>
              exact cpsTripleWithin_mono_nSteps (by omega)
                (cpsTripleWithin_weaken (fun h hp => hp) sepConj_own2_after3
                  (evm_tload_cmp_exit5_spec_within b2 ent envAddr sp x16old x17old
                    a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 h0 h1 h2 h3 h4 h5))
            case pos =>
              by_cases h6 : e6 = k2
              case neg =>
                exact cpsTripleWithin_mono_nSteps (by omega)
                  (cpsTripleWithin_weaken (fun h hp => hp) sepConj_own2_after3
                    (evm_tload_cmp_exit6_spec_within b2 ent envAddr sp x16old x17old
                      a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 h0 h1 h2 h3 h4 h5 h6))
              case pos =>
                by_cases h7 : e7 = k3
                case neg =>
                  exact cpsTripleWithin_mono_nSteps (by omega)
                    (cpsTripleWithin_weaken (fun h hp => hp) sepConj_own2_after3
                      (evm_tload_cmp_exit7_spec_within b2 ent envAddr sp x16old x17old
                        a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 h0 h1 h2 h3 h4 h5 h6 h7))
                case pos =>
                exact absurd ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ hne


/-! ## Copy arm and decrement/zero tail -/


end Transient
end EvmAsm.Evm64
