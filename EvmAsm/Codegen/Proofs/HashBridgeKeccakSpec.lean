/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSpec

  Proof-only correspondence facts for the inline Keccak bridge.  The emitted
  `zkvmKeccak256_prog` remains the flat 69-instruction Program in
  `HashBridgeProg`; this module supplies the concrete CSRS seam and the pure
  padding/absorption facts needed to structure its proof.  The loop-framing
  toolkit now has the three relevant shapes: `countdownLoop_spec`, the
  count-up sibling `upLoop_spec`, and this signed `BLT` companion
  `signedCountdownLoop_spec`.

  The eventual wrapper theorem quantifies over the ABI envelope documented at
  `docs/4ch8f-top-spec.md:55` and §2a (`MAX_INPUT_BYTES = 0x37FFFFF8`).  That
  envelope is a resource fact, not a smaller proof convenience cap; the fuel
  bound is derived from the input length.
-/

import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Rv64.SAsm.KeccakStep
import EvmAsm.Rv64.SAsm.AbiFrameLoop
import EvmAsm.Rv64.SAsm.AbiFrameLoopBottom
import EvmAsm.Rv64.SAsm.Flatten
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef
open Stmt

abbrev KeccakLoopInv :=
  Nat → RegFile → List (BitVec 8) → Assertion → Prop

/-! ## Proof-only wrapper shape

The flat wrapper cannot be expressed with `Stmt.callRegS`: that node emits a
`JALR`, while the guest has the two Keccak `CSRS 0x800` instructions inline.
The decomposition below therefore keeps every emitted instruction in the same
raw block, but gives the three runtime loops structured boundaries and leaves
their invariants as explicit arguments.  In particular, the block-loop
invariant below names the sponge state after `k` full input blocks; it is the
fact that the eventual VC proof must preserve, not a proof-convenience size
cap.
-/

def keccakAbsorbBlocks (input : Bytes) (k : Nat) : List Bytes :=
  chunkBytes keccakRateBytes (input.take (keccakRateBytes * k))

def keccakStateBytes (st : List (BitVec 64)) : List (BitVec 8) :=
  st.flatMap dwordBytes

def keccakAbsorbedState (input : Bytes) (k : Nat) : List (BitVec 8) :=
  keccakStateBytes
    (keccakAbsorb (List.replicate 25 (0 : BitVec 64))
      (keccakAbsorbBlocks input k))

/-- Runtime fuel derived from the input length: one slot beyond the maximum
    number of complete rate blocks, so the final failing header check is
    representable.  This is not a proof-convenience input cap. -/
def keccakAbsorbFuel (len : Nat) : Nat := len / keccakRateBytes + 1

/-- The remainder loop's fuel is exactly the input remainder after complete
    rate blocks; the enclosing `when` makes the zero case unreachable. -/
def keccakRemainderFuel (len : Nat) : Nat := len % keccakRateBytes

private theorem word_ofNat_slt_iff {i j : Nat} (hi : i < 2 ^ 63) (hj : j < 2 ^ 63) :
    BitVec.slt (BitVec.ofNat 64 i) (BitVec.ofNat 64 j) ↔ i < j := by
  have hiNat : (BitVec.ofNat 64 i).toNat = i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hjNat : (BitVec.ofNat 64 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hi' : (BitVec.ofNat 64 i).toInt = i := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hiNat]; omega), hiNat]
  have hj' : (BitVec.ofNat 64 j).toInt = j := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hjNat]; omega), hjNat]
  simp only [BitVec.slt, hi', hj', decide_eq_true_eq]
  omega

/-! ### The outer loop's direct CPS shape

`countdownLoop_spec` is the reusable BEQ-counter form used by the inline
bottom-test loops below.  The outer loop is the one deliberate variation in
the emitted wrapper: it is a signed `BLT remaining, rate, exit`, followed by a
136-byte decrement and a `JAL` back-edge.  This companion keeps that variation
at the same register-agnostic `cpsTripleWithin` level.  Its only arithmetic
side condition is the signed-comparison envelope needed to justify the RV64
`BLT`; it is not an additional input-size cap.  At the wrapper call site,
`remaining` is derived from the ABI resource envelope
`MAX_INPUT_BYTES = 0x37FFFFF8`, so `step * N + rem` is at most that bound and
therefore lies inside the signed range; the envelope is a resource fact, not
a smaller proof-domain assumption.  The caller supplies that ABI envelope,
and the fuel is still derived from `len`.
-/

theorem signedCountdownLoop_spec
    (cr : CodeReq) (hdr exitAddr : Word) (ctr lim : Reg) (exitOff : BitVec 13)
    (bodyStep step N rem : Nat) (inv : Nat → Assertion)
    (_hctr_ne : ctr ≠ .x0) (_hctr_lim_ne : ctr ≠ lim)
    (hrem : rem < step) (hstepBound : step < 2 ^ 63)
    (hNbound : step * N + rem < 2 ^ 63)
    (hexit : hdr + signExtend13 exitOff = exitAddr)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hguardMem : ∀ a i,
      CodeReq.singleton hdr (.BLT ctr lim exitOff) a = some i → cr a = some i)
    (hbody : ∀ n, n < N →
      cpsTripleWithin bodyStep (hdr + 4) hdr cr
        ((ctr ↦ᵣ BitVec.ofNat 64 (step * (n + 1) + rem))
          ** (lim ↦ᵣ BitVec.ofNat 64 step) ** inv (n + 1))
        ((ctr ↦ᵣ BitVec.ofNat 64 (step * n + rem))
          ** (lim ↦ᵣ BitVec.ofNat 64 step) ** inv n)) :
    cpsTripleWithin (N * (bodyStep + 1) + 1) hdr exitAddr cr
      ((ctr ↦ᵣ BitVec.ofNat 64 (step * N + rem))
        ** (lim ↦ᵣ BitVec.ofNat 64 step) ** inv N)
      ((ctr ↦ᵣ BitVec.ofNat 64 rem)
        ** (lim ↦ᵣ BitVec.ofNat 64 step) ** inv 0) := by
  suffices h : ∀ n, n ≤ N →
      cpsTripleWithin (n * (bodyStep + 1) + 1) hdr exitAddr cr
        ((ctr ↦ᵣ BitVec.ofNat 64 (step * n + rem))
          ** (lim ↦ᵣ BitVec.ofNat 64 step) ** inv n)
        ((ctr ↦ᵣ BitVec.ofNat 64 rem)
          ** (lim ↦ᵣ BitVec.ofNat 64 step) ** inv 0) from
    h N (Nat.le_refl N)
  intro n
  induction n with
  | zero =>
    intro _
    have hblt := blt_spec_gen_within ctr lim exitOff
      (BitVec.ofNat 64 rem) (BitVec.ofNat 64 step) hdr
    rw [hexit] at hblt
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv 0) (hpcFree 0) hblt)
    have hlt := (word_ofNat_slt_iff (by omega) hstepBound).2 hrem
    have htaken := cpsBranchWithin_takenPath hbr
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact ((sepConj_pure_right _).1 h_pure).2 hlt)
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add]
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by
        have hq1 := sepConj_mono_left
          (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
        xperm_hyp hq1) htaken
  | succ k ih =>
    intro hk
    have hkN : k < N := Nat.lt_of_succ_le hk
    have hkn_le : k + 1 ≤ N := Nat.succ_le_iff.mp hk
    have hcurr : step * (k + 1) + rem < 2 ^ 63 := by
      have hmono : step * (k + 1) ≤ step * N :=
        Nat.mul_le_mul_left step hkn_le
      omega
    have hge : step ≤ step * (k + 1) + rem := by
      have hstep_pos : 0 < step := by omega
      have hmul : step ≤ step * (k + 1) := by
        rw [Nat.mul_succ]
        omega
      omega
    have hblt := blt_spec_gen_within ctr lim exitOff
      (BitVec.ofNat 64 (step * (k + 1) + rem))
      (BitVec.ofNat 64 step) hdr
    rw [hexit] at hblt
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv (k + 1)) (hpcFree (k + 1)) hblt)
    have hnlt : ¬BitVec.slt
        (BitVec.ofNat 64 (step * (k + 1) + rem))
        (BitVec.ofNat 64 step) := by
      intro hlt'
      exact (Nat.not_lt_of_ge hge)
        ((word_ofNat_slt_iff hcurr hstepBound).1 hlt')
    have hguard := cpsBranchWithin_ntakenPath hbr
      (fun hp hQt => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
        exact hnlt ((sepConj_pure_right _).1 h_pure).2)
    have hbodyk := hbody k hkN
    have ihk := ih (Nat.le_of_lt hkN)
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left
          (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2) hguard hbodyk
    have s2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) s1 ihk
    have hstep' : (k + 1) * (bodyStep + 1) + 1
        = 1 + bodyStep + (k * (bodyStep + 1) + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hstep']
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s2

/-- **Reload-header countdown** for loops whose back edge lands on a
    stride-reload `LI lim, step` rather than on the `BLT` itself.

    Geometry (one iteration):
    ```
      hdr:     LI lim, step          -- re-establish stride (body may clobber lim)
      hdr+4:   BLT ctr, lim, exit    -- guard
      hdr+8:   <body ... JAL hdr>    -- body returns to hdr; lim NOT preserved
    ```
    `hbody` runs from `hdr+8` back to `hdr`.  Body **post** keeps only `ctr` and
    `inv` — lim is allowed to be clobbered (as in `zkvm_keccak256`, where CSRS
    owns x29=lim and the next LI reloads 136).  Exit target is measured from the
    `BLT` at `hdr+4`.

    Why this exists alongside `signedCountdownLoop_spec`: the emitted
    `zkvm_keccak256` outer absorb loop has JAL target = LI (e.g. guest
    `0x8000368c`) while BLT sits four bytes later (`0x80003690`).  The BLT-header
    lemma requires the body to return to `hdr=BLT` and therefore **cannot be
    discharged for that loop**.  Do not modify the BLT-header lemma. -/
theorem signedCountdownLoop_reload_spec
    (cr : CodeReq) (hdr exitAddr : Word) (ctr lim : Reg) (exitOff : BitVec 13)
    (bodyStep step N rem : Nat) (inv : Nat → Assertion)
    (_hctr_ne : ctr ≠ .x0) (_hctr_lim_ne : ctr ≠ lim) (hlim_ne : lim ≠ .x0)
    (hrem : rem < step) (hstepbound : step < 2 ^ 63)
    (hNbound : step * N + rem < 2 ^ 63)
    (hexit : (hdr + 4) + signExtend13 exitOff = exitAddr)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hliMem : ∀ a i,
      CodeReq.singleton hdr (.LI lim (BitVec.ofNat 64 step)) a = some i →
        cr a = some i)
    (hguardMem : ∀ a i,
      CodeReq.singleton (hdr + 4) (.BLT ctr lim exitOff) a = some i →
        cr a = some i)
    (hbody : ∀ n, n < N →
      cpsTripleWithin bodyStep (hdr + 8) hdr cr
        ((ctr ↦ᵣ BitVec.ofNat 64 (step * (n + 1) + rem))
          ** (lim ↦ᵣ BitVec.ofNat 64 step) ** inv (n + 1))
        -- body may clobber lim; post only requires ownership for the next LI
        ((ctr ↦ᵣ BitVec.ofNat 64 (step * n + rem))
          ** (regOwn lim) ** inv n)) :
    cpsTripleWithin (N * (bodyStep + 2) + 2) hdr exitAddr cr
      ((ctr ↦ᵣ BitVec.ofNat 64 (step * N + rem)) ** (regOwn lim) ** inv N)
      ((ctr ↦ᵣ BitVec.ofNat 64 rem)
        ** (lim ↦ᵣ BitVec.ofNat 64 step) ** inv 0) := by
  have hpc_blt_fall : (hdr + 4 : Word) + 4 = hdr + 8 := by
    rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]
  have hLI_own (F : Assertion) (hF : F.pcFree) :
      cpsTripleWithin 1 hdr (hdr + 4) cr
        ((regOwn lim) ** F) ((lim ↦ᵣ BitVec.ofNat 64 step) ** F) := by
    have hsingle : ∀ vOld,
        cpsTripleWithin 1 hdr (hdr + 4) cr
          (lim ↦ᵣ vOld) (lim ↦ᵣ BitVec.ofNat 64 step) := fun vOld =>
      cpsTripleWithin_extend_code hliMem
        (li_spec_gen_within lim vOld (BitVec.ofNat 64 step) hdr hlim_ne)
    have hown : cpsTripleWithin 1 hdr (hdr + 4) cr
        (regOwn lim) (lim ↦ᵣ BitVec.ofNat 64 step) :=
      cpsTripleWithin_of_forall_regIs_to_regOwn_single hsingle
    exact cpsTripleWithin_frameR F hF hown
  suffices h : ∀ n, n ≤ N →
      cpsTripleWithin (n * (bodyStep + 2) + 2) hdr exitAddr cr
        ((ctr ↦ᵣ BitVec.ofNat 64 (step * n + rem)) ** (regOwn lim) ** inv n)
        ((ctr ↦ᵣ BitVec.ofNat 64 rem)
          ** (lim ↦ᵣ BitVec.ofNat 64 step) ** inv 0) from
    h N (Nat.le_refl N)
  intro n
  induction n with
  | zero =>
    intro _
    have cLI := hLI_own ((ctr ↦ᵣ BitVec.ofNat 64 rem) ** inv 0)
      (pcFree_sepConj (by pcFree) (hpcFree 0))
    have hblt := blt_spec_gen_within ctr lim exitOff
      (BitVec.ofNat 64 rem) (BitVec.ofNat 64 step) (hdr + 4)
    rw [hexit] at hblt
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv 0) (hpcFree 0) hblt)
    have hlt := (word_ofNat_slt_iff (by omega) hstepbound).2 hrem
    have htaken := cpsBranchWithin_takenPath hbr
      (fun _h hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact ((sepConj_pure_right _).1 h_pure).2 hlt)
    have htakenW : cpsTripleWithin 1 (hdr + 4) exitAddr cr
        ((ctr ↦ᵣ BitVec.ofNat 64 rem) **
          (lim ↦ᵣ BitVec.ofNat 64 step) ** inv 0)
        ((ctr ↦ᵣ BitVec.ofNat 64 rem) **
          (lim ↦ᵣ BitVec.ofNat 64 step) ** inv 0) := by
      refine cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hq => by
          have hq1 := sepConj_mono_left
            (sepConj_mono_right
              (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
          xperm_hyp hq1) htaken
    have s := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) cLI htakenW
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add] at s ⊢
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) s
  | succ k ih =>
    intro hk
    have hkN : k < N := Nat.lt_of_succ_le hk
    have hkn_le : k + 1 ≤ N := Nat.succ_le_iff.mp hk
    have hcurr : step * (k + 1) + rem < 2 ^ 63 := by
      have hmono : step * (k + 1) ≤ step * N := Nat.mul_le_mul_left step hkn_le
      omega
    have hge : step ≤ step * (k + 1) + rem := by
      have hmul : step ≤ step * (k + 1) := by rw [Nat.mul_succ]; omega
      omega
    have cLI := hLI_own
      ((ctr ↦ᵣ BitVec.ofNat 64 (step * (k + 1) + rem)) ** inv (k + 1))
      (pcFree_sepConj (by pcFree) (hpcFree (k + 1)))
    have hblt := blt_spec_gen_within ctr lim exitOff
      (BitVec.ofNat 64 (step * (k + 1) + rem))
      (BitVec.ofNat 64 step) (hdr + 4)
    rw [hexit] at hblt
    have hbr := cpsBranchWithin_extend_code hguardMem
      (cpsBranchWithin_frameR (inv (k + 1)) (hpcFree (k + 1)) hblt)
    have hnlt : ¬BitVec.slt
        (BitVec.ofNat 64 (step * (k + 1) + rem))
        (BitVec.ofNat 64 step) := by
      intro hlt'
      exact (Nat.not_lt_of_ge hge)
        ((word_ofNat_slt_iff hcurr hstepbound).1 hlt')
    have hguard0 := cpsBranchWithin_ntakenPath hbr
      (fun _h hQt => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
        exact hnlt ((sepConj_pure_right _).1 h_pure).2)
    have hguardW : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
        ((ctr ↦ᵣ BitVec.ofNat 64 (step * (k + 1) + rem)) **
          (lim ↦ᵣ BitVec.ofNat 64 step) ** inv (k + 1))
        ((ctr ↦ᵣ BitVec.ofNat 64 (step * (k + 1) + rem)) **
          (lim ↦ᵣ BitVec.ofNat 64 step) ** inv (k + 1)) := by
      have h0 : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
          (((ctr ↦ᵣ BitVec.ofNat 64 (step * (k + 1) + rem)) **
              lim ↦ᵣ BitVec.ofNat 64 step) ** inv (k + 1))
          ((((ctr ↦ᵣ BitVec.ofNat 64 (step * (k + 1) + rem)) **
                (lim ↦ᵣ BitVec.ofNat 64 step) **
                  ⌜¬(BitVec.ofNat 64 (step * (k + 1) + rem)).slt
                    (BitVec.ofNat 64 step) = true⌝) **
            inv (k + 1))) := by
        convert hguard0 using 1
        exact hpc_blt_fall.symm
      refine cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hq => by
          have hq1 := sepConj_mono_left
            (sepConj_mono_right
              (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
          xperm_hyp hq1) h0
    have hbodyk := hbody k hkN
    have ihk := ih (Nat.le_of_lt hkN)
    have s1 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) cLI hguardW
    have s2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) s1 hbodyk
    have s3 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) s2 ihk
    have hstep' : (k + 1) * (bodyStep + 2) + 2
        = 1 + 1 + bodyStep + (k * (bodyStep + 2) + 2) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [hstep']
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s3

/- The two inner loops use the existing register-agnostic countdown abstraction;
   these wrappers make their fixed emitted counts explicit without changing the
   flat program.  The caller supplies the per-iteration body triple and the
   enclosing `CodeReq` membership, so the loop proof remains proof-only. -/

theorem keccakDwordLoop_spec
    (cr : CodeReq) (hdr : Word) (inv : Nat → Assertion)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hguardMem : ∀ a i,
      CodeReq.singleton (hdr + BitVec.ofNat 64 28)
        (.BNE .x31 .x0 (-28 : BitVec 13)) a = some i → cr a = some i)
    (hbody : ∀ n, n < 17 →
      cpsTripleWithin 7 hdr (hdr + BitVec.ofNat 64 28) cr
        ((.x31 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) ** inv (n + 1))
        ((.x31 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) ** inv n)) :
    cpsTripleWithin (17 * 8) hdr (hdr + BitVec.ofNat 64 32) cr
      ((.x31 ↦ᵣ BitVec.ofNat 64 17) ** (.x0 ↦ᵣ (0 : Word)) ** inv 17)
      ((.x31 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) ** inv 0) := by
  have hloop := countdownLoopBottom_spec cr hdr (hdr + BitVec.ofNat 64 28) .x31
    (-28 : BitVec 13) 7 17 inv (by decide) (by decide) (by decide)
    (by
      rw [show signExtend13 (-28 : BitVec 13) = (-28 : Word) by decide]
      bv_omega) hpcFree (by simpa using hguardMem) hbody
  rw [show 17 * (7 + 1) = 17 * 8 by decide,
    show hdr + BitVec.ofNat 64 28 + 4 = hdr + BitVec.ofNat 64 32 by bv_omega] at hloop
  exact hloop

theorem keccakRemainderLoop_spec
    (cr : CodeReq) (hdr : Word) (rem : Nat) (inv : Nat → Assertion)
    (hrem_pos : 1 ≤ rem) (hrem_bound : rem < 2 ^ 64)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hguardMem : ∀ a i,
      CodeReq.singleton (hdr + BitVec.ofNat 64 28)
        (.BNE .x9 .x0 (-28 : BitVec 13)) a = some i → cr a = some i)
    (hbody : ∀ n, n < rem →
      cpsTripleWithin 7 hdr (hdr + BitVec.ofNat 64 28) cr
        ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) ** inv (n + 1))
        ((.x9 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) ** inv n)) :
    cpsTripleWithin (rem * 8) hdr (hdr + BitVec.ofNat 64 32) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) ** inv rem)
      ((.x9 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) ** inv 0) := by
  have hloop := countdownLoopBottom_spec cr hdr (hdr + BitVec.ofNat 64 28) .x9
    (-28 : BitVec 13) 7 rem inv (by decide) hrem_pos hrem_bound
    (by
      rw [show signExtend13 (-28 : BitVec 13) = (-28 : Word) by decide]
      bv_omega) hpcFree (by simpa using hguardMem) hbody
  rw [show rem * (7 + 1) = rem * 8 by omega,
    show hdr + BitVec.ofNat 64 28 + 4 = hdr + BitVec.ofNat 64 32 by bv_omega] at hloop
  exact hloop

/-- The outer-loop relation after `k` complete 136-byte blocks.  The scratch
    bytes are the concrete 25-lane sponge state, while `x20`/`x9` identify the
    unconsumed input suffix.  The output atom is carried in the ambient
    assertion and is untouched until the final `blockAt` copy. -/
def keccakAbsorbInv (inputBase scratchBase outputBase : Word)
    (input output : Bytes) (len : Nat) : KeccakLoopInv :=
  fun k rf ws A =>
    k ≤ len / keccakRateBytes ∧
    input.length = len ∧
    rf.get .x8 = scratchBase ∧
    rf.get .x9 = BitVec.ofNat 64 (len - keccakRateBytes * k) ∧
    rf.get .x20 = inputBase + BitVec.ofNat 64 (keccakRateBytes * k) ∧
    rf.get .x29 = BitVec.ofNat 64 keccakRateBytes ∧
    ws = keccakAbsorbedState input k ∧
    ws.length = 200 ∧
    A = bytesRegion outputBase output

def keccakZeroStateBody : Stmt :=
  .block "zero_state.body"
    [.SD .x28 .x0 (0 : BitVec 12),
     .ADDI .x28 .x28 (8 : BitVec 12),
     .ADDI .x29 .x29 (-1 : BitVec 12)]

def keccakDwordAbsorbBody : Stmt :=
  .block "absorb_dword.body"
    [.LD .x5 .x30 (0 : BitVec 12),
     .LD .x6 .x28 (0 : BitVec 12),
     .XOR .x6 .x6 .x5,
     .SD .x28 .x6 (0 : BitVec 12),
     .ADDI .x28 .x28 (8 : BitVec 12),
     .ADDI .x30 .x30 (8 : BitVec 12),
     .ADDI .x31 .x31 (-1 : BitVec 12)]

def keccakRemainderBody : Stmt :=
  .block "remainder.body"
    [.LBU .x5 .x30 (0 : BitVec 12),
     .LBU .x6 .x28 (0 : BitVec 12),
     .XOR .x5 .x5 .x6,
     .SB .x28 .x5 (0 : BitVec 12),
     .ADDI .x28 .x28 (1 : BitVec 12),
     .ADDI .x30 .x30 (1 : BitVec 12),
     .ADDI .x9 .x9 (-1 : BitVec 12)]

def keccakOutputWinR (outputBase : Word) (output : Bytes) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest =>
    rf.get .x18 = outputBase ∧ win = output ∧ rest.pcFree

def keccakWrapperStmt (L : GuestLayout) (len : Nat)
    (outputBase : Word) (output : Bytes)
    (zeroInv dwordInv absorbInv remainderInv : KeccakLoopInv) : Stmt :=
  .block "prologue"
    [.ADDI .x2 .x2 (-32 : BitVec 12),
     .SD .x2 .x8 (0 : BitVec 12),
     .SD .x2 .x9 (8 : BitVec 12),
     .SD .x2 .x18 (16 : BitVec 12),
     .SD .x2 .x20 (24 : BitVec 12),
     .MV .x20 .x10,
     .MV .x9 .x11,
     .MV .x18 .x12,
     .AUIPC .x8 (laHi L.zk3_state (L.zkvm_keccak256 + 32)),
     .ADDI .x8 .x8 (laLo L.zk3_state (L.zkvm_keccak256 + 32)),
     .MV .x28 .x8,
     .LI .x29 (25 : Word)]
  ;;; .doWhile "zero_state" (.bne .x29 .x0) 25 zeroInv
        keccakZeroStateBody
  ;;; .whileHeader "absorb_blocks" (.block "absorb_blocks.header"
          [.LI .x29 (136 : Word)]) (.bge .x9 .x29)
        (keccakAbsorbFuel len) absorbInv
        (.block "absorb_blocks.setup"
          [.MV .x28 .x8, .MV .x30 .x20, .LI .x31 (17 : Word)]
         ;;; .doWhile "absorb_dword" (.bne .x31 .x0) 17 dwordInv
               keccakDwordAbsorbBody
         ;;; .block "absorb_blocks.permute"
          [.MV .x10 .x8,
           .CSRS (2048 : BitVec 12) .x10,
           .ADDI .x20 .x20 (136 : BitVec 12),
           .ADDI .x9 .x9 (-136 : BitVec 12)])
  ;;; .block "remainder.setup" [.MV .x28 .x8, .MV .x30 .x20]
  ;;; .when "remainder" (.bne .x9 .x0)
        (.doWhile "remainder_bytes" (.bne .x9 .x0) (keccakRemainderFuel len)
          remainderInv keccakRemainderBody)
  ;;; .block "pad"
    [.LBU .x5 .x28 (0 : BitVec 12),
     .XORI .x5 .x5 (1 : BitVec 12),
     .SB .x28 .x5 (0 : BitVec 12),
     .ADDI .x28 .x8 (135 : BitVec 12),
     .LBU .x5 .x28 (0 : BitVec 12),
     .XORI .x5 .x5 (128 : BitVec 12),
     .SB .x28 .x5 (0 : BitVec 12)]
  ;;; .block "final_permute"
    [.MV .x10 .x8, .CSRS (2048 : BitVec 12) .x10]
  ;;; .blockAt "digest_out" .x18 (keccakOutputWinR outputBase output)
    [.LD .x5 .x8 (0 : BitVec 12),
     .SD .x18 .x5 (0 : BitVec 12),
     .LD .x5 .x8 (8 : BitVec 12),
     .SD .x18 .x5 (8 : BitVec 12),
     .LD .x5 .x8 (16 : BitVec 12),
     .SD .x18 .x5 (16 : BitVec 12),
     .LD .x5 .x8 (24 : BitVec 12),
     .SD .x18 .x5 (24 : BitVec 12)]
  ;;; .block "return"
    [.LI .x10 (0 : Word),
     .LD .x8 .x2 (0 : BitVec 12),
     .LD .x9 .x2 (8 : BitVec 12),
     .LD .x18 .x2 (16 : BitVec 12),
     .LD .x20 .x2 (24 : BitVec 12),
     .ADDI .x2 .x2 (32 : BitVec 12),
     .JALR .x0 .x1 (0 : BitVec 12)]

/- The list shape is a proof-only view: the emitted program remains the
   generated flat `zkvmKeccak256_prog_of`; no emitter or byte changes flow from
   this statement.  Keeping the guard here makes that promise kernel-checked. -/
theorem keccakWrapperStmt_flatten (L : GuestLayout) (len : Nat)
    (outputBase : Word) (output : Bytes)
    (zeroInv dwordInv absorbInv remainderInv : KeccakLoopInv) :
    (keccakWrapperStmt L len outputBase output zeroInv dwordInv absorbInv remainderInv).flatten 0 =
      zkvmKeccak256_prog_of L := by
  rfl

#guard (keccakWrapperStmt .zero 0 0 []
    (fun _ _ _ _ => True) (fun _ _ _ _ => True)
    (fun _ _ _ _ => True) (fun _ _ _ _ => True)).flatten 0 =
  zkvmKeccak256_prog_of .zero
#guard (keccakWrapperStmt .zero 0 0 []
    (fun _ _ _ _ => True) (fun _ _ _ _ => True)
    (fun _ _ _ _ => True) (fun _ _ _ _ => True)).size = 69

/- `offsetsOk` is intentionally not asserted here: the flat wrapper's `BLT`
   and `BNE` guards read `x9`, a callee-saved register that the caller-only
   SAsm AST excludes from `Reg.isExposed`.  The flatten tie is therefore a
   structural map for the direct `cpsTripleWithin`/ABI-frame proof route, not
   a claim that `Stmt.sound` can consume this shape. -/

/-- The padding suffix for a message whose length is a multiple of the rate.
    This is the branch that is easy to lose when modelling the emitted
    residual loop: a zero remainder still gets a complete pad-only block. -/
theorem keccakPad_zero_remainder (msg : Bytes)
    (hrem : msg.length % keccakRateBytes = 0) :
    (keccakPad msg).drop msg.length =
      (0x01 : Byte) :: List.replicate 134 (0 : Byte) ++ [(0x80 : Byte)] := by
  have hrem' : msg.length % 136 = 0 := by
    simpa [keccakRateBytes] using hrem
  simp [keccakPad, keccakRateBytes, hrem']

/-- Two consecutive inline accelerator calls cover the two adjacent
    permutation points used by a full block followed by a pad-only block.
    This is proof-only structure: the emitted bridge remains the flat
    69-instruction program, and this theorem deliberately keeps the concrete
    `Accel.keccakF` image at each seam. -/
theorem keccak_two_csrs_spec_within
    (entry : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff : Nat) (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 200 ≤ len) :
    cpsTripleWithin 2 entry (entry + BitVec.ofNat 64 8)
      (CodeReq.ofProg entry [.CSRS 0x800 rs1, .CSRS 0x800 rs1])
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B
        (setBytes (setBytes ws pOff (keccakBytes ws pOff)) pOff
          (keccakBytes (setBytes ws pOff (keccakBytes ws pOff)) pOff))) := by
  have hws1len : (setBytes ws pOff (keccakBytes ws pOff)).length = len := by
    rw [length_setBytes]
    exact hwslen
  have h1 := csrs_keccak_spec_within entry rs1 hrs1 B len ws rf hwslen
    hb8 hvalid pOff hp h8p hpfit
  have h2 := csrs_keccak_spec_within (entry + 4) rs1 hrs1 B len
    (setBytes ws pOff (keccakBytes ws pOff)) rf hws1len hb8 hvalid pOff hp
    h8p hpfit
  have hd : (CodeReq.singleton entry (.CSRS 0x800 rs1)).Disjoint
      (CodeReq.singleton (entry + 4) (.CSRS 0x800 rs1)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have hseq := cpsTripleWithin_seq hd h1 h2
  rw [← CodeReq.ofProg_pair] at hseq
  have hExit : entry + 4 + 4 = entry + BitVec.ofNat 64 8 := by bv_omega
  rw [hExit] at hseq
  exact hseq

end EvmAsm.Codegen.Proofs
