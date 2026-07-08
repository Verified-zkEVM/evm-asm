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
import EvmAsm.Evm64.Transient.LoadLoopSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Transient

open EvmAsm.Rv64
open EvmAsm.Evm64
/-- The 9-instruction match-copy arm (`evm_tload_copy`): copy the matched
    entry's `current` limbs to the stack top in place, then JAL to the loop
    exit. Proven `∀ base` over its own slice code (`runBlock` needs a
    variable entry) and instantiated at loop-slice offset +100. -/
theorem evm_tload_copy_spec_within
    (b3 ent sp x16old : Word) (c0 c1 c2 c3 k0 k1 k2 k3 : Word) :
    cpsTripleWithin 9 b3 (b3 + 60) (evm_tload_copy_code b3)
      ((((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) ** (((.x16)) ↦ᵣ x16old) **
       ((ent + 96) ↦ₘ c0) ** ((ent + 104) ↦ₘ c1) **
       ((ent + 112) ↦ₘ c2) ** ((ent + 120) ↦ₘ c3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3))
      ((((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) ** (((.x16)) ↦ᵣ c3) **
       ((ent + 96) ↦ₘ c0) ** ((ent + 104) ↦ₘ c1) **
       ((ent + 112) ↦ₘ c2) ** ((ent + 120) ↦ₘ c3) **
       ((sp) ↦ₘ c0) ** ((sp + 8) ↦ₘ c1) **
       ((sp + 16) ↦ₘ c2) ** ((sp + 24) ↦ₘ c3)) := by
  have hLD0 := ld_spec_gen_within .x16 .x14 ent x16old c0
    (BitVec.ofNat 12 96) b3 (by decide)
  have hSD0 := sd_spec_gen_within .x12 .x16 sp c0 k0
    (BitVec.ofNat 12 0) (b3 + 4)
  have hLD1 := ld_spec_gen_within .x16 .x14 ent c0 c1
    (BitVec.ofNat 12 104) (b3 + 8) (by decide)
  have hSD1 := sd_spec_gen_within .x12 .x16 sp c1 k1
    (BitVec.ofNat 12 8) (b3 + 12)
  have hLD2 := ld_spec_gen_within .x16 .x14 ent c1 c2
    (BitVec.ofNat 12 112) (b3 + 16) (by decide)
  have hSD2 := sd_spec_gen_within .x12 .x16 sp c2 k2
    (BitVec.ofNat 12 16) (b3 + 20)
  have hLD3 := ld_spec_gen_within .x16 .x14 ent c2 c3
    (BitVec.ofNat 12 120) (b3 + 24) (by decide)
  have hSD3 := sd_spec_gen_within .x12 .x16 sp c3 k3
    (BitVec.ofNat 12 24) (b3 + 28)
  simp only [sE0, sE8, sE16, sE24, sE96, sE104, sE112, sE120]
    at hLD0 hSD0 hLD1 hSD1 hLD2 hSD2 hLD3 hSD3
  have hjal := jal_x0_spec_gen_within (BitVec.ofNat 21 28) (b3 + 32)
  rw [show signExtend21 (BitVec.ofNat 21 28) = BitVec.ofNat 64 28 from by decide,
      show (b3 + 32 : Word) + BitVec.ofNat 64 28 = b3 + 60 from by bv_omega]
    at hjal
  runBlock hLD0 hSD0 hLD1 hSD1 hLD2 hSD2 hLD3 hSD3 hjal

/-- The decrement/loop-back path of the tail (`evm_tload_tail`): one fewer
    entry left and it is nonzero, so the backward BNE returns to the loop
    entry 136 bytes above this slice. -/
theorem evm_tload_tail_continue_spec_within
    (b4 v : Word) (hv : v - 1 ≠ 0) :
    cpsTripleWithin 2 b4 (b4 - 136) (evm_tload_tail_code b4)
      ((((.x15)) ↦ᵣ v) ** (((.x0)) ↦ᵣ (0 : Word)))
      ((((.x15)) ↦ᵣ (v - 1)) ** (((.x0)) ↦ᵣ (0 : Word))) := by
  have haddi := addi_spec_gen_same_within .x15 v (-1 : BitVec 12) b4 (by decide)
  rw [addi_neg1_eq_sub_one] at haddi
  have hbne_raw := bne_spec_gen_within .x15 .x0 (-140 : BitVec 13)
    (v - 1) (0 : Word) (b4 + 4)
  rw [show signExtend13 (-140 : BitVec 13) = (18446744073709551476 : Word)
        from by decide,
      show (b4 + 4 : Word) + 18446744073709551476 = b4 - 136 from by bv_omega]
    at hbne_raw
  have hbne := cpsBranchWithin_takenStripPure2 hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hv ((sepConj_pure_right _).mp h_rest).2)
  runBlock haddi hbne

/-- The scan-exhausted path of the tail: the decremented counter is zero, so
    the BNE falls through into the zero arm — no entry matched and the stack
    top becomes 0. -/
theorem evm_tload_tail_exit_spec_within
    (b4 sp v : Word) (k0 k1 k2 k3 : Word) (hv : v - 1 = 0) :
    cpsTripleWithin 6 b4 (b4 + 24) (evm_tload_tail_code b4)
      ((((.x15)) ↦ᵣ v) ** (((.x0)) ↦ᵣ (0 : Word)) ** (((.x12)) ↦ᵣ sp) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3))
      ((((.x15)) ↦ᵣ (v - 1)) ** (((.x0)) ↦ᵣ (0 : Word)) ** (((.x12)) ↦ᵣ sp) **
       ((sp) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
       ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word))) := by
  have haddi := addi_spec_gen_same_within .x15 v (-1 : BitVec 12) b4 (by decide)
  rw [addi_neg1_eq_sub_one] at haddi
  have hbne_raw := bne_spec_gen_within .x15 .x0 (-140 : BitVec 13)
    (v - 1) (0 : Word) (b4 + 4)
  rw [show (b4 + 4 : Word) + 4 = b4 + 8 from by bv_omega] at hbne_raw
  have hbne := cpsBranchWithin_ntakenStripPure2 hbne_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hv)
  have hsd0 := sd_x0_spec_gen_within .x12 sp k0 (BitVec.ofNat 12 0) (b4 + 8)
  have hsd1 := sd_x0_spec_gen_within .x12 sp k1 (BitVec.ofNat 12 8) (b4 + 12)
  have hsd2 := sd_x0_spec_gen_within .x12 sp k2 (BitVec.ofNat 12 16) (b4 + 16)
  have hsd3 := sd_x0_spec_gen_within .x12 sp k3 (BitVec.ofNat 12 24) (b4 + 20)
  simp only [sE0, sE8, sE16, sE24] at hsd0 hsd1 hsd2 hsd3
  runBlock haddi hbne hsd0 hsd1 hsd2 hsd3

/-! ## Slice-inclusion plumbing (sub-slice CodeReqs into the loop slice) -/

private theorem cmp_sub_loop (b2 : Word) :
    ∀ a i, (evm_tload_cmp_code b2) a = some i →
      (evm_tload_loop_code b2) a = some i := by
  intro a i h
  exact CodeReq.ofProg_mono_append_left b2
    (evm_tload_cmp .x20 ++ evm_tload_copy) evm_tload_tail a i
    (CodeReq.ofProg_mono_append_left b2 (evm_tload_cmp .x20) evm_tload_copy a i h)

private theorem copy_sub_loop (b2 : Word) :
    ∀ a i, (evm_tload_copy_code (b2 + 100)) a = some i →
      (evm_tload_loop_code b2) a = some i := by
  have h := CodeReq.ofProg_mono_subrange b2 (evm_tload_cmp .x20) evm_tload_copy
    evm_tload_tail (by decide)
  rw [show BitVec.ofNat 64 (4 * (evm_tload_cmp .x20).length) = (100 : Word)
        from by decide] at h
  exact h

private theorem tail_sub_loop (b2 : Word) :
    ∀ a i, (evm_tload_tail_code (b2 + 136)) a = some i →
      (evm_tload_loop_code b2) a = some i := by
  have h := CodeReq.ofProg_mono_append_right b2
    (evm_tload_cmp .x20 ++ evm_tload_copy) evm_tload_tail (by decide)
  rw [show BitVec.ofNat 64 (4 * (evm_tload_cmp .x20 ++ evm_tload_copy).length)
        = (136 : Word) from by decide] at h
  exact h

private theorem loop_sub_full (base : Word) :
    ∀ a i, (evm_tload_loop_code (base + 28)) a = some i →
      (evm_tload_code .x20 base) a = some i := by
  have h := CodeReq.ofProg_mono_append_right base
    (evm_tload_head .x20) (evm_tload_loop .x20) (by decide)
  rw [show BitVec.ofNat 64 (4 * (evm_tload_head .x20).length) = (28 : Word)
        from by decide] at h
  exact h

/-! ## One full loop iteration (over the loop-slice code) -/

/-- Iteration on a MATCHING entry: all eight compare pairs pass and the entry's
    `current` limbs replace the stack top; exits the loop (34 steps). -/
theorem evm_tload_iter_match_spec_within
    (b2 ent envAddr sp x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 c0 c1 c2 c3 : Word) :
    cpsTripleWithin 34 b2 (b2 + 160) (evm_tload_loop_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ a0) ** ((ent + 8) ↦ₘ a1) **
       ((ent + 16) ↦ₘ a2) ** ((ent + 24) ↦ₘ a3) **
       ((ent + 32) ↦ₘ k0) ** ((ent + 40) ↦ₘ k1) **
       ((ent + 48) ↦ₘ k2) ** ((ent + 56) ↦ₘ k3) **
       ((ent + 96) ↦ₘ c0) ** ((ent + 104) ↦ₘ c1) **
       ((ent + 112) ↦ₘ c2) ** ((ent + 120) ↦ₘ c3))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
       (((.x16)) ↦ᵣ c3) ** (((.x17)) ↦ᵣ k3) **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ c0) ** ((sp + 8) ↦ₘ c1) **
       ((sp + 16) ↦ₘ c2) ** ((sp + 24) ↦ₘ c3) **
       ((ent) ↦ₘ a0) ** ((ent + 8) ↦ₘ a1) **
       ((ent + 16) ↦ₘ a2) ** ((ent + 24) ↦ₘ a3) **
       ((ent + 32) ↦ₘ k0) ** ((ent + 40) ↦ₘ k1) **
       ((ent + 48) ↦ₘ k2) ** ((ent + 56) ↦ₘ k3) **
       ((ent + 96) ↦ₘ c0) ** ((ent + 104) ↦ₘ c1) **
       ((ent + 112) ↦ₘ c2) ** ((ent + 120) ↦ₘ c3)) := by
  have pass := cpsTripleWithin_extend_code (cmp_sub_loop b2)
    (evm_tload_cmp_pass_spec_within b2 ent envAddr sp x16old x17old
      a0 a1 a2 a3 k0 k1 k2 k3)
  have copy := cpsTripleWithin_extend_code (copy_sub_loop b2)
    (evm_tload_copy_spec_within (b2 + 100) ent sp k3 c0 c1 c2 c3 k0 k1 k2 k3)
  have passF := cpsTripleWithin_frameR
    (((ent + 96) ↦ₘ c0) ** ((ent + 104) ↦ₘ c1) **
     ((ent + 112) ↦ₘ c2) ** ((ent + 120) ↦ₘ c3)) (by pcFree) pass
  have copyF := cpsTripleWithin_frameR
    ((((.x20)) ↦ᵣ envAddr) ** (((.x17)) ↦ᵣ k3) **
     ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
     ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
     ((ent) ↦ₘ a0) ** ((ent + 8) ↦ₘ a1) **
     ((ent + 16) ↦ₘ a2) ** ((ent + 24) ↦ₘ a3) **
     ((ent + 32) ↦ₘ k0) ** ((ent + 40) ↦ₘ k1) **
     ((ent + 48) ↦ₘ k2) ** ((ent + 56) ↦ₘ k3)) (by pcFree) copy
  have comp := cpsTripleWithin_seq_perm_same_cr
    (fun h hq => by xperm_hyp hq) passF copyF
  rw [show (b2 + 100 : Word) + 60 = b2 + 160 from by bv_omega] at comp
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) comp

/-- Iteration on a NON-matching entry with more entries left: some compare
    pair differs, the counter decrements to a nonzero value, and control
    returns to the loop entry (27 steps). -/
theorem evm_tload_iter_nomatch_continue_spec_within
    (b2 ent envAddr sp m x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (hne : ¬(e0 = a0 ∧ e1 = a1 ∧ e2 = a2 ∧ e3 = a3 ∧
             e4 = k0 ∧ e5 = k1 ∧ e6 = k2 ∧ e7 = k3))
    (hm : m - 1 ≠ 0) :
    cpsTripleWithin 27 b2 b2 (evm_tload_loop_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x15)) ↦ᵣ m) ** (((.x0)) ↦ᵣ (0 : Word)) **
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
       (((.x15)) ↦ᵣ (m - 1)) ** (((.x0)) ↦ᵣ (0 : Word)) **
       regOwn .x16 ** regOwn .x17 **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  have mis := cpsTripleWithin_extend_code (cmp_sub_loop b2)
    (evm_tload_cmp_mismatch_spec_within b2 ent envAddr sp x16old x17old
      a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 hne)
  have tailc := cpsTripleWithin_extend_code (tail_sub_loop b2)
    (evm_tload_tail_continue_spec_within (b2 + 136) m hm)
  rw [show (b2 + 136 : Word) - 136 = b2 from by bv_omega] at tailc
  have misF := cpsTripleWithin_frameR
    ((((.x15)) ↦ᵣ m) ** (((.x0)) ↦ᵣ (0 : Word))) (by pcFree) mis
  have tailF := cpsTripleWithin_frameR
    ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ ent) **
     regOwn .x16 ** regOwn .x17 **
     ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
     ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
     ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
     ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3) **
     ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
     ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
     ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
     ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) (by pcFree) tailc
  have comp := cpsTripleWithin_seq_perm_same_cr
    (fun h hq => by xperm_hyp hq) misF tailF
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) comp

/-- Iteration on a NON-matching LAST entry: some compare pair differs and the
    counter hits zero, so the zero arm writes 0 to the stack top and the loop
    exits (31 steps). -/
theorem evm_tload_iter_nomatch_exit_spec_within
    (b2 ent envAddr sp m x16old x17old : Word)
    (a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 : Word)
    (hne : ¬(e0 = a0 ∧ e1 = a1 ∧ e2 = a2 ∧ e3 = a3 ∧
             e4 = k0 ∧ e5 = k1 ∧ e6 = k2 ∧ e7 = k3))
    (hm : m - 1 = 0) :
    cpsTripleWithin 31 b2 (b2 + 160) (evm_tload_loop_code b2)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x14)) ↦ᵣ (ent + 128)) **
       (((.x15)) ↦ᵣ m) ** (((.x0)) ↦ᵣ (0 : Word)) **
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
       (((.x15)) ↦ᵣ (m - 1)) ** (((.x0)) ↦ᵣ (0 : Word)) **
       regOwn .x16 ** regOwn .x17 **
       ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
       ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
       ((sp) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
       ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)) **
       ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
       ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
       ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
       ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) := by
  have mis := cpsTripleWithin_extend_code (cmp_sub_loop b2)
    (evm_tload_cmp_mismatch_spec_within b2 ent envAddr sp x16old x17old
      a0 a1 a2 a3 k0 k1 k2 k3 e0 e1 e2 e3 e4 e5 e6 e7 hne)
  have taile := cpsTripleWithin_extend_code (tail_sub_loop b2)
    (evm_tload_tail_exit_spec_within (b2 + 136) sp m k0 k1 k2 k3 hm)
  rw [show (b2 + 136 : Word) + 24 = b2 + 160 from by bv_omega] at taile
  have misF := cpsTripleWithin_frameR
    ((((.x15)) ↦ᵣ m) ** (((.x0)) ↦ᵣ (0 : Word))) (by pcFree) mis
  have tailF := cpsTripleWithin_frameR
    ((((.x20)) ↦ᵣ envAddr) ** (((.x14)) ↦ᵣ ent) **
     regOwn .x16 ** regOwn .x17 **
     ((envAddr) ↦ₘ a0) ** ((envAddr + 8) ↦ₘ a1) **
     ((envAddr + 16) ↦ₘ a2) ** ((envAddr + 24) ↦ₘ a3) **
     ((ent) ↦ₘ e0) ** ((ent + 8) ↦ₘ e1) **
     ((ent + 16) ↦ₘ e2) ** ((ent + 24) ↦ₘ e3) **
     ((ent + 32) ↦ₘ e4) ** ((ent + 40) ↦ₘ e5) **
     ((ent + 48) ↦ₘ e6) ** ((ent + 56) ↦ₘ e7)) (by pcFree) taile
  have comp := cpsTripleWithin_seq_perm_same_cr
    (fun h hq => by xperm_hyp hq) misF tailF
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) comp

/-- Weaken two leading concrete register atoms to `regOwn`. -/
private theorem sepConj_own2 {r1 r2 : Reg} {v1 v2 : Word} {Q : Assertion} :
    ∀ h, ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Q) h →
      (regOwn r1 ** regOwn r2 ** Q) h :=
  fun h hp =>
    sepConj_mono (regIs_implies_regOwn r1)
      (sepConj_mono_left (regIs_implies_regOwn r2)) h hp

/-- Flat (limb-atom) unfold of `evmWordIs`, for hypothesis/goal rewrites. -/
private theorem evmWordIs_flat (addr : Word) (v : EvmWord) :
    evmWordIs addr v =
      ((addr ↦ₘ v.getLimbN 0) ** ((addr + 8) ↦ₘ v.getLimbN 1) **
       ((addr + 16) ↦ₘ v.getLimbN 2) ** ((addr + 24) ↦ₘ v.getLimbN 3)) := rfl

/-! ## The scan loop (snoc induction over the unscanned prefix)

Invariant at the loop entry with `m = es.length ≥ 1` entries left to scan:
`x15 = m`, `x14 = TRANSIENT_STORAGE_LOG_BASE + 128*m` (one past entry `m-1`),
and the log prefix `es` is owned. On exit the stack top holds
`transientLookup addrHash slotKey es` — the reverse scan finds the LAST
matching entry of `es` first. -/

theorem evm_tload_loop_spec_within
    (b2 envAddr sp : Word) (addrHash slotKey : EvmWord) :
    ∀ es : List StorageLogEntry, es ≠ [] → es.length < 2 ^ 64 →
    cpsTripleWithin (34 * es.length) b2 (b2 + 160) (evm_tload_loop_code b2)
      (regOwn .x16 ** regOwn .x17 **
       (((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) **
       (((.x14)) ↦ᵣ (TRANSIENT_STORAGE_LOG_BASE +
          BitVec.ofNat 64 (es.length * 128))) **
       (((.x15)) ↦ᵣ BitVec.ofNat 64 es.length) ** (((.x0)) ↦ᵣ (0 : Word)) **
       evmWordIs envAddr addrHash ** evmWordIs sp slotKey **
       storageLogIs TRANSIENT_STORAGE_LOG_BASE es)
      (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
       (((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) ** (((.x0)) ↦ᵣ (0 : Word)) **
       evmWordIs envAddr addrHash **
       evmWordIs sp (transientLookup addrHash slotKey es) **
       storageLogIs TRANSIENT_STORAGE_LOG_BASE es) := by
  intro es
  induction es using List.reverseRecOn with
  | nil => intro hne _; exact absurd rfl hne
  | append_singleton es' e ih =>
    intro _ hlen
    simp only [List.length_append, List.length_cons, List.length_nil,
               Nat.zero_add] at hlen ⊢
    have hent : TRANSIENT_STORAGE_LOG_BASE +
        BitVec.ofNat 64 ((es'.length + 1) * 128)
        = (TRANSIENT_STORAGE_LOG_BASE +
           BitVec.ofNat 64 (es'.length * 128)) + 128 :=
      tloadEnt_succ es'.length
    refine cpsTripleWithin_regOwn2_pre fun v16 v17 => ?_
    by_cases hm : e.addrHash = addrHash ∧ e.slotKey = slotKey
    · -- The most-recent entry matches: copy its `current`, exit.
      have coreF := cpsTripleWithin_frameR
        (storageLogIs TRANSIENT_STORAGE_LOG_BASE es' **
         (((TRANSIENT_STORAGE_LOG_BASE +
             BitVec.ofNat 64 (es'.length * 128)) + 64) ↦ₘ
            e.original.getLimbN 0) **
         (((TRANSIENT_STORAGE_LOG_BASE +
             BitVec.ofNat 64 (es'.length * 128)) + 72) ↦ₘ
            e.original.getLimbN 1) **
         (((TRANSIENT_STORAGE_LOG_BASE +
             BitVec.ofNat 64 (es'.length * 128)) + 80) ↦ₘ
            e.original.getLimbN 2) **
         (((TRANSIENT_STORAGE_LOG_BASE +
             BitVec.ofNat 64 (es'.length * 128)) + 88) ↦ₘ
            e.original.getLimbN 3) **
         (((.x15)) ↦ᵣ BitVec.ofNat 64 (es'.length + 1)) **
         (((.x0)) ↦ᵣ (0 : Word)))
        (by pcFree)
        (evm_tload_iter_match_spec_within b2
          (TRANSIENT_STORAGE_LOG_BASE + BitVec.ofNat 64 (es'.length * 128))
          envAddr sp v16 v17
          (addrHash.getLimbN 0) (addrHash.getLimbN 1)
          (addrHash.getLimbN 2) (addrHash.getLimbN 3)
          (slotKey.getLimbN 0) (slotKey.getLimbN 1)
          (slotKey.getLimbN 2) (slotKey.getLimbN 3)
          (e.current.getLimbN 0) (e.current.getLimbN 1)
          (e.current.getLimbN 2) (e.current.getLimbN 3))
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) coreF)
      · rw [storageLogIs_snoc, storageSlotIs_eq_flat, hm.1, hm.2,
            evmWordIs_flat envAddr addrHash, evmWordIs_flat sp slotKey,
            hent] at hp
        xperm_hyp hp
      · rw [transientLookup_snoc, if_pos hm, storageLogIs_snoc,
            storageSlotIs_eq_flat, hm.1, hm.2,
            evmWordIs_flat envAddr addrHash, evmWordIs_flat sp e.current]
        exact sepConj_own4
          (v1 := TRANSIENT_STORAGE_LOG_BASE +
            BitVec.ofNat 64 (es'.length * 128))
          (v2 := BitVec.ofNat 64 (es'.length + 1))
          (v3 := e.current.getLimbN 3) (v4 := slotKey.getLimbN 3)
          h (by xperm_hyp hq)
    · -- The most-recent entry does not match.
      have hlimb : ¬(e.addrHash.getLimbN 0 = addrHash.getLimbN 0 ∧
          e.addrHash.getLimbN 1 = addrHash.getLimbN 1 ∧
          e.addrHash.getLimbN 2 = addrHash.getLimbN 2 ∧
          e.addrHash.getLimbN 3 = addrHash.getLimbN 3 ∧
          e.slotKey.getLimbN 0 = slotKey.getLimbN 0 ∧
          e.slotKey.getLimbN 1 = slotKey.getLimbN 1 ∧
          e.slotKey.getLimbN 2 = slotKey.getLimbN 2 ∧
          e.slotKey.getLimbN 3 = slotKey.getLimbN 3) := fun hall =>
        hm ⟨evmWord_eq_of_limbs_eq hall.1 hall.2.1 hall.2.2.1 hall.2.2.2.1,
            evmWord_eq_of_limbs_eq hall.2.2.2.2.1 hall.2.2.2.2.2.1
              hall.2.2.2.2.2.2.1 hall.2.2.2.2.2.2.2⟩
      by_cases hnil : es' = []
      · -- Last entry scanned without a match: fall into the zero arm.
        have hm0 : BitVec.ofNat 64 (es'.length + 1) - 1 = 0 := by
          rw [ofNat_succ_sub_one, hnil]; simp
        have hTL : transientLookup addrHash slotKey es' = 0 := by
          rw [hnil]; rfl
        have coreF := cpsTripleWithin_frameR
          (storageLogIs TRANSIENT_STORAGE_LOG_BASE es' **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 64) ↦ₘ
              e.original.getLimbN 0) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 72) ↦ₘ
              e.original.getLimbN 1) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 80) ↦ₘ
              e.original.getLimbN 2) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 88) ↦ₘ
              e.original.getLimbN 3) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 96) ↦ₘ
              e.current.getLimbN 0) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 104) ↦ₘ
              e.current.getLimbN 1) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 112) ↦ₘ
              e.current.getLimbN 2) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 120) ↦ₘ
              e.current.getLimbN 3))
          (by pcFree)
          (evm_tload_iter_nomatch_exit_spec_within b2
            (TRANSIENT_STORAGE_LOG_BASE + BitVec.ofNat 64 (es'.length * 128))
            envAddr sp (BitVec.ofNat 64 (es'.length + 1)) v16 v17
            (addrHash.getLimbN 0) (addrHash.getLimbN 1)
            (addrHash.getLimbN 2) (addrHash.getLimbN 3)
            (slotKey.getLimbN 0) (slotKey.getLimbN 1)
            (slotKey.getLimbN 2) (slotKey.getLimbN 3)
            (e.addrHash.getLimbN 0) (e.addrHash.getLimbN 1)
            (e.addrHash.getLimbN 2) (e.addrHash.getLimbN 3)
            (e.slotKey.getLimbN 0) (e.slotKey.getLimbN 1)
            (e.slotKey.getLimbN 2) (e.slotKey.getLimbN 3)
            hlimb hm0)
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) coreF)
        · rw [storageLogIs_snoc, storageSlotIs_eq_flat,
              evmWordIs_flat envAddr addrHash, evmWordIs_flat sp slotKey,
              hent] at hp
          xperm_hyp hp
        · rw [transientLookup_snoc, if_neg hm, hTL, storageLogIs_snoc,
              storageSlotIs_eq_flat, evmWordIs_flat envAddr addrHash,
              evmWordIs_zero]
          exact sepConj_own2
            (v1 := TRANSIENT_STORAGE_LOG_BASE +
              BitVec.ofNat 64 (es'.length * 128))
            (v2 := BitVec.ofNat 64 (es'.length + 1) - 1)
            h (by xperm_hyp hq)
      · -- No match and more entries left: loop and use the IH on `es'`.
        have hm1 : BitVec.ofNat 64 (es'.length + 1) - 1 ≠ 0 := by
          rw [ofNat_succ_sub_one]
          exact ofNat64_ne_zero
            (fun h0 => hnil (List.eq_nil_of_length_eq_zero h0)) (by omega)
        have iterF := cpsTripleWithin_frameR
          (storageLogIs TRANSIENT_STORAGE_LOG_BASE es' **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 64) ↦ₘ
              e.original.getLimbN 0) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 72) ↦ₘ
              e.original.getLimbN 1) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 80) ↦ₘ
              e.original.getLimbN 2) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 88) ↦ₘ
              e.original.getLimbN 3) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 96) ↦ₘ
              e.current.getLimbN 0) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 104) ↦ₘ
              e.current.getLimbN 1) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 112) ↦ₘ
              e.current.getLimbN 2) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 120) ↦ₘ
              e.current.getLimbN 3))
          (by pcFree)
          (evm_tload_iter_nomatch_continue_spec_within b2
            (TRANSIENT_STORAGE_LOG_BASE + BitVec.ofNat 64 (es'.length * 128))
            envAddr sp (BitVec.ofNat 64 (es'.length + 1)) v16 v17
            (addrHash.getLimbN 0) (addrHash.getLimbN 1)
            (addrHash.getLimbN 2) (addrHash.getLimbN 3)
            (slotKey.getLimbN 0) (slotKey.getLimbN 1)
            (slotKey.getLimbN 2) (slotKey.getLimbN 3)
            (e.addrHash.getLimbN 0) (e.addrHash.getLimbN 1)
            (e.addrHash.getLimbN 2) (e.addrHash.getLimbN 3)
            (e.slotKey.getLimbN 0) (e.slotKey.getLimbN 1)
            (e.slotKey.getLimbN 2) (e.slotKey.getLimbN 3)
            hlimb hm1)
        have ihF := cpsTripleWithin_frameR
          ((((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128))) ↦ₘ
              e.addrHash.getLimbN 0) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 8) ↦ₘ
              e.addrHash.getLimbN 1) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 16) ↦ₘ
              e.addrHash.getLimbN 2) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 24) ↦ₘ
              e.addrHash.getLimbN 3) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 32) ↦ₘ
              e.slotKey.getLimbN 0) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 40) ↦ₘ
              e.slotKey.getLimbN 1) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 48) ↦ₘ
              e.slotKey.getLimbN 2) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 56) ↦ₘ
              e.slotKey.getLimbN 3) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 64) ↦ₘ
              e.original.getLimbN 0) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 72) ↦ₘ
              e.original.getLimbN 1) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 80) ↦ₘ
              e.original.getLimbN 2) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 88) ↦ₘ
              e.original.getLimbN 3) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 96) ↦ₘ
              e.current.getLimbN 0) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 104) ↦ₘ
              e.current.getLimbN 1) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 112) ↦ₘ
              e.current.getLimbN 2) **
           (((TRANSIENT_STORAGE_LOG_BASE +
               BitVec.ofNat 64 (es'.length * 128)) + 120) ↦ₘ
              e.current.getLimbN 3))
          (by pcFree)
          (ih hnil (by omega))
        have comp := cpsTripleWithin_seq_perm_same_cr
          (fun h hq => by
            rw [ofNat_succ_sub_one] at hq
            rw [evmWordIs_flat envAddr addrHash, evmWordIs_flat sp slotKey]
            xperm_hyp hq)
          iterF ihF
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) comp)
        · rw [storageLogIs_snoc, storageSlotIs_eq_flat,
              evmWordIs_flat envAddr addrHash, evmWordIs_flat sp slotKey,
              hent] at hp
          xperm_hyp hp
        · rw [transientLookup_snoc, if_neg hm, storageLogIs_snoc,
              storageSlotIs_eq_flat]
          xperm_hyp hq

/-! ## Head, empty-log path, and the raw full-program spec -/

private theorem sE464 :
    signExtend12 (BitVec.ofNat 12 transientLogLengthOff) = (464 : Word) := by
  decide

/-- The 7-instruction head on a nonempty log: loads `n`, falls through the
    BEQ, materializes the transient-log base, and computes the one-past-end
    scan pointer. -/
theorem evm_tload_head_spec_within
    (base envAddr : Word) (x14old x15old x16old : Word) (n : Nat)
    (hn : BitVec.ofNat 64 n ≠ 0) :
    cpsTripleWithin 7 base (base + 28) (evm_tload_code .x20 base)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x14)) ↦ᵣ x14old) **
       (((.x15)) ↦ᵣ x15old) ** (((.x16)) ↦ᵣ x16old) **
       (((.x0)) ↦ᵣ (0 : Word)) **
       ((envAddr + 464) ↦ₘ BitVec.ofNat 64 n))
      ((((.x20)) ↦ᵣ envAddr) **
       (((.x14)) ↦ᵣ (TRANSIENT_STORAGE_LOG_BASE +
          BitVec.ofNat 64 (n * 128))) **
       (((.x15)) ↦ᵣ BitVec.ofNat 64 n) **
       (((.x16)) ↦ᵣ BitVec.ofNat 64 (n * 128)) **
       (((.x0)) ↦ᵣ (0 : Word)) **
       ((envAddr + 464) ↦ₘ BitVec.ofNat 64 n)) := by
  have hld := ld_spec_gen_within .x15 .x20 envAddr x15old (BitVec.ofNat 64 n)
    (BitVec.ofNat 12 transientLogLengthOff) base (by decide)
  simp only [sE464] at hld
  have hbeq_raw := beq_spec_gen_within .x15 .x0 (BitVec.ofNat 13 168)
    (BitVec.ofNat 64 n) (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbeq_raw
  have hbeq := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact hn ((sepConj_pure_right _).mp h_rest).2)
  have hlui := lui_spec_gen_within .x14 x14old (BitVec.ofNat 20 0xa)
    (base + 8) (by decide)
  rw [show (((BitVec.ofNat 20 0xa).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
        = (40960 : Word) from by decide] at hlui
  have haddiw := addiw_spec_gen_same_within .x14 (40960 : Word)
    (BitVec.ofNat 12 131) (base + 12) (by decide)
  rw [show (((40960 : Word).truncate 32 +
        (signExtend12 (BitVec.ofNat 12 131)).truncate 32 : BitVec 32).signExtend 64)
        = (41091 : Word) from by decide] at haddiw
  have hslli16 := slli_spec_gen_same_within .x14 (41091 : Word) (16 : BitVec 6)
    (base + 16) (by decide)
  rw [show (41091 : Word) <<< (16 : BitVec 6).toNat = TRANSIENT_STORAGE_LOG_BASE
        from by decide] at hslli16
  have hslli7 := slli_spec_gen_within .x16 .x15 x16old (BitVec.ofNat 64 n)
    (7 : BitVec 6) (base + 20) (by decide)
  rw [shift7_eq_mul128] at hslli7
  have hadd := add_spec_gen_rd_eq_rs1_within .x14 .x16 TRANSIENT_STORAGE_LOG_BASE
    (BitVec.ofNat 64 (n * 128)) (base + 24) (by decide)
  runBlock hld hbeq hlui haddiw hslli16 hslli7 hadd

/-- Empty transient log: the head BEQ jumps straight to the zero arm and the
    stack top becomes 0. -/
theorem evm_tload_empty_spec_within
    (base envAddr sp : Word) (x15old : Word) (k0 k1 k2 k3 : Word) :
    cpsTripleWithin 6 base (base + 188) (evm_tload_code .x20 base)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) **
       (((.x15)) ↦ᵣ x15old) ** (((.x0)) ↦ᵣ (0 : Word)) **
       ((envAddr + 464) ↦ₘ BitVec.ofNat 64 0) **
       ((sp) ↦ₘ k0) ** ((sp + 8) ↦ₘ k1) **
       ((sp + 16) ↦ₘ k2) ** ((sp + 24) ↦ₘ k3))
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) **
       (((.x15)) ↦ᵣ BitVec.ofNat 64 0) ** (((.x0)) ↦ᵣ (0 : Word)) **
       ((envAddr + 464) ↦ₘ BitVec.ofNat 64 0) **
       ((sp) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
       ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word))) := by
  have hld := ld_spec_gen_within .x15 .x20 envAddr x15old (BitVec.ofNat 64 0)
    (BitVec.ofNat 12 transientLogLengthOff) base (by decide)
  simp only [sE464] at hld
  have hbeq_raw := beq_spec_gen_within .x15 .x0 (BitVec.ofNat 13 168)
    (BitVec.ofNat 64 0) (0 : Word) (base + 4)
  rw [show signExtend13 (BitVec.ofNat 13 168) = BitVec.ofNat 64 168 from by decide,
      show (base + 4 : Word) + BitVec.ofNat 64 168 = base + 172 from by bv_omega]
    at hbeq_raw
  have hbeq := cpsBranchWithin_takenStripPure2 hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact ((sepConj_pure_right _).mp h_rest).2 (by decide))
  have hsd0 := sd_x0_spec_gen_within .x12 sp k0 (BitVec.ofNat 12 0) (base + 172)
  have hsd1 := sd_x0_spec_gen_within .x12 sp k1 (BitVec.ofNat 12 8) (base + 176)
  have hsd2 := sd_x0_spec_gen_within .x12 sp k2 (BitVec.ofNat 12 16) (base + 180)
  have hsd3 := sd_x0_spec_gen_within .x12 sp k3 (BitVec.ofNat 12 24) (base + 184)
  simp only [sE0, sE8, sE16, sE24] at hsd0 hsd1 hsd2 hsd3
  runBlock hld hbeq hsd0 hsd1 hsd2 hsd3

/-- Raw full-program TLOAD spec: from the length cell (`env+464`), the frame's
    `env.ADDRESS`, the slot key at the stack top, and the transient log, the
    47-instruction scan replaces the stack top in place by
    `transientLookup addrHash slotKey entries` within `7 + 34*n` steps.
    Scratch registers `x14`–`x17` end clobbered; everything else is
    preserved. -/
theorem evm_tload_spec_within
    (n : Nat) (base envAddr sp : Word)
    (x14old x15old x16old x17old : Word)
    (addrHash slotKey : EvmWord) (entries : List StorageLogEntry)
    (hlen : entries.length = n) (hcap : n < 2 ^ 64) :
    cpsTripleWithin (7 + 34 * n) base (base + 188) (evm_tload_code .x20 base)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) **
       (((.x14)) ↦ᵣ x14old) ** (((.x15)) ↦ᵣ x15old) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       (((.x0)) ↦ᵣ (0 : Word)) **
       ((envAddr + 464) ↦ₘ BitVec.ofNat 64 n) **
       evmWordIs envAddr addrHash ** evmWordIs sp slotKey **
       storageLogIs TRANSIENT_STORAGE_LOG_BASE entries)
      (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
       (((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) **
       (((.x0)) ↦ᵣ (0 : Word)) **
       ((envAddr + 464) ↦ₘ BitVec.ofNat 64 n) **
       evmWordIs envAddr addrHash **
       evmWordIs sp (transientLookup addrHash slotKey entries) **
       storageLogIs TRANSIENT_STORAGE_LOG_BASE entries) := by
  by_cases hn0 : n = 0
  · -- Empty log: the head BEQ takes the zero arm.
    subst hn0
    have hemp : entries = [] := List.eq_nil_of_length_eq_zero hlen
    subst hemp
    have coreF := cpsTripleWithin_frameR
      ((((.x14)) ↦ᵣ x14old) ** (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       evmWordIs envAddr addrHash **
       storageLogIs TRANSIENT_STORAGE_LOG_BASE ([] : List StorageLogEntry))
      (by pcFree)
      (evm_tload_empty_spec_within base envAddr sp x15old
        (slotKey.getLimbN 0) (slotKey.getLimbN 1)
        (slotKey.getLimbN 2) (slotKey.getLimbN 3))
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) coreF)
    · rw [evmWordIs_flat sp slotKey] at hp
      xperm_hyp hp
    · rw [transientLookup_nil, evmWordIs_zero]
      exact sepConj_own4 (v1 := x14old) (v2 := BitVec.ofNat 64 0)
        (v3 := x16old) (v4 := x17old) h (by xperm_hyp hq)
  · -- Nonempty log: head then loop.
    have hne : entries ≠ [] := by
      intro h; apply hn0; rw [← hlen, h]; rfl
    have headF := cpsTripleWithin_frameR
      ((((.x12)) ↦ᵣ sp) ** (((.x17)) ↦ᵣ x17old) **
       evmWordIs envAddr addrHash ** evmWordIs sp slotKey **
       storageLogIs TRANSIENT_STORAGE_LOG_BASE entries)
      (by pcFree)
      (evm_tload_head_spec_within base envAddr x14old x15old x16old n
        (ofNat64_ne_zero hn0 hcap))
    have loop := evm_tload_loop_spec_within (base + 28) envAddr sp
      addrHash slotKey entries hne (by rw [hlen]; exact hcap)
    rw [hlen] at loop
    have loopF := cpsTripleWithin_frameR
      ((envAddr + 464) ↦ₘ BitVec.ofNat 64 n) (by pcFree)
      (cpsTripleWithin_extend_code (loop_sub_full base) loop)
    have comp := cpsTripleWithin_seq_perm_same_cr
      (fun h hq =>
        sepConj_mono_left
          (sepConj_own2 (r1 := .x16) (r2 := .x17)
            (v1 := BitVec.ofNat 64 (n * 128)) (v2 := x17old))
          h (by xperm_hyp hq))
      headF loopF
    rw [show (base + 28 : Word) + 160 = base + 188 from by bv_omega] at comp
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq) comp

/-! ## Public stack-level witness -/

/-- **TLOAD stack spec** (the `.proven` witness): with the transient log of
    length `n` (`transientLogLenIs`/`storageLogIs`), the executing frame's
    `env.ADDRESS` word, and the slot key at the stack top, the reverse scan
    replaces the stack top IN PLACE (pop-1-push-1: `x12` unchanged) by
    `transientLookup addrHash slotKey entries` — the `current` of the
    most-recent matching TSTORE entry, or 0 when none matches (EIP-1153).
    The log, its length cell, and the frame address are preserved; the
    scratch registers `x14`–`x17` end clobbered (`regOwn`). `hcap` is the
    dispatcher-guaranteed arena-capacity shape fact. -/
theorem evm_tload_stack_spec_within
    (n : Nat) (codeBase envAddr sp : Word)
    (x14old x15old x16old x17old : Word)
    (addrHash slotKey : EvmWord)
    (entries : List StorageLogEntry) (hlen : entries.length = n)
    (hcap : n < 2 ^ 64) (rest : List EvmWord) :
    cpsTripleWithin (7 + 34 * n) codeBase (codeBase + 188)
      (evm_tload_code .x20 codeBase)
      ((((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) **
       (((.x14)) ↦ᵣ x14old) ** (((.x15)) ↦ᵣ x15old) **
       (((.x16)) ↦ᵣ x16old) ** (((.x17)) ↦ᵣ x17old) **
       (((.x0)) ↦ᵣ (0 : Word)) **
       transientLogLenIs envAddr n **
       storageLogIs TRANSIENT_STORAGE_LOG_BASE entries **
       evmWordIs envAddr addrHash **
       evmStackIs sp (slotKey :: rest))
      (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
       (((.x20)) ↦ᵣ envAddr) ** (((.x12)) ↦ᵣ sp) **
       (((.x0)) ↦ᵣ (0 : Word)) **
       transientLogLenIs envAddr n **
       storageLogIs TRANSIENT_STORAGE_LOG_BASE entries **
       evmWordIs envAddr addrHash **
       evmStackIs sp (transientLookup addrHash slotKey entries :: rest)) := by
  have framed := cpsTripleWithin_frameR (evmStackIs (sp + 32) rest)
    (by pcFree)
    (evm_tload_spec_within n codeBase envAddr sp x14old x15old x16old x17old
      addrHash slotKey entries hlen hcap)
  have hoff : (BitVec.ofNat 64 EvmEnv.transientLogLengthOff) = (464 : Word) := by
    decide
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) framed
  · rw [evmStackIs_cons] at hp
    simp only [transientLogLenIs, hoff] at hp
    xperm_hyp hp
  · rw [evmStackIs_cons]
    simp only [transientLogLenIs, hoff]
    xperm_hyp hq

end Transient
end EvmAsm.Evm64
