/-
  EvmAsm.Evm64.MulMod.ReduceInnerStepSpecs

  Full-code lifting substrate for MULMOD reducer inner-step subpath specs.
-/

import EvmAsm.Evm64.MulMod.Program
import EvmAsm.Evm64.MulMod.ReduceCorrect
import EvmAsm.Evm64.MulMod.ReduceInnerStepPrefix
import EvmAsm.Evm64.MulMod.ReduceInnerStepCompare
import EvmAsm.Evm64.MulMod.ReduceInnerStepTail
import EvmAsm.Evm64.MulMod.ReduceInnerStepSubtract
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPermPure
import EvmAsm.Rv64.BitAux

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- Full code requirement for one reducer inner step. -/
abbrev evm_mulmod_reduce512_inner_step_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_reduce512_inner_step

theorem evm_mulmod_reduce512_inner_step_shift_prefix_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_shift_prefix_code base a = some i →
      evm_mulmod_reduce512_inner_step_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_shift_prefix_code
  unfold evm_mulmod_reduce512_inner_step_code
  refine CodeReq.ofProg_mono_sub base base
    evm_mulmod_reduce512_inner_step evm_mulmod_reduce512_inner_step_shift_prefix
    0 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 0) = (0 : Word) by decide]
    bv_omega
  · rfl
  · decide
  · decide

/-- The new `SRLI .x8 .x5 63` at byte 84 (program index 21) is subsumed by the
    full inner-step CodeReq. -/
theorem evm_mulmod_reduce512_inner_step_srli_carry_code_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 84) (.SRLI .x8 .x5 (63 : BitVec 6)) a = some i →
      evm_mulmod_reduce512_inner_step_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_code
  rw [← CodeReq.ofProg_singleton]
  refine CodeReq.ofProg_mono_sub base (base + 84)
    evm_mulmod_reduce512_inner_step [.SRLI .x8 .x5 (63 : BitVec 6)]
    21 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 21) = (84 : Word) by decide]
  · rfl
  · decide
  · decide

/-- The new `BNE .x8 .x0 (64)` carry branch at byte 88 (program index 22) is
    subsumed by the full inner-step CodeReq. -/
theorem evm_mulmod_reduce512_inner_step_bne_carry_code_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 88) (.BNE .x8 .x0 (64 : BitVec 13)) a = some i →
      evm_mulmod_reduce512_inner_step_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_code
  rw [← CodeReq.ofProg_singleton]
  refine CodeReq.ofProg_mono_sub base (base + 88)
    evm_mulmod_reduce512_inner_step [.BNE .x8 .x0 (64 : BitVec 13)]
    22 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 22) = (88 : Word) by decide]
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_compare_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_compare_code (base + 8) a = some i →
      evm_mulmod_reduce512_inner_step_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_compare_code
  unfold evm_mulmod_reduce512_inner_step_code
  rw [show (base + 8 : Word) + 84 = base + 92 by bv_omega]
  refine CodeReq.ofProg_mono_sub base (base + 92)
    evm_mulmod_reduce512_inner_step evm_mulmod_reduce512_inner_step_compare
    23 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 23) = (92 : Word) by decide]
  · rfl
  · decide
  · decide

theorem evm_mulmod_reduce512_inner_step_subtract_store_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_subtract_store_code (base + 8) a = some i →
      evm_mulmod_reduce512_inner_step_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_subtract_store_code
  unfold evm_mulmod_reduce512_inner_step_code
  rw [show (base + 8 : Word) + 144 = base + 152 by bv_omega]
  refine CodeReq.ofProg_mono_sub base (base + 152)
    evm_mulmod_reduce512_inner_step evm_mulmod_reduce512_inner_step_subtract_store
    38 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 38) = (152 : Word) by decide]
  · rfl
  · decide
  · decide

/-- The loop-control tail of the (carry-aware) inner step now lives at byte 256
    (program index 64) with the loop-back `BNE` offset `-260`. -/
def evm_mulmod_reduce512_inner_step_tail_carry : Program :=
  ADDI .x15 .x15 4095 ;;
  BNE .x15 .x0 (-260 : BitVec 13)

theorem evm_mulmod_reduce512_inner_step_tail_code_sub (base : Word) :
    ∀ a i, CodeReq.ofProg (base + 256) evm_mulmod_reduce512_inner_step_tail_carry a = some i →
      evm_mulmod_reduce512_inner_step_code base a = some i := by
  unfold evm_mulmod_reduce512_inner_step_code
  refine CodeReq.ofProg_mono_sub base (base + 256)
    evm_mulmod_reduce512_inner_step evm_mulmod_reduce512_inner_step_tail_carry
    64 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 64) = (256 : Word) by decide]
  · rfl
  · decide
  · decide

/-- Carry-aware loop-control tail branch spec at byte 256: decrement `x15`, then
    `BNE` back to `base` (loop) or fall through to `base + 264` (done). Mirrors
    `evm_mulmod_reduce512_inner_step_tail_spec_within` at the shifted offset with
    the `-260` loop-back. -/
theorem evm_mulmod_reduce512_inner_step_tail_carry_spec_within
    (base x15 : Word) :
    cpsBranchWithin 2 (base + 256)
      (CodeReq.ofProg (base + 256) evm_mulmod_reduce512_inner_step_tail_carry)
      ((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)))
      base (mulModReduceTailPost x15 false)
      (base + 264) (mulModReduceTailPost x15 true) := by
  rw [show CodeReq.ofProg (base + 256) evm_mulmod_reduce512_inner_step_tail_carry =
      (CodeReq.singleton (base + 256) (.ADDI .x15 .x15 4095)).union
        (CodeReq.singleton (base + 260) (.BNE .x15 .x0 (-260 : BitVec 13))) by
    unfold evm_mulmod_reduce512_inner_step_tail_carry
    show CodeReq.ofProg (base + 256)
        [.ADDI .x15 .x15 4095, .BNE .x15 .x0 (-260 : BitVec 13)] = _
    rw [CodeReq.ofProg_pair]
    rw [show (base + 256 : Word) + 4 = base + 260 by bv_omega]]
  unfold mulModReduceTailPost
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hnext : (base + 256 : Word) + 4 = base + 260 := by bv_omega
  have hfallthrough : (base + 260 : Word) + 4 = base + 264 := by bv_omega
  have hse : signExtend13 ((-260 : BitVec 13)) = (18446744073709551356 : Word) := by
    decide
  have hloop : (base + 260 : Word) + signExtend13 ((-260 : BitVec 13)) = base := by
    rw [hse]
    bv_omega
  have hdisjoint : CodeReq.Disjoint
      (CodeReq.singleton (base + 256) (.ADDI .x15 .x15 4095))
      (CodeReq.singleton (base + 260) (.BNE .x15 .x0 (-260 : BitVec 13))) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have haddi_raw := addi_spec_gen_same_within .x15 x15 4095 (base + 256) (by decide)
  rw [hnext] at haddi_raw
  have haddi : cpsTripleWithin 1 (base + 256) (base + 260)
      (CodeReq.singleton (base + 256) (.ADDI .x15 .x15 4095))
      ((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x15 ↦ᵣ (x15 + signExtend12 (4095 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) haddi_raw
  have hbne := bne_spec_gen_within .x15 .x0 (-260 : BitVec 13)
    (x15 + signExtend12 (4095 : BitVec 12)) (0 : Word) (base + 260)
  rw [hloop, hfallthrough] at hbne
  simpa only [Nat.reduceAdd, sepConj_assoc'] using
    (cpsTripleWithin_seq_cpsBranchWithin_with_perm hdisjoint
      (fun _ hp => hp) haddi hbne)

theorem evm_mulmod_reduce512_inner_step_shift_prefix_full_code_spec_within
    (sp base x17Old r0 r1 r2 r3 v5 v6 v19 v20 : Word) :
    cpsTripleWithin 21 base (base + 84)
      (evm_mulmod_reduce512_inner_step_code base)
      ((.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3))
      (mulModReduceShiftPrefixPost sp x17Old r0 r1 r2 r3) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_shift_prefix_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_shift_prefix_spec_within
      sp base x17Old r0 r1 r2 r3 v5 v6 v19 v20)

theorem evm_mulmod_reduce512_inner_step_compare_ge_full_code_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hge : mulModReduceRemGE r n) :
    cpsTripleWithin 15 (base + 92) (base + 152)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceComparePre sp x6Old x7Old r n ** ⌜mulModReduceRemGE r n⌝)
      (mulModReduceComparePost sp r n true) := by
  have h := cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_ge_spec_within
      sp (base + 8) x6Old x7Old r n hge)
  rwa [show (base + 8 : Word) + 84 = base + 92 by bv_omega,
    show (base + 8 : Word) + 144 = base + 152 by bv_omega] at h

theorem evm_mulmod_reduce512_inner_step_compare_lt_full_code_spec_within
    (sp base x6Old x7Old : Word) (r n : EvmWord)
    (hlt : mulModReduceRemLT r n) :
    cpsTripleWithin 15 (base + 92) (base + 256)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceComparePre sp x6Old x7Old r n ** ⌜mulModReduceRemLT r n⌝)
      (mulModReduceComparePost sp r n false) := by
  have h := cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_compare_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_compare_lt_spec_within
      sp (base + 8) x6Old x7Old r n hlt)
  rwa [show (base + 8 : Word) + 84 = base + 92 by bv_omega,
    show (base + 8 : Word) + 248 = base + 256 by bv_omega] at h

theorem evm_mulmod_reduce512_inner_step_subtract_store_full_code_spec_within
    (sp base v5 v6 v7 v10 v11 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 26 (base + 152) (base + 256)
      (evm_mulmod_reduce512_inner_step_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
       mulModReduceCompareMem sp r n)
      (mulModReduceSubtractPost sp r n) := by
  have h := cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_subtract_store_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_subtract_store_spec_within
      sp (base + 8) v5 v6 v7 v10 v11 v13 r n)
  rwa [show (base + 8 : Word) + 144 = base + 152 by bv_omega,
    show (base + 8 : Word) + 248 = base + 256 by bv_omega] at h

theorem evm_mulmod_reduce512_inner_step_tail_full_code_spec_within
    (base x15 : Word) :
    cpsBranchWithin 2 (base + 256)
      (evm_mulmod_reduce512_inner_step_code base)
      ((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)))
      base (mulModReduceTailPost x15 false)
      (base + 264) (mulModReduceTailPost x15 true) :=
  cpsBranchWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_tail_code_sub base)
    (h := evm_mulmod_reduce512_inner_step_tail_carry_spec_within base x15)


/-! ## Carry branch -/

/-- Bit-255 of the remainder (the shift carry-out) is detected by the high limb's
    top bit: `(r.getLimbN 3) >>> 63 ≠ 0 ↔ r.getLsbD 255 = true`. -/
theorem getLimbN3_ushr63_ne_zero_iff_getLsbD255 (r : EvmWord) :
    (EvmWord.getLimbN r 3 >>> 63 ≠ 0) ↔ r.getLsbD 255 = true := by
  have hbit : (EvmWord.getLimbN r 3).getLsbD 63 = r.getLsbD 255 := by
    rw [EvmWord.getLimbN_lt r 3 (by decide)]
    unfold EvmWord.getLimb
    rw [BitVec.getLsbD_extractLsb']
    simp
  rcases EvmAsm.Rv64.BitAux.ushr63_bool (EvmWord.getLimbN r 3) with h0 | h1
  · rw [h0]
    have hb : (EvmWord.getLimbN r 3).getLsbD 63 = false := by
      have : (EvmWord.getLimbN r 3 >>> 63).getLsbD 0 = false := by rw [h0]; rfl
      rwa [BitVec.getLsbD_ushiftRight, Nat.add_zero] at this
    rw [hbit] at hb
    rw [hb]; simp
  · rw [h1]
    have hb : (EvmWord.getLimbN r 3).getLsbD 63 = true := by
      have : (EvmWord.getLimbN r 3 >>> 63).getLsbD 0 = true := by rw [h1]; rfl
      rwa [BitVec.getLsbD_ushiftRight, Nat.add_zero] at this
    rw [hbit] at hb
    rw [hb]; simp

/-- Carry-branch (`BNE .x8 .x0 (64)` at byte 88, program index 22) spec over the
    full inner-step code. The carry bit `c = r3 >>> 63` (held in `x8`) selects:
    when `c ≠ 0` (remainder bit 255 set) branch to the subtract entry `base+152`;
    when `c = 0` fall through to the compare ladder at `base+92`. The exits carry
    the `getLsbD 255` reading of the carry. -/
theorem evm_mulmod_reduce512_inner_step_carry_branch_spec_within
    (base : Word) (r : EvmWord) :
    cpsBranchWithin 1 (base + 88)
      (evm_mulmod_reduce512_inner_step_code base)
      ((.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) ** (.x0 ↦ᵣ (0 : Word)))
      (base + 152)
        (((.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) **
          ⌜r.getLsbD 255 = true⌝)
      (base + 92)
        (((.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) **
          ⌜r.getLsbD 255 = false⌝) := by
  have hbne := bne_spec_gen_within .x8 .x0 (64 : BitVec 13)
    (EvmWord.getLimbN r 3 >>> 63) (0 : Word) (base + 88)
  rw [show (base + 88 : Word) + signExtend13 (64 : BitVec 13) = base + 152 by
      rw [show signExtend13 (64 : BitVec 13) = (64 : Word) by decide]; bv_omega,
    show (base + 88 : Word) + 4 = base + 92 by bv_omega] at hbne
  have hlift := cpsBranchWithin_extend_code
    (hmono := evm_mulmod_reduce512_inner_step_bne_carry_code_sub base)
    (h := hbne)
  refine cpsBranchWithin_weaken (fun _ hp => hp) ?_ ?_ hlift
  · intro h hp
    rw [← sepConj_assoc'] at hp
    refine (sepConj_pure_right h).2 ⟨((sepConj_pure_right h).1 hp).1, ?_⟩
    exact (getLimbN3_ushr63_ne_zero_iff_getLsbD255 r).1 ((sepConj_pure_right h).1 hp).2
  · intro h hp
    rw [← sepConj_assoc'] at hp
    refine (sepConj_pure_right h).2 ⟨((sepConj_pure_right h).1 hp).1, ?_⟩
    have heq : EvmWord.getLimbN r 3 >>> 63 = 0 := ((sepConj_pure_right h).1 hp).2
    rw [Bool.eq_false_iff]
    intro hc
    exact ((getLimbN3_ushr63_ne_zero_iff_getLsbD255 r).2 hc) heq

theorem evm_mulmod_reduce512_inner_step_tail_done_full_code_spec_within
    (base x15 : Word)
    (h_done : x15 + signExtend12 (4095 : BitVec 12) = 0) :
    cpsTripleWithin 2 (base + 256) (base + 264)
      (evm_mulmod_reduce512_inner_step_code base)
      (((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜x15 + signExtend12 (4095 : BitVec 12) = 0⌝)
      (mulModReduceTailPost x15 true) := by
  have hbr := evm_mulmod_reduce512_inner_step_tail_full_code_spec_within base x15
  have hdone_pre : cpsBranchWithin 2 (base + 256)
      (evm_mulmod_reduce512_inner_step_code base)
      (((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜x15 + signExtend12 (4095 : BitVec 12) = 0⌝)
      base (mulModReduceTailPost x15 false)
      (base + 264) (mulModReduceTailPost x15 true) :=
    cpsBranchWithin_weaken (fun h hp => ((sepConj_pure_right h).1 hp).1)
      (fun _ hp => hp) (fun _ hp => hp) hbr
  exact cpsBranchWithin_ntakenPath hdone_pre (by
    intro h hp
    unfold mulModReduceTailPost at hp
    simp only [Bool.false_eq_true, ↓reduceIte] at hp
    obtain ⟨hregs, h_ne⟩ := (sepConj_pure_right h).1 hp
    exact h_ne h_done)

theorem evm_mulmod_reduce512_inner_step_tail_loop_full_code_spec_within
    (base x15 : Word)
    (h_loop : x15 + signExtend12 (4095 : BitVec 12) ≠ 0) :
    cpsTripleWithin 2 (base + 256) base
      (evm_mulmod_reduce512_inner_step_code base)
      (((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜x15 + signExtend12 (4095 : BitVec 12) ≠ 0⌝)
      (mulModReduceTailPost x15 false) := by
  have hbr := evm_mulmod_reduce512_inner_step_tail_full_code_spec_within base x15
  have hloop_pre : cpsBranchWithin 2 (base + 256)
      (evm_mulmod_reduce512_inner_step_code base)
      (((.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))) **
        ⌜x15 + signExtend12 (4095 : BitVec 12) ≠ 0⌝)
      base (mulModReduceTailPost x15 false)
      (base + 264) (mulModReduceTailPost x15 true) :=
    cpsBranchWithin_weaken (fun h hp => ((sepConj_pure_right h).1 hp).1)
      (fun _ hp => hp) (fun _ hp => hp) hbr
  exact cpsBranchWithin_takenPath hloop_pre (by
    intro h hp
    unfold mulModReduceTailPost at hp
    simp only [ite_true] at hp
    obtain ⟨hregs, h_eq⟩ := (sepConj_pure_right h).1 hp
    exact h_loop h_eq)



/-- Subtract-store precondition with compare-clobbered registers kept as ownership. -/
@[irreducible]
def mulModReduceSubtractOwnPre
    (sp v5 v10 v11 v13 : Word) (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** regOwn .x6 ** regOwn .x7 **
  (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
  mulModReduceCompareMem sp r n

theorem evm_mulmod_reduce512_inner_step_subtract_store_own_full_code_spec_within
    (sp base v5 v10 v11 v13 : Word) (r n : EvmWord) :
    cpsTripleWithin 26 (base + 152) (base + 256)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceSubtractOwnPre sp v5 v10 v11 v13 r n)
      (mulModReduceSubtractPost sp r n) := by
  have hown7 : cpsTripleWithin 26 (base + 152) (base + 256)
      (evm_mulmod_reduce512_inner_step_code base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** regOwn .x6 **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
        mulModReduceCompareMem sp r n) ** regOwn .x7)
      (mulModReduceSubtractPost sp r n) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7) ?_
    intro v7
    have hown6 : cpsTripleWithin 26 (base + 152) (base + 256)
        (evm_mulmod_reduce512_inner_step_code base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) **
          (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x13 ↦ᵣ v13) **
          mulModReduceCompareMem sp r n ** (.x7 ↦ᵣ v7)) ** regOwn .x6)
        (mulModReduceSubtractPost sp r n) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6) ?_
      intro v6
      exact cpsTripleWithin_weaken (fun h hp => by
          xperm_hyp hp)
        (fun _ hp => hp)
        (evm_mulmod_reduce512_inner_step_subtract_store_full_code_spec_within
          sp base v5 v6 v7 v10 v11 v13 r n)
    exact cpsTripleWithin_weaken (fun h hp => by
        xperm_hyp hp)
      (fun _ hp => hp) hown6
  exact cpsTripleWithin_weaken (fun h hp => by
      unfold mulModReduceSubtractOwnPre at hp
      xperm_hyp hp)
    (fun _ hp => hp) hown7

/-- Folded precondition for the reducer inner-step no-subtract path. -/
@[irreducible]
def mulModReduceInnerStepNoSubtractPre
    (sp x17Old x5Old x6Old x7Old x8Old x15 x19Old x20Old : Word)
    (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) **
  (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) ** (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x19 ↦ᵣ x19Old) ** (.x20 ↦ᵣ x20Old) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Folded postcondition for the reducer inner-step no-subtract path. -/
@[irreducible]
def mulModReduceInnerStepNoSubtractPost
    (sp x17Old x15 : Word) (r n : EvmWord) (done : Bool) : Assertion :=
  let shifted := mulModReduceShiftInBit r (mulModReduceInputBit x17Old)
  mulModReduceTailPost x15 done **
  mulModReduceComparePost sp shifted n false **
  (.x17 ↦ᵣ (x17Old <<< 1)) **
  (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
  (.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) **
  (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
  (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63))

/-- Compose carry-prefix, carry-branch (not-taken), compare-LT, and tail into the
    no-subtract reducer inner-step path. The no-subtract path additionally
    requires the shift carry-out (remainder bit 255) to be FALSE. -/
theorem evm_mulmod_reduce512_inner_step_no_subtract_path_spec_within
    (sp base x17Old x5Old x6Old x7Old x8Old x15 x19Old x20Old : Word)
    (r n : EvmWord)
    (hcarry : r.getLsbD 255 = false)
    (hlt : mulModReduceRemLT (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n) :
    cpsBranchWithin 40 base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepNoSubtractPre sp x17Old x5Old x6Old x7Old x8Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemLT (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n⌝)
      base (mulModReduceInnerStepNoSubtractPost sp x17Old x15 r n false)
      (base + 264) (mulModReduceInnerStepNoSubtractPost sp x17Old x15 r n true) := by
  let shifted := mulModReduceShiftInBit r (mulModReduceInputBit x17Old)
  let prefixFrame : Assertion :=
    (.x7 ↦ᵣ x7Old) ** (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
    ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
    ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
    ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
    ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3) **
    ⌜mulModReduceRemLT shifted n⌝
  let compareFrame : Assertion :=
    (.x17 ↦ᵣ (x17Old <<< 1)) **
    (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
    (.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) **
    (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
    (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
    (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word))
  let tailFrame : Assertion :=
    mulModReduceComparePost sp shifted n false **
    (.x17 ↦ᵣ (x17Old <<< 1)) **
    (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
    (.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) **
    (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
    (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63))
  -- Carry prefix (22 instructions, base → base+88), producing x8 = r3 >>> 63.
  have hprefix0 := evm_mulmod_reduce512_inner_step_shift_prefix_carry_spec_within
    sp base x17Old (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
    (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) x5Old x6Old x19Old x20Old x8Old
  have hprefix := cpsTripleWithin_frameR prefixFrame (by pcFree) hprefix0
  have hprefixTop : cpsTripleWithin 22 base (base + 88)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepNoSubtractPre sp x17Old x5Old x6Old x7Old x8Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemLT shifted n⌝)
      ((mulModReduceShiftPrefixPost sp x17Old (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
        (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) **
        (.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63))) ** prefixFrame) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold mulModReduceInnerStepNoSubtractPre at hp
      dsimp only [prefixFrame, shifted] at hp ⊢
      xperm_hyp hp)
      (fun _ hp => hp) hprefix
  -- Carry branch (1 instruction, base+88), not taken because the carry is FALSE.
  have hcarry_branch := evm_mulmod_reduce512_inner_step_carry_branch_spec_within base r
  have hcarry_ntaken : cpsTripleWithin 1 (base + 88) (base + 92)
      (evm_mulmod_reduce512_inner_step_code base)
      ((.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hp => ((sepConj_pure_right h).1 hp).1)
      (cpsBranchWithin_ntakenPath hcarry_branch (by
        intro h hp
        have h255 : r.getLsbD 255 = true := ((sepConj_pure_right h).1 hp).2
        rw [hcarry] at h255; exact absurd h255 (by decide)))
  -- Frame the carry-branch with everything except x8/x0.
  let branchFrame : Assertion :=
    (.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ (x17Old <<< 1)) ** (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
    (.x6 ↦ᵣ EvmWord.getLimbN shifted 3) **
    (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) ** (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
    ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 0) **
    ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 1) **
    ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 2) **
    ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 3) **
    (.x7 ↦ᵣ x7Old) ** (.x15 ↦ᵣ x15) **
    ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
    ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
    ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
    ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3) **
    ⌜mulModReduceRemLT shifted n⌝
  have hcarry_framed := cpsTripleWithin_frameR branchFrame (by
    dsimp only [branchFrame, prefixFrame]; pcFree) hcarry_ntaken
  -- prefix then carry-branch: base → base+92.
  have hprefix_carry : cpsTripleWithin (22 + 1) base (base + 92)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepNoSubtractPre sp x17Old x5Old x6Old x7Old x8Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemLT shifted n⌝)
      (((.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) ** branchFrame) :=
    cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      unfold mulModReduceShiftPrefixPost at hp
      have hrem : mulModReduceRemWord (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
          (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) = r := by
        apply (EvmWord.eq_iff_limbs).2
        intro i
        fin_cases i <;> simp [EvmWord.getLimb_as_getLimbN_0,
          EvmWord.getLimb_as_getLimbN_1, EvmWord.getLimb_as_getLimbN_2,
          EvmWord.getLimb_as_getLimbN_3]
      rw [hrem] at hp
      dsimp only [shifted, prefixFrame, branchFrame] at hp ⊢
      xperm_hyp hp)
      hprefixTop hcarry_framed
  -- Compare-LT (15 instructions, base+92 → base+256).
  have hcompare0 := evm_mulmod_reduce512_inner_step_compare_lt_full_code_spec_within
    sp base (EvmWord.getLimbN shifted 3) x7Old shifted n hlt
  have hcompare := cpsTripleWithin_frameR compareFrame (by pcFree) hcompare0
  have hprefix_compare : cpsTripleWithin (22 + 1 + 15) base (base + 256)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepNoSubtractPre sp x17Old x5Old x6Old x7Old x8Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemLT shifted n⌝)
      (mulModReduceComparePost sp shifted n false ** compareFrame) :=
    cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      unfold mulModReduceComparePre mulModReduceCompareMem
      dsimp only [shifted, branchFrame, prefixFrame, compareFrame] at hp ⊢
      xperm_hyp hp)
      hprefix_carry hcompare
  have htail0 := evm_mulmod_reduce512_inner_step_tail_full_code_spec_within base x15
  have htail := cpsBranchWithin_frameR tailFrame (by
    dsimp only [tailFrame]
    unfold mulModReduceComparePost mulModReduceCompareMem
    pcFree) htail0
  have hbranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr (fun h hp => by
      dsimp only [compareFrame, tailFrame] at hp ⊢
      xperm_hyp hp)
    hprefix_compare htail
  change cpsBranchWithin (22 + 1 + 15 + 2) base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepNoSubtractPre sp x17Old x5Old x6Old x7Old x8Old x15 x19Old x20Old r n **
        ⌜mulModReduceRemLT shifted n⌝)
      base (mulModReduceInnerStepNoSubtractPost sp x17Old x15 r n false)
      (base + 264) (mulModReduceInnerStepNoSubtractPost sp x17Old x15 r n true)
  exact cpsBranchWithin_weaken (fun _ hp => hp) (fun h hp => by
      unfold mulModReduceInnerStepNoSubtractPost
      dsimp only [shifted, tailFrame] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      unfold mulModReduceInnerStepNoSubtractPost
      dsimp only [shifted, tailFrame] at hp ⊢
      xperm_hyp hp)
    hbranch


/-- The carry-aware subtract decision for one reducer step: subtract the modulus
    when the shift overflowed (`r.getLsbD 255`) or the truncated shifted remainder
    is already `≥ n`. Mirrors the condition in `mulModReduceStepCarry`. -/
def mulModReduceSubtractDecision (r n : EvmWord) (x17Old : Word) : Prop :=
  r.getLsbD 255 = true ∨
    ¬ ((mulModReduceShiftInBit r (mulModReduceInputBit x17Old)).toNat < n.toNat)

/-- Folded precondition for the reducer inner-step subtract path. -/
@[irreducible]
def mulModReduceInnerStepSubtractPre
    (sp x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old x15 x19Old x20Old : Word)
    (r n : EvmWord) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) **
  (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
  (.x13 ↦ᵣ x13Old) ** (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x19 ↦ᵣ x19Old) ** (.x20 ↦ᵣ x20Old) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN r 3) **
  ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
  ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
  ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
  ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3)

/-- Folded postcondition for the reducer inner-step subtract path. -/
@[irreducible]
def mulModReduceInnerStepSubtractPost
    (sp x17Old x15 : Word) (r n : EvmWord) (done : Bool) : Assertion :=
  let shifted := mulModReduceShiftInBit r (mulModReduceInputBit x17Old)
  mulModReduceTailPost x15 done **
  mulModReduceSubtractPost sp shifted n **
  (.x17 ↦ᵣ (x17Old <<< 1)) **
  (.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) **
  (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
  (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
  ⌜mulModReduceSubtractDecision r n x17Old⌝

/-- Drop the path-selecting pure fact carried by the compare-ladder post. -/
theorem mulModReduceComparePost_drop (sp : Word) (r n : EvmWord) (b : Bool) :
    ∀ h, mulModReduceComparePost sp r n b h →
      ((.x12 ↦ᵣ sp) ** regOwn .x6 ** regOwn .x7 ** mulModReduceCompareMem sp r n) h := by
  intro h hp
  unfold mulModReduceComparePost at hp
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (fun _ hq => ((sepConj_pure_right _).1 hq).1))) h hp

/-- Compose carry-prefix, the carry/compare merge into the subtract entry,
    subtract-store, and tail into the subtract reducer path. The subtract path
    triggers when the shift overflowed (`r.getLsbD 255`) OR the truncated shifted
    remainder is `≥ n`. -/
theorem evm_mulmod_reduce512_inner_step_subtract_path_spec_within
    (sp base x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old x15 x19Old x20Old : Word)
    (r n : EvmWord)
    (hdec : mulModReduceSubtractDecision r n x17Old) :
    cpsBranchWithin 66 base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old x15 x19Old x20Old r n **
        ⌜mulModReduceSubtractDecision r n x17Old⌝)
      base (mulModReduceInnerStepSubtractPost sp x17Old x15 r n false)
      (base + 264) (mulModReduceInnerStepSubtractPost sp x17Old x15 r n true) := by
  let shifted := mulModReduceShiftInBit r (mulModReduceInputBit x17Old)
  -- Frame carried alongside the subtract-store (everything but its own footprint).
  let subtractFrame : Assertion :=
    (.x17 ↦ᵣ (x17Old <<< 1)) **
    (.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) **
    (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
    (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
    (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
    ⌜mulModReduceSubtractDecision r n x17Old⌝
  let tailFrame : Assertion :=
    mulModReduceSubtractPost sp shifted n **
    (.x17 ↦ᵣ (x17Old <<< 1)) **
    (.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) **
    (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
    (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
    ⌜mulModReduceSubtractDecision r n x17Old⌝
  -- The carry prefix (22 instructions, base → base+88, exposing x8 = r3 >>> 63).
  let prefixFrame : Assertion :=
    (.x7 ↦ᵣ x7Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
    (.x13 ↦ᵣ x13Old) ** (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
    ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
    ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
    ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
    ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3) **
    ⌜mulModReduceSubtractDecision r n x17Old⌝
  have hprefix0 := evm_mulmod_reduce512_inner_step_shift_prefix_carry_spec_within
    sp base x17Old (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
    (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) x5Old x6Old x19Old x20Old x8Old
  have hprefix := cpsTripleWithin_frameR prefixFrame (by pcFree) hprefix0
  -- The post of the framed carry prefix, refolded over the subtract precondition.
  let prefixPost : Assertion :=
    (mulModReduceShiftPrefixPost sp x17Old (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
      (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) **
      (.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63))) ** prefixFrame
  have hprefixTop : cpsTripleWithin 22 base (base + 88)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old x15 x19Old x20Old r n **
        ⌜mulModReduceSubtractDecision r n x17Old⌝)
      prefixPost :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold mulModReduceInnerStepSubtractPre at hp
      dsimp only [prefixFrame, prefixPost, shifted] at hp ⊢
      xperm_hyp hp)
      (fun _ hp => hp) hprefix
  -- The subtract-store-own precondition (at base+152) with its frame.
  let subtractOwn : Assertion :=
    mulModReduceSubtractOwnPre sp (EvmWord.getLimbN r 3) x10Old x11Old x13Old shifted n **
    subtractFrame
  -- Merge sub-paths: base+88 → base+152 (≤ 16 steps), reaching the subtract entry.
  have hmerge : cpsTripleWithin 16 (base + 88) (base + 152)
      (evm_mulmod_reduce512_inner_step_code base) prefixPost subtractOwn := by
    have hcarry_branch := evm_mulmod_reduce512_inner_step_carry_branch_spec_within base r
    by_cases hc : r.getLsbD 255 = true
    · -- Carry set: branch TAKEN straight to the subtract entry (1 ≤ 16 steps).
      let takenFrame : Assertion :=
        (.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ (x17Old <<< 1)) ** (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
        (.x6 ↦ᵣ EvmWord.getLimbN shifted 3) **
        (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) ** (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 3) **
        (.x7 ↦ᵣ x7Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old) **
        (.x15 ↦ᵣ x15) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3) **
        ⌜mulModReduceSubtractDecision r n x17Old⌝
      have htaken : cpsTripleWithin 1 (base + 88) (base + 152)
          (evm_mulmod_reduce512_inner_step_code base)
          ((.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) ** (.x0 ↦ᵣ (0 : Word)))
          ((.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) :=
        cpsTripleWithin_weaken (fun _ hp => hp)
          (fun h hp => ((sepConj_pure_right h).1 hp).1)
          (cpsBranchWithin_takenPath hcarry_branch (by
            intro h hp
            have h255 : r.getLsbD 255 = false := ((sepConj_pure_right h).1 hp).2
            rw [hc] at h255; exact absurd h255 (by decide)))
      have htaken_framed := cpsTripleWithin_frameR takenFrame (by
        dsimp only [takenFrame]; pcFree) htaken
      refine cpsTripleWithin_mono_nSteps (show (1 : Nat) ≤ 16 by omega) ?_
      refine cpsTripleWithin_weaken ?_ ?_ htaken_framed
      · intro h hp
        dsimp only [prefixPost, prefixFrame] at hp
        unfold mulModReduceShiftPrefixPost at hp
        have hrem : mulModReduceRemWord (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
            (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) = r := by
          apply (EvmWord.eq_iff_limbs).2
          intro i
          fin_cases i <;> simp [EvmWord.getLimb_as_getLimbN_0,
            EvmWord.getLimb_as_getLimbN_1, EvmWord.getLimb_as_getLimbN_2,
            EvmWord.getLimb_as_getLimbN_3]
        rw [hrem] at hp
        dsimp only [takenFrame, shifted] at hp ⊢
        xperm_hyp hp
      · intro h hp
        dsimp only [subtractOwn, subtractFrame] at ⊢
        unfold mulModReduceSubtractOwnPre mulModReduceCompareMem
        dsimp only [takenFrame, shifted] at hp ⊢
        -- Convert the concrete x6 and x7 into ownership.
        have hp6 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x6 _))))) h hp
        have hp7 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (regIs_to_regOwn .x7 _))))))))))))
          h hp6
        xperm_hyp hp7
    · -- Carry clear: branch NOT-TAKEN to compare (1), then compare-GE (15) to base+152.
      have hge : mulModReduceRemGE shifted n := by
        rcases hdec with h | h
        · exact absurd h hc
        · unfold mulModReduceRemGE
          dsimp only [shifted]
          simpa only [BitVec.ult, Bool.not_eq_true, decide_eq_false_iff_not,
            decide_eq_true_eq] using h
      let compareFrame : Assertion :=
        (.x17 ↦ᵣ (x17Old <<< 1)) **
        (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
        (.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) **
        (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
        (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
        (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old) **
        (.x15 ↦ᵣ x15) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜mulModReduceSubtractDecision r n x17Old⌝
      -- Carry branch not taken: base+88 → base+92.
      have hntaken : cpsTripleWithin 1 (base + 88) (base + 92)
          (evm_mulmod_reduce512_inner_step_code base)
          ((.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) ** (.x0 ↦ᵣ (0 : Word)))
          ((.x8 ↦ᵣ (EvmWord.getLimbN r 3 >>> 63)) ** (.x0 ↦ᵣ (0 : Word))) :=
        cpsTripleWithin_weaken (fun _ hp => hp)
          (fun h hp => ((sepConj_pure_right h).1 hp).1)
          (cpsBranchWithin_ntakenPath hcarry_branch (by
            intro h hp
            have h255 : r.getLsbD 255 = true := ((sepConj_pure_right h).1 hp).2
            exact absurd h255 hc))
      let ntakenFrame : Assertion :=
        (.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ (x17Old <<< 1)) ** (.x5 ↦ᵣ EvmWord.getLimbN r 3) **
        (.x6 ↦ᵣ EvmWord.getLimbN shifted 3) **
        (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) ** (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
        ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 0) **
        ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 1) **
        ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 2) **
        ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 3) **
        (.x7 ↦ᵣ x7Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old) **
        (.x15 ↦ᵣ x15) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 0) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 1) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 2) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ EvmWord.getLimbN n 3) **
        ⌜mulModReduceSubtractDecision r n x17Old⌝
      have hntaken_framed := cpsTripleWithin_frameR ntakenFrame (by
        dsimp only [ntakenFrame]; pcFree) hntaken
      -- prefixPost → compare-GE precondition at base+92 (with compareFrame).
      have hprefix_to_compare : cpsTripleWithin 1 (base + 88) (base + 92)
          (evm_mulmod_reduce512_inner_step_code base) prefixPost
          (mulModReduceComparePre sp (EvmWord.getLimbN shifted 3) x7Old shifted n **
            compareFrame) :=
        cpsTripleWithin_weaken
          (fun h hp => by
            dsimp only [prefixPost, prefixFrame] at hp
            unfold mulModReduceShiftPrefixPost at hp
            have hrem : mulModReduceRemWord (EvmWord.getLimbN r 0) (EvmWord.getLimbN r 1)
                (EvmWord.getLimbN r 2) (EvmWord.getLimbN r 3) = r := by
              apply (EvmWord.eq_iff_limbs).2
              intro i
              fin_cases i <;> simp [EvmWord.getLimb_as_getLimbN_0,
                EvmWord.getLimb_as_getLimbN_1, EvmWord.getLimb_as_getLimbN_2,
                EvmWord.getLimb_as_getLimbN_3]
            rw [hrem] at hp
            dsimp only [ntakenFrame, shifted] at hp ⊢
            xperm_hyp hp)
          (fun h hp => by
            unfold mulModReduceComparePre mulModReduceCompareMem
            dsimp only [ntakenFrame, compareFrame, shifted] at hp ⊢
            xperm_hyp hp)
          hntaken_framed
      have hcompare0' := evm_mulmod_reduce512_inner_step_compare_ge_full_code_spec_within
        sp base (EvmWord.getLimbN shifted 3) x7Old shifted n hge
      have hcompare0 : cpsTripleWithin 15 (base + 92) (base + 152)
          (evm_mulmod_reduce512_inner_step_code base)
          (mulModReduceComparePre sp (EvmWord.getLimbN shifted 3) x7Old shifted n)
          (mulModReduceComparePost sp shifted n true) :=
        cpsTripleWithin_weaken
          (fun h hp => (sepConj_pure_right h).2 ⟨hp, hge⟩)
          (fun _ hp => hp) hcompare0'
      have hcompare := cpsTripleWithin_frameR compareFrame (by
        dsimp only [compareFrame]; pcFree) hcompare0
      have hcompose : cpsTripleWithin (1 + 15) (base + 88) (base + 152)
          (evm_mulmod_reduce512_inner_step_code base) prefixPost
          (mulModReduceComparePost sp shifted n true ** compareFrame) :=
        cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          dsimp only [compareFrame] at hp ⊢
          xperm_hyp hp)
          hprefix_to_compare hcompare
      refine cpsTripleWithin_mono_nSteps (show (1 + 15 : Nat) ≤ 16 by omega) ?_
      refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hcompose
      intro h hp
      -- Drop the redundant compare-ladder pure fact; the decision pure comes from
      -- `compareFrame`.
      have hp' := sepConj_mono_left (mulModReduceComparePost_drop sp shifted n true) h hp
      dsimp only [subtractOwn, subtractFrame] at ⊢
      unfold mulModReduceSubtractOwnPre mulModReduceCompareMem
      unfold mulModReduceCompareMem at hp'
      dsimp only [compareFrame, shifted] at hp' ⊢
      xperm_hyp hp'
  -- prefix-carry (22) then merge (16): base → base+152.
  have hprefix_subtract : cpsTripleWithin (22 + 16) base (base + 152)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old x15 x19Old x20Old r n **
        ⌜mulModReduceSubtractDecision r n x17Old⌝)
      subtractOwn :=
    cpsTripleWithin_seq_same_cr hprefixTop hmerge
  -- Subtract-store (26 instructions, base+152 → base+256).
  have hsubtract0 := evm_mulmod_reduce512_inner_step_subtract_store_own_full_code_spec_within
    sp base (EvmWord.getLimbN r 3) x10Old x11Old x13Old shifted n
  have hsubtract := cpsTripleWithin_frameR subtractFrame (by pcFree) hsubtract0
  have hthrough_subtract : cpsTripleWithin (22 + 16 + 26) base (base + 256)
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old x15 x19Old x20Old r n **
        ⌜mulModReduceSubtractDecision r n x17Old⌝)
      (mulModReduceSubtractPost sp shifted n ** subtractFrame) :=
    cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      dsimp only [subtractOwn, subtractFrame] at hp ⊢
      xperm_hyp hp)
      hprefix_subtract hsubtract
  have htail0 := evm_mulmod_reduce512_inner_step_tail_full_code_spec_within base x15
  have htail := cpsBranchWithin_frameR tailFrame (by
    dsimp only [tailFrame]
    unfold mulModReduceSubtractPost mulModReduceSubtractMem
    pcFree) htail0
  have hbranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr (fun h hp => by
      dsimp only [subtractFrame, tailFrame] at hp ⊢
      xperm_hyp hp)
    hthrough_subtract htail
  change cpsBranchWithin (22 + 16 + 26 + 2) base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old x15 x19Old x20Old r n **
        ⌜mulModReduceSubtractDecision r n x17Old⌝)
      base (mulModReduceInnerStepSubtractPost sp x17Old x15 r n false)
      (base + 264) (mulModReduceInnerStepSubtractPost sp x17Old x15 r n true)
  exact cpsBranchWithin_weaken (fun _ hp => hp) (fun h hp => by
      unfold mulModReduceInnerStepSubtractPost
      dsimp only [shifted, tailFrame] at hp ⊢
      xperm_hyp hp)
    (fun h hp => by
      unfold mulModReduceInnerStepSubtractPost
      dsimp only [shifted, tailFrame] at hp ⊢
      xperm_hyp hp)
    hbranch


/-! ## Full reducer inner-step composition

Compose the subtract and no-subtract reducer inner-step paths into one
branch specification whose folded post records a single bit step
`mulModReduceStep`: it shifts the consumed product bit into the remainder
and conditionally subtracts the modulus. -/

/-- Under the no-subtract (`<`) branch the bit step keeps the shifted-in
    remainder unchanged. -/
theorem mulModReduceStep_of_lt {r n : EvmWord} {bit : Bool}
    (hlt : mulModReduceRemLT (mulModReduceShiftInBit r bit) n) :
    mulModReduceStep r n bit = mulModReduceShiftInBit r bit := by
  have hlt' : (mulModReduceShiftInBit r bit).toNat < n.toNat := by
    unfold mulModReduceRemLT at hlt
    simpa only [BitVec.ult, decide_eq_true_eq] using hlt
  unfold mulModReduceStep
  simp only [hlt', if_true]

/-- Under the subtract (`≥`) branch the bit step subtracts the modulus from
    the shifted-in remainder. -/
theorem mulModReduceStep_of_ge {r n : EvmWord} {bit : Bool}
    (hge : mulModReduceRemGE (mulModReduceShiftInBit r bit) n) :
    mulModReduceStep r n bit = mulModReduceShiftInBit r bit - n := by
  have hge' : ¬ (mulModReduceShiftInBit r bit).toNat < n.toNat := by
    unfold mulModReduceRemGE at hge
    simpa only [BitVec.ult, decide_eq_true_eq] using hge
  unfold mulModReduceStep
  simp only [hge', if_false]

/-- When the carry-aware subtract decision holds, the carry-aware step subtracts
    the modulus. -/
theorem mulModReduceStepCarry_of_decision {r n : EvmWord} {x17Old : Word}
    (hdec : mulModReduceSubtractDecision r n x17Old) :
    mulModReduceStepCarry r n (mulModReduceInputBit x17Old)
      = mulModReduceShiftInBit r (mulModReduceInputBit x17Old) - n := by
  unfold mulModReduceStepCarry
  simp only [mulModReduceSubtractDecision] at hdec
  rw [if_pos hdec]

/-- When the carry-aware subtract decision fails (carry clear and `<`), the
    carry-aware step keeps the shifted-in remainder unchanged. -/
theorem mulModReduceStepCarry_of_not_decision {r n : EvmWord} {x17Old : Word}
    (hcarry : r.getLsbD 255 = false)
    (hlt : mulModReduceRemLT (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n) :
    mulModReduceStepCarry r n (mulModReduceInputBit x17Old)
      = mulModReduceShiftInBit r (mulModReduceInputBit x17Old) := by
  have hlt' : (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)).toNat < n.toNat := by
    unfold mulModReduceRemLT at hlt
    simpa only [BitVec.ult, decide_eq_true_eq] using hlt
  unfold mulModReduceStepCarry
  rw [if_neg]
  rw [not_or]
  exact ⟨by rw [hcarry]; exact (by decide), by rw [not_not]; exact hlt'⟩

/-- Folded precondition for the full reducer inner step.

It owns the loop-carried registers and the remainder/modulus memory window,
agreeing with the subtract-path precondition so both branch paths share it. -/
@[irreducible]
def mulModReduceInnerStepPre
    (sp x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old x15 x19Old x20Old : Word)
    (r n : EvmWord) : Assertion :=
  mulModReduceInnerStepSubtractPre sp x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old
    x15 x19Old x20Old r n

/-- Folded postcondition for the full reducer inner step.

The remainder window at `sp - 32 .. sp - 8` holds the limbs of one semantic step
`mulModReduceStep r n bit` (shift the consumed bit in, conditionally subtract
the modulus); the modulus window at `sp + 64..88` is preserved; the loop
counter `x15` is decremented and the `done` flag records whether it reached
zero. The scratch registers clobbered along the way are surrendered as
ownership. -/
@[irreducible]
def mulModReduceInnerStepPost
    (sp x17Old x15 : Word) (r n : EvmWord) (done : Bool) : Assertion :=
  let stepped := mulModReduceStepCarry r n (mulModReduceInputBit x17Old)
  mulModReduceTailPost x15 done **
  (.x12 ↦ᵣ sp) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
  (.x17 ↦ᵣ (x17Old <<< 1)) **
  (.x19 ↦ᵣ (EvmWord.getLimbN r 1 >>> 63)) **
  (.x20 ↦ᵣ (EvmWord.getLimbN r 2 >>> 63)) **
  mulModReduceCompareMem sp stepped n

/-- Surrender the subtract-path scratch registers as ownership. -/
theorem mulModReduceSubtractPost_regOwn (sp : Word) (r n : EvmWord) :
    ∀ h, mulModReduceSubtractPost sp r n h →
      ((.x12 ↦ᵣ sp) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** regOwn .x13 **
       mulModReduceSubtractMem sp r n) h := by
  intro h hp
  unfold mulModReduceSubtractPost at hp
  have hp1 := sepConj_mono_right (sepConj_mono_left
    (regIs_to_regOwn .x5 _)) h hp
  have hp2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (regIs_to_regOwn .x6 _))) h hp1
  have hp3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (regIs_to_regOwn .x7 _)))) h hp2
  have hp4 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _))))) h hp3
  have hp5 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (regIs_to_regOwn .x11 _)))))) h hp4
  have hp6 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (regIs_to_regOwn .x13 _))))))) h hp5
  xperm_hyp hp6

/-- Bridge the subtract-path post into the unified inner-step post. -/
theorem mulModReduceInnerStepPost_of_subtractPost
    (sp x17Old x15 : Word) (r n : EvmWord) (done : Bool)
    (hdec : mulModReduceSubtractDecision r n x17Old) :
    ∀ h, mulModReduceInnerStepSubtractPost sp x17Old x15 r n done h →
      mulModReduceInnerStepPost sp x17Old x15 r n done h := by
  intro h hp
  unfold mulModReduceInnerStepSubtractPost at hp
  -- Convert the subtract-store post's concrete scratch into ownership.
  have hp1 := sepConj_mono_right (sepConj_mono_left
    (mulModReduceSubtractPost_regOwn sp
      (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n)) h hp
  -- Surrender x8 ownership.
  have hp2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (regIs_to_regOwn .x8 _)))) h hp1
  unfold mulModReduceInnerStepPost mulModReduceCompareMem
  unfold mulModReduceSubtractMem at hp2
  rw [mulModReduceStepCarry_of_decision hdec]
  xperm_pure hp2

/-- Bridge the no-subtract-path post (with the frame-in scratch registers)
    into the unified inner-step post. -/
theorem mulModReduceInnerStepPost_of_noSubtractPost
    (sp x17Old x10Old x11Old x13Old x15 : Word) (r n : EvmWord) (done : Bool)
    (hcarry : r.getLsbD 255 = false)
    (hlt : mulModReduceRemLT (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n) :
    ∀ h, (mulModReduceInnerStepNoSubtractPost sp x17Old x15 r n done **
            ((.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old))) h →
      mulModReduceInnerStepPost sp x17Old x15 r n done h := by
  intro h hp
  unfold mulModReduceInnerStepNoSubtractPost at hp
  have hp1 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
    (mulModReduceComparePost_drop sp
      (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n false))) h hp
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x5 _))))) h hp1
  have hp2b := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (regIs_to_regOwn .x8 _)))))) h hp2
  have hp3 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h hp2b
  have hp4 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (regIs_to_regOwn .x11 _))) h hp3
  have hp5 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (regIs_to_regOwn .x13 _))) h hp4
  unfold mulModReduceInnerStepPost
  rw [mulModReduceStepCarry_of_not_decision hcarry hlt]
  xperm_hyp hp5

/-- Full reducer inner-step branch specification: one bit-serial step of the
    512-bit modular reduction, dispatching the subtract / no-subtract paths on
    the comparison of the shifted remainder against the modulus. -/
theorem evm_mulmod_reduce512_inner_step_spec_within
    (sp base x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old x15 x19Old x20Old : Word)
    (r n : EvmWord) :
    cpsBranchWithin 66 base
      (evm_mulmod_reduce512_inner_step_code base)
      (mulModReduceInnerStepPre sp x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old
        x15 x19Old x20Old r n)
      base (mulModReduceInnerStepPost sp x17Old x15 r n false)
      (base + 264) (mulModReduceInnerStepPost sp x17Old x15 r n true) := by
  by_cases hdec : mulModReduceSubtractDecision r n x17Old
  · -- Subtract path (66 steps): the shift overflowed or the truncated value ≥ n.
    have hsub := evm_mulmod_reduce512_inner_step_subtract_path_spec_within
      sp base x17Old x5Old x6Old x7Old x8Old x10Old x11Old x13Old x15 x19Old x20Old r n hdec
    exact cpsBranchWithin_weaken
      (fun h hp => by
        unfold mulModReduceInnerStepPre at hp
        exact (sepConj_pure_right h).2 ⟨hp, hdec⟩)
      (mulModReduceInnerStepPost_of_subtractPost sp x17Old x15 r n false hdec)
      (mulModReduceInnerStepPost_of_subtractPost sp x17Old x15 r n true hdec)
      hsub
  · -- No-subtract path: carry clear and truncated value < n.
    have hcarry : r.getLsbD 255 = false := by
      by_contra hc
      exact hdec (Or.inl (by simpa using hc))
    have hlt : mulModReduceRemLT (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)) n := by
      unfold mulModReduceRemLT
      have hlt' : (mulModReduceShiftInBit r (mulModReduceInputBit x17Old)).toNat < n.toNat := by
        by_contra h
        exact hdec (Or.inr h)
      simpa only [BitVec.ult, decide_eq_true_eq] using hlt'
    have hns0 := evm_mulmod_reduce512_inner_step_no_subtract_path_spec_within
      sp base x17Old x5Old x6Old x7Old x8Old x15 x19Old x20Old r n hcarry hlt
    have hns1 := cpsBranchWithin_frameR
      ((.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) ** (.x13 ↦ᵣ x13Old)) (by pcFree) hns0
    have hns := cpsBranchWithin_mono_nSteps (show (40 : Nat) ≤ 66 by omega) hns1
    exact cpsBranchWithin_weaken
      (fun h hp => by
        unfold mulModReduceInnerStepPre mulModReduceInnerStepSubtractPre at hp
        unfold mulModReduceInnerStepNoSubtractPre
        have hp2 := (sepConj_pure_right h).2 ⟨hp, hlt⟩
        xperm_hyp hp2)
      (mulModReduceInnerStepPost_of_noSubtractPost sp x17Old x10Old x11Old x13Old x15 r n false hcarry hlt)
      (mulModReduceInnerStepPost_of_noSubtractPost sp x17Old x10Old x11Old x13Old x15 r n true hcarry hlt)
      hns

end EvmAsm.Evm64
