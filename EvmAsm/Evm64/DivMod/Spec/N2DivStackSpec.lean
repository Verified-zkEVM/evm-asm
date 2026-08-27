/-
  EvmAsm.Evm64.DivMod.Spec.N2DivStackSpec

  Stack-level entry points for the n=2 DIV path: composes
  `evm_div_n2_full_bundled_spec` with a `divStackDispatchPost` bridge,
  mirroring `evm_mod_n2_stack_spec_within{,_word}` from
  `Spec.N2ModStackSpec`.

  The `_word` variant takes a single packed `EvmWord` equality hypothesis
  `fullDivN2QuotientWord ... = EvmWord.div a b` and projects it into the
  four per-limb hypotheses required by `evm_div_n2_stack_spec_within`,
  using `fullDivN2_hdivs_of_word_eq`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

  See beads `evm-asm-8bu1`, parent `evm-asm-pb40` (#61 slice 2a-ii).

  Legacy note:
  The stack wrappers in this file predate the selected-carry v4 retrofit and
  still expose the counterexample-false universal `Carry2NzAll` package.
  Treat them as compatibility shims for older v1/no-NOP composition paths, not
  as the surface for new public DIV n=2 stack work. New v4 callable/final
  wrappers should use the selected-carry surfaces in
  `Spec.N2V4CallableExactSelected` and `CallableV4DivSelected` instead.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallablePost
public import EvmAsm.Evm64.DivMod.Spec.Dispatcher
public import EvmAsm.Evm64.DivMod.Spec.N2QuotientWord
public import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Full

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Lift the bundled n=2 DIV postcondition
`fullDivN2DenormPost ** fullDivN2Frame` to `divStackDispatchPost`.

Structurally identical to `fullModN2UnifiedPost_to_modStackDispatchPost`
(Spec/N2ModBridge.lean): the only difference is that the `sp + 32 .. sp + 56`
limb cells now hold the quotient limbs (`r0.1, r1.1, r2.1, 0`) instead of
the denormalised remainder limbs. -/
theorem fullDivN2DenormPost_fullDivN2Frame_to_divStackDispatchPost
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN2DenormPost bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN2Frame bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
         retMem dMem dloMem scratch_un0) h →
      divStackDispatchPost sp a b h := by
  intro h hq
  let shift := fullDivN2Shift b1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let scratch := fullDivN2ScratchFinal bltu_2 bltu_1 bltu_0 base
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
  let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
  let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
  let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
  let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
  refine divStackDispatchPost_weaken (sp := sp) (a := a) (b := b)
    (v1 := signExtend12 4095) (v2 := antiShift)
    (v5 := r0.1) (v6 := r1.1) (v7 := r2.1)
    (v10 := (0 : Word)) (v11 := r0.1)
    (q0 := r0.1) (q1 := r1.1) (q2 := r2.1) (q3 := (0 : Word))
    (u0 := u0') (u1 := u1') (u2 := u2') (u3 := u3')
    (u4 := r0.2.2.2.2.2) (u5 := r1.2.2.2.2.2)
    (u6 := r2.2.2.2.2.2) (u7 := (0 : Word))
    (shiftMem := shift) (nMem := 2) (jMem := 0)
    (retMem := n2ScratchRet scratch)
    (dMem := n2ScratchD scratch)
    (dloMem := n2ScratchDLo scratch)
    (scratch_un0 := n2ScratchUn0 scratch) h ?_
  delta fullDivN2DenormPost fullDivN2Frame at hq
  simp only [denormDivPost_unfold] at hq
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ
          (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 40) ↦ₘ
          (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 48) ↦ₘ
          (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
          hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

theorem fullDivN2DenormPost_fullDivN2Frame_to_divStackDispatchPostNoX1
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN2DenormPost bltu_2 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
       fullDivN2Frame bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
         retMem dMem dloMem scratch_un0) h →
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) h := by
  intro h hq
  let shift := fullDivN2Shift b1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let scratch := fullDivN2ScratchFinal bltu_2 bltu_1 bltu_0 base
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
  let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
  let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
  let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
  let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
  refine divStackDispatchPostNoX1_weaken (sp := sp) (a := a) (b := b)
    (v1 := signExtend12 4095) (v2 := antiShift)
    (v5 := r0.1) (v6 := r1.1) (v7 := r2.1)
    (v10 := (0 : Word)) (v11 := r0.1)
    (q0 := r0.1) (q1 := r1.1) (q2 := r2.1) (q3 := (0 : Word))
    (u0 := u0') (u1 := u1') (u2 := u2') (u3 := u3')
    (u4 := r0.2.2.2.2.2) (u5 := r1.2.2.2.2.2)
    (u6 := r2.2.2.2.2.2) (u7 := (0 : Word))
    (shiftMem := shift) (nMem := 2) (jMem := 0)
    (retMem := n2ScratchRet scratch)
    (dMem := n2ScratchD scratch)
    (dloMem := n2ScratchDLo scratch)
    (scratch_un0 := n2ScratchUn0 scratch) h ?_
  delta fullDivN2DenormPost fullDivN2Frame at hq
  simp only [denormDivPost_unfold] at hq
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ
          (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 40) ↦ₘ
          (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 48) ↦ₘ
          (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
          hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- Convert the split n=2 full-path post plus exact caller `x1` to the
    exact-register concrete callable post surface. -/
theorem fullDivN2UnifiedPostNoX1_frame_to_divConcretePostNoX1ExactRegsFrame
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN2UnifiedPostNoX1 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 **
        (.x1 ↦ᵣ raVal)) h →
      divConcretePostNoX1ExactRegsFrame sp a b
        (signExtend12 4095) raVal
        (signExtend12 (0 : BitVec 12) - fullDivN2Shift b1)
        (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat) % 64)))
        (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat) % 64)))
        (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat) % 64)))
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64))
        (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (0 : Word)
        (fullDivN2Shift b1) (2 : Word) (0 : Word)
        (n2ScratchRet (fullDivN2ScratchFinal bltu_2 bltu_1 bltu_0 base
          a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0))
        (n2ScratchD (fullDivN2ScratchFinal bltu_2 bltu_1 bltu_0 base
          a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0))
        (n2ScratchDLo (fullDivN2ScratchFinal bltu_2 bltu_1 bltu_0 base
          a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0))
        (n2ScratchUn0 (fullDivN2ScratchFinal bltu_2 bltu_1 bltu_0 base
          a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0)) h := by
  intro h hq
  let shift := fullDivN2Shift b1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let scratch := fullDivN2ScratchFinal bltu_2 bltu_1 bltu_0 base
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
  let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
  let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
  let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
  let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
  rw [divConcretePostNoX1ExactRegsFrame_unfold]
  change
    (((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0.1) ** (.x10 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
     ((.x9 ↦ᵣ (signExtend12 4095 : Word)) ** (.x1 ↦ᵣ raVal) **
      (.x2 ↦ᵣ antiShift) ** (.x6 ↦ᵣ r1.1) ** (.x7 ↦ᵣ r2.1) **
      (.x11 ↦ᵣ r0.1) ** evmWordIs sp a **
      divScratchValuesCallNoX1 sp r0.1 r1.1 r2.1 (0 : Word)
        u0' u1' u2' u3' r0.2.2.2.2.2 r1.2.2.2.2.2
        r2.2.2.2.2.2 (0 : Word) shift (2 : Word) (0 : Word)
        (n2ScratchRet scratch) (n2ScratchD scratch)
        (n2ScratchDLo scratch) (n2ScratchUn0 scratch))) h
  delta fullDivN2UnifiedPostNoX1 fullDivN2DenormPost fullDivN2FrameNoX1 at hq
  simp only [denormDivPost_unfold] at hq
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ
          (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 40) ↦ₘ
          (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 48) ↦ₘ
          (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
          hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- Convert the split n=2 full-path post plus exact caller `x1` directly to
    the public callable post with exact caller-framed `x1` and `x9`. -/
theorem fullDivN2UnifiedPostNoX1_frame_to_divStackDispatchPostCallableExact
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN2UnifiedPostNoX1 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 **
        (.x1 ↦ᵣ raVal)) h →
      (((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) h) := by
  intro h hp
  exact divConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h
    (fullDivN2UnifiedPostNoX1_frame_to_divConcretePostNoX1ExactRegsFrame
      bltu_2 bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 raVal
      ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hp)

/-- Named-post version of
    `fullDivN2UnifiedPostNoX1_frame_to_divStackDispatchPostCallableExact`. -/
theorem fullDivN2UnifiedPostNoX1_frame_to_divStackDispatchPostCallableExactFrame
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN2UnifiedPostNoX1 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 **
        (.x1 ↦ᵣ raVal)) h →
      divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) h := by
  intro h hp
  rw [divStackDispatchPostCallableExactFrame_unfold]
  exact fullDivN2UnifiedPostNoX1_frame_to_divStackDispatchPostCallableExact
    bltu_2 bltu_1 bltu_0 sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 raVal
    ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hp

/-- Legacy N=2 DIV stack-level entry point.

    This mirrors `evm_div_n3_stack_spec_within` and
    `evm_mod_n2_stack_spec_within`, but still exposes the old universal
    `Carry2NzAll` premise. Do not use this as the final/public v4 DIV n=2
    route; prefer selected-carry wrappers in `N2V4CallableExactSelected`. -/
theorem evm_div_n2_stack_spec_within
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    cpsTripleWithin 744 base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  have hFull := evm_div_n2_full_bundled_spec
    bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta divModStackDispatchPre at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun h hq =>
      fullDivN2DenormPost_fullDivN2Frame_to_divStackDispatchPost
        bltu_2 bltu_1 bltu_0 sp base a b
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
        ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq)
    hFull

/-- Legacy no-NOP variant of `evm_div_n2_stack_spec_within`.

    This retains the old public `Carry2NzAll` premise for compatibility only. -/
theorem evm_div_n2_stack_spec_within_noNop
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    cpsTripleWithin 744 base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  have hFull := evm_div_n2_full_bundled_spec_noNop
    bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta divModStackDispatchPre at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun h hq =>
      fullDivN2DenormPost_fullDivN2Frame_to_divStackDispatchPost
        bltu_2 bltu_1 bltu_0 sp base a b
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
        ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq)
    hFull

/-- Legacy `_word` form: mirror of `evm_div_n1_stack_spec_within_word`.

    Takes a single `EvmWord`-valued equality
    `fullDivN2QuotientWord ... = EvmWord.div a b` and projects it into the four
    per-limb hypotheses via `fullDivN2_hdivs_of_word_eq`. It still exposes the
    old `Carry2NzAll` premise, so new v4 work should use selected-carry
    wrappers instead. -/
theorem evm_div_n2_stack_spec_within_word
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdivWord : fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin 744 base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN2_hdivs_of_word_eq bltu_2 bltu_1 bltu_0
      a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord
  exact evm_div_n2_stack_spec_within bltu_2 bltu_1 bltu_0
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1nz
    hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2
    hdiv0 hdiv1 hdiv2 hdiv3

/-- Legacy exact-x1 form of `evm_div_n2_stack_spec_within_word`, exposing the
    dispatcher postcondition without consuming the caller's `x1` atom.

    This is a compatibility wrapper over the raw `Carry2NzAll` path. -/
theorem evm_div_n2_stack_spec_within_word_exact_x1
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdivWord : fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin 744 base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN2_hdivs_of_word_eq bltu_2 bltu_1 bltu_0
      a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord
  have hFull := evm_div_n2_full_bundled_spec
    bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta divModStackDispatchPre at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun h hq =>
      fullDivN2DenormPost_fullDivN2Frame_to_divStackDispatchPostNoX1
        bltu_2 bltu_1 bltu_0 sp base a b
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
        ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq)
    hFull

/-- Legacy no-NOP variant of `evm_div_n2_stack_spec_within_word`.

    This is a compatibility wrapper over the raw `Carry2NzAll` path. -/
theorem evm_div_n2_stack_spec_within_word_noNop
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdivWord : fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin 744 base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN2_hdivs_of_word_eq bltu_2 bltu_1 bltu_0
      a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord
  exact evm_div_n2_stack_spec_within_noNop bltu_2 bltu_1 bltu_0
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1nz
    hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2
    hdiv0 hdiv1 hdiv2 hdiv3

/-- Legacy exact-x1 no-NOP form of `evm_div_n2_stack_spec_within_word`.

    This is a compatibility wrapper over the raw `Carry2NzAll` path. -/
theorem evm_div_n2_stack_spec_within_word_exact_x1_noNop
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdivWord : fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin 744 base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN2_hdivs_of_word_eq bltu_2 bltu_1 bltu_0
      a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord
  have hFull := evm_div_n2_full_bundled_spec_noNop
    bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta divModStackDispatchPre at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun h hq =>
      fullDivN2DenormPost_fullDivN2Frame_to_divStackDispatchPostNoX1
        bltu_2 bltu_1 bltu_0 sp base a b
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
        ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq)
    hFull

/-- Legacy no-NOP n=2 DIV stack spec weakened to the callable post surface with
    separate `x1` ownership and exact `x9`.

    This compatibility wrapper still routes through the raw `Carry2NzAll`
    theorem stack. New v4 callable surfaces should use selected carry evidence
    instead. -/
theorem evm_div_n2_stack_spec_within_word_noNop_callableOwnPost
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdivWord : fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin 744 base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun h hp =>
      divStackDispatchPostNoX1_weaken_callable_own_x1_frame_x9
        sp a b (signExtend12 4095 : Word) h hp)
    (evm_div_n2_stack_spec_within_word_exact_x1_noNop
      bltu_2 bltu_1 bltu_0 sp base
      a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1nz
      hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Legacy no-NOP n=2 DIV stack spec from the callable precondition shape to the
    public callable post, with separate `x1` ownership and exact `x9`.

    This compatibility wrapper still routes through the raw `Carry2NzAll`
    theorem stack. New v4 callable surfaces should use selected carry evidence
    instead. -/
theorem evm_div_n2_stack_spec_within_word_noNop_preNoX1_callableOwnPost
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdivWord : fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin 744 base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold] at hp
      rw [divModStackDispatchPre_unfold, divScratchValuesCall_unfold]
      have hpOwn :
          ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (4 : Word))) **
            regOwn .x1 ** (.x2 ↦ᵣ ((clzResult b1).2 >>> (63 : Nat))) **
            (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
            (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
            evmWordIs sp a ** evmWordIs (sp + 32) b **
            divScratchValues sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
              shiftMem nMem jMem **
            ((sp + signExtend12 3968) ↦ₘ retMem) **
            ((sp + signExtend12 3960) ↦ₘ dMem) **
            ((sp + signExtend12 3952) ↦ₘ dloMem) **
            ((sp + signExtend12 3944) ↦ₘ scratch_un0)) h := by
        apply sepConj_mono_right
        apply sepConj_mono_right
        apply sepConj_mono (regIs_implies_regOwn .x1 (v := raVal))
        exact fun _ hp => hp
        exact hp
      xperm_hyp hpOwn)
    (fun _ hq => hq)
    (evm_div_n2_stack_spec_within_word_noNop_callableOwnPost
      bltu_2 bltu_1 bltu_0 sp base
      a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1nz
      hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

end EvmAsm.Evm64
