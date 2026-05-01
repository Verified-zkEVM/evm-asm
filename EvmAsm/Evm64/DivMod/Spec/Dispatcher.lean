/-
  EvmAsm.Evm64.DivMod.Spec.Dispatcher

  Public stack-level dispatcher contract for DIV/MOD.
-/

import EvmAsm.Evm64.DivMod.Spec.Base
import EvmAsm.Evm64.DivMod.Spec.CallSkipOverestimateBridge
import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Final stack-dispatch precondition shared by DIV and MOD.

The contract intentionally keeps the caller-owned scratch registers as values
instead of hard-coding one branch's CLZ-derived register values. Branch proofs
can specialize this bundle before calling the existing n=1/2/3/4 path specs. -/
@[irreducible]
def divModStackDispatchPre (sp : Word) (a b : EvmWord)
    (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0

theorem divModStackDispatchPre_unfold {sp : Word} {a b : EvmWord}
    {v1 v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
     retMem dMem dloMem scratch_un0 : Word} :
    divModStackDispatchPre sp a b v1 v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
      retMem dMem dloMem scratch_un0 =
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) b **
     divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  delta divModStackDispatchPre
  rfl

/-- Final DIV stack-dispatch postcondition. -/
@[irreducible]
def divStackDispatchPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
  divScratchOwnCall sp

theorem divStackDispatchPost_unfold {sp : Word} {a b : EvmWord} :
    divStackDispatchPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
     divScratchOwnCall sp) := by
  delta divStackDispatchPost
  rfl

theorem divStackDispatchPost_weaken
    (sp : Word) (a b : EvmWord)
    {v1 v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
       divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0) h →
      divStackDispatchPost sp a b h := by
  intro h hp
  delta divStackDispatchPost
  refine sepConj_mono_right ?_ h hp
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValuesCall_implies_divScratchOwnCall
    sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
      retMem dMem dloMem scratch_un0

/-- Final MOD stack-dispatch postcondition. -/
@[irreducible]
def modStackDispatchPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
  divScratchOwnCall sp

theorem modStackDispatchPost_unfold {sp : Word} {a b : EvmWord} :
    modStackDispatchPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
     divScratchOwnCall sp) := by
  delta modStackDispatchPost
  rfl

theorem modStackDispatchPost_weaken
    (sp : Word) (a b : EvmWord)
    {v1 v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
       divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0) h →
      modStackDispatchPost sp a b h := by
  intro h hp
  delta modStackDispatchPost
  refine sepConj_mono_right ?_ h hp
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValuesCall_implies_divScratchOwnCall
    sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
      retMem dMem dloMem scratch_un0

theorem fullDivN1UnifiedPost_to_divStackDispatchPost
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1) :
    ∀ h,
      fullDivN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h →
      divStackDispatchPost sp a b h := by
  intro h hq
  let shift := fullDivN1Shift b0
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
  let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
  let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
  let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let scratch_ret3 := if bltu_3 then (base + 516) else retMem
  let scratch_d3 := if bltu_3 then v.1 else dMem
  let scratch_dlo3 := if bltu_3 then div128DLo v.1 else dloMem
  let scratch_un03 := if bltu_3 then div128Un0 u.2.2.2.1 else scratch_un0
  let scratch_ret2 := if bltu_2 then (base + 516) else scratch_ret3
  let scratch_d2 := if bltu_2 then v.1 else scratch_d3
  let scratch_dlo2 := if bltu_2 then div128DLo v.1 else scratch_dlo3
  let scratch_un02 := if bltu_2 then div128Un0 u.2.2.1 else scratch_un03
  let scratch_ret1 := if bltu_1 then (base + 516) else scratch_ret2
  let scratch_d1 := if bltu_1 then v.1 else scratch_d2
  let scratch_dlo1 := if bltu_1 then div128DLo v.1 else scratch_dlo2
  let scratch_un01 := if bltu_1 then div128Un0 u.2.1 else scratch_un02
  refine divStackDispatchPost_weaken (sp := sp) (a := a) (b := b)
    (v1 := signExtend12 4095) (v2 := antiShift)
    (v5 := r0.1) (v6 := r1.1) (v7 := r2.1)
    (v10 := r3.1) (v11 := r0.1)
    (q0 := r0.1) (q1 := r1.1) (q2 := r2.1) (q3 := r3.1)
    (u0 := u0') (u1 := u1') (u2 := u2') (u3 := u3')
    (u4 := r0.2.2.2.2.2) (u5 := r1.2.2.2.2.2)
    (u6 := r2.2.2.2.2.2) (u7 := r3.2.2.2.2.2)
    (shiftMem := shift) (nMem := 1) (jMem := 0)
    (retMem := if bltu_0 then (base + 516) else scratch_ret1)
    (dMem := if bltu_0 then v.1 else scratch_d1)
    (dloMem := if bltu_0 then div128DLo v.1 else scratch_dlo1)
    (scratch_un0 := if bltu_0 then div128Un0 u.1 else scratch_un01) h ?_
  delta fullDivN1UnifiedPost fullDivN1DenormPost fullDivN1Frame fullDivN1Scratch at hq
  simp only [denormDivPost_unfold] at hq
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ
          (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 40) ↦ₘ
          (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 48) ↦ₘ
          (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 56) ↦ₘ
          (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1))
      from by
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
          hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

theorem fullModN1UnifiedPost_to_modStackDispatchPost
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod3 : (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64))) :
    ∀ h,
      fullModN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h →
      modStackDispatchPost sp a b h := by
  intro h hq
  let shift := fullDivN1Shift b0
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
  let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
  let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
  let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let scratch_ret3 := if bltu_3 then (base + 516) else retMem
  let scratch_d3 := if bltu_3 then v.1 else dMem
  let scratch_dlo3 := if bltu_3 then div128DLo v.1 else dloMem
  let scratch_un03 := if bltu_3 then div128Un0 u.2.2.2.1 else scratch_un0
  let scratch_ret2 := if bltu_2 then (base + 516) else scratch_ret3
  let scratch_d2 := if bltu_2 then v.1 else scratch_d3
  let scratch_dlo2 := if bltu_2 then div128DLo v.1 else scratch_dlo3
  let scratch_un02 := if bltu_2 then div128Un0 u.2.2.1 else scratch_un03
  let scratch_ret1 := if bltu_1 then (base + 516) else scratch_ret2
  let scratch_d1 := if bltu_1 then v.1 else scratch_d2
  let scratch_dlo1 := if bltu_1 then div128DLo v.1 else scratch_dlo2
  let scratch_un01 := if bltu_1 then div128Un0 u.2.1 else scratch_un02
  refine modStackDispatchPost_weaken (sp := sp) (a := a) (b := b)
    (v1 := signExtend12 4095) (v2 := antiShift)
    (v5 := u0') (v6 := u1') (v7 := u2')
    (v10 := u3') (v11 := r0.1)
    (q0 := r0.1) (q1 := r1.1) (q2 := r2.1) (q3 := r3.1)
    (u0 := u0') (u1 := u1') (u2 := u2') (u3 := u3')
    (u4 := r0.2.2.2.2.2) (u5 := r1.2.2.2.2.2)
    (u6 := r2.2.2.2.2.2) (u7 := r3.2.2.2.2.2)
    (shiftMem := shift) (nMem := 1) (jMem := 0)
    (retMem := if bltu_0 then (base + 516) else scratch_ret1)
    (dMem := if bltu_0 then v.1 else scratch_d1)
    (dloMem := if bltu_0 then div128DLo v.1 else scratch_dlo1)
    (scratch_un0 := if bltu_0 then div128Un0 u.1 else scratch_un01) h ?_
  delta fullModN1UnifiedPost fullModN1DenormPost fullDivN1Frame fullDivN1Scratch at hq
  simp only [denormModPost_unfold] at hq
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.mod a b) =
      (((sp + 32) ↦ₘ u0') ** ((sp + 40) ↦ₘ u1') **
       ((sp + 48) ↦ₘ u2') ** ((sp + 56) ↦ₘ u3'))
      from by
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
          hmod0 hmod1 hmod2 hmod3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

theorem evm_div_n1_stack_spec_within
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1) :
    cpsTripleWithin 946 base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  have hFull := evm_div_n1_full_unified_spec
    bltu_3 bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1z hshift_nz halign
    hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta divModStackDispatchPre at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun h hq =>
      fullDivN1UnifiedPost_to_divStackDispatchPost
        bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
        ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq)
    hFull

@[irreducible]
def fullDivN1QuotientWord (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 1 => (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 2 => (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 3 => (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1)

theorem fullDivN1_hdivs_of_word_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv : fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  constructor
  · rw [← hdiv]
    delta fullDivN1QuotientWord
    exact EvmWord.getLimbN_fromLimbs_0
  constructor
  · rw [← hdiv]
    delta fullDivN1QuotientWord
    exact EvmWord.getLimbN_fromLimbs_1
  constructor
  · rw [← hdiv]
    delta fullDivN1QuotientWord
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]
    delta fullDivN1QuotientWord
    exact EvmWord.getLimbN_fromLimbs_3

theorem fullDivN1QuotientWord_eq_div_of_toNat_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv_toNat :
      (fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.div a b).toNat) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b :=
  BitVec.eq_of_toNat_eq hdiv_toNat

theorem fullDivN1QuotientWord_toNat
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat =
    EvmWord.val256
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  delta fullDivN1QuotientWord
  rw [EvmWord.fromLimbs_toNat]
  rfl

theorem fullDivN1QuotientWord_toNat_eq_div_toNat_of_val256_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hquot :
      EvmWord.val256
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 =
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3) :
    (fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.div a b).toNat := by
  have ha_val : EvmWord.val256 a0 a1 a2 a3 = a.toNat := by
    rw [← ha0, ← ha1, ← ha2, ← ha3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : EvmWord.val256 b0 b1 b2 b3 = b.toNat := by
    rw [← hb0, ← hb1, ← hb2, ← hb3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rw [← hb_val]
    exact EvmWord.val256_pos_of_or_ne_zero hbnz
  have hb_ne : b ≠ 0 := by
    intro hb_zero
    have hb_toNat_zero : b.toNat = 0 := by simp [hb_zero]
    omega
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div
    rw [if_neg hb_ne]
    exact BitVec.toNat_udiv
  rw [fullDivN1QuotientWord_toNat, hquot, ha_val, hb_val, hdiv_toNat]

theorem evm_div_n1_stack_spec_within_word
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hdivWord : fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin 946 base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN1_hdivs_of_word_eq bltu_3 bltu_2 bltu_1 bltu_0
      a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord
  exact evm_div_n1_stack_spec_within bltu_3 bltu_2 bltu_1 bltu_0
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2
    hdiv0 hdiv1 hdiv2 hdiv3

@[irreducible]
def fullModN1RemainderWord (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 =>
        (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
    | 1 =>
        (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
    | 2 =>
        (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
    | 3 =>
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)))

theorem fullModN1_hmods_of_word_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod : fullModN1RemainderWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64)) := by
  constructor
  · rw [← hmod]
    delta fullModN1RemainderWord
    exact EvmWord.getLimbN_fromLimbs_0
  constructor
  · rw [← hmod]
    delta fullModN1RemainderWord
    exact EvmWord.getLimbN_fromLimbs_1
  constructor
  · rw [← hmod]
    delta fullModN1RemainderWord
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod]
    delta fullModN1RemainderWord
    exact EvmWord.getLimbN_fromLimbs_3

theorem fullModN1RemainderWord_eq_mod_of_toNat_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod_toNat :
      (fullModN1RemainderWord bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.mod a b).toNat) :
    fullModN1RemainderWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b :=
  BitVec.eq_of_toNat_eq hmod_toNat

theorem fullModN1RemainderWord_toNat
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullModN1RemainderWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat =
    EvmWord.val256
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64)) := by
  delta fullModN1RemainderWord
  rw [EvmWord.fromLimbs_toNat]
  rfl

theorem fullModN1RemainderWord_toNat_eq_mod_toNat_of_val256_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hrem :
      EvmWord.val256
        (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
        (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
        (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) =
      EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3) :
    (fullModN1RemainderWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.mod a b).toNat := by
  have ha_val : EvmWord.val256 a0 a1 a2 a3 = a.toNat := by
    rw [← ha0, ← ha1, ← ha2, ← ha3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : EvmWord.val256 b0 b1 b2 b3 = b.toNat := by
    rw [← hb0, ← hb1, ← hb2, ← hb3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rw [← hb_val]
    exact EvmWord.val256_pos_of_or_ne_zero hbnz
  have hb_ne : b ≠ 0 := by
    intro hb_zero
    have hb_toNat_zero : b.toNat = 0 := by simp [hb_zero]
    omega
  have hmod_toNat : (EvmWord.mod a b).toNat = a.toNat % b.toNat := by
    unfold EvmWord.mod
    rw [if_neg hb_ne]
    exact BitVec.toNat_umod
  rw [fullModN1RemainderWord_toNat, hrem, ha_val, hb_val, hmod_toNat]

theorem fullModN1_denorm_val256_eq_mod_of_limb_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod3 : (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64))) :
    EvmWord.val256
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64)) =
    EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3 := by
  have ha_val : EvmWord.val256 a0 a1 a2 a3 = a.toNat := by
    rw [← ha0, ← ha1, ← ha2, ← ha3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : EvmWord.val256 b0 b1 b2 b3 = b.toNat := by
    rw [← hb0, ← hb1, ← hb2, ← hb3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rw [← hb_val]
    exact EvmWord.val256_pos_of_or_ne_zero hbnz
  have hb_ne : b ≠ 0 := by
    intro hb_zero
    have hb_toNat_zero : b.toNat = 0 := by simp [hb_zero]
    omega
  have hmod_toNat : (EvmWord.mod a b).toNat = a.toNat % b.toNat := by
    unfold EvmWord.mod
    rw [if_neg hb_ne]
    exact BitVec.toNat_umod
  have hdenorm_toNat :
      EvmWord.val256
        (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
        (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
        (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64)))
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) =
      (EvmWord.mod a b).toNat := by
    rw [← hmod0, ← hmod1, ← hmod2, ← hmod3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat (EvmWord.mod a b)
  rw [hdenorm_toNat, hmod_toNat, ha_val, hb_val]

theorem fullModN1_hmods_of_normalized_val256_eq
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hshift_nz : fullDivN1Shift b0 ≠ 0)
    (h_val_eq :
      EvmWord.val256
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 =
      EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3 *
        2 ^ ((fullDivN1Shift b0).toNat % 64)) :
    (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0 := by
    rw [hb0, hb1, hb2, hb3]
    exact hbnz
  have hs0 : 0 < (fullDivN1Shift b0).toNat % 64 := by
    rw [fullDivN1Shift_toNat_mod_eq]
    exact fullDivN1Shift_toNat_pos_of_ne_zero hshift_nz
  have hs : (fullDivN1Shift b0).toNat % 64 < 64 :=
    Nat.mod_lt _ (by decide)
  have h_val_eq' : EvmWord.val256
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 =
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((fullDivN1Shift b0).toNat % 64) := by
    rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
    exact h_val_eq
  have hmods :=
    denorm_4limb_eq_mod_of_val256_eq_amod_pow_s_of_or_ne_zero hs0 hs hbnz' h_val_eq'
  have hanti_mod :
      (signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64 =
        64 - (fullDivN1Shift b0).toNat % 64 := by
    rw [fullDivN1AntiShift_toNat_mod_eq hshift_nz,
      fullDivN1Shift_toNat_mod_eq b0]
  rw [hanti_mod]
  exact hmods

theorem evm_mod_n1_stack_spec_within
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64)) |||
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))))
    (hmod3 : (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN1Shift b0).toNat % 64))) :
    cpsTripleWithin 946 base (base + nopOff) (modCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) := by
  have hFull := evm_mod_n1_full_unified_spec
    bltu_3 bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1z hshift_nz halign
    hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta divModStackDispatchPre at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun h hq =>
      fullModN1UnifiedPost_to_modStackDispatchPost
        bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
        ha0 ha1 ha2 ha3 hmod0 hmod1 hmod2 hmod3 h hq)
    hFull

theorem evm_mod_n1_stack_spec_within_word
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hmodWord : fullModN1RemainderWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    cpsTripleWithin 946 base (base + nopOff) (modCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) := by
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ :=
    fullModN1_hmods_of_word_eq bltu_3 bltu_2 bltu_1 bltu_0
      a b a0 a1 a2 a3 b0 b1 b2 b3 hmodWord
  exact evm_mod_n1_stack_spec_within bltu_3 bltu_2 bltu_1 bltu_0
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2
    hmod0 hmod1 hmod2 hmod3

/-! ### n=3 mod remainder-word helpers (mirror of fullModN1RemainderWord) -/

/-- n=3 mirror of `fullModN1RemainderWord`. The output limbs are
the four `denormModPost` u-limb formulas (shift right by `shift`,
OR'd with the next-limb left-shifted by `antiShift`) applied to
the four `fullDivN3R0` u-components and `fullDivN3Shift b2`. -/
@[irreducible]
def fullModN3RemainderWord (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 =>
        (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    | 1 =>
        (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    | 2 =>
        (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    | 3 =>
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)))

theorem fullModN3_hmods_of_word_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod : fullModN3RemainderWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN3Shift b2).toNat % 64)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmod]
    delta fullModN3RemainderWord
    exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hmod]
    delta fullModN3RemainderWord
    exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hmod]
    delta fullModN3RemainderWord
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod]
    delta fullModN3RemainderWord
    exact EvmWord.getLimbN_fromLimbs_3

theorem fullModN3RemainderWord_eq_mod_of_toNat_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod_toNat :
      (fullModN3RemainderWord bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.mod a b).toNat) :
    fullModN3RemainderWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b :=
  BitVec.eq_of_toNat_eq hmod_toNat

theorem fullModN3RemainderWord_toNat
    (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullModN3RemainderWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat =
    EvmWord.val256
      (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
      (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
      (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
      ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN3Shift b2).toNat % 64)) := by
  delta fullModN3RemainderWord
  rw [EvmWord.fromLimbs_toNat]
  rfl

theorem fullModN3RemainderWord_toNat_eq_mod_toNat_of_val256_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hrem :
      EvmWord.val256
        (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) =
      EvmWord.val256 a0 a1 a2 a3 % EvmWord.val256 b0 b1 b2 b3) :
    (fullModN3RemainderWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.mod a b).toNat := by
  have ha_val : EvmWord.val256 a0 a1 a2 a3 = a.toNat := by
    rw [← ha0, ← ha1, ← ha2, ← ha3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : EvmWord.val256 b0 b1 b2 b3 = b.toNat := by
    rw [← hb0, ← hb1, ← hb2, ← hb3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rw [← hb_val]
    exact EvmWord.val256_pos_of_or_ne_zero hbnz
  have hb_ne : b ≠ 0 := by
    intro hb_zero
    have hb_toNat_zero : b.toNat = 0 := by simp [hb_zero]
    omega
  have hmod_toNat : (EvmWord.mod a b).toNat = a.toNat % b.toNat := by
    unfold EvmWord.mod
    rw [if_neg hb_ne]
    exact BitVec.toNat_umod
  rw [fullModN3RemainderWord_toNat, hrem, ha_val, hb_val, hmod_toNat]
/- ============================================================================
   N=3 DIV stack-dispatch wrapper (slice 2b of #61).
   Mirrors `evm_div_n1_stack_spec_within` using `evm_div_n3_full_unified_spec`.
   ============================================================================ -/

/-- Bridge from the `fullDivN3UnifiedPost` postcondition (raw memory atoms +
    frame) to the value-agnostic `divStackDispatchPost`. Mirror of
    `fullDivN1UnifiedPost_to_divStackDispatchPost`; the only structural
    differences are that `q2`/`q3` are statically `0` at n=3, and there is no
    `b3`/`b2/b1` zero-limb conditional in the call paths. -/
theorem fullDivN3UnifiedPost_to_divStackDispatchPost
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (0 : Word))
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      fullDivN3UnifiedPost bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h →
      divStackDispatchPost sp a b h := by
  intro h hq
  let shift := fullDivN3Shift b2
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
  let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
  let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
  let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let scratch_ret1 := if bltu_1 then (base + 516) else retMem
  let scratch_d1 := if bltu_1 then v.2.2.1 else dMem
  let scratch_dlo1 := if bltu_1 then div128DLo v.2.2.1 else dloMem
  let scratch_un01 := if bltu_1 then div128Un0 u.2.2.2.1 else scratch_un0
  refine divStackDispatchPost_weaken (sp := sp) (a := a) (b := b)
    (v1 := signExtend12 4095) (v2 := antiShift)
    (v5 := r0.1) (v6 := r1.1) (v7 := (0 : Word))
    (v10 := (0 : Word)) (v11 := r0.1)
    (q0 := r0.1) (q1 := r1.1) (q2 := (0 : Word)) (q3 := (0 : Word))
    (u0 := u0') (u1 := u1') (u2 := u2') (u3 := u3')
    (u4 := r0.2.2.2.2.2) (u5 := r1.2.2.2.2.2)
    (u6 := (0 : Word)) (u7 := (0 : Word))
    (shiftMem := shift) (nMem := 3) (jMem := 0)
    (retMem := if bltu_0 then (base + 516) else scratch_ret1)
    (dMem := if bltu_0 then v.2.2.1 else scratch_d1)
    (dloMem := if bltu_0 then div128DLo v.2.2.1 else scratch_dlo1)
    (scratch_un0 := if bltu_0 then div128Un0 r1.2.2.1 else scratch_un01) h ?_
  delta fullDivN3UnifiedPost fullDivN3DenormPost fullDivN3Frame fullDivN3Scratch at hq
  simp only [denormDivPost_unfold] at hq
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ
          (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 40) ↦ₘ
          (fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 48) ↦ₘ (0 : Word)) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
          hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- N=3 DIV stack-level entry point: mirrors `evm_div_n1_stack_spec_within`. -/
theorem evm_div_n3_stack_spec_within
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : isTrialN3_j1 bltu_1 a3 b1 b2)
    (hbltu_0 : isTrialN3_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b2).1).toNat % 64))
      ((b1 <<< (((clzResult b2).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b2 <<< (((clzResult b2).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b3 <<< (((clzResult b2).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64))))
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (0 : Word))
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    cpsTripleWithin 542 base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b2).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  have hFull := evm_div_n3_full_unified_spec
    bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3z hb2nz hshift_nz halign hbltu_1 hbltu_0 hcarry2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta divModStackDispatchPre at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun h hq =>
      fullDivN3UnifiedPost_to_divStackDispatchPost
        bltu_1 bltu_0 sp base a b
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
        ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq)
    hFull

end EvmAsm.Evm64
