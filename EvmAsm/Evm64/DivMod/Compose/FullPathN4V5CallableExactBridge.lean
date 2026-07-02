/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5CallableExactBridge

  Callable exact-frame pre/post bridges for the n=4 v5 DIV lane.  x1-preserving
  twins of the PostV5 bridges (`n4_dispatchPre_to_pathEntry_v5`,
  `n4_denormDivPost_frame_to_divStackDispatchPost_v5`,
  `n4_shift0_post_to_divStackDispatchPost_v5`): the pre-bridge keeps the caller
  return address `x1 = x1Val` concrete instead of weakening to `regOwn .x1`, and
  the two post-bridges land `divStackDispatchPostCallableExactFrame` (concrete
  `x1 = raVal`, `x9 = x9Val`) via
  `divConcretePostNoX1ExactRegs_weaken_callable_frame` instead of the ownership
  `divStackDispatchPost`.  Both post-bridges are generic in the single-limb
  quotient `qVal` / remainder / scratch, so both call branches (skip/addback) of
  each shift arm instantiate them.  Toward `evm_div_callable_v5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPre
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPostBridge
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5Shift0PostBridge
import EvmAsm.Evm64.DivMod.Spec.CallablePost

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- x1-preserving twin of `n4_dispatchPre_to_pathEntry_v5`: bridge the v5 stack
    dispatch pre to the n=4 explicit path-entry pre, keeping the caller return
    address `x1 = x1Val` concrete (framed) instead of `regOwn .x1`. -/
theorem n4_dispatchPre_to_pathEntry_v5_exact_x1 (sp : Word) (a b : EvmWord)
    (x1Val v2 v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3) :
    ∀ h,
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        v2 v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem)) h →
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ v2) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** (.x1 ↦ᵣ x1Val)) h := by
  intro h hp
  delta divModStackDispatchPreNoX1 at hp
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp b b0 b1 b2 b3 hb0 hb1 hb2 hb3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
  rw [word_add_zero]
  xperm_hyp hp

/-- Callable exact-frame twin of `n4_denormDivPost_frame_to_divStackDispatchPost_v5`:
    the denorm output (single-limb quotient `qVal`) plus the residual scratch
    frame with concrete `x1 = raVal` implies
    `divStackDispatchPostCallableExactFrame sp a b raVal x9Val ** memOwn (sp+3936)`. -/
theorem n4_denormDivPost_frame_to_divStackDispatchPostCallableExactFrame_v5
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 : Word)
    (shift qVal rem0 rem1 rem2 rem3 u4f x9Val raVal dMemV dloMemV scratchUn0V scratchOutV : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = qVal)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = 0)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = 0)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = 0) :
    ∀ h,
      (denormDivPost sp shift rem0 rem1 rem2 rem3 qVal 0 0 0 **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ u4f) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
       (.x9 ↦ᵣ x9Val) ** (.x11 ↦ᵣ qVal) **
       (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
       (sp + signExtend12 3960 ↦ₘ dMemV) **
       (sp + signExtend12 3952 ↦ₘ dloMemV) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0V) **
       (sp + signExtend12 3936 ↦ₘ scratchOutV) ** (.x1 ↦ᵣ raVal)) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal x9Val **
       memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  delta denormDivPost at hp
  rw [word_add_zero] at hp
  rw [divStackDispatchPostCallableExactFrame_unfold]
  apply sepConj_mono_right
    (P := (divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** (.x9 ↦ᵣ x9Val))
    memIs_implies_memOwn h
  apply sepConj_mono_left (divConcretePostNoX1ExactRegs_weaken_callable_frame sp a b) h
  rw [divConcretePostNoX1ExactRegsFrame_unfold,
      evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _ hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  xperm_hyp hp

/-- Callable exact-frame twin of `n4_shift0_post_to_divStackDispatchPost_v5`:
    the shift=0 epilogue output (single-limb quotient `qVal` in the output slots)
    plus the residual scratch frame with concrete `x1 = raVal` implies
    `divStackDispatchPostCallableExactFrame sp a b raVal x9Val ** memOwn (sp+3936)`. -/
theorem n4_shift0_post_to_divStackDispatchPostCallableExactFrame_v5
    (sp : Word) (a b : EvmWord)
    (a0 a1 a2 a3 : Word)
    (qVal un3OutV x9Val raVal un0V un1V un2V u4V shiftV : Word)
    (retMemV dMemV dloMemV scratchUn0V scratchOutV : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = qVal)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = 0)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = 0)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = 0) :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ qVal) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ un3OutV) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftV) **
       ((sp + signExtend12 4088) ↦ₘ qVal) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + 32) ↦ₘ qVal) ** ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
       (.x9 ↦ᵣ x9Val) ** (.x11 ↦ᵣ qVal) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ un0V) ** ((sp + signExtend12 4048) ↦ₘ un1V) **
       ((sp + signExtend12 4040) ↦ₘ un2V) ** ((sp + signExtend12 4032) ↦ₘ un3OutV) **
       ((sp + signExtend12 4024) ↦ₘ u4V) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (4 : Word)) ** ((sp + signExtend12 3976) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3968) ↦ₘ retMemV) ** ((sp + signExtend12 3960) ↦ₘ dMemV) **
       ((sp + signExtend12 3952) ↦ₘ dloMemV) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0V) **
       ((sp + signExtend12 3936) ↦ₘ scratchOutV) ** (.x1 ↦ᵣ raVal)) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal x9Val **
       memOwn (sp + signExtend12 3936)) h := by
  intro h hp
  rw [word_add_zero] at hp
  rw [divStackDispatchPostCallableExactFrame_unfold]
  apply sepConj_mono_right
    (P := (divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** (.x9 ↦ᵣ x9Val))
    memIs_implies_memOwn h
  apply sepConj_mono_left (divConcretePostNoX1ExactRegs_weaken_callable_frame sp a b) h
  rw [divConcretePostNoX1ExactRegsFrame_unfold,
      evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _ hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  xperm_hyp hp

end EvmAsm.Evm64
