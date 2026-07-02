/-
  EvmAsm.Evm64.DivMod.Spec.N3V5Shift0PostBridgeCallable

  Shift=0 CALLABLE post bridge for the n=3 v5 exact-frame lane: the flag-param
  full-path post (epilogue regs + `fullDivN3FrameShift0V5`, regIs `x1`) →
  `divStackDispatchPostCallableExactFrame` plus the concrete scratch cell.
  Stop-early variant of `n3_shift0_fullPost_to_divStackDispatchPostV5`
  (N3V5Shift0PostBridge): identical `divConcretePostNoX1ExactRegsFrame`
  reassociation, but keeps the caller-exact `x1 = raVal` (the callable frame)
  instead of weakening the register file to `regOwn`.  n=3 shift=0 counterpart
  of `fullDivN2UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch`
  (N2V5ConcretePostBridge).
-/

import EvmAsm.Evm64.DivMod.Spec.N3V5Shift0PostBridge

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Shift=0 callable bridge: the flag-param full-path post →
    `divStackDispatchPostCallableExactFrame` + the concrete scratch cell. -/
theorem n3_shift0_fullPost_to_divStackDispatchPostCallableExactFrame
    (bltu_1 bltu_0 : Bool) (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (0 : Word))
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x5 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
        (.x6 ↦ᵣ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
        (.x7 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1) **
        ((sp + signExtend12 4088) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
        ((sp + signExtend12 4080) ↦ₘ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + 32) ↦ₘ (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1) **
        ((sp + 40) ↦ₘ (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1) **
        ((sp + 48) ↦ₘ (0 : Word)) **
        ((sp + 56) ↦ₘ (0 : Word))) **
       fullDivN3FrameShift0V5 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2
         retMem dMem dloMem scratchUn0 scratchMem raVal) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        n3Shift0ScratchMemF bltu_1 bltu_0 a1 a2 a3 b0 b1 b2 scratchMem)) h := by
  intro h hq
  rw [fullDivN3FrameShift0V5_unfold] at hq
  have hExact :
      (divConcretePostNoX1ExactRegsFrame sp a b (signExtend12 4095) raVal
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1
        (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1
        (0 : Word) (0 : Word)
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1
        (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1
        (0 : Word) (0 : Word)
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.1
        (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).2.2.2.2.2
        (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.2.2.2
        (0 : Word) (0 : Word)
        (clzResult b2).1 (3 : Word) (0 : Word)
        (if bltu_0 then (base + div128CallRetOff)
          else if bltu_1 then (base + div128CallRetOff) else retMem)
        (if bltu_0 then b2 else if bltu_1 then b2 else dMem)
        (if bltu_0 then divKTrialCallV5DLo b2
          else if bltu_1 then divKTrialCallV5DLo b2 else dloMem)
        (if bltu_0 then divKTrialCallV5Un0 (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).2.2.1
          else if bltu_1 then divKTrialCallV5Un0 a3 else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ
        n3Shift0ScratchMemF bltu_1 bltu_0 a1 a2 a3 b0 b1 b2 scratchMem)) h := by
    rw [divConcretePostNoX1ExactRegsFrame_unfold,
        evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
        evmWordIs_sp32_limbs_eq sp (EvmWord.div a b)
          (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1
          (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1 (0 : Word) (0 : Word)
          hdiv0 hdiv1 hdiv2 hdiv3,
        divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
    delta n3Shift0ScratchMemF
    rw [word_add_zero] at hq
    xperm_hyp hq
  rw [divStackDispatchPostCallableExactFrame_unfold]
  exact sepConj_mono_left
    (fun h hp => divConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp)
    h hExact

end EvmAsm.Evm64
