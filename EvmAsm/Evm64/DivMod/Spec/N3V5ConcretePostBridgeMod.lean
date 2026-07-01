/-
  EvmAsm.Evm64.DivMod.Spec.N3V5ConcretePostBridgeMod

  N=3 V5 MOD bridge from `fullModN3UnifiedPostNoX1V5` (with exact caller `x1`) to
  the public concrete post `modConcretePostNoX1ExactRegsFrame` (then to the named
  `modStackDispatchPostCallableExactFrame`), plus the v5 div128 scratch cell.
  MOD mirror of `N3V5ConcretePostBridge` (DIV n=3), applying the div→mod
  transformation of `N2V5ConcretePostBridgeMod`: the readout registers hold the
  denormalized REMAINDER (`u_i'` funnel-shift of `fullDivN3R0V5`), the `sp+32`
  result is `EvmWord.mod a b`, and the quotient cells (`r0.1`/`r1.1`/0/0) remain
  framed.  Bead: n=3 MOD lane, Milestone D.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopDenormDefs
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5FamiliesMod
import EvmAsm.Evm64.DivMod.Spec.N3V5ModRemainder
import EvmAsm.Evm64.DivMod.Spec.CallablePost
import EvmAsm.Evm64.DivMod.Spec.Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- N=3 v5 MOD bridge: `fullModN3UnifiedPostNoX1V5` + exact `x1` → the public
    concrete `modConcretePostNoX1ExactRegsFrame` + the v5 scratch cell. -/
theorem fullModN3UnifiedPostNoX1V5_frame_to_modConcretePostNoX1ExactRegsFrame_scratch
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.mod a b).getLimbN 0 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hdiv1 : (EvmWord.mod a b).getLimbN 1 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hdiv2 : (EvmWord.mod a b).getLimbN 2 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hdiv3 : (EvmWord.mod a b).getLimbN 3 =
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64))) :
    ∀ h,
      (fullModN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (modConcretePostNoX1ExactRegsFrame sp a b
        (signExtend12 4095) raVal
        (signExtend12 (0 : BitVec 12) - fullDivN3Shift b2)
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64))
        (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (0 : Word)
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat) % 64)))
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat) % 64)))
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat) % 64)))
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64))
        (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (0 : Word)
        (0 : Word)
        (fullDivN3Shift b2) (3 : Word) (0 : Word)
        (if bltu_0 then (base + div128CallRetOff)
          else if bltu_1 then (base + div128CallRetOff) else retMem)
        (if bltu_0 then (fullDivN3NormV b0 b1 b2 b3).2.2.1
          else if bltu_1 then (fullDivN3NormV b0 b1 b2 b3).2.2.1 else dMem)
        (if bltu_0 then divKTrialCallV5DLo (fullDivN3NormV b0 b1 b2 b3).2.2.1
          else if bltu_1 then divKTrialCallV5DLo (fullDivN3NormV b0 b1 b2 b3).2.2.1 else dloMem)
        (if bltu_0 then divKTrialCallV5Un0
            (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
          else if bltu_1 then divKTrialCallV5Un0
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV5 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hq
  delta fullModN3UnifiedPostNoX1V5 fullModN3DenormPostV5 fullDivN3FrameNoX1V5
    fullDivN3ScratchNoX1V5 at hq
  simp (config := { zeta := true }) only [denormModPost_unfold] at hq
  rw [word_add_zero] at hq
  rw [modConcretePostNoX1ExactRegsFrame_unfold,
      evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b)
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64))
        hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  xperm_hyp hq

/-- Named callable-frame version for n=3 MOD. -/
theorem fullModN3UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.mod a b).getLimbN 0 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hdiv1 : (EvmWord.mod a b).getLimbN 1 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hdiv2 : (EvmWord.mod a b).getLimbN 2 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hdiv3 : (EvmWord.mod a b).getLimbN 3 =
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64))) :
    ∀ h,
      (fullModN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV5 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hp
  rw [modStackDispatchPostCallableExactFrame_unfold]
  exact sepConj_mono_left
    (fun h hp => modConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp)
    h
    (fullModN3UnifiedPostNoX1V5_frame_to_modConcretePostNoX1ExactRegsFrame_scratch
      bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem
      raVal ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hp)

/-- Word-remainder form: from `hdivWord : fullModN3RemainderWordV5 ... = EvmWord.mod a b`. -/
theorem fullModN3UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch_word
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullModN3RemainderWordV5 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.mod a b) :
    ∀ h,
      (fullModN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV5 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) h := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullModN3V5_hmods_of_word_eq a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      bltu_1 bltu_0
      hdivWord
  exact fullModN3UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch
    bltu_1 bltu_0 sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl hdiv0 hdiv1 hdiv2 hdiv3

end EvmAsm.Evm64
