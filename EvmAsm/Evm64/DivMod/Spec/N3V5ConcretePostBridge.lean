/-
  EvmAsm.Evm64.DivMod.Spec.N3V5ConcretePostBridge

  N=3 V5 bridge from `fullDivN3UnifiedPostNoX1V5` (with exact caller `x1`) to the
  public concrete post `divConcretePostNoX1ExactRegsFrame` (then to the named
  `divStackDispatchPostCallableExactFrame`), plus the v5 div128 scratch cell.
  Faithful v5 mirror of the v4 n=3 chain (`N3V4StackPre.lean` :1018–1204), over the
  v5 callable-trial quotient/remainder families (`fullDivN3R{0,1}V5`) and the v5
  trial scratch helpers (`divKTrialCallV5DLo`/`Un0`).  Bead `evm-asm-wbc4i.9.3.3.7`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopDenormDefs
public import EvmAsm.Evm64.DivMod.Spec.N3V5QuotientWord
public import EvmAsm.Evm64.DivMod.Spec.Dispatcher
public import EvmAsm.Evm64.DivMod.Spec.CallablePost

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- N=3 v5 bridge: `fullDivN3UnifiedPostNoX1V5` + exact `x1` → the public concrete
    `divConcretePostNoX1ExactRegsFrame` + the v5 scratch cell. -/
theorem fullDivN3UnifiedPostNoX1V5_frame_to_divConcretePostNoX1ExactRegsFrame_scratch
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (0 : Word))
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (divConcretePostNoX1ExactRegsFrame sp a b
        (signExtend12 4095) raVal
        (signExtend12 (0 : BitVec 12) - fullDivN3Shift b2)
        (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (0 : Word)
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
          else if bltu_1 then divKTrialCallV5DLo
            (fullDivN3NormV b0 b1 b2 b3).2.2.1 else dloMem)
        (if bltu_0 then divKTrialCallV5Un0
            (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
          else if bltu_1 then divKTrialCallV5Un0
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV5 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hq
  let shift := fullDivN3Shift b2
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r1 := fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let scratchRet := if bltu_0 then (base + div128CallRetOff)
    else if bltu_1 then (base + div128CallRetOff) else retMem
  let scratchD := if bltu_0 then v.2.2.1
    else if bltu_1 then v.2.2.1 else dMem
  let scratchDLo := if bltu_0 then divKTrialCallV5DLo v.2.2.1
    else if bltu_1 then divKTrialCallV5DLo v.2.2.1 else dloMem
  let scratchUn0' := if bltu_0 then divKTrialCallV5Un0 r1.2.2.1
    else if bltu_1 then divKTrialCallV5Un0 u.2.2.2.1 else scratchUn0
  let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
  let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
  let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
  let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
  rw [divConcretePostNoX1ExactRegsFrame_unfold]
  change
    ((((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0.1) ** (.x10 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
     ((.x9 ↦ᵣ (signExtend12 4095 : Word)) ** (.x1 ↦ᵣ raVal) **
      (.x2 ↦ᵣ antiShift) ** (.x6 ↦ᵣ r1.1) ** (.x7 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ r0.1) ** evmWordIs sp a **
      divScratchValuesCallNoX1 sp r0.1 r1.1 (0 : Word) (0 : Word)
        u0' u1' u2' u3' r0.2.2.2.2.2 r1.2.2.2.2.2
        (0 : Word) (0 : Word) shift (3 : Word) (0 : Word)
        scratchRet scratchD scratchDLo scratchUn0')) **
     ((sp + signExtend12 3936) ↦ₘ
      fullDivN3ScratchMemV5 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h
  delta fullDivN3UnifiedPostNoX1V5 fullDivN3DenormPostV5 fullDivN3FrameNoX1V5
    fullDivN3ScratchNoX1V5 at hq
  simp only [denormDivPost_unfold] at hq
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ
          (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 40) ↦ₘ
          (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1) **
       ((sp + 48) ↦ₘ (0 : Word)) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
          hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- Named callable-frame version. -/
theorem fullDivN3UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = (0 : Word))
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV5 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hp
  rw [divStackDispatchPostCallableExactFrame_unfold]
  have hExact :=
    fullDivN3UnifiedPostNoX1V5_frame_to_divConcretePostNoX1ExactRegsFrame_scratch
      bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem
      raVal ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hp
  exact sepConj_mono_left
    (fun h hp => divConcretePostNoX1ExactRegs_weaken_callable_frame sp a b h hp)
    h hExact

/-- Word-quotient form: from `hdivWord : fullDivN3QuotientWordV5 ... = EvmWord.div a b`. -/
theorem fullDivN3UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch_word
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullDivN3QuotientWordV5 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b) :
    ∀ h,
      (fullDivN3UnifiedPostNoX1V5 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN3ScratchMemV5 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          scratchMem)) h := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN3V5_hdivs_of_word_eq bltu_1 bltu_0 a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord
  exact fullDivN3UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch
    bltu_1 bltu_0 sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl hdiv0 hdiv1 hdiv2 hdiv3

end EvmAsm.Evm64
