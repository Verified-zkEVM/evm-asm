/-
  EvmAsm.Evm64.SMod.Compose.DispatchReadyView

  SMOD-local views of the dispatch-ready post consumed by the unsigned MOD
  callable.
-/

import EvmAsm.Evm64.SMod.Compose.AbsComponents
import EvmAsm.Evm64.SMod.Compose.Bridges
import EvmAsm.Evm64.SMod.Compose.DispatchReadyPost

namespace EvmAsm.Evm64.SMod.Compose

/-- Unfold `saveRaAbsThenModCallDispatchReadyPost` using the SMOD-local
    absolute-value component names. -/
theorem saveRaAbsThenModCallDispatchReadyPost_unfold_smod_components
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    {v2 v5 v6 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word} :
    saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 =
      (let dividendSign := smodAbsSign dividendTop
       let divisorSign := smodAbsSign divisorTop
       let divisorMask := smodAbsMask divisorTop
       let divisorSum3 :=
         smodAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let divisorCarry3 :=
         smodAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let dividendAbsWord : EvmWord :=
         smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
           divisorSign ((base + modCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
           q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((.x8 ↦ᵣ dividendSign) ** (.x13 ↦ᵣ dividendSign) **
           (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))) := by
  rw [saveRaAbsThenModCallDispatchReadyPost_unfold]
  rfl

/-- Fully explicit SMOD-offset view of the dispatch-ready post. This exposes
    the normalized dividend/divisor limbs as `smodAbsSum*` atoms while keeping
    the private SMOD result-sign frame. -/
theorem saveRaAbsThenModCallDispatchReadyPost_unfold_explicit_smod_components
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    {v2 v5 v6 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word} :
    saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 =
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ smodAbsSign divisorTop) **
       (.x1 ↦ᵣ ((base + modCallOff) + 4)) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ smodAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
       (.x10 ↦ᵣ smodAbsMask divisorTop) **
       (.x11 ↦ᵣ smodAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
       (.x0 ↦ᵣ (0 : Word)) **
       (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ
          smodAbsSum0 dividendLimb0 dividendTop) **
        ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ
          smodAbsSum1 dividendLimb0 dividendLimb1 dividendTop) **
        ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ
          smodAbsSum2 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
          smodAbsSum3 dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)) **
       (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ
          smodAbsSum0 divisorLimb0 divisorTop) **
        ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ
          smodAbsSum1 divisorLimb0 divisorLimb1 divisorTop) **
        ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ
          smodAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          smodAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)) **
       EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0) **
      ((.x8 ↦ᵣ smodAbsSign dividendTop) ** (.x13 ↦ᵣ smodAbsSign dividendTop) **
        (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))) := by
  rw [saveRaAbsThenModCallDispatchReadyPost_unfold_smod_components]
  dsimp only
  rw [divModStackDispatchPreNoX1_unfold_explicit_smod]
  rw [smodAbsDividendWord_getLimbN_0, smodAbsDividendWord_getLimbN_1,
    smodAbsDividendWord_getLimbN_2, smodAbsDividendWord_getLimbN_3,
    smodAbsDivisorWord_getLimbN_0, smodAbsDivisorWord_getLimbN_1,
    smodAbsDivisorWord_getLimbN_2, smodAbsDivisorWord_getLimbN_3]

end EvmAsm.Evm64.SMod.Compose
