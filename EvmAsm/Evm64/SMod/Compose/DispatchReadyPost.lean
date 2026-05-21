/-
  EvmAsm.Evm64.SMod.Compose.DispatchReadyPost

  Named postcondition consumed by the unsigned MOD callable after the SMOD
  prefix has normalized signs and absolute values.
-/

import EvmAsm.Evm64.DivMod.Spec.Dispatcher
import EvmAsm.Evm64.SDiv.Compose.Words
import EvmAsm.Evm64.SMod.Compose.BaseOffsets

namespace EvmAsm.Evm64.SMod.Compose

/-- Post-shape consumed by the unsigned MOD callable: the dispatcher's pre,
    built from the normalized absolute-value operands, paired with the
    SMOD-wrapper-private dividend-sign frame. -/
@[irreducible]
def saveRaAbsThenModCallDispatchReadyPost
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word) : EvmAsm.Rv64.Assertion :=
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let divisorMask := (0 : Word) - divisorSign
  let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
  let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
  let dividendAbsWord : EvmWord :=
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDividendWord
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord : EvmWord :=
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDivisorWord
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
      divisorSign ((base + modCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
    ((.x8 ↦ᵣ dividendSign) ** (.x13 ↦ᵣ dividendSign) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))

theorem saveRaAbsThenModCallDispatchReadyPost_unfold
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
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let divisorMask := (0 : Word) - divisorSign
       let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
       let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
       let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
       let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
       let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
       let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
       let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
       let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
       let dividendAbsWord : EvmWord :=
         EvmAsm.Evm64.SDiv.Compose.sdivAbsDividendWord
           dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         EvmAsm.Evm64.SDiv.Compose.sdivAbsDivisorWord
           divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
           divisorSign ((base + modCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
           q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((.x8 ↦ᵣ dividendSign) ** (.x13 ↦ᵣ dividendSign) **
           (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))) := by
  delta saveRaAbsThenModCallDispatchReadyPost
  rfl

theorem saveRaAbsThenModCallDispatchReadyPost_pcFree
    {vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop v2 v5 v6
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word} :
    (saveRaAbsThenModCallDispatchReadyPost vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0).pcFree := by
  rw [saveRaAbsThenModCallDispatchReadyPost_unfold]
  dsimp
  rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold,
    EvmAsm.Evm64.divScratchValuesCallNoX1_unfold]
  pcFree

instance pcFreeInst_saveRaAbsThenModCallDispatchReadyPost
    (vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop divisorLimb0
      divisorLimb1 divisorLimb2 divisorTop v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5
      u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) :=
  ⟨saveRaAbsThenModCallDispatchReadyPost_pcFree⟩

end EvmAsm.Evm64.SMod.Compose
