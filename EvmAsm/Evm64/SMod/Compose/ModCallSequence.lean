/-
  EvmAsm.Evm64.SMod.Compose.ModCallSequence

  SMOD wrapper composition from entry through the JAL into the appended unsigned
  MOD callable.
-/

module

public import EvmAsm.Evm64.SMod.Compose.DivisorAbsSequence
public import EvmAsm.Evm64.SMod.Compose.ModCall

public section

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_signs_abs_then_modCall_spec_in_smodCodeV4
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base (base + wrapperEndOff)
      (smodCodeV4 base)
      ((((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendLimb0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendLimb1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendLimb2)))) **
       (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorLimb0) **
        ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorLimb1) **
        ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorLimb2))) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let dividendMask := (0 : Word) - dividendSign
       let dividendXored0 := dividendLimb0 ^^^ dividendMask
       let dividendSum0 := dividendXored0 + dividendSign
       let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
       let dividendXored1 := dividendLimb1 ^^^ dividendMask
       let dividendSum1 := dividendXored1 + dividendCarry0
       let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
       let dividendXored2 := dividendLimb2 ^^^ dividendMask
       let dividendSum2 := dividendXored2 + dividendCarry1
       let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
       let dividendXored3 := dividendTop ^^^ dividendMask
       let dividendSum3 := dividendXored3 + dividendCarry2
       let divisorMask := (0 : Word) - divisorSign
       let divisorXored0 := divisorLimb0 ^^^ divisorMask
       let divisorSum0 := divisorXored0 + divisorSign
       let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
       let divisorXored1 := divisorLimb1 ^^^ divisorMask
       let divisorSum1 := divisorXored1 + divisorCarry0
       let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
       let divisorXored2 := divisorLimb2 ^^^ divisorMask
       let divisorSum2 := divisorXored2 + divisorCarry1
       let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
       let divisorXored3 := divisorTop ^^^ divisorMask
       let divisorSum3 := divisorXored3 + divisorCarry2
       let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
       (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
       (((((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
        ((.x8 ↦ᵣ dividendSign) **
         ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ dividendSum0) **
         ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ dividendSum1) **
         ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ dividendSum2) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendSum3))) **
        (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
         (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) ** (.x11 ↦ᵣ divisorCarry3) **
         ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ divisorSum0) **
         ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ divisorSum1) **
         ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ divisorSum2) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
           divisorSum3))) **
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         EvmAsm.Evm64.divScratchValuesCallNoX1 sp
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))) := by
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff
  let dividendMask := (0 : Word) - dividendSign
  let dividendXored0 := dividendLimb0 ^^^ dividendMask
  let dividendSum0 := dividendXored0 + dividendSign
  let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
  let dividendXored1 := dividendLimb1 ^^^ dividendMask
  let dividendSum1 := dividendXored1 + dividendCarry0
  let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
  let dividendXored2 := dividendLimb2 ^^^ dividendMask
  let dividendSum2 := dividendXored2 + dividendCarry1
  let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
  let dividendXored3 := dividendTop ^^^ dividendMask
  let dividendSum3 := dividendXored3 + dividendCarry2
  let divisorMask := (0 : Word) - divisorSign
  let divisorXored0 := divisorLimb0 ^^^ divisorMask
  let divisorSum0 := divisorXored0 + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorXored1 := divisorLimb1 ^^^ divisorMask
  let divisorSum1 := divisorXored1 + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorXored2 := divisorLimb2 ^^^ divisorMask
  let divisorSum2 := divisorXored2 + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorXored3 := divisorTop ^^^ divisorMask
  let divisorSum3 := divisorXored3 + divisorCarry2
  let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
  let dispatchExtra : EvmAsm.Rv64.Assertion :=
    ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
     EvmAsm.Evm64.divScratchValuesCallNoX1 sp
       q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratchUn0)
  let pre : EvmAsm.Rv64.Assertion :=
    ((((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (dividendMem3 ↦ₘ dividendTop))) **
     (.x13 ↦ᵣ x13Old)) **
     ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
     (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
       (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
      ((dividendMem0 ↦ₘ dividendLimb0) **
       (dividendMem1 ↦ₘ dividendLimb1) **
       (dividendMem2 ↦ₘ dividendLimb2)))) **
     ((divisorMem0 ↦ₘ divisorLimb0) **
      (divisorMem1 ↦ₘ divisorLimb1) **
      (divisorMem2 ↦ₘ divisorLimb2))) **
     dispatchExtra)
  let mid : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x8 ↦ᵣ dividendSign) **
      (dividendMem0 ↦ₘ dividendSum0) **
      (dividendMem1 ↦ₘ dividendSum1) **
      (dividendMem2 ↦ₘ dividendSum2) **
      (dividendMem3 ↦ₘ dividendSum3))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))) **
     dispatchExtra)
  let callFrame : EvmAsm.Rv64.Assertion :=
    (((((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
      ((.x8 ↦ᵣ dividendSign) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
      (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
       (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
       (.x11 ↦ᵣ divisorCarry3) **
       (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
       (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))) **
      dispatchExtra)
  let callPre : EvmAsm.Rv64.Assertion := (.x1 ↦ᵣ vRa) ** callFrame
  let callPost : EvmAsm.Rv64.Assertion :=
    (.x1 ↦ᵣ ((base + modCallOff) + 4)) ** callFrame
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 48 base (base + modCallOff)
      (smodCodeV4 base) pre mid := by
    dsimp [pre, mid, dispatchExtra, dividendMem0, dividendMem1, dividendMem2,
      dividendMem3, divisorMem0, divisorMem1, divisorMem2, divisorMem3,
      dividendSign, divisorSign, dividendMask, dividendXored0, dividendSum0,
      dividendCarry0, dividendXored1, dividendSum1, dividendCarry1,
      dividendXored2, dividendSum2, dividendCarry2, dividendXored3,
      dividendSum3, divisorMask, divisorXored0, divisorSum0, divisorCarry0,
      divisorXored1, divisorSum1, divisorCarry1, divisorXored2, divisorSum2,
      divisorCarry2, divisorXored3, divisorSum3, divisorCarry3]
    simpa [divisorAbsOff, modCallOff, BitVec.add_assoc] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        dispatchExtra
        (by pcFree)
        (saveRa_signs_abs_then_divisorAbs_spec_in_smodCodeV4
          vRa vSavedOld sp sDividendOld x13Old sDivisorOld
          dividendMaskOld dividendValueOld dividendCarryOld
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base))
  have hCall : EvmAsm.Rv64.cpsTripleWithin 1 (base + modCallOff)
      ((base + modCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_smodCallOff)
      (smodCodeV4 base) callPre callPost := by
    dsimp [callPre, callPost]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameR
        callFrame
        (by pcFree)
        (modCall_spec_in_smodCodeV4 vRa base)
  have hCallExit :
      (base + modCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_smodCallOff =
        base + wrapperEndOff := by
    simp [modCallOff, wrapperEndOff, EvmAsm.Evm64.evm_smodCallOff]
    bv_addr
  have hCall' : EvmAsm.Rv64.cpsTripleWithin 1 (base + modCallOff)
      (base + wrapperEndOff) (smodCodeV4 base) callPre callPost := by
    rw [← hCallExit]
    exact hCall
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [mid, callPre, callFrame, dispatchExtra] at hp ⊢
      xperm_hyp hp) hPrefix hCall'
  simpa [pre, callPost, callFrame, dispatchExtra, dividendSign, divisorSign,
    dividendMask, dividendXored0, dividendSum0, dividendCarry0, dividendXored1,
    dividendSum1, dividendCarry1, dividendXored2, dividendSum2, dividendCarry2,
    dividendXored3, dividendSum3, divisorMask, divisorXored0, divisorSum0,
    divisorCarry0, divisorXored1, divisorSum1, divisorCarry1, divisorXored2,
    divisorSum2, divisorCarry2, divisorXored3, divisorSum3, divisorCarry3,
    dividendMem0, dividendMem1, dividendMem2, dividendMem3, divisorMem0,
    divisorMem1, divisorMem2, divisorMem3] using hSeq

end EvmAsm.Evm64.SMod.Compose
