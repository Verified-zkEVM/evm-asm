/-
  EvmAsm.Evm64.SDiv.Compose.DivCallPrefix

  Sequencing proof for the SDIV wrapper prefix through the near call into
  `evm_div_callable`, before adding dispatcher scratch framing.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallViews
import EvmAsm.Evm64.SDiv.Compose.SignXorSequence

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_signs_abs_signXor_then_divCall_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (saveRaSignsAbsSignXorThenDivCallPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  rw [saveRaSignsAbsSignXorThenDivCallPre_unfold,
      saveRaSignsAbsSignXorThenDivCallPost_unfold]
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let resultSign := dividendSign ^^^ divisorSign
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
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
  let pre : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         (dividendMem3 ↦ₘ dividendTop))) **
       ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
      (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
        (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
       ((dividendMem0 ↦ₘ dividendLimb0) **
        (dividendMem1 ↦ₘ dividendLimb1) **
        (dividendMem2 ↦ₘ dividendLimb2)))) **
     ((divisorMem0 ↦ₘ divisorLimb0) **
      (divisorMem1 ↦ₘ divisorLimb1) **
      (divisorMem2 ↦ₘ divisorLimb2)))
  let signPost : EvmAsm.Rv64.Assertion :=
    (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) **
     (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
       (.x11 ↦ᵣ divisorCarry3) **
       (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
       (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))))
  let callFrame : EvmAsm.Rv64.Assertion :=
    (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) **
     ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
      ((dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
       (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
       (.x11 ↦ᵣ divisorCarry3) **
       (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
       (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))))
  let callPre : EvmAsm.Rv64.Assertion := (.x1 ↦ᵣ vRa) ** callFrame
  let post : EvmAsm.Rv64.Assertion := (.x1 ↦ᵣ ((base + divCallOff) + 4)) ** callFrame
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 48 base (base + divCallOff)
      (sdivCodeV4 base) pre signPost := by
    dsimp [pre, signPost, dividendSign, divisorSign, resultSign, dividendMem0,
      dividendMem1, dividendMem2, dividendMem3, divisorMem0, divisorMem1,
      divisorMem2, divisorMem3, EvmAsm.Evm64.evm_sdivDividendTopLimbOff,
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff, dividendMask, dividendXored0,
      dividendSum0, dividendCarry0, dividendXored1, dividendSum1,
      dividendCarry1, dividendXored2, dividendSum2, dividendCarry2,
      dividendXored3, dividendSum3, divisorMask, divisorXored0, divisorSum0,
      divisorCarry0, divisorXored1, divisorSum1, divisorCarry1,
      divisorXored2, divisorSum2, divisorCarry2, divisorXored3, divisorSum3,
      divisorCarry3]
    simpa [signXorOff, divCallOff, BitVec.add_assoc,
      saveRaSignsAbsThenSignXorPre_unfold,
      saveRaSignsAbsThenSignXorPost_unfold] using
      (saveRa_signs_abs_then_signXor_spec_in_sdivCodeV4
        vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)
  have hCall : EvmAsm.Rv64.cpsTripleWithin 1 (base + divCallOff)
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV4 base) callPre post := by
    dsimp [callPre, post]
    exact EvmAsm.Rv64.cpsTripleWithin_frameR callFrame (by pcFree)
      (divCall_spec_in_sdivCodeV4 vRa base)
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [signPost, callPre, callFrame] at hp ⊢
      xperm_hyp hp) hPrefix hCall
  simpa [pre, post, callFrame] using hSeq

end EvmAsm.Evm64.SDiv.Compose
