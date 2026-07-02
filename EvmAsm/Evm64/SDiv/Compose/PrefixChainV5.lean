/-
  EvmAsm.Evm64.SDiv.Compose.PrefixChainV5

  v5 SDIV wrapper-prefix composition ladder over `sdivCodeV5` — verbatim v4→v5
  mirrors (the wrapper prefix is identical between evm_sdiv_v4 and evm_sdiv_v5).
  Bottom-up: saveRa → signs → abs → signXor → divCall → framed → dispatchReady
  → exact_callable. Toward the SDIV `.proven` flip over evm_div_callable_v5.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseCodeV5
import EvmAsm.Evm64.SDiv.Compose.SaveRaSignBlocks
import EvmAsm.Evm64.SDiv.Compose.BaseSignSequence
import EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsSequence
import EvmAsm.Evm64.SDiv.Compose.DivisorAbsSequence
import EvmAsm.Evm64.SDiv.Compose.SignXorSequence
import EvmAsm.Evm64.SDiv.Compose.DivCallPrefix
import EvmAsm.Evm64.SDiv.Compose.DivCallDispatchFrame
import EvmAsm.Evm64.SDiv.Compose.DispatchPrefix

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_then_dividendSign_spec_in_sdivCodeV5
    (vRa vSavedOld sp sOld dividendTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 3 base ((base + dividendSignOff) + 8) (sdivCodeV5 base)
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
       ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
          dividendTop)))
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x12 ↦ᵣ sp) **
        (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
          dividendTop))) := by
  have hSave :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
          dividendTop)))
      (by pcFree)
      (saveRa_spec_in_sdivCodeV5 vRa vSavedOld base)
  have hSign :=
    EvmAsm.Rv64.cpsTripleWithin_frameL
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))))
      (by pcFree)
      (dividendSign_spec_in_sdivCodeV5 sp sOld dividendTop base)
  exact EvmAsm.Rv64.cpsTripleWithin_seq_same_cr hSave hSign


theorem saveRa_dividendSign_then_divisorSign_spec_in_sdivCodeV5
    (vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 5 base ((base + divisorSignOff) + 8) (sdivCodeV5 base)
      (saveRaDividendSignThenDivisorSignPre vRa vSavedOld sp sDividendOld
        dividendTop sDivisorOld divisorTop)
      (saveRaDividendSignThenDivisorSignPost vRa sp dividendTop divisorTop) := by
  rw [saveRaDividendSignThenDivisorSignPre_unfold,
      saveRaDividendSignThenDivisorSignPost_unfold]
  let pre : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     ((.x9 ↦ᵣ sDivisorOld) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  let mid : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x12 ↦ᵣ sp) **
       (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     ((.x9 ↦ᵣ sDivisorOld) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  let midDivisor : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sDivisorOld) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  let post : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     ((.x12 ↦ᵣ sp) **
      (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 3 base (base + divisorSignOff)
      (sdivCodeV5 base) pre mid := by
    dsimp [pre, mid]
    simpa [dividendSignOff, divisorSignOff, BitVec.add_assoc] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        ((.x9 ↦ᵣ sDivisorOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
          divisorTop))
        (by pcFree)
        (saveRa_then_dividendSign_spec_in_sdivCodeV5
          vRa vSavedOld sp sDividendOld dividendTop base))
  have hDivisor : EvmAsm.Rv64.cpsTripleWithin 2 (base + divisorSignOff)
      ((base + divisorSignOff) + 8) (sdivCodeV5 base) midDivisor post := by
    dsimp [midDivisor, post]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameL
        (((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
          ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
            dividendTop)))
        (by pcFree)
        (divisorSign_spec_in_sdivCodeV5 sp sDivisorOld divisorTop base)
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, midDivisor] at hp ⊢
      xperm_hyp hp) hPrefix hDivisor
  simpa [pre, post] using hSeq


theorem saveRa_signs_then_dividendAbs_spec_in_sdivCodeV5
    (vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld limb0 limb1 limb2 dividendTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 26 base ((base + dividendAbsOff) + 84) (sdivCodeV5 base)
      (saveRaSignsThenDividendAbsPre vRa vSavedOld sp sDividendOld sDivisorOld
        divisorTop maskOld valueOld carryOld
        limb0 limb1 limb2 dividendTop)
      (saveRaSignsThenDividendAbsPost vRa sp divisorTop
        limb0 limb1 limb2 dividendTop) := by
  rw [saveRaSignsThenDividendAbsPre_unfold,
      saveRaSignsThenDividendAbsPost_unfold]
  let sign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let mem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let mem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let mem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let mem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let mask := (0 : Word) - sign
  let xored0 := limb0 ^^^ mask
  let sum0 := xored0 + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let xored1 := limb1 ^^^ mask
  let sum1 := xored1 + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let xored2 := limb2 ^^^ mask
  let sum2 := xored2 + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let xored3 := dividendTop ^^^ mask
  let sum3 := xored3 + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  let extra : EvmAsm.Rv64.Assertion :=
    (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
      (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
     ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
  let pre : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
       ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
      ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let mid : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x8 ↦ᵣ sign) ** (mem3 ↦ₘ dividendTop))) **
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let absPre : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
      (mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) **
      (mem2 ↦ₘ limb2) ** (mem3 ↦ₘ dividendTop)))
  let post : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
      (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
      (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 5 base (base + dividendAbsOff)
      (sdivCodeV5 base) pre mid := by
    dsimp [pre, mid, extra, mem3, divisorMem3, sign, divisorSign]
    simpa [divisorSignOff, dividendAbsOff, BitVec.add_assoc,
      saveRaDividendSignThenDivisorSignPre_unfold,
      saveRaDividendSignThenDivisorSignPost_unfold] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
          (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
         ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
        (by pcFree)
        (saveRa_dividendSign_then_divisorSign_spec_in_sdivCodeV5
          vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop
          base))
  have hAbs : EvmAsm.Rv64.cpsTripleWithin 21 (base + dividendAbsOff)
      ((base + dividendAbsOff) + 84) (sdivCodeV5 base) absPre post := by
    have hSpec := dividendAbs_spec_in_sdivCodeV5
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 dividendTop
      base
    rw [dividendAbsPre_unfold, dividendAbsPost_unfold] at hSpec
    simpa [absPre, post, mem0, mem1, mem2, mem3,
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff, mask, xored0, sum0,
      carry0, xored1, sum1, carry1, xored2, sum2, carry2, xored3, sum3,
      carry3] using
      EvmAsm.Rv64.cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
          ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))))
        (by pcFree)
        hSpec
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, absPre, extra] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post] using hSeq


theorem saveRa_signs_abs_then_divisorAbs_spec_in_sdivCodeV5
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 47 base ((base + divisorAbsOff) + 84) (sdivCodeV5 base)
      (saveRaSignsAbsThenDivisorAbsPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (saveRaSignsAbsThenDivisorAbsPost vRa sp
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  rw [saveRaSignsAbsThenDivisorAbsPre_unfold,
      saveRaSignsAbsThenDivisorAbsPost_unfold]
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
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
  let dividendCarry3 := if BitVec.ult dividendSum3 dividendCarry2 then (1 : Word) else 0
  let divisorLower : EvmAsm.Rv64.Assertion :=
    ((divisorMem0 ↦ₘ divisorLimb0) ** (divisorMem1 ↦ₘ divisorLimb1) **
     (divisorMem2 ↦ₘ divisorLimb2))
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
     divisorLower)
  let mid : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ dividendSign) **
       (.x10 ↦ᵣ dividendMask) ** (.x7 ↦ᵣ dividendSum3) **
       (.x11 ↦ᵣ dividendCarry3) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     divisorLower)
  let absPre : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ dividendSign) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ dividendMask) ** (.x7 ↦ᵣ dividendSum3) **
      (.x11 ↦ᵣ dividendCarry3) **
      (divisorMem0 ↦ₘ divisorLimb0) **
      (divisorMem1 ↦ₘ divisorLimb1) **
      (divisorMem2 ↦ₘ divisorLimb2) **
      (divisorMem3 ↦ₘ divisorTop)))
  let post : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ dividendSign) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 26 base (base + divisorAbsOff)
      (sdivCodeV5 base) pre mid := by
    dsimp [pre, mid, divisorLower, dividendSign, divisorSign, dividendMem0,
      dividendMem1, dividendMem2, dividendMem3, divisorMem3,
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff,
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff, dividendMask, dividendXored0,
      dividendSum0, dividendCarry0, dividendXored1, dividendSum1,
      dividendCarry1, dividendXored2, dividendSum2, dividendCarry2,
      dividendXored3, dividendSum3, dividendCarry3]
    simpa [dividendAbsOff, divisorAbsOff, BitVec.add_assoc,
      saveRaSignsThenDividendAbsPre_unfold,
      saveRaSignsThenDividendAbsPost_unfold] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        ((divisorMem0 ↦ₘ divisorLimb0) **
         (divisorMem1 ↦ₘ divisorLimb1) **
         (divisorMem2 ↦ₘ divisorLimb2))
        (by pcFree)
        (saveRa_signs_then_dividendAbs_spec_in_sdivCodeV5
          vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
          dividendMaskOld dividendValueOld dividendCarryOld
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop base))
  have hAbs : EvmAsm.Rv64.cpsTripleWithin 21 (base + divisorAbsOff)
      ((base + divisorAbsOff) + 84) (sdivCodeV5 base) absPre post := by
    simpa [absPre, post, divisorMem0, divisorMem1, divisorMem2, divisorMem3,
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff, divisorMask, divisorXored0,
      divisorSum0, divisorCarry0, divisorXored1, divisorSum1, divisorCarry1,
      divisorXored2, divisorSum2, divisorCarry2, divisorXored3, divisorSum3,
      divisorCarry3, divisorAbsPre_unfold, divisorAbsPost_unfold] using
      EvmAsm.Rv64.cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
          ((.x8 ↦ᵣ dividendSign) **
           (dividendMem0 ↦ₘ dividendSum0) **
           (dividendMem1 ↦ₘ dividendSum1) **
           (dividendMem2 ↦ₘ dividendSum2) **
           (dividendMem3 ↦ₘ dividendSum3))))
        (by pcFree)
        (divisorAbs_spec_in_sdivCodeV5
          sp divisorSign dividendMask dividendSum3 dividendCarry3
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, absPre, divisorLower] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post] using hSeq


theorem saveRa_signs_abs_then_signXor_spec_in_sdivCodeV5
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 48 base ((base + signXorOff) + 4) (sdivCodeV5 base)
      (saveRaSignsAbsThenSignXorPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (saveRaSignsAbsThenSignXorPost vRa sp
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  rw [saveRaSignsAbsThenSignXorPre_unfold,
      saveRaSignsAbsThenSignXorPost_unfold]
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
  let prefixPost : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ dividendSign) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))
  let signFrame : EvmAsm.Rv64.Assertion :=
    (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((dividendMem0 ↦ₘ dividendSum0) **
      (dividendMem1 ↦ₘ dividendSum1) **
      (dividendMem2 ↦ₘ dividendSum2) **
      (dividendMem3 ↦ₘ dividendSum3) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))
  let signPre : EvmAsm.Rv64.Assertion :=
    (((.x8 ↦ᵣ dividendSign) ** (.x9 ↦ᵣ divisorSign)) ** signFrame)
  let post : EvmAsm.Rv64.Assertion :=
    (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) ** signFrame)
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 47 base (base + signXorOff)
      (sdivCodeV5 base) pre prefixPost := by
    dsimp [pre, prefixPost, dividendSign, divisorSign, dividendMem0,
      dividendMem1, dividendMem2, dividendMem3, divisorMem0, divisorMem1,
      divisorMem2, divisorMem3, EvmAsm.Evm64.evm_sdivDividendTopLimbOff,
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff, dividendMask, dividendXored0,
      dividendSum0, dividendCarry0, dividendXored1, dividendSum1,
      dividendCarry1, dividendXored2, dividendSum2, dividendCarry2,
      dividendXored3, dividendSum3, divisorMask, divisorXored0, divisorSum0,
      divisorCarry0, divisorXored1, divisorSum1, divisorCarry1,
      divisorXored2, divisorSum2, divisorCarry2, divisorXored3, divisorSum3,
      divisorCarry3]
    simpa [divisorAbsOff, signXorOff, BitVec.add_assoc,
      saveRaSignsAbsThenDivisorAbsPre_unfold,
      saveRaSignsAbsThenDivisorAbsPost_unfold] using
      (saveRa_signs_abs_then_divisorAbs_spec_in_sdivCodeV5
        vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)
  have hXor : EvmAsm.Rv64.cpsTripleWithin 1 (base + signXorOff) ((base + signXorOff) + 4)
      (sdivCodeV5 base) signPre post := by
    dsimp [signPre, post, signFrame, resultSign]
    exact EvmAsm.Rv64.cpsTripleWithin_frameR signFrame (by pcFree)
      (signXor_spec_in_sdivCodeV5 dividendSign divisorSign base)
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [prefixPost, signPre, signFrame] at hp ⊢
      xperm_hyp hp) hPrefix hXor
  simpa [pre, post] using hSeq


theorem saveRa_signs_abs_signXor_then_divCall_spec_in_sdivCodeV5
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV5 base)
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
      (sdivCodeV5 base) pre signPost := by
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
      (saveRa_signs_abs_then_signXor_spec_in_sdivCodeV5
        vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)
  have hCall : EvmAsm.Rv64.cpsTripleWithin 1 (base + divCallOff)
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV5 base) callPre post := by
    dsimp [callPre, post]
    exact EvmAsm.Rv64.cpsTripleWithin_frameR callFrame (by pcFree)
      (divCall_spec_in_sdivCodeV5 vRa base)
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [signPost, callPre, callFrame] at hp ⊢
      xperm_hyp hp) hPrefix hCall
  simpa [pre, post, callFrame] using hSeq


theorem saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCodeV5
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV5 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaSignsAbsSignXorThenDivCallPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) := by
  have hFramePcFree :
      ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0).pcFree := by
    rw [EvmAsm.Evm64.divScratchValuesCallNoX1_unfold]
    unfold EvmAsm.Evm64.divScratchValues
    pcFree
  exact EvmAsm.Rv64.cpsTripleWithin_frameR _ hFramePcFree
    (saveRa_signs_abs_signXor_then_divCall_spec_in_sdivCodeV5
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)


theorem saveRa_signs_abs_signXor_then_divCall_dispatchReady_spec_in_sdivCodeV5
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base
      ((base + divCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCodeV5 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  have hPrefix :=
    saveRa_signs_abs_signXor_then_divCall_framed_for_dispatch_spec_in_sdivCodeV5
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    rw [saveRaSignsAbsSignXorThenDivCallPost_unfold] at hq
    rw [saveRaDivCallDispatchReadyPost_unfold]
    dsimp only at hq ⊢
    rw [divModStackDispatchPreNoX1_unfold_explicit_sdiv]
    simp [sdivAbsDividendWord, sdivAbsDivisorWord, rippleNegWord, EvmWord.getLimbN,
      EvmWord.getLimb_fromLimbs] at hq ⊢
    xperm_hyp hq) hPrefix

/-- v4 sequence of the SDIV wrapper prefix with any callable proof that consumes
    the exact dispatch-ready post. -/

theorem saveRa_signs_abs_signXor_then_divCall_then_exact_callable_spec_in_sdivCodeV5
    {nSteps : Nat} {callPost : EvmAsm.Rv64.Assertion}
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base callableExit : Word)
    (hCallable :
      EvmAsm.Rv64.cpsTripleWithin nSteps (base + wrapperEndOff) callableExit (sdivCodeV5 base)
        (saveRaDivCallDispatchReadyPost vRa sp base
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
          v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
        callPost) :
    EvmAsm.Rv64.cpsTripleWithin (49 + nSteps) base callableExit (sdivCodeV5 base)
      ((saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) **
       ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem))
      callPost := by
  have hPrefixRaw :=
    saveRa_signs_abs_signXor_then_divCall_dispatchReady_spec_in_sdivCodeV5
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 49 base (base + wrapperEndOff) (sdivCodeV5 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
    rw [← divCall_target_eq_wrapperEndOff base]
    exact hPrefixRaw
  have hPrefixFramed := EvmAsm.Rv64.cpsTripleWithin_frameR
    ((sp + EvmAsm.Rv64.signExtend12 3936) ↦ₘ scratchMem) (by pcFree) hPrefix
  exact EvmAsm.Rv64.cpsTripleWithin_seq_same_cr hPrefixFramed hCallable


end EvmAsm.Evm64.SDiv.Compose
