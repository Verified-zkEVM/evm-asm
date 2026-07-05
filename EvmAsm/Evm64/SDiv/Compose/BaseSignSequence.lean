/-
  EvmAsm.Evm64.SDiv.Compose.BaseSignSequence

  SDIV wrapper composition for the saved-`ra` prologue followed by the
  dividend and divisor sign-bit probes.
-/

import EvmAsm.Evm64.SDiv.Compose.SaveRaSignBlocks

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
theorem saveRa_dividendSign_then_divisorSign_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 5 base ((base + divisorSignOff) + 8) (sdivCodeV4 base)
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
      (sdivCodeV4 base) pre mid := by
    dsimp [pre, mid]
    simpa [dividendSignOff, divisorSignOff, BitVec.add_assoc] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        ((.x9 ↦ᵣ sDivisorOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
          divisorTop))
        (by pcFree)
        (saveRa_then_dividendSign_spec_in_sdivCodeV4
          vRa vSavedOld sp sDividendOld dividendTop base))
  have hDivisor : EvmAsm.Rv64.cpsTripleWithin 2 (base + divisorSignOff)
      ((base + divisorSignOff) + 8) (sdivCodeV4 base) midDivisor post := by
    dsimp [midDivisor, post]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameL
        (((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
          ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
            dividendTop)))
        (by pcFree)
        (divisorSign_spec_in_sdivCodeV4 sp sDivisorOld divisorTop base)
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, midDivisor] at hp ⊢
      xperm_hyp hp) hPrefix hDivisor
  simpa [pre, post] using hSeq

end EvmAsm.Evm64.SDiv.Compose
