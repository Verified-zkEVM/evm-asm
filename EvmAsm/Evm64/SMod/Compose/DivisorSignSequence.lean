/-
  EvmAsm.Evm64.SMod.Compose.DivisorSignSequence

  SMOD wrapper composition from the saved-`ra` prologue through probing the
  divisor sign.
-/

module

public import EvmAsm.Evm64.SMod.Compose.PreserveDividendSignSequence
public import EvmAsm.Evm64.SMod.Compose.SignBlockSpecs

public section

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_dividendSign_preserve_then_divisorSign_spec_in_smodCodeV4
    (vRa vSavedOld sp sDividendOld x13Old dividendTop sDivisorOld divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 6 base ((base + divisorSignOff) + 8)
      (smodCodeV4 base)
      (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old)) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop)))
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       ((((.x1 ↦ᵣ vRa) **
         (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
        ((.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ dividendSign) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
        (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x9 ↦ᵣ divisorSign) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
          divisorTop))) := by
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let divisorFrame : EvmAsm.Rv64.Assertion :=
    ((.x9 ↦ᵣ sDivisorOld) **
     ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
       divisorTop))
  let pre : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     (.x13 ↦ᵣ x13Old)) **
     divisorFrame)
  let mid : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      (.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     divisorFrame)
  let midDivisor : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sDivisorOld) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  let postFrame : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  let post : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      (.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x9 ↦ᵣ divisorSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 4 base
      ((base + preserveDividendSignOff) + 4) (smodCodeV4 base) pre mid := by
    dsimp [pre, mid, divisorFrame]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameR
        divisorFrame
        (by pcFree)
        (saveRa_dividendSign_then_preserve_spec_in_smodCodeV4
          vRa vSavedOld sp sDividendOld x13Old dividendTop base)
  have hDivisor : EvmAsm.Rv64.cpsTripleWithin 2 (base + divisorSignOff)
      ((base + divisorSignOff) + 8) (smodCodeV4 base) midDivisor postFrame := by
    dsimp [midDivisor, postFrame]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((.x8 ↦ᵣ dividendSign) **
          ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
            dividendTop))) **
         (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))
        (by pcFree)
        (divisorSign_spec_in_smodCodeV4 sp sDivisorOld divisorTop base)
  have hFall :
      (base + preserveDividendSignOff) + 4 = base + divisorSignOff := by
    simp [preserveDividendSignOff, divisorSignOff]
    bv_addr
  have hDivisor' :
      EvmAsm.Rv64.cpsTripleWithin 2 ((base + preserveDividendSignOff) + 4)
        ((base + divisorSignOff) + 8) (smodCodeV4 base) midDivisor postFrame := by
    rw [hFall]
    exact hDivisor
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [mid, midDivisor, divisorFrame] at hp ⊢
      xperm_hyp hp) hPrefix hDivisor'
  have hPostPerm : ∀ h, postFrame h → post h := by
    intro h hp
    dsimp [postFrame, post] at hp ⊢
    xperm_hyp hp
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      simpa [pre, divisorFrame] using hp)
    hPostPerm
    (by
      simpa [pre, saveRaOff, dividendSign, divisorSign] using hSeq)

end EvmAsm.Evm64.SMod.Compose
