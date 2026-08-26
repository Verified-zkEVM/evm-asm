/-
  EvmAsm.Evm64.SMod.Compose.PreserveDividendSignSequence

  SMOD wrapper composition from the saved-`ra` prologue through preserving
  the dividend sign in `x13`.
-/

module

public import EvmAsm.Evm64.SMod.Compose.SaveRaSignSequence
public import EvmAsm.Evm64.SMod.Compose.PreserveDividendSign

@[expose] public section

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_dividendSign_then_preserve_spec_in_smodCodeV4
    (vRa vSavedOld sp sOld x13Old dividendTop : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 4 base ((base + preserveDividendSignOff) + 4)
      (smodCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
         ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       (.x13 ↦ᵣ x13Old))
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       (((.x1 ↦ᵣ vRa) **
        (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x12 ↦ᵣ sp) **
        (.x8 ↦ᵣ dividendSign) **
        ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
          dividendTop))) **
       (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let pre : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     (.x13 ↦ᵣ x13Old))
  let mid : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      (.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ x13Old))
  let midPreserve : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     ((.x8 ↦ᵣ dividendSign) ** (.x13 ↦ᵣ x13Old)))
  let post : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      (.x8 ↦ᵣ dividendSign) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))
  let postFrame : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
     ((.x12 ↦ᵣ sp) **
      ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
        dividendTop))) **
     ((.x8 ↦ᵣ dividendSign) **
      (.x13 ↦ᵣ (dividendSign + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 3 base
      ((base + dividendSignOff) + 8) (smodCodeV4 base) pre mid := by
    dsimp [pre, mid]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameR
        (.x13 ↦ᵣ x13Old)
        (by pcFree)
        (saveRa_then_dividendSign_spec_in_smodCodeV4
          vRa vSavedOld sp sOld dividendTop base)
  have hPreserve : EvmAsm.Rv64.cpsTripleWithin 1
      (base + preserveDividendSignOff) ((base + preserveDividendSignOff) + 4)
      (smodCodeV4 base) midPreserve postFrame := by
    dsimp [midPreserve, postFrame]
    exact
      EvmAsm.Rv64.cpsTripleWithin_frameL
        (((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((.x12 ↦ᵣ sp) **
          ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
            dividendTop)))
        (by pcFree)
        (preserveDividendSign_spec_in_smodCodeV4 dividendSign x13Old base)
  have hFall :
      (base + dividendSignOff) + 8 = base + preserveDividendSignOff := by
    simp [dividendSignOff, preserveDividendSignOff]
    bv_addr
  have hPreserve' :
      EvmAsm.Rv64.cpsTripleWithin 1 ((base + dividendSignOff) + 8)
        ((base + preserveDividendSignOff) + 4) (smodCodeV4 base) midPreserve postFrame := by
    rw [hFall]
    exact hPreserve
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp [mid, midPreserve] at hp ⊢
      xperm_hyp hp) hPrefix hPreserve'
  have hPostPerm : ∀ h, postFrame h → post h := by
    intro h hp
    dsimp [postFrame, post] at hp ⊢
    xperm_hyp hp
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      simpa [pre] using hp)
    hPostPerm
    (by
      simpa [pre, saveRaOff, dividendSign] using hSeq)

end EvmAsm.Evm64.SMod.Compose
