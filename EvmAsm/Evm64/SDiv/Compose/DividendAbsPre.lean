/-
  EvmAsm.Evm64.SDiv.Compose.DividendAbsPre

  Irreducible precondition for the SDIV dividend absolute-value block.
-/

import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64.SDiv.Compose

/-- Precondition for the SDIV dividend-abs (conditional 2's-complement
    negation) block. Wraps the register/memory entry shape as an
    `@[irreducible]` def so downstream proofs do not re-unfold the
    sepConj atoms at each use site. -/
@[irreducible]
def dividendAbsPre (sp sign maskOld valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
  (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
  ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
  ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
  ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
  ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)

theorem dividendAbsPre_unfold
    {sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    dividendAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
       ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
       ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
       ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) := by
  delta dividendAbsPre
  rfl

end EvmAsm.Evm64.SDiv.Compose
