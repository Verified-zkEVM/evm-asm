/-
  EvmAsm.Evm64.SDiv.Compose.BaseResultSignFix

  SDIV wrapper base spec for the result sign-fixup block.
-/

module

public import EvmAsm.Rv64.SepLogic

@[expose] public section

namespace EvmAsm.Evm64.SDiv.Compose

/-- Precondition for the SDIV result sign-fixup (conditional 2's-complement
    negation) block. The unsigned DIV callable returns with `x12` advanced
    to the quotient cell, so this block operates on offsets `0…24` from the
    live stack pointer. Wrapped `@[irreducible]` so downstream proofs do not
    re-unfold the sepConj atoms at each use site. -/
@[irreducible]
def resultSignFixPre (sp sign maskOld valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
  (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
  ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
  ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
  ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
  ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)

theorem resultSignFixPre_unfold
    {sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    resultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
       ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
       ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
       ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) := by
  delta resultSignFixPre
  rfl

/-- Postcondition for the SDIV result sign-fixup block: mirrors
    `divisorAbsPost` but with the sign register `x8`. Wrapped
    `@[irreducible]` to hide the let chain from downstream proofs. -/
@[irreducible]
def resultSignFixPost (sp sign limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
  (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
  ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
  ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
  ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
  ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ sum3)

theorem resultSignFixPost_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    resultSignFixPost sp sign limb0 limb1 limb2 limb3 =
      (let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (limb3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
       ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
       ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
       ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ sum3)) := by
  delta resultSignFixPost
  rfl

end EvmAsm.Evm64.SDiv.Compose
