/-
  EvmAsm.Evm64.SDiv.Compose.DivisorAbsPre

  Irreducible precondition for the SDIV prefix through divisor absolute value.
-/

module

public import EvmAsm.Evm64.SDiv.Program
public import EvmAsm.Rv64.SepLogic

@[expose] public section

namespace EvmAsm.Evm64.SDiv.Compose

/-- Precondition for the SDIV save-ra/signs/dividendAbs/divisorAbs block
    (entry to the wrapper, just after the saved-`ra` slot is materialized
    in `x1`). Takes only the bare wrapper inputs; the `sp`-relative
    dividend/divisor memory addresses are computed internally so the
    huge let-chain that previously lived in the theorem signature stays
    hidden inside this `@[irreducible]` def. -/
@[irreducible]
def saveRaSignsAbsThenDivisorAbsPre
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
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

theorem saveRaSignsAbsThenDivisorAbsPre_unfold
    {vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaSignsAbsThenDivisorAbsPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
       let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
       let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
       let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
       let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
       let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
       let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
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
         (divisorMem2 ↦ₘ divisorLimb2)))) := by
  delta saveRaSignsAbsThenDivisorAbsPre
  rfl

end EvmAsm.Evm64.SDiv.Compose
