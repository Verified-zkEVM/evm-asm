/-
  EvmAsm.Evm64.SDiv.Compose.DispatchStackViews

  Stack-entry folding lemmas for the SDIV div-call dispatch composition.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallPreView
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
/-- Entry assertion view for stack-level SDIV callers: when the raw limb
    parameters are instantiated from two EVM words, the operand memory atoms
    in `saveRaSignsAbsSignXorThenDivCallPre` fold into a two-word stack. -/
theorem saveRaSignsAbsSignXorThenDivCallPre_stack_pair
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord) :
    saveRaSignsAbsSignXorThenDivCallPre
        vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) =
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
        (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
        (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
       evmStackIs sp [dividend, divisor]) := by
  rw [saveRaSignsAbsSignXorThenDivCallPre_unfold, evmStackIs_pair]
  rw [evmWordIs_sp_unfold, evmWordIs_sp32_unfold]
  unfold EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  unfold EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  simp only [EvmAsm.Rv64.signExtend12_0, EvmAsm.Rv64.signExtend12_8,
    EvmAsm.Rv64.signExtend12_16, EvmAsm.Rv64.signExtend12_24,
    EvmAsm.Rv64.signExtend12_32, EvmAsm.Rv64.signExtend12_40,
    EvmAsm.Rv64.signExtend12_48, EvmAsm.Rv64.signExtend12_56]
  rw [show (sp + 0 : Word) = sp by bv_omega]
  xperm

/-- Tail-stack companion to `saveRaSignsAbsSignXorThenDivCallPre_stack_pair`:
    folds the two SDIV operands together with the untouched stack tail. -/
theorem saveRaSignsAbsSignXorThenDivCallPre_stack_pair_rest
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    (saveRaSignsAbsSignXorThenDivCallPre
        vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) **
      evmStackIs (sp + 64) rest) =
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
        (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
        (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
       evmStackIs sp (dividend :: divisor :: rest)) := by
  rw [saveRaSignsAbsSignXorThenDivCallPre_stack_pair]
  have h_stack :
      evmStackIs sp (dividend :: divisor :: rest) =
        (evmStackIs sp [dividend, divisor] ** evmStackIs (sp + 64) rest) := by
    change evmStackIs sp ([dividend, divisor] ++ rest) =
      (evmStackIs sp [dividend, divisor] ** evmStackIs (sp + 64) rest)
    rw [evmStackIs_append sp [dividend, divisor] rest]
    rfl
  rw [h_stack]
  rw [EvmAsm.Rv64.sepConj_assoc']

end EvmAsm.Evm64.SDiv.Compose
