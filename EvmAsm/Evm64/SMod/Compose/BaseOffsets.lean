/-
  EvmAsm.Evm64.SMod.Compose.BaseOffsets

  Shared byte offsets for the concrete SMOD wrapper layout.
-/

namespace EvmAsm.Evm64.SMod.Compose

/-- Byte offset of the saved-`ra` prologue inside `evm_smod_wrapper`. -/
def saveRaOff : Nat := 0

/-- Byte offset of the dividend sign probe inside `evm_smod_wrapper`. -/
def dividendSignOff : Nat := 4

/-- Byte offset of the dividend-sign preservation instruction. -/
def preserveDividendSignOff : Nat := 12

/-- Byte offset of the divisor sign probe inside `evm_smod_wrapper`. -/
def divisorSignOff : Nat := 16

/-- Byte offset of the in-place dividend absolute-value block. -/
def dividendAbsOff : Nat := 24

/-- Byte offset of the in-place divisor absolute-value block. -/
def divisorAbsOff : Nat := 108

/-- Byte offset of the near call into `evm_mod_callable`. -/
def modCallOff : Nat := 192

/-- Byte offset of the in-place remainder sign-fixup block. -/
def resultSignFixOff : Nat := 196

/-- Byte offset of the saved-`ra` return instruction. -/
def savedRaRetOff : Nat := 280

/-- Byte offset at the end of the SMOD wrapper. The appended unsigned
    modulo callable starts here. -/
def wrapperEndOff : Nat := 284

/-- Bundled byte offsets for the concrete SMOD wrapper layout. -/
theorem smod_wrapper_block_byte_offsets :
    saveRaOff = 0 ∧
    dividendSignOff = 4 ∧
    preserveDividendSignOff = 12 ∧
    divisorSignOff = 16 ∧
    dividendAbsOff = 24 ∧
    divisorAbsOff = 108 ∧
    modCallOff = 192 ∧
    resultSignFixOff = 196 ∧
    savedRaRetOff = 280 ∧
    wrapperEndOff = 284 := by
  unfold saveRaOff dividendSignOff preserveDividendSignOff divisorSignOff dividendAbsOff
    divisorAbsOff modCallOff resultSignFixOff savedRaRetOff wrapperEndOff
  decide

/-- Successive fall-through byte offsets for the concrete SMOD wrapper. -/
theorem smod_wrapper_fallthrough_offsets :
    saveRaOff + 4 = dividendSignOff ∧
    dividendSignOff + 8 = preserveDividendSignOff ∧
    preserveDividendSignOff + 4 = divisorSignOff ∧
    divisorSignOff + 8 = dividendAbsOff ∧
    dividendAbsOff + 84 = divisorAbsOff ∧
    divisorAbsOff + 84 = modCallOff ∧
    modCallOff + 4 = resultSignFixOff ∧
    resultSignFixOff + 84 = savedRaRetOff ∧
    savedRaRetOff + 4 = wrapperEndOff := by
  unfold saveRaOff dividendSignOff preserveDividendSignOff divisorSignOff dividendAbsOff
    divisorAbsOff modCallOff resultSignFixOff savedRaRetOff wrapperEndOff
  decide

end EvmAsm.Evm64.SMod.Compose
