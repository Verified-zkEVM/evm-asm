/-
  EvmAsm.Evm64.SDiv.Compose.CodeHandles

  CodeReq handles for the SDIV wrapper and its sub-blocks.
-/

import EvmAsm.Evm64.SDiv.LimbSpec
import EvmAsm.Evm64.SDiv.AddrNorm
import EvmAsm.Evm64.SDiv.Compose.BaseOffsets

namespace EvmAsm.Evm64.SDiv.Compose

/-- v4 full SDIV code region handle: wrapper followed by `evm_div_callable_v4`. -/
abbrev sdivCodeV4 (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base EvmAsm.Evm64.evm_sdiv_v4

/-- v5 full SDIV code region handle: wrapper followed by `evm_div_callable_v5`. -/
abbrev sdivCodeV5 (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base EvmAsm.Evm64.evm_sdiv_v5

/-- Code handle for the saved-`ra` prologue block. -/
abbrev saveRaCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + saveRaOff) (EvmAsm.Evm64.evm_sdiv_save_ra_block .x18)

/-- Code handle for the dividend sign-bit probe. -/
abbrev dividendSignCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + dividendSignOff)
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff)

/-- Code handle for the divisor sign-bit probe. -/
abbrev divisorSignCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + divisorSignOff)
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff)

/-- Code handle for the in-place dividend absolute-value block. -/
abbrev dividendAbsCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + dividendAbsOff)
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24)

/-- Code handle for the in-place divisor absolute-value block. -/
abbrev divisorAbsCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + divisorAbsOff)
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56)

/-- Code handle for the sign-xor instruction selecting result negation. -/
abbrev signXorCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + signXorOff) (EvmAsm.Rv64.XOR' .x8 .x8 .x9)

/-- Code handle for the near call into the legacy v1 DIV callable. -/
abbrev divCallCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + divCallOff)
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_sdivCallOff)

/-- Code handle for the in-place quotient sign-fixup block. -/
abbrev resultSignFixCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + resultSignFixOff)
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24)

/-- Code handle for the saved-`ra` return instruction. -/
abbrev savedRaRetCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + savedRaRetOff)
    (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block .x18)

/-- Code handle for the appended legacy v1 unsigned divider callable. -/
abbrev divCallableCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + wrapperEndOff) EvmAsm.Evm64.evm_div_callable_v1

/-- Code handle for the appended v4 unsigned divider callable. -/
abbrev divCallableCodeV4 (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + wrapperEndOff) EvmAsm.Evm64.evm_div_callable_v4

/-- Code handle for the appended v5 unsigned divider callable. -/
abbrev divCallableCodeV5 (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + wrapperEndOff) EvmAsm.Evm64.evm_div_callable_v5

end EvmAsm.Evm64.SDiv.Compose
