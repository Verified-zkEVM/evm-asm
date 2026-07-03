/-
  EvmAsm.Evm64.SMod.Compose.CodeHandles

  CodeReq handles for the SMOD wrapper and its sub-blocks.
-/

import EvmAsm.Evm64.SMod.LimbSpec
import EvmAsm.Evm64.SMod.AddrNorm
import EvmAsm.Evm64.SMod.Compose.BaseOffsets

namespace EvmAsm.Evm64.SMod.Compose

/-- Legacy verified SMOD code region handle: wrapper followed by `evm_mod_callable_v1`. -/
abbrev smodCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base EvmAsm.Evm64.evm_smod_legacy

/-- v4 full SMOD code region handle: the canonical production `evm_smod`
    body, which is the wrapper followed by `evm_mod_callable_v4`. -/
abbrev smodCodeV4 (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base EvmAsm.Evm64.evm_smod

/-- Canonical production SMOD code region handle.

    This is the non-legacy public handle for the current executable
    `evm_smod`, kept separate from `smodCode` while legacy v1 compatibility
    lemmas are still present. -/
abbrev smodCodeCanonical (base : Word) : EvmAsm.Rv64.CodeReq :=
  smodCodeV4 base

theorem smodCodeCanonical_eq_v4 {base : Word} :
    smodCodeCanonical base = smodCodeV4 base :=
  rfl

/-- Code handle for the saved-`ra` prologue block. -/
abbrev saveRaCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + saveRaOff) (EvmAsm.Evm64.evm_smod_save_ra_block .x18)

/-- Code handle for the dividend sign-bit probe. -/
abbrev dividendSignCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + dividendSignOff)
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_smodDividendTopLimbOff)

/-- Code handle for preserving the dividend sign across the nested MOD call. -/
abbrev preserveDividendSignCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + preserveDividendSignOff) (EvmAsm.Rv64.ADDI .x13 .x8 0)

/-- Code handle for the divisor sign-bit probe. -/
abbrev divisorSignCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + divisorSignOff)
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_smodDivisorTopLimbOff)

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

/-- Code handle for the near call into the legacy v1 MOD callable. -/
abbrev modCallCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + modCallOff)
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_smodCallOff)

/-- Code handle for the in-place remainder sign-fixup block. -/
abbrev resultSignFixCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + resultSignFixOff)
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x13 .x10 .x7 .x11
      0 8 16 24)

/-- Code handle for the saved-`ra` return instruction. -/
abbrev savedRaRetCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + savedRaRetOff)
    (EvmAsm.Evm64.evm_smod_saved_ra_ret_block .x18)

/-- Code handle for the appended legacy v1 unsigned modulo callable. -/
abbrev modCallableCode (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + wrapperEndOff) EvmAsm.Evm64.evm_mod_callable_v1

/-- Code handle for the appended v4 unsigned modulo callable. -/
abbrev modCallableCodeV4 (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + wrapperEndOff) EvmAsm.Evm64.evm_mod_callable_v4

/-- Code handle for the appended canonical production unsigned modulo callable. -/
abbrev modCallableCodeCanonical (base : Word) : EvmAsm.Rv64.CodeReq :=
  modCallableCodeV4 base

theorem modCallableCodeCanonical_eq_v4 {base : Word} :
    modCallableCodeCanonical base = modCallableCodeV4 base :=
  rfl

/-- v5 full SMOD code region handle: wrapper followed by `evm_mod_callable_v5`. -/
abbrev smodCodeV5 (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg base EvmAsm.Evm64.evm_smod_v5

/-- Code handle for the appended v5 unsigned modulo callable. -/
abbrev modCallableCodeV5 (base : Word) : EvmAsm.Rv64.CodeReq :=
  EvmAsm.Rv64.CodeReq.ofProg (base + wrapperEndOff) EvmAsm.Evm64.evm_mod_callable_v5

end EvmAsm.Evm64.SMod.Compose
