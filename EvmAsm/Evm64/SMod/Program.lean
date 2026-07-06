/-
  EvmAsm.Evm64.SMod.Program

  Signed remainder opcode SMOD (`SMOD(a, b)` = signed-remainder under EVM
  rules) as a 64-bit RISC-V program.

  Per `docs/sdiv-smod-design.md` the algorithm is

      1. extract sign of each operand (top bit of limb 3)
      2. conditionally two's-complement negate operands so both are
         non-negative; remember `sign(a)`
      3. JAL to an `evm_mod_callable_v4` shim (LP64) for unsigned modulo
      4. conditionally negate the remainder based on `sign(a)`
         (EVM SMOD takes the sign of the dividend)

  This file fixes the executable layout used by the later composition
  proof. The unsigned modulo body is appended after the SMOD wrapper and
  reached by a near `JAL`, so it is present in code memory but not in the
  wrapper fall-through path.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.CallableV1Legacy

namespace EvmAsm.Evm64

open EvmAsm.Rv64

def evm_smodDividendTopLimbOff : BitVec 12 := 24
def evm_smodDivisorTopLimbOff : BitVec 12 := 56
def evm_smodCallOff : BitVec 21 := 92

/-- Copy the current return address to a preserved scratch register. -/
def evm_smod_save_ra_block (savedRaReg : Reg) : Program :=
  ADDI savedRaReg .x1 0

theorem evm_smod_save_ra_block_length (savedRaReg : Reg) :
    (evm_smod_save_ra_block savedRaReg).length = 1 := rfl

theorem evm_smod_save_ra_block_byte_length (savedRaReg : Reg) :
    4 * (evm_smod_save_ra_block savedRaReg).length = 4 := by
  rw [evm_smod_save_ra_block_length]

/-- Return to the address saved before the nested MOD call. -/
def evm_smod_saved_ra_ret_block (savedRaReg : Reg) : Program :=
  JALR .x0 savedRaReg 0

theorem evm_smod_saved_ra_ret_block_length (savedRaReg : Reg) :
    (evm_smod_saved_ra_ret_block savedRaReg).length = 1 := rfl

theorem evm_smod_saved_ra_ret_block_byte_length (savedRaReg : Reg) :
    4 * (evm_smod_saved_ra_ret_block savedRaReg).length = 4 := by
  rw [evm_smod_saved_ra_ret_block_length]

/-- The executable SMOD wrapper, excluding the appended unsigned MOD callable.

    Register layout:
    * `x18` saves the caller return address across the nested `JAL`.
    * `x8` stores `sign(dividend)` and drives the final remainder correction.
    * `x13` preserves `sign(dividend)` across the nested MOD callable.
    * `x9` stores `sign(divisor)` only for absolute-value normalization.
    * `x10`, `x11`, and `x7` are scratch registers for conditional negation.

    Memory layout matches `evm_mod_callable_v4`: dividend at `sp + 0..24`,
    divisor at `sp + 32..56`, remainder result at `sp + 32..56`. -/
def evm_smod_wrapper : Program :=
  evm_smod_save_ra_block .x18 ;;
  evm_sdiv_sign_bit_block .x12 .x8 evm_smodDividendTopLimbOff ;;
  ADDI .x13 .x8 0 ;;
  evm_sdiv_sign_bit_block .x12 .x9 evm_smodDivisorTopLimbOff ;;
  evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11 0 8 16 24 ;;
  evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11 32 40 48 56 ;;
  evm_sdiv_div_call_block evm_smodCallOff ;;
  evm_sdiv_cond_negate_256_block .x12 .x13 .x10 .x7 .x11 0 8 16 24 ;;
  evm_smod_saved_ra_ret_block .x18

theorem evm_smod_wrapper_length : evm_smod_wrapper.length = 71 := by
  decide

theorem evm_smod_wrapper_byte_length :
    4 * evm_smod_wrapper.length = 284 := by
  rw [evm_smod_wrapper_length]

theorem evm_smod_call_target_byte_offset :
    4 *
      ((evm_smod_save_ra_block .x18).length +
       (evm_sdiv_sign_bit_block .x12 .x8 evm_smodDividendTopLimbOff).length +
       (ADDI .x13 .x8 0).length +
       (evm_sdiv_sign_bit_block .x12 .x9 evm_smodDivisorTopLimbOff).length +
       (evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11 0 8 16 24).length +
       (evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11 32 40 48 56).length) +
      signExtend21 evm_smodCallOff =
    4 * evm_smod_wrapper.length := by
  decide

/-- Legacy SMOD code region. The wrapper returns via `x18`; the appended
    `evm_mod_callable_v1` block is reached only by the wrapper's near call. -/
def evm_smod_legacy : Program :=
  evm_smod_wrapper ;; evm_mod_callable_v1

/-- Full SMOD code region, using the corrected v4 unsigned MOD callable. -/
def evm_smod : Program :=
  evm_smod_wrapper ;; evm_mod_callable_v4

/-- v4 full SMOD code region. Kept as an explicit alias while downstream
    scripts and proofs finish migrating to the canonical `evm_smod` name. -/
def evm_smod_v4 : Program :=
  evm_smod_wrapper ;; evm_mod_callable_v4

/-- Full SMOD code region, using the v5 unsigned MOD callable. -/
def evm_smod_v5 : Program :=
  evm_smod_wrapper ;; evm_mod_callable_v5

/-- Regression pin: canonical executable SMOD is now the v4 body. -/
theorem evm_smod_eq_v4 : evm_smod = evm_smod_v4 := rfl

theorem evm_smod_legacy_length : evm_smod_legacy.length = 390 := by
  have h_v1 : evm_mod_callable_v1.length = 319 := by
    simp only [evm_mod_callable_v1, EvmAsm.Rv64.seq, EvmAsm.Rv64.Program.length_append,
      divK_phaseA_len,
      divK_phaseB_len, divK_clz_len, divK_phaseC2_len, divK_normB_len, divK_normA_len,
      divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len, divK_denorm_len,
      divK_modEpilogue_len, divK_zeroPath_len, cc_ret_len, divK_div128_len]
  simp only [evm_smod_legacy, EvmAsm.Rv64.seq, EvmAsm.Rv64.Program.length_append,
    evm_smod_wrapper_length, h_v1]

theorem evm_smod_length : evm_smod.length = 414 := by
  simp only [evm_smod, EvmAsm.Rv64.seq, EvmAsm.Rv64.Program.length_append,
    evm_smod_wrapper_length, evm_mod_callable_v4_length]

theorem evm_smod_v4_length : evm_smod_v4.length = 414 := by
  simp only [evm_smod_v4, EvmAsm.Rv64.seq, EvmAsm.Rv64.Program.length_append,
    evm_smod_wrapper_length, evm_mod_callable_v4_length]

theorem evm_smod_v5_length : evm_smod_v5.length = 424 := by
  simp only [evm_smod_v5, EvmAsm.Rv64.seq, EvmAsm.Rv64.Program.length_append,
    evm_smod_wrapper_length, evm_mod_callable_v5_length]

theorem evm_smod_legacy_byte_length : 4 * evm_smod_legacy.length = 1560 := by
  rw [evm_smod_legacy_length]

theorem evm_smod_byte_length : 4 * evm_smod.length = 1656 := by
  rw [evm_smod_length]

theorem evm_smod_v4_byte_length : 4 * evm_smod_v4.length = 1656 := by
  rw [evm_smod_v4_length]

theorem evm_smod_v5_byte_length : 4 * evm_smod_v5.length = 1696 := by
  rw [evm_smod_v5_length]

end EvmAsm.Evm64
