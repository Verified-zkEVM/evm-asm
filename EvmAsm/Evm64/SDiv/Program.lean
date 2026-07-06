/-
  EvmAsm.Evm64.SDiv.Program

  Signed division opcode SDIV (`SDIV(a, b)` = signed-quotient under EVM
  rules) as a 64-bit RISC-V program.

  Per `docs/sdiv-smod-design.md` the algorithm is

      1. extract sign of each operand (top bit of limb 3)
      2. conditionally two's-complement negate operands so both are
         non-negative; remember the sign-pair
      3. JAL to an `evm_div_callable_v4` shim (LP64) for unsigned division
      4. conditionally negate the quotient based on `sign(a) XOR sign(b)`.

  The `SDIV(-2^255, -1)` case follows this same bitvector path: the
  two's-complement "absolute value" of `-2^255` is the unsigned word
  `2^255`, division by `1` returns that word, and the equal signs skip
  the final negation.

  This file fixes the executable layout used by the later composition
  proof. The unsigned divider body is appended after the SDIV wrapper and
  reached by a near `JAL`, so it is present in code memory but not in the
  wrapper fall-through path.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.CallableV1Legacy

namespace EvmAsm.Evm64

/-- Load the top limb of a 256-bit word and extract its sign bit.

    On entry, `addrReg + topLimbOff` points at limb 3 of the word.
    On exit, `signReg` is `0` for non-negative inputs and `1` for
    negative inputs. The block is intentionally register-parametric so
    the SDIV and SMOD callers can reuse it for dividend/divisor sign
    probes before normalizing operands in place.

    2 instructions: `LD; SRLI 63`. -/
def evm_sdiv_sign_bit_block
    (addrReg signReg : EvmAsm.Rv64.Reg) (topLimbOff : BitVec 12) :
    EvmAsm.Rv64.Program :=
  EvmAsm.Rv64.LD signReg addrReg topLimbOff ;;
  EvmAsm.Rv64.SRLI signReg signReg 63

theorem evm_sdiv_sign_bit_block_length
    (addrReg signReg : EvmAsm.Rv64.Reg) (topLimbOff : BitVec 12) :
    (evm_sdiv_sign_bit_block addrReg signReg topLimbOff).length = 2 := by
  unfold evm_sdiv_sign_bit_block EvmAsm.Rv64.LD EvmAsm.Rv64.SRLI
    EvmAsm.Rv64.single EvmAsm.Rv64.seq EvmAsm.Rv64.Program
  rfl

theorem evm_sdiv_sign_bit_block_byte_length
    (addrReg signReg : EvmAsm.Rv64.Reg) (topLimbOff : BitVec 12) :
    4 * (evm_sdiv_sign_bit_block addrReg signReg topLimbOff).length = 8 := by
  rw [evm_sdiv_sign_bit_block_length]

/-- One limb of the conditional 256-bit negation loop.

    The caller has already materialized `maskReg = 0 - sign`. This step
    loads one limb, xors it with the mask, adds the incoming carry, stores
    the resulting carry in `carryReg`, and writes the limb back in place.
    Limb 0 passes the sign register as `carryInReg`; later limbs pass
    `carryReg` itself.

    5 instructions: `LD; XOR; ADD; SLTU; SD`. -/
def evm_sdiv_cond_negate_limb_step
    (addrReg carryInReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limbOff : BitVec 12) : EvmAsm.Rv64.Program :=
  EvmAsm.Rv64.LD valueReg addrReg limbOff ;;
  EvmAsm.Rv64.XOR' valueReg valueReg maskReg ;;
  EvmAsm.Rv64.ADD valueReg valueReg carryInReg ;;
  EvmAsm.Rv64.SLTU carryReg valueReg carryInReg ;;
  EvmAsm.Rv64.SD addrReg valueReg limbOff

theorem evm_sdiv_cond_negate_limb_step_length
    (addrReg carryInReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limbOff : BitVec 12) :
    (evm_sdiv_cond_negate_limb_step addrReg carryInReg maskReg valueReg carryReg
      limbOff).length = 5 := by
  unfold evm_sdiv_cond_negate_limb_step EvmAsm.Rv64.LD EvmAsm.Rv64.XOR'
    EvmAsm.Rv64.ADD EvmAsm.Rv64.SLTU EvmAsm.Rv64.SD EvmAsm.Rv64.single
    EvmAsm.Rv64.seq EvmAsm.Rv64.Program
  rfl

/-- Conditionally negate a 256-bit word in place.

    `signReg` must hold `0` or `1`. The block computes
    `maskReg := 0 - signReg`, xors all four limbs with that mask, and
    then adds the incoming carry (`signReg` for limb 0, propagated
    through `carryReg` for limbs 1..3). When `signReg = 0` this is the
    identity; when `signReg = 1` it is two's-complement negation.

    The limb offsets are parameters so callers can use the same block
    for the dividend, divisor, and quotient/result windows. The scratch
    registers `maskReg`, `valueReg`, and `carryReg` are clobbered.

    21 instructions: one `SUB` mask setup plus four 5-instruction limb
    steps (`LD; XOR; ADD; SLTU; SD`). -/
def evm_sdiv_cond_negate_256_block
    (addrReg signReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limb0Off limb1Off limb2Off limb3Off : BitVec 12) : EvmAsm.Rv64.Program :=
  EvmAsm.Rv64.SUB maskReg .x0 signReg ;;
  evm_sdiv_cond_negate_limb_step addrReg signReg maskReg valueReg carryReg limb0Off ;;
  evm_sdiv_cond_negate_limb_step addrReg carryReg maskReg valueReg carryReg limb1Off ;;
  evm_sdiv_cond_negate_limb_step addrReg carryReg maskReg valueReg carryReg limb2Off ;;
  evm_sdiv_cond_negate_limb_step addrReg carryReg maskReg valueReg carryReg limb3Off

theorem evm_sdiv_cond_negate_256_block_length
    (addrReg signReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limb0Off limb1Off limb2Off limb3Off : BitVec 12) :
    (evm_sdiv_cond_negate_256_block addrReg signReg maskReg valueReg carryReg
      limb0Off limb1Off limb2Off limb3Off).length = 21 := by
  unfold evm_sdiv_cond_negate_256_block evm_sdiv_cond_negate_limb_step
    EvmAsm.Rv64.SUB EvmAsm.Rv64.LD EvmAsm.Rv64.XOR' EvmAsm.Rv64.ADD
    EvmAsm.Rv64.SLTU EvmAsm.Rv64.SD EvmAsm.Rv64.single EvmAsm.Rv64.seq
    EvmAsm.Rv64.Program
  rfl

theorem evm_sdiv_cond_negate_256_block_byte_length
    (addrReg signReg maskReg valueReg carryReg : EvmAsm.Rv64.Reg)
    (limb0Off limb1Off limb2Off limb3Off : BitVec 12) :
    4 * (evm_sdiv_cond_negate_256_block addrReg signReg maskReg valueReg carryReg
      limb0Off limb1Off limb2Off limb3Off).length = 84 := by
  rw [evm_sdiv_cond_negate_256_block_length]

/-- Near-call block from SDIV into the unsigned `evm_div_callable_v4` body.
    The concrete signed 21-bit offset is pinned by the eventual top-level
    `evm_sdiv` layout. -/
def evm_sdiv_div_call_block (divOff : BitVec 21) : EvmAsm.Rv64.Program :=
  EvmAsm.Rv64.JAL .x1 divOff

theorem evm_sdiv_div_call_block_length (divOff : BitVec 21) :
    (evm_sdiv_div_call_block divOff).length = 1 := rfl

theorem evm_sdiv_div_call_block_byte_length (divOff : BitVec 21) :
    4 * (evm_sdiv_div_call_block divOff).length = 4 := by
  rw [evm_sdiv_div_call_block_length]

/-- Copy the current return address to a preserved scratch register. SDIV
    cannot use `cc_prologue` / `cc_epilogue` around `evm_div_callable`
    because the divider body owns `x2` as a scratch/link register. -/
def evm_sdiv_save_ra_block (savedRaReg : EvmAsm.Rv64.Reg) : EvmAsm.Rv64.Program :=
  EvmAsm.Rv64.ADDI savedRaReg .x1 0

theorem evm_sdiv_save_ra_block_length (savedRaReg : EvmAsm.Rv64.Reg) :
    (evm_sdiv_save_ra_block savedRaReg).length = 1 := rfl

theorem evm_sdiv_save_ra_block_byte_length (savedRaReg : EvmAsm.Rv64.Reg) :
    4 * (evm_sdiv_save_ra_block savedRaReg).length = 4 := by
  rw [evm_sdiv_save_ra_block_length]

/-- Return to the address saved before the nested DIV call. -/
def evm_sdiv_saved_ra_ret_block (savedRaReg : EvmAsm.Rv64.Reg) : EvmAsm.Rv64.Program :=
  EvmAsm.Rv64.JALR .x0 savedRaReg 0

theorem evm_sdiv_saved_ra_ret_block_length (savedRaReg : EvmAsm.Rv64.Reg) :
    (evm_sdiv_saved_ra_ret_block savedRaReg).length = 1 := rfl

theorem evm_sdiv_saved_ra_ret_block_byte_length (savedRaReg : EvmAsm.Rv64.Reg) :
    4 * (evm_sdiv_saved_ra_ret_block savedRaReg).length = 4 := by
  rw [evm_sdiv_saved_ra_ret_block_length]

def evm_sdivDividendTopLimbOff : BitVec 12 := 24
def evm_sdivDivisorTopLimbOff : BitVec 12 := 56
def evm_sdivCallOff : BitVec 21 := 92

/-- The executable SDIV wrapper, excluding the appended unsigned DIV callable.

    Register layout:
    * `x18` saves the caller return address across the nested `JAL`.
    * `x8` stores `sign(dividend)` and then `sign(dividend) XOR sign(divisor)`.
    * `x9` stores `sign(divisor)`.
    * `x10`, `x11`, and `x7` are scratch registers for conditional negation.

    Memory layout matches `evm_div_callable_v4`: dividend at `sp + 0..24`,
    divisor at `sp + 32..56`, quotient result at `sp + 32..56`. -/
def evm_sdiv_wrapper : EvmAsm.Rv64.Program :=
  evm_sdiv_save_ra_block .x18 ;;
  evm_sdiv_sign_bit_block .x12 .x8 evm_sdivDividendTopLimbOff ;;
  evm_sdiv_sign_bit_block .x12 .x9 evm_sdivDivisorTopLimbOff ;;
  evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11 0 8 16 24 ;;
  evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11 32 40 48 56 ;;
  EvmAsm.Rv64.XOR' .x8 .x8 .x9 ;;
  evm_sdiv_div_call_block evm_sdivCallOff ;;
  evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11 0 8 16 24 ;;
  evm_sdiv_saved_ra_ret_block .x18

theorem evm_sdiv_wrapper_length : evm_sdiv_wrapper.length = 71 := by
  decide

theorem evm_sdiv_wrapper_byte_length :
    4 * evm_sdiv_wrapper.length = 284 := by
  rw [evm_sdiv_wrapper_length]

theorem evm_sdiv_call_target_byte_offset :
    4 *
      ((evm_sdiv_save_ra_block .x18).length +
       (evm_sdiv_sign_bit_block .x12 .x8 evm_sdivDividendTopLimbOff).length +
       (evm_sdiv_sign_bit_block .x12 .x9 evm_sdivDivisorTopLimbOff).length +
       (evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11 0 8 16 24).length +
       (evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11 32 40 48 56).length +
       (EvmAsm.Rv64.XOR' .x8 .x8 .x9).length) +
      EvmAsm.Rv64.signExtend21 evm_sdivCallOff =
    4 * evm_sdiv_wrapper.length := by
  decide

/-- Legacy verified SDIV code region. The wrapper returns via `x18`; the
    appended `evm_div_callable` block is reached only by the wrapper's near
    call. Existing `sdivCode` composition proofs still target this surface
    until the dispatcher proofs are lifted to the v4 no-NOP code surface. -/
def evm_sdiv_legacy : EvmAsm.Rv64.Program :=
  evm_sdiv_wrapper ;; evm_div_callable_v1

theorem evm_sdiv_legacy_length : evm_sdiv_legacy.length = 390 := by
  have h_v1 : evm_div_callable_v1.length = 319 := by
    simp only [evm_div_callable_v1, EvmAsm.Rv64.seq, EvmAsm.Rv64.Program.length_append,
      divK_phaseA_len,
      divK_phaseB_len, divK_clz_len, divK_phaseC2_len, divK_normB_len, divK_normA_len,
      divK_copyAU_len, divK_loopSetup_len, divK_loopBody_len, divK_denorm_len,
      divK_divEpilogue_len, divK_zeroPath_len, cc_ret_len, divK_div128_len]
  simp only [evm_sdiv_legacy, EvmAsm.Rv64.seq, EvmAsm.Rv64.Program.length_append,
    evm_sdiv_wrapper_length, h_v1]

theorem evm_sdiv_legacy_byte_length : 4 * evm_sdiv_legacy.length = 1560 := by
  rw [evm_sdiv_legacy_length]

/-- Full SDIV code region, using the corrected v4 unsigned DIV callable. -/
def evm_sdiv : EvmAsm.Rv64.Program :=
  evm_sdiv_wrapper ;; evm_div_callable_v4

/-- v4 full SDIV code region. Kept as an explicit alias while downstream
    scripts and proofs finish migrating to the canonical `evm_sdiv` name. -/
def evm_sdiv_v4 : EvmAsm.Rv64.Program :=
  evm_sdiv_wrapper ;; evm_div_callable_v4

/-- Regression pin: canonical executable SDIV is now the v4 body. -/
theorem evm_sdiv_eq_v4 : evm_sdiv = evm_sdiv_v4 := rfl

/-- Regression pin: the executable v4 SDIV body uses the corrected v4
    callable divider. -/
theorem evm_sdiv_v4_uses_div_callable_v4 :
    evm_sdiv_v4 = (evm_sdiv_wrapper ;; evm_div_callable_v4) := rfl

/-- Full SDIV code region, using the v5 unsigned DIV callable. -/
def evm_sdiv_v5 : EvmAsm.Rv64.Program :=
  evm_sdiv_wrapper ;; evm_div_callable_v5

theorem evm_sdiv_v5_uses_div_callable_v5 :
    evm_sdiv_v5 = (evm_sdiv_wrapper ;; evm_div_callable_v5) := rfl

theorem evm_sdiv_length : evm_sdiv.length = 414 := by
  simp only [evm_sdiv, EvmAsm.Rv64.seq, EvmAsm.Rv64.Program.length_append,
    evm_sdiv_wrapper_length, evm_div_callable_v4_length]

theorem evm_sdiv_v4_length : evm_sdiv_v4.length = 414 := by
  simp only [evm_sdiv_v4, EvmAsm.Rv64.seq, EvmAsm.Rv64.Program.length_append,
    evm_sdiv_wrapper_length, evm_div_callable_v4_length]

theorem evm_sdiv_byte_length : 4 * evm_sdiv.length = 1656 := by
  rw [evm_sdiv_length]

theorem evm_sdiv_v4_byte_length : 4 * evm_sdiv_v4.length = 1656 := by
  rw [evm_sdiv_v4_length]

theorem evm_sdiv_v5_length : evm_sdiv_v5.length = 424 := by
  simp only [evm_sdiv_v5, EvmAsm.Rv64.seq, EvmAsm.Rv64.Program.length_append,
    evm_sdiv_wrapper_length, evm_div_callable_v5_length]

theorem evm_sdiv_v5_byte_length : 4 * evm_sdiv_v5.length = 1696 := by
  rw [evm_sdiv_v5_length]

example :
    (evm_sdiv_sign_bit_block .x12 .x5 24).length +
      (evm_sdiv_cond_negate_256_block .x12 .x5 .x6 .x7 .x11 0 8 16 24).length +
      (evm_sdiv_div_call_block 0).length = 24 := by
  decide

end EvmAsm.Evm64
