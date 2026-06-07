/-
  EvmAsm.Codegen.Programs.HeaderBaseFee

  EIP-1559 base-fee math + the full-validate composite carved
  out of `EvmAsm.Codegen.Programs.Header` per the file-size hard
  cap. Hosts:

    K73  eip1559_calc_base_fee_per_gas
    K74  header_validate_base_fee
    K75  validate_header_full

  K75 is the per-header semantic+structural validator: composes
  K43 `validate_header_basic`, K67 `header_validate_post_merge`,
  K68 `header_validate_extra_data_length`, K72 `check_gas_limit`,
  K74 `header_validate_base_fee`, and the Amsterdam excess-blob-gas
  recurrence. K43/K67/K68/K72 remain in `Programs/Header.lean`;
  `HeaderBaseFee.lean` imports `Header.lean` plus the u256 + RLP helpers.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Header

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## eip1559_calc_base_fee_per_gas -- PR-K73

    Full EIP-1559 base-fee formula. Mirrors Python's
    `calculate_base_fee_per_gas`:

      parent_gas_target = parent.gas_limit // 2

      if parent.gas_used == parent_gas_target:
          expected = parent.base_fee_per_gas
      elif parent.gas_used > parent_gas_target:
          gas_used_delta = parent.gas_used - parent_gas_target
          parent_fee_gas_delta = parent.base_fee_per_gas * gas_used_delta
          target_fee_gas_delta = parent_fee_gas_delta // parent_gas_target
          base_fee_delta = max(target_fee_gas_delta // 8, 1)
          expected = parent.base_fee_per_gas + base_fee_delta
      else:
          gas_used_delta = parent_gas_target - parent.gas_used
          parent_fee_gas_delta = parent.base_fee_per_gas * gas_used_delta
          target_fee_gas_delta = parent_fee_gas_delta // parent_gas_target
          base_fee_delta = target_fee_gas_delta // 8
          expected = parent.base_fee_per_gas - base_fee_delta

    Where `ELASTICITY_MULTIPLIER = 2` and
    `BASE_FEE_MAX_CHANGE_DENOMINATOR = 8`.

    First end-to-end EIP-1559 helper composed on the u256 toolkit:
    - PR-K54 `u256_mul_u64_be` — parent.base_fee × gas_used_delta
    - PR-K61 `u256_div_u64_be` — divide by parent_gas_target, then by 8
    - PR-K58 `u256_is_zero`    — max(_, 1) on the above path
    - PR-K56 `u256_from_u64_be` — materialize the literal 1
    - PR-K51 `u256_add_be`     — final add (above path)
    - PR-K52 `u256_sub_be`     — final sub (below path)

    ## Preconditions

    - `parent.gas_limit >= 2` (so `parent_gas_target >= 1`; we
      divide by it). Mainnet has GAS_LIMIT_MINIMUM = 5000, so
      this always holds for valid chains.
    - `parent.base_fee_per_gas <= 2^56` (PR-K61 div precondition).
      All mainnet base fees fit easily.

    Calling convention:
      a0 (input)  : parent.gas_limit       (u64)
      a1 (input)  : parent.gas_used        (u64)
      a2 (input)  : parent.base_fee_per_gas ptr (u256 BE, 32 B)
      a3 (input)  : output ptr (u256 BE, 32 B; receives expected
                    base_fee_per_gas)
      ra (input)  : return
      a0 (output) : 0 on success, 1 on overflow at any step. -/
def eip1559CalcBaseFeePerGasFunction : String :=
  "eip1559_calc_base_fee_per_gas:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a2                    # base_fee ptr\n" ++
  "  mv s1, a3                    # out ptr\n" ++
  "  srli s2, a0, 1               # parent_gas_target = parent.gas_limit / 2\n" ++
  "  beq a1, s2, .Lebf_eq         # gas_used == target → expected = base_fee\n" ++
  "  li s4, 0                     # path flag: 0 = below, 1 = above\n" ++
  "  bgtu a1, s2, .Lebf_set_above\n" ++
  "  beqz a1, .Lebf_below_zero_used\n" ++
  "  sub s3, s2, a1               # below: delta = target - gas_used\n" ++
  "  j .Lebf_compute\n" ++
  ".Lebf_set_above:\n" ++
  "  li s4, 1\n" ++
  "  sub s3, a1, s2               # above: delta = gas_used - target\n" ++
  ".Lebf_compute:\n" ++
  "  # parent_fee_gas_delta = parent.base_fee × gas_used_delta\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s3\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lebf_fail\n" ++
  "  # target_fee_gas_delta = parent_fee_gas_delta / parent_gas_target\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_div_u64_be\n" ++
  "  # base_fee_delta = target_fee_gas_delta / 8\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 8\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_div_u64_be\n" ++
  "  # If above path: max(delta, 1).\n" ++
  "  beqz s4, .Lebf_apply\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, u256_is_zero\n" ++
  "  beqz a0, .Lebf_apply\n" ++
  "  li a0, 1\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, u256_from_u64_be\n" ++
  "  j .Lebf_apply\n" ++
  ".Lebf_below_zero_used:\n" ++
  "  # When parent_gas_used = 0, gas_used_delta = target, so\n" ++
  "  # (base_fee * target) / target = base_fee exactly. Avoid the large\n" ++
  "  # intermediate product for very high test gas limits.\n" ++
  "  mv a0, s0\n" ++
  "  li a1, 8\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_div_u64_be\n" ++
  ".Lebf_apply:\n" ++
  "  beqz s4, .Lebf_sub_path\n" ++
  "  # above: out = base_fee + delta\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lebf_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lebf_ret\n" ++
  ".Lebf_sub_path:\n" ++
  "  # below: out = base_fee - delta\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  bnez a0, .Lebf_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lebf_ret\n" ++
  ".Lebf_eq:\n" ++
  "  # Copy base_fee to out (32 B chunk copy).\n" ++
  "  ld t0,  0(s0); sd t0,  0(s1)\n" ++
  "  ld t0,  8(s0); sd t0,  8(s1)\n" ++
  "  ld t0, 16(s0); sd t0, 16(s1)\n" ++
  "  ld t0, 24(s0); sd t0, 24(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lebf_ret\n" ++
  ".Lebf_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lebf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_eip1559_calc_base_fee_per_gas`: probe BuildUnit. Reads
    (parent_gas_limit u64, parent_gas_used u64, parent_base_fee
    u256 BE) from host input, writes (status, expected_base_fee
    BE) to OUTPUT (40 bytes total). -/
def ziskEip1559CalcBaseFeePerGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a0,  8(a4)               # parent.gas_limit\n" ++
  "  ld a1, 16(a4)               # parent.gas_used\n" ++
  "  addi a2, a4, 24             # parent.base_fee ptr\n" ++
  "  li a3, 0xa0010008           # out ptr\n" ++
  "  mv t0, a3; li t1, 4\n" ++
  ".Lebf_zout:\n" ++
  "  beqz t1, .Lebf_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lebf_zout\n" ++
  ".Lebf_zout_done:\n" ++
  "  jal ra, eip1559_calc_base_fee_per_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lebf_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  ".Lebf_pdone:"

def ziskEip1559CalcBaseFeePerGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40"

def ziskEip1559CalcBaseFeePerGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip1559CalcBaseFeePerGasPrologue
  dataAsm     := ziskEip1559CalcBaseFeePerGasDataSection
}

/-! ## header_validate_base_fee -- PR-K74

    Verify a header's `base_fee_per_gas` matches the value
    computed from the parent header by EIP-1559's
    `calculate_base_fee_per_gas`:

      expected = eip1559_calc_base_fee_per_gas(
                   parent.gas_limit,
                   parent.gas_used,
                   parent.base_fee_per_gas)
      assert header.base_fee_per_gas == expected

    This is the per-block invariant added by EIP-1559 §4.4.4
    (Python: `validate_header`).

    Composes PR-K73 `eip1559_calc_base_fee_per_gas` +
    PR-K53 `u256_eq`. The 32-byte computed expected base fee
    lands in `.data` scratch, then is compared bytewise against
    the header's claimed value.

    Calling convention:
      a0 (input)  : header.base_fee_per_gas ptr (u256 BE, 32 B)
      a1 (input)  : parent.gas_limit (u64)
      a2 (input)  : parent.gas_used (u64)
      a3 (input)  : parent.base_fee_per_gas ptr (u256 BE, 32 B)
      ra (input)  : return
      a0 (output) :
        0  : header.base_fee_per_gas == expected
        1  : mismatch (reject)
        2  : compute step (K73) overflow / precondition failure

    Uses 32 bytes of `.data` scratch (`hvbf_expected`). -/
def headerValidateBaseFeeFunction : String :=
  "header_validate_base_fee:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a0                   # save header.base_fee ptr\n" ++
  "  # expected = eip1559_calc_base_fee_per_gas(...)  → hvbf_expected\n" ++
  "  mv a0, a1                   # parent.gas_limit\n" ++
  "  mv a1, a2                   # parent.gas_used\n" ++
  "  mv a2, a3                   # parent.base_fee\n" ++
  "  la a3, hvbf_expected\n" ++
  "  jal ra, eip1559_calc_base_fee_per_gas\n" ++
  "  bnez a0, .Lhvbf_fail_compute\n" ++
  "  # Compare header.base_fee vs expected.\n" ++
  "  mv a0, s0\n" ++
  "  la a1, hvbf_expected\n" ++
  "  jal ra, u256_eq             # a0 = 1 if equal, 0 if not\n" ++
  "  beqz a0, .Lhvbf_fail_mismatch\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvbf_ret\n" ++
  ".Lhvbf_fail_mismatch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhvbf_ret\n" ++
  ".Lhvbf_fail_compute:\n" ++
  "  li a0, 2\n" ++
  ".Lhvbf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_header_validate_base_fee`: probe BuildUnit. Reads
    (header_bf u256 BE, parent_gas_limit u64, parent_gas_used u64,
    parent_bf u256 BE) from host input, writes 8-byte status. -/
def ziskHeaderValidateBaseFeePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # header_bf ptr\n" ++
  "  ld a1, 40(a4)               # parent.gas_limit\n" ++
  "  ld a2, 48(a4)               # parent.gas_used\n" ++
  "  addi a3, a4, 56             # parent_bf ptr\n" ++
  "  jal ra, header_validate_base_fee\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhvbf_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  ".Lhvbf_pdone:"

def ziskHeaderValidateBaseFeeDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "hvbf_expected:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40"

def ziskHeaderValidateBaseFeeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateBaseFeePrologue
  dataAsm     := ziskHeaderValidateBaseFeeDataSection
}

/-! ## header_validate_excess_blob_gas -- Amsterdam recurrence

    Validate the Amsterdam `header.excess_blob_gas` recurrence from
    `execution-specs/src/ethereum/forks/amsterdam/vm/gas.py`.

    The spec computes:

      parent_blob_gas = parent.excess_blob_gas + parent.blob_gas_used
      if parent_blob_gas < BLOB_TARGET_GAS_PER_BLOCK:
        expected = 0
      elif BLOB_BASE_COST * parent.base_fee_per_gas
           > PER_BLOB * calculate_blob_gas_price(parent.excess_blob_gas):
        expected = parent.excess_blob_gas
                 + parent.blob_gas_used
                   * (BLOB_SCHEDULE_MAX - BLOB_SCHEDULE_TARGET)
                   // BLOB_SCHEDULE_MAX
      else:
        expected = parent_blob_gas - BLOB_TARGET_GAS_PER_BLOCK

    Constants for Amsterdam are PER_BLOB=131072, BLOB_SCHEDULE_TARGET=14,
    BLOB_SCHEDULE_MAX=21, and BLOB_BASE_COST=8192. The branch comparison
    simplifies to:

      parent.base_fee_per_gas > 16 * calculate_blob_gas_price(...)

    because `PER_BLOB / BLOB_BASE_COST = 16`.

    Calling convention:
      a0 (input)  : this.excess_blob_gas (u64)
      a1 (input)  : parent.blob_gas_used (u64)
      a2 (input)  : parent.excess_blob_gas (u64)
      a3 (input)  : parent.base_fee_per_gas ptr (u256 BE, 32 B)
      ra (input)  : return
      a0 (output) : 0 ok / 1 helper overflow / 2 mismatch.

    Uses 32 bytes of `.data` scratch (`hvebg_threshold`) and the existing
    u256 multiplication scratch (`u256m_acc`). -/
def headerValidateExcessBlobGasFunction : String :=
  "header_validate_excess_blob_gas:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # this.excess_blob_gas\n" ++
  "  mv s1, a1                   # parent.blob_gas_used\n" ++
  "  mv s2, a2                   # parent.excess_blob_gas\n" ++
  "  mv s3, a3                   # parent.base_fee_per_gas ptr\n" ++
  "  add s4, s2, s1              # parent_blob_gas\n" ++
  "  bltu s4, s2, .Lhvebg_overflow\n" ++
  "  li t0, 1835008              # 14 * 131072\n" ++
  "  bltu s4, t0, .Lhvebg_expected_zero\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, amsterdam_blob_gas_price\n" ++
  "  bnez a0, .Lhvebg_overflow\n" ++
  "  mv a0, a1                   # blob gas price\n" ++
  "  la a1, hvebg_threshold\n" ++
  "  jal ra, u256_from_u64_be\n" ++
  "  la a0, hvebg_threshold\n" ++
  "  li a1, 16\n" ++
  "  la a2, hvebg_threshold\n" ++
  "  jal ra, u256_mul_u64_be     # threshold = 16 * price\n" ++
  "  bnez a0, .Lhvebg_overflow\n" ++
  "  la a0, hvebg_threshold\n" ++
  "  mv a1, s3\n" ++
  "  jal ra, u256_lt_be          # threshold < parent_base_fee?\n" ++
  "  beqz a0, .Lhvebg_normal\n" ++
  "  li t0, 3\n" ++
  "  divu t1, s1, t0             # used * 7 // 21 == used // 3\n" ++
  "  add s5, s2, t1\n" ++
  "  bltu s5, s2, .Lhvebg_overflow\n" ++
  "  j .Lhvebg_compare\n" ++
  ".Lhvebg_normal:\n" ++
  "  li t0, 1835008\n" ++
  "  sub s5, s4, t0\n" ++
  "  j .Lhvebg_compare\n" ++
  ".Lhvebg_expected_zero:\n" ++
  "  li s5, 0\n" ++
  ".Lhvebg_compare:\n" ++
  "  bne s0, s5, .Lhvebg_mismatch\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvebg_ret\n" ++
  ".Lhvebg_overflow:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhvebg_ret\n" ++
  ".Lhvebg_mismatch:\n" ++
  "  li a0, 2\n" ++
  ".Lhvebg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-! ## validate_header_full -- PR-K75 complete per-header validation

    Run all six per-header validation checks in sequence, returning
    a single status code that distinguishes which step failed:

      1. PR-K67 `header_validate_post_merge`        — ommers/difficulty/nonce
      2. PR-K68 `header_validate_extra_data_length` — extra_data ≤ 32 bytes
      3. PR-K43 `validate_header_basic`             — gas_used ≤ gas_limit + number/timestamp
      4. PR-K72 `check_gas_limit`                   — elasticity
      5. PR-K74 `header_validate_base_fee`          — EIP-1559 invariant
      6. `header_validate_excess_blob_gas`          — Amsterdam blob recurrence

    Chain-level checks (parent_hash continuity, validate_chain
    PR-K18) are NOT included here — they iterate across multiple
    headers and live at the SSZ-list walk level.

    Status encoding:

      0                : all five checks pass
      100..104         : step 1 failed with K67's sub-status 0..4
      201..202         : step 2 failed with K68's sub-status 1..2
      301..303         : step 3 failed with K43's sub-status 1..3
      401..402         : step 4 failed with K72's sub-status 1..2
      501..502         : step 5 failed with K74's sub-status 1..2
      601..602         : step 6 failed with sub-status 1..2

    Distinct decades let callers `floor(status/100)` to identify
    the failing step.

    Calling convention:
      a0 (input)  : this header's RLP ptr
      a1 (input)  : this header's RLP byte length
      a2 (input)  : this header's PR-K39 extended-decode struct
                    (144 B, with gas_limit @ 80, gas_used @ 88,
                    base_fee_per_gas @ 96..128, blob fields @ 128..144)
      a3 (input)  : parent header's PR-K39 extended-decode struct
                    (same layout)
      ra (input)  : return
      a0 (output) : composite status (see encoding above).

    Composes 5 validators + their transitive deps (rlp_list_nth_item,
    eip1559_calc_base_fee_per_gas plus the u256 toolkit). The probe
    inlines every function it transitively calls. -/
def validateHeaderFullFunction : String :=
  "validate_header_full:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # this_rlp ptr\n" ++
  "  mv s1, a1                   # this_rlp_len\n" ++
  "  mv s2, a2                   # this_struct (144 B)\n" ++
  "  mv s3, a3                   # parent_struct (144 B)\n" ++
  "  # Step 1: post_merge check\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, header_validate_post_merge\n" ++
  "  beqz a0, .Lvhf_s2\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s2:\n" ++
  "  # Step 2: extra_data length check\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, header_validate_extra_data_length\n" ++
  "  beqz a0, .Lvhf_s3\n" ++
  "  li t0, 200\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s3:\n" ++
  "  # Step 3: gas_used/number/timestamp\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  jal ra, validate_header_basic\n" ++
  "  beqz a0, .Lvhf_s4\n" ++
  "  li t0, 300\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s4:\n" ++
  "  # Step 4: check_gas_limit(this.gas_limit, parent.gas_limit)\n" ++
  "  ld a0, 80(s2)\n" ++
  "  ld a1, 80(s3)\n" ++
  "  jal ra, check_gas_limit\n" ++
  "  beqz a0, .Lvhf_s5\n" ++
  "  li t0, 400\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s5:\n" ++
  "  # Step 5: base_fee continuity\n" ++
  "  addi a0, s2, 96\n" ++
  "  ld a1, 80(s3)\n" ++
  "  ld a2, 88(s3)\n" ++
  "  addi a3, s3, 96\n" ++
  "  jal ra, header_validate_base_fee\n" ++
  "  beqz a0, .Lvhf_s6\n" ++
  "  li t0, 500\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s6:\n" ++
  "  # Step 6: Amsterdam excess_blob_gas recurrence\n" ++
  "  ld a0, 136(s2)\n" ++
  "  ld a1, 128(s3)\n" ++
  "  ld a2, 136(s3)\n" ++
  "  addi a3, s3, 96\n" ++
  "  jal ra, header_validate_excess_blob_gas\n" ++
  "  beqz a0, .Lvhf_ret\n" ++
  "  li t0, 600\n" ++
  "  add a0, a0, t0\n" ++
  ".Lvhf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_validate_header_full`: probe BuildUnit. Reads (this_rlp_len,
    this_rlp_bytes [up to 1024 B], this_struct 144 B, parent_struct
    144 B) from host input, writes 8-byte composite status to OUTPUT. -/
def ziskValidateHeaderFullPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # this_rlp_len\n" ++
  "  addi a0, a4, 16             # this_rlp ptr\n" ++
  "  addi a2, a4, 16             # placeholder; reset after rlp\n" ++
  "  # this_struct offset = 16 + rlp_len_aligned\n" ++
  "  # parent_struct offset = this_struct + 144\n" ++
  "  # We require the caller to lay them out at fixed positions:\n" ++
  "  # bytes 8..16  : rlp_len\n" ++
  "  # bytes 16..16+1024 : this_rlp (padded to 1024)\n" ++
  "  # bytes 1040..1184  : this_struct (144 B)\n" ++
  "  # bytes 1184..1328  : parent_struct (144 B)\n" ++
  "  li a2, 0x40000410           # this_struct  (= INPUT_ADDR + 1040)\n" ++
  "  li a3, 0x400004a0           # parent_struct (= INPUT_ADDR + 1184)\n" ++
  "  jal ra, validate_header_full\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvhf_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  amsterdamBlobGasPriceFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  headerValidateExcessBlobGasFunction ++ "\n" ++
  validateHeaderFullFunction ++ "\n" ++
  ".Lvhf_pdone:"

def ziskValidateHeaderFullDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 32\n" ++
  "hvbf_expected:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "hvebg_threshold:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 8\n" ++
  "hvpm_off:\n" ++
  "  .zero 8\n" ++
  "hvpm_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hved_off:\n" ++
  "  .zero 8\n" ++
  "hved_len:\n" ++
  "  .zero 8"

def ziskValidateHeaderFullProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderFullPrologue
  dataAsm     := ziskValidateHeaderFullDataSection
}


end EvmAsm.Codegen
