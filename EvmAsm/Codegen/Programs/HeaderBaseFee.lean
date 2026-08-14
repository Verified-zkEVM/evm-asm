/-
  EvmAsm.Codegen.Programs.HeaderBaseFee

  EIP-1559 base-fee math + the full-validate composite carved
  out of `EvmAsm.Codegen.Programs.Header` per the file-size hard
  cap. Hosts:

    K73  eip1559_calc_base_fee_per_gas
    K74  header_validate_base_fee

  K75 `validate_header_full` was retired in #12345 in favor of SpecRef-shaped
  `validate_header` (`Programs/ValidateHeader.lean`).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
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
def eip1559CalcBaseFeePerGas_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .SRLI .x18 .x10 (1 : BitVec 6),
    .BEQ .x11 .x18 (192 : BitVec 13),
    .LI .x20 (0 : Word),
    .BLTU .x18 .x11 (16 : BitVec 13),
    .BEQ .x11 .x0 (104 : BitVec 13),
    .SUB .x19 .x18 .x11,
    .JAL .x0 (12 : BitVec 21),
    .LI .x20 (1 : Word),
    .SUB .x19 .x11 .x18,
    .MV .x10 .x8,
    .MV .x11 .x19,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_mul_u64_be (GuestAddrs.eip1559_calc_base_fee_per_gas + 84)),
    .BNE .x10 .x0 (184 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_div_u64_be (GuestAddrs.eip1559_calc_base_fee_per_gas + 104)),
    .MV .x10 .x9,
    .LI .x11 (8 : Word),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_div_u64_be (GuestAddrs.eip1559_calc_base_fee_per_gas + 120)),
    .BEQ .x20 .x0 (48 : BitVec 13),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_is_zero (GuestAddrs.eip1559_calc_base_fee_per_gas + 132)),
    .BEQ .x10 .x0 (36 : BitVec 13),
    .LI .x10 (1 : Word),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_from_u64_be (GuestAddrs.eip1559_calc_base_fee_per_gas + 148)),
    .JAL .x0 (20 : BitVec 21),
    .MV .x10 .x8,
    .LI .x11 (8 : Word),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_div_u64_be (GuestAddrs.eip1559_calc_base_fee_per_gas + 168)),
    .BEQ .x20 .x0 (32 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.eip1559_calc_base_fee_per_gas + 188)),
    .BNE .x10 .x0 (80 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (76 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.eip1559_calc_base_fee_per_gas + 216)),
    .BNE .x10 .x0 (52 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (48 : BitVec 21),
    .LD .x5 .x8 (0 : BitVec 12),
    .SD .x9 .x5 (0 : BitVec 12),
    .LD .x5 .x8 (8 : BitVec 12),
    .SD .x9 .x5 (8 : BitVec 12),
    .LD .x5 .x8 (16 : BitVec 12),
    .SD .x9 .x5 (16 : BitVec 12),
    .LD .x5 .x8 (24 : BitVec 12),
    .SD .x9 .x5 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `eip1559CalcBaseFeePerGas_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def eip1559CalcBaseFeePerGas_relocs : RelocTable :=
  [ (21, .jal .x1 "u256_mul_u64_be"),
    (26, .jal .x1 "u256_div_u64_be"),
    (30, .jal .x1 "u256_div_u64_be"),
    (33, .jal .x1 "u256_is_zero"),
    (37, .jal .x1 "u256_from_u64_be"),
    (42, .jal .x1 "u256_div_u64_be"),
    (47, .jal .x1 "u256_add_be"),
    (54, .jal .x1 "u256_sub_be") ]

def eip1559CalcBaseFeePerGasFunction : String :=
  "eip1559_calc_base_fee_per_gas:\n" ++ emitProgramR eip1559CalcBaseFeePerGas_prog eip1559CalcBaseFeePerGas_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `eip1559CalcBaseFeePerGas_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem eip1559CalcBaseFeePerGasFunction_eq_prog :
    eip1559CalcBaseFeePerGasFunction = "eip1559_calc_base_fee_per_gas:\n" ++ emitProgramR eip1559CalcBaseFeePerGas_prog eip1559CalcBaseFeePerGas_relocs := rfl

#guard eip1559CalcBaseFeePerGasFunction.startsWith "eip1559_calc_base_fee_per_gas:\n"
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
def headerValidateBaseFee_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .MV .x10 .x11,
    .MV .x11 .x12,
    .MV .x12 .x13,
    .AUIPC .x13 (laHi GuestAddrs.hvbf_expected (GuestAddrs.header_validate_base_fee + 28)),
    .ADDI .x13 .x13 (laLo GuestAddrs.hvbf_expected (GuestAddrs.header_validate_base_fee + 28)),
    .JAL .x1 (jalOff GuestAddrs.eip1559_calc_base_fee_per_gas (GuestAddrs.header_validate_base_fee + 36)),
    .BNE .x10 .x0 (40 : BitVec 13),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.hvbf_expected (GuestAddrs.header_validate_base_fee + 48)),
    .ADDI .x11 .x11 (laLo GuestAddrs.hvbf_expected (GuestAddrs.header_validate_base_fee + 48)),
    .JAL .x1 (jalOff GuestAddrs.u256_eq (GuestAddrs.header_validate_base_fee + 56)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerValidateBaseFee_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerValidateBaseFee_relocs : RelocTable :=
  [ (7, .la .x13 "hvbf_expected"),
    (9, .jal .x1 "eip1559_calc_base_fee_per_gas"),
    (12, .la .x11 "hvbf_expected"),
    (14, .jal .x1 "u256_eq") ]

def headerValidateBaseFeeFunction : String :=
  "header_validate_base_fee:\n" ++ emitProgramR headerValidateBaseFee_prog headerValidateBaseFee_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerValidateBaseFee_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerValidateBaseFeeFunction_eq_prog :
    headerValidateBaseFeeFunction = "header_validate_base_fee:\n" ++ emitProgramR headerValidateBaseFee_prog headerValidateBaseFee_relocs := rfl

#guard headerValidateBaseFeeFunction.startsWith "header_validate_base_fee:\n"
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

    The schedule branch computes `used // 3` (algebraically `used * 7 // 21`),
    but the spec's `blob_gas_used * 7` is an overflow-checked U64 multiply:
    when `blob_gas_used > (2^64-1) // 7` the spec raises OverflowError and the
    block is invalid, so that range must return the overflow status here too.

    Calling convention:
      a0 (input)  : this.excess_blob_gas (u64)
      a1 (input)  : parent.blob_gas_used (u64)
      a2 (input)  : parent.excess_blob_gas (u64)
      a3 (input)  : parent.base_fee_per_gas ptr (u256 BE, 32 B)
      ra (input)  : return
      a0 (output) : 0 ok / 1 helper overflow / 2 mismatch.

    Uses 32 bytes of `.data` scratch (`hvebg_threshold`) and the existing
    u256 multiplication scratch (`u256m_acc`). -/
def headerValidateExcessBlobGas_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .ADD .x20 .x18 .x9,
    .BLTU .x20 .x18 (184 : BitVec 13),
    .LUI .x5 (448 : BitVec 20),
    .BLTU .x20 .x5 (160 : BitVec 13),
    .MV .x10 .x18,
    .AUIPC .x11 (laHi GuestAddrs.hvebg_threshold (GuestAddrs.header_validate_excess_blob_gas + 68)),
    .ADDI .x11 .x11 (laLo GuestAddrs.hvebg_threshold (GuestAddrs.header_validate_excess_blob_gas + 68)),
    .JAL .x1 (jalOff GuestAddrs.amsterdam_blob_gas_price_u256 (GuestAddrs.header_validate_excess_blob_gas + 76)),
    .BNE .x10 .x0 (156 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.hvebg_threshold (GuestAddrs.header_validate_excess_blob_gas + 84)),
    .ADDI .x10 .x10 (laLo GuestAddrs.hvebg_threshold (GuestAddrs.header_validate_excess_blob_gas + 84)),
    .LI .x11 (16 : Word),
    .AUIPC .x12 (laHi GuestAddrs.hvebg_threshold (GuestAddrs.header_validate_excess_blob_gas + 96)),
    .ADDI .x12 .x12 (laLo GuestAddrs.hvebg_threshold (GuestAddrs.header_validate_excess_blob_gas + 96)),
    .JAL .x1 (jalOff GuestAddrs.u256_mul_u64_be (GuestAddrs.header_validate_excess_blob_gas + 104)),
    .BNE .x10 .x0 (128 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.hvebg_threshold (GuestAddrs.header_validate_excess_blob_gas + 112)),
    .ADDI .x10 .x10 (laLo GuestAddrs.hvebg_threshold (GuestAddrs.header_validate_excess_blob_gas + 112)),
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.u256m_acc (GuestAddrs.header_validate_excess_blob_gas + 124)),
    .ADDI .x12 .x12 (laLo GuestAddrs.u256m_acc (GuestAddrs.header_validate_excess_blob_gas + 124)),
    .JAL .x1 (jalOff GuestAddrs.u256_lt_be (GuestAddrs.header_validate_excess_blob_gas + 132)),
    .AUIPC .x5 (laHi GuestAddrs.u256m_acc (GuestAddrs.header_validate_excess_blob_gas + 136)),
    .ADDI .x5 .x5 (laLo GuestAddrs.u256m_acc (GuestAddrs.header_validate_excess_blob_gas + 136)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (60 : BitVec 13),
    .LUI .x5 (4681 : BitVec 20),
    .ADDIW .x5 .x5 (585 : BitVec 12),
    .SLLI .x5 .x5 (12 : BitVec 6),
    .ADDI .x5 .x5 (585 : BitVec 12),
    .SLLI .x5 .x5 (12 : BitVec 6),
    .ADDI .x5 .x5 (585 : BitVec 12),
    .SLLI .x5 .x5 (13 : BitVec 6),
    .ADDI .x5 .x5 (1170 : BitVec 12),
    .BLTU .x5 .x9 (52 : BitVec 13),
    .LI .x5 (3 : Word),
    .DIVU .x6 .x9 .x5,
    .ADD .x21 .x18 .x6,
    .BLTU .x21 .x18 (36 : BitVec 13),
    .JAL .x0 (20 : BitVec 21),
    .LUI .x5 (448 : BitVec 20),
    .SUB .x21 .x20 .x5,
    .JAL .x0 (8 : BitVec 21),
    .LI .x21 (0 : Word),
    .BNE .x8 .x21 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerValidateExcessBlobGas_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerValidateExcessBlobGas_relocs : RelocTable :=
  [ (17, .la .x11 "hvebg_threshold"),
    (19, .jal .x1 "amsterdam_blob_gas_price_u256"),
    (21, .la .x10 "hvebg_threshold"),
    (24, .la .x12 "hvebg_threshold"),
    (26, .jal .x1 "u256_mul_u64_be"),
    (28, .la .x10 "hvebg_threshold"),
    (31, .la .x12 "u256m_acc"),
    (33, .jal .x1 "u256_lt_be"),
    (34, .la .x5 "u256m_acc") ]

def headerValidateExcessBlobGasFunction : String :=
  "header_validate_excess_blob_gas:\n" ++ emitProgramR headerValidateExcessBlobGas_prog headerValidateExcessBlobGas_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerValidateExcessBlobGas_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerValidateExcessBlobGasFunction_eq_prog :
    headerValidateExcessBlobGasFunction = "header_validate_excess_blob_gas:\n" ++ emitProgramR headerValidateExcessBlobGas_prog headerValidateExcessBlobGas_relocs := rfl

#guard headerValidateExcessBlobGasFunction.startsWith "header_validate_excess_blob_gas:\n"
/-! ## validate_header_full — RETIRED (#12345)

    Replaced by SpecRef-shaped `validate_header` in
    `EvmAsm/Codegen/Programs/ValidateHeader.lean`. Do not reintroduce.
-/

end EvmAsm.Codegen
