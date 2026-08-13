/-
  EvmAsm.Codegen.Programs.BlockGasRemaining

  EIP-7778 remaining block-gas availability checker. The full block executor
  will eventually feed exact per-transaction `block_gas_used_in_tx` increments
  from gas-metered execution; this helper isolates the execution-spec
  `tx.gas <= block_gas_limit - block_output.block_gas_used` gate.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Account

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## eip7778_remaining_block_gas_check

    ABI:
      a0 = block_gas_limit
      a1 = pointer to `count` u64 transaction gas limits
      a2 = pointer to `count` u64 exact block-gas-used increments
      a3 = count

    Returns:
      a0 = status:
        0 ok
        1 transaction gas exceeds currently available block gas
        2 cumulative block-gas-used overflow while applying increments
      a1 = first failing transaction index, 1-based; 0 on success
      a2 = block_gas_used before the failing transaction/increment, or final
           block_gas_used on success.

    The check mirrors execution-specs Amsterdam `check_transaction`:
      gas_available = block_env.block_gas_limit - block_output.block_gas_used
      if min(TX_MAX_GAS_LIMIT, tx.gas) > gas_available: raise GasUsedExceedsLimitError
    (EIP-7825 caps the worst-case regular contribution at TX_MAX_GAS_LIMIT.
     EIP-8037 keeps this regular-dimension check on the full declared
     `tx.gas`; intrinsic state gas is checked independently.)

    The helper intentionally takes block-gas-used increments as input rather
    than deriving them from tx gas limits. EIP-7778 increments
    `block_output.block_gas_used` by max(gas used before refund, calldata
    floor), which only a gas-metered execution slice can compute exactly. -/
def eip7778RemainingBlockGasCheckFunction : String :=
  "eip7778_remaining_block_gas_check:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd s0, 0(sp)\n" ++
  "  mv s0, a4                   # a4 reserved for callers' intrinsic-state array\n" ++
  "  mv t0, a0                   # block_gas_limit\n" ++
  "  mv t1, a1                   # tx_gas ptr\n" ++
  "  mv t2, a2                   # block_gas_used_in_tx ptr\n" ++
  "  mv t3, a3                   # count\n" ++
  "  li t4, 0                    # i\n" ++
  "  li t5, 0                    # block_gas_used\n" ++
  ".Le7778_loop:\n" ++
  "  beq t4, t3, .Le7778_ok\n" ++
  "  bltu t0, t5, .Le7778_tx_fail\n" ++
  "  slli t6, t4, 3\n" ++
  "  add a4, t1, t6\n" ++
  "  ld a5, 0(a4)                # tx.gas\n" ++
  -- execution-specs EIP-8037 regular-dimension admission is intentionally
  -- `min(TX_MAX_GAS_LIMIT, tx.gas)`: do not subtract intrinsic.state here.
  -- The state dimension has its own independent admission check.
  "  li a7, 16777216             # TX_MAX_GAS_LIMIT (2^24)\n" ++
  "  bleu a5, a7, .Le7778_cap_done\n" ++
  "  mv a5, a7                   # worst_regular = min(TX_MAX_GAS_LIMIT, tx.gas)\n" ++
  ".Le7778_cap_done:\n" ++
  "  sub a6, t0, t5              # gas_available\n" ++
  "  bgtu a5, a6, .Le7778_tx_fail\n" ++
  "  add a4, t2, t6\n" ++
  "  ld a5, 0(a4)                # exact block_gas_used_in_tx\n" ++
  "  add a6, t5, a5\n" ++
  "  bltu a6, t5, .Le7778_overflow\n" ++
  "  mv t5, a6\n" ++
  "  addi t4, t4, 1\n" ++
  "  j .Le7778_loop\n" ++
  ".Le7778_tx_fail:\n" ++
  "  li a0, 1\n" ++
  "  addi a1, t4, 1\n" ++
  "  mv a2, t5\n" ++
  "  j .Le7778_ret\n" ++
  ".Le7778_overflow:\n" ++
  "  li a0, 2\n" ++
  "  addi a1, t4, 1\n" ++
  "  mv a2, t5\n" ++
  "  j .Le7778_ret\n" ++
  ".Le7778_ok:\n" ++
  "  li a0, 0\n" ++
  "  li a1, 0\n" ++
  "  mv a2, t5\n" ++
  ".Le7778_ret:\n" ++
  "  ld s0, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_eip7778_remaining_block_gas_check`: focused zisk probe.
    Host input payload after the zisk length prefix:
      +0  block_gas_limit u64
      +8  count u64
      +16 count u64 tx.gas entries
      then count u64 exact block_gas_used_in_tx entries

    Output:
      +0  status
      +8  failing tx index, 1-based
      +16 block_gas_used before failure, or final block_gas_used. -/
def ziskEip7778RemainingBlockGasCheckPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  li s1, 0xa0010000\n" ++
  "  ld a0, 8(s0)                # block_gas_limit\n" ++
  "  ld a3, 16(s0)               # count\n" ++
  "  addi a1, s0, 24             # tx_gas array\n" ++
  "  slli t0, a3, 3\n" ++
  "  add a2, a1, t0              # block_gas_used_in_tx array\n" ++
  "  li a4, 0                    # .6.5.2: no intrinsic_state in the probe -> legacy 1D behaviour\n" ++
  "  jal ra, eip7778_remaining_block_gas_check\n" ++
  "  sd a0, 0(s1)\n" ++
  "  sd a1, 8(s1)\n" ++
  "  sd a2, 16(s1)\n" ++
  "  j .Le7778_probe_done\n" ++
  eip7778RemainingBlockGasCheckFunction ++ "\n" ++
  ".Le7778_probe_done:"


/-! ## eip7778_remaining_block_gas_from_results

    Adapter from runtime transaction execution results to the EIP-7778
    remaining block-gas gate. The full block verdict path eventually feeds the
    same runtime-derived arrays rather than precomputed increment fixtures.

    ABI:
      a0 = block_gas_limit
      a1 = pointer to `count` u64 transaction gas limits
      a2 = pointer to `count` u64 gas_left values after execution
      a3 = pointer to `count` u64 refund_counter values
      a4 = pointer to `count` u64 calldata_floor_gas_cost values
      a5 = count
      a6 = scratch pointer for `count` u64 block-gas increments
      a7 = pointer to `count` u64 per-tx total state gas
           (intrinsic.state + executed state gas, fork.py:1174), or 0 for the
           legacy 1D increment (`max(before_refund, floor)`)

    With a nonzero a7, the per-tx block-gas increment follows the v0.6
    settlement identity (fork.py:1176-1181):

      tx_regular_gas = max(before_refund - tx_state_gas, calldata_floor)

    i.e. only the regular dimension accumulates into `block_gas_used`; state
    gas is admitted/settled on its own dimension.

    Returns:
      a0 = status:
        0 ok
        1 transaction gas exceeds currently available block gas
        2 cumulative block-gas-used overflow while applying increments
        3 invalid runtime gas result (`gas_left > tx_gas_limit`)
        4 per-tx state gas exceeds before-refund gas (Uint underflow in
          fork.py:1178 -> invalid block)
      a1 = first failing transaction index, 1-based; 0 on success
      a2 = block_gas_used before the failing transaction/increment, or final
           block_gas_used on success. For status 3/4 this is currently 0. -/
def eip7778RemainingBlockGasFromResults_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .MV .x24 .x17,
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .LI .x23 (0 : Word),
    .BEQ .x23 .x21 (brOff (GuestAddrs.eip7778_remaining_block_gas_from_results + 192) (GuestAddrs.eip7778_remaining_block_gas_from_results + 80)),
    .SLLI .x5 .x23 (3 : BitVec 6),
    .ADD .x6 .x9 .x5,
    .LD .x10 .x6 (0 : BitVec 12),
    .ADD .x6 .x18 .x5,
    .LD .x11 .x6 (0 : BitVec 12),
    .ADD .x6 .x19 .x5,
    .LD .x12 .x6 (0 : BitVec 12),
    .ADD .x6 .x20 .x5,
    .LD .x13 .x6 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_gas_result_increments (GuestAddrs.eip7778_remaining_block_gas_from_results + 120)),
    .BNE .x10 .x0 (brOff (GuestAddrs.eip7778_remaining_block_gas_from_results + 220) (GuestAddrs.eip7778_remaining_block_gas_from_results + 124)),
    .BEQ .x24 .x0 (44 : BitVec 13),
    .SLLI .x5 .x23 (3 : BitVec 6),
    .ADD .x6 .x24 .x5,
    .LD .x7 .x6 (0 : BitVec 12),
    .BLTU .x13 .x7 (brOff (GuestAddrs.eip7778_remaining_block_gas_from_results + 236) (GuestAddrs.eip7778_remaining_block_gas_from_results + 144)),
    .SUB .x13 .x13 .x7,
    .ADD .x6 .x20 .x5,
    .LD .x7 .x6 (0 : BitVec 12),
    .BGEU .x13 .x7 (8 : BitVec 13),
    .MV .x13 .x7,
    .MV .x11 .x13,
    .SLLI .x5 .x23 (3 : BitVec 6),
    .ADD .x6 .x22 .x5,
    .SD .x6 .x11 (0 : BitVec 12),
    .ADDI .x23 .x23 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.eip7778_remaining_block_gas_from_results + 80) (GuestAddrs.eip7778_remaining_block_gas_from_results + 188)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x22,
    .MV .x13 .x21,
    .MV .x14 .x24,
    .JAL .x1 (jalOff GuestAddrs.eip7778_remaining_block_gas_check (GuestAddrs.eip7778_remaining_block_gas_from_results + 212)),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (3 : Word),
    .ADDI .x11 .x23 (1 : BitVec 12),
    .LI .x12 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (4 : Word),
    .ADDI .x11 .x23 (1 : BitVec 12),
    .LI .x12 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `eip7778RemainingBlockGasFromResults_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def eip7778RemainingBlockGasFromResults_relocs : RelocTable :=
  [ (30, .jal .x1 "tx_gas_result_increments"),
    (53, .jal .x1 "eip7778_remaining_block_gas_check") ]

def eip7778RemainingBlockGasFromResultsFunction : String :=
  "eip7778_remaining_block_gas_from_results:\n" ++ emitProgramR eip7778RemainingBlockGasFromResults_prog eip7778RemainingBlockGasFromResults_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `eip7778RemainingBlockGasFromResults_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem eip7778RemainingBlockGasFromResultsFunction_eq_prog :
    eip7778RemainingBlockGasFromResultsFunction = "eip7778_remaining_block_gas_from_results:\n" ++ emitProgramR eip7778RemainingBlockGasFromResults_prog eip7778RemainingBlockGasFromResults_relocs := rfl

#guard eip7778RemainingBlockGasFromResultsFunction.startsWith "eip7778_remaining_block_gas_from_results:\n"
#guard eip7778RemainingBlockGasFromResults_prog.length = 74
/-- `zisk_eip7778_remaining_block_gas_from_results`: focused zisk probe.
    Host input payload after the zisk length prefix:
      +0  block_gas_limit u64
      +8  count u64
      +16 count u64 tx.gas entries
      then count u64 gas_left entries
      then count u64 refund_counter entries
      then count u64 calldata_floor_gas_cost entries

    Output:
      +0  status
      +8  failing tx index, 1-based
      +16 block_gas_used before failure, or final block_gas_used. -/
def ziskEip7778RemainingBlockGasFromResultsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  li s1, 0xa0010000\n" ++
  "  ld a0, 8(s0)                # block_gas_limit\n" ++
  "  ld a5, 16(s0)               # count\n" ++
  "  addi a1, s0, 24             # tx_gas_limits array\n" ++
  "  slli t0, a5, 3\n" ++
  "  add a2, a1, t0              # gas_left array\n" ++
  "  add a3, a2, t0              # refund_counter array\n" ++
  "  add a4, a3, t0              # calldata_floor array\n" ++
  "  la a6, e7778rr_block_increments\n" ++
  "  li a7, 0                    # .6.5.2: no intrinsic_state in the probe -> legacy 1D behaviour\n" ++
  "  jal ra, eip7778_remaining_block_gas_from_results\n" ++
  "  sd a0, 0(s1)\n" ++
  "  sd a1, 8(s1)\n" ++
  "  sd a2, 16(s1)\n" ++
  "  j .Le7778rr_probe_done\n" ++
  txGasResultIncrementsFunction ++ "\n" ++
  eip7778RemainingBlockGasCheckFunction ++ "\n" ++
  eip7778RemainingBlockGasFromResultsFunction ++ "\n" ++
  ".Le7778rr_probe_done:"

def ziskEip7778RemainingBlockGasFromResultsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "e7778rr_block_increments:\n" ++
  "  .zero 8192\n"


end EvmAsm.Codegen
