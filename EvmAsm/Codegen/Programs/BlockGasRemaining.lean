/-
  EvmAsm.Codegen.Programs.BlockGasRemaining

  EIP-7778 remaining block-gas availability checker. The full block executor
  will eventually feed exact per-transaction `block_gas_used_in_tx` increments
  from gas-metered execution; this helper isolates the execution-spec
  `tx.gas <= block_gas_limit - block_output.block_gas_used` gate.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
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
      if tx.gas > gas_available: raise GasUsedExceedsLimitError

    The helper intentionally takes block-gas-used increments as input rather
    than deriving them from tx gas limits. EIP-7778 increments
    `block_output.block_gas_used` by max(gas used before refund, calldata
    floor), which only a gas-metered execution slice can compute exactly. -/
def eip7778RemainingBlockGasCheckFunction : String :=
  "eip7778_remaining_block_gas_check:\n" ++
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
  "  ret\n" ++
  ".Le7778_overflow:\n" ++
  "  li a0, 2\n" ++
  "  addi a1, t4, 1\n" ++
  "  mv a2, t5\n" ++
  "  ret\n" ++
  ".Le7778_ok:\n" ++
  "  li a0, 0\n" ++
  "  li a1, 0\n" ++
  "  mv a2, t5\n" ++
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
  "  jal ra, eip7778_remaining_block_gas_check\n" ++
  "  sd a0, 0(s1)\n" ++
  "  sd a1, 8(s1)\n" ++
  "  sd a2, 16(s1)\n" ++
  "  j .Le7778_probe_done\n" ++
  eip7778RemainingBlockGasCheckFunction ++ "\n" ++
  ".Le7778_probe_done:"

def ziskEip7778RemainingBlockGasCheckProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip7778RemainingBlockGasCheckPrologue
  dataAsm     := ".section .data\n.balign 8\n"
}

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

    Returns:
      a0 = status:
        0 ok
        1 transaction gas exceeds currently available block gas
        2 cumulative block-gas-used overflow while applying increments
        3 invalid runtime gas result (`gas_left > tx_gas_limit`)
      a1 = first failing transaction index, 1-based; 0 on success
      a2 = block_gas_used before the failing transaction/increment, or final
           block_gas_used on success. For status 3 this is currently 0. -/
def eip7778RemainingBlockGasFromResultsFunction : String :=
  "eip7778_remaining_block_gas_from_results:\n" ++
  "  addi sp, sp, -72\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # block_gas_limit\n" ++
  "  mv s1, a1                   # tx_gas_limits ptr\n" ++
  "  mv s2, a2                   # gas_left ptr\n" ++
  "  mv s3, a3                   # refund_counter ptr\n" ++
  "  mv s4, a4                   # calldata_floor ptr\n" ++
  "  mv s5, a5                   # count\n" ++
  "  mv s6, a6                   # scratch block increments ptr\n" ++
  "  li s7, 0                    # i\n" ++
  ".Le7778rr_loop:\n" ++
  "  beq s7, s5, .Le7778rr_check\n" ++
  "  slli t0, s7, 3\n" ++
  "  add t1, s1, t0\n" ++
  "  ld a0, 0(t1)                # tx_gas_limit\n" ++
  "  add t1, s2, t0\n" ++
  "  ld a1, 0(t1)                # gas_left\n" ++
  "  add t1, s3, t0\n" ++
  "  ld a2, 0(t1)                # refund_counter\n" ++
  "  add t1, s4, t0\n" ++
  "  ld a3, 0(t1)                # calldata_floor_gas_cost\n" ++
  "  jal ra, tx_gas_result_increments\n" ++
  "  bnez a0, .Le7778rr_bad_result\n" ++
  "  slli t0, s7, 3\n" ++
  "  add t1, s6, t0\n" ++
  "  sd a1, 0(t1)                # exact block_gas_used_in_tx\n" ++
  "  addi s7, s7, 1\n" ++
  "  j .Le7778rr_loop\n" ++
  ".Le7778rr_check:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s6\n" ++
  "  mv a3, s5\n" ++
  "  jal ra, eip7778_remaining_block_gas_check\n" ++
  "  j .Le7778rr_ret\n" ++
  ".Le7778rr_bad_result:\n" ++
  "  li a0, 3\n" ++
  "  addi a1, s7, 1\n" ++
  "  li a2, 0\n" ++
  ".Le7778rr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 72\n" ++
  "  ret"

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

def ziskEip7778RemainingBlockGasFromResultsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip7778RemainingBlockGasFromResultsPrologue
  dataAsm     := ziskEip7778RemainingBlockGasFromResultsDataSection
}

end EvmAsm.Codegen
