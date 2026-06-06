/-
  EvmAsm.Codegen.Programs.BlockVerdictGasResults

  Transaction gas-result helpers for the stateless block verdict path.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.BlockGasRemaining
import EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords
import EvmAsm.Codegen.Programs.TxExtract

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_verdict_tx_gas_limits

    Materialize `tx.gas` values from `exec_payload.transactions`.

    ABI:
      a0 = execution payload ptr
      a1 = output pointer for `max_count` u64 gas limits
      a2 = max_count

    Returns:
      a0 = status:
        0 ok
        1 malformed SSZ transaction list offsets
        2 transaction count exceeds max_count
        3 transaction type dispatch failed
        4 nonce/gas extraction failed
      a1 = transaction count decoded from the SSZ list
      a2 = failing transaction index, 1-based; 0 if not transaction-specific
      a3 = transaction type from `tx_type_dispatch` when available

    Debug globals mirror the return values for `zisk_stateless_verdict_v2`
    wiring in the next slice. -/
def blockVerdictTxGasLimitsFunction : String :=
  "block_verdict_tx_gas_limits:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # execution payload\n" ++
  "  mv s1, a1                   # gas limit output array\n" ++
  "  mv s2, a2                   # max_count\n" ++
  "  la t0, bvgr_status; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_count; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_fail_index; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_tx_type; sd zero, 0(t0)\n" ++
  "  addi a0, s0, 504; jal ra, bgv_u32le\n" ++
  "  mv s3, a0                   # transactions_offset\n" ++
  "  addi a0, s0, 508; jal ra, bgv_u32le\n" ++
  "  mv s4, a0                   # withdrawals_offset\n" ++
  "  bleu s4, s3, .Lbvgr_ok_zero # no transactions\n" ++
  "  add s5, s0, s3              # tx list ptr\n" ++
  "  sub s6, s4, s3              # tx list byte length\n" ++
  "  li t0, 4; bltu s6, t0, .Lbvgr_malformed\n" ++
  "  mv a0, s5; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbvgr_malformed\n" ++
  "  bgtu a0, s6, .Lbvgr_malformed\n" ++
  "  srli s7, a0, 2              # tx_count\n" ++
  "  la t0, bvgr_count; sd s7, 0(t0)\n" ++
  "  bgtu s7, s2, .Lbvgr_capacity\n" ++
  "  beqz s7, .Lbvgr_ok\n" ++
  "  mv s8, zero                 # tx index\n" ++
  "  slli s11, s7, 2             # minimum item offset = offset table len\n" ++
  ".Lbvgr_loop:\n" ++
  "  beq s8, s7, .Lbvgr_ok\n" ++
  "  slli t0, s8, 2\n" ++
  "  add a0, s5, t0\n" ++
  "  jal ra, bgv_u32le\n" ++
  "  mv s9, a0                   # current tx offset\n" ++
  "  bltu s9, s11, .Lbvgr_malformed_tx\n" ++
  "  bgtu s9, s6, .Lbvgr_malformed_tx\n" ++
  "  addi t0, s8, 1\n" ++
  "  beq t0, s7, .Lbvgr_last_tx\n" ++
  "  slli t1, t0, 2\n" ++
  "  add a0, s5, t1\n" ++
  "  jal ra, bgv_u32le\n" ++
  "  mv s10, a0                  # next tx offset\n" ++
  "  j .Lbvgr_have_next\n" ++
  ".Lbvgr_last_tx:\n" ++
  "  mv s10, s6                  # final tx ends at list end\n" ++
  ".Lbvgr_have_next:\n" ++
  "  bltu s10, s9, .Lbvgr_malformed_tx\n" ++
  "  bgtu s10, s6, .Lbvgr_malformed_tx\n" ++
  "  add t0, s5, s9              # tx ptr\n" ++
  "  sub t1, s10, s9             # tx len\n" ++
  "  mv a0, t0; mv a1, t1; la a2, bvgr_tx_type; la a3, bvgr_tx_inner\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbvgr_type_fail\n" ++
  "  add t0, s5, s9\n" ++
  "  sub t1, s10, s9\n" ++
  "  mv a0, t0; mv a1, t1; la a2, bvgr_nonce; la a3, bvgr_gas\n" ++
  "  jal ra, tx_extract_nonce_and_gas\n" ++
  "  bnez a0, .Lbvgr_extract_fail\n" ++
  "  slli t0, s8, 3\n" ++
  "  add t1, s1, t0\n" ++
  "  la t2, bvgr_gas; ld t3, 0(t2)\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi s8, s8, 1\n" ++
  "  j .Lbvgr_loop\n" ++
  ".Lbvgr_ok_zero:\n" ++
  "  mv s7, zero\n" ++
  ".Lbvgr_ok:\n" ++
  "  li a0, 0; mv a1, s7; li a2, 0; la t0, bvgr_tx_type; ld a3, 0(t0)\n" ++
  "  j .Lbvgr_store_ret\n" ++
  ".Lbvgr_malformed_tx:\n" ++
  "  addi a2, s8, 1; li a0, 1; mv a1, s7; j .Lbvgr_store_ret\n" ++
  ".Lbvgr_malformed:\n" ++
  "  li a0, 1; li a1, 0; li a2, 0; li a3, 0; j .Lbvgr_store_ret\n" ++
  ".Lbvgr_capacity:\n" ++
  "  li a0, 2; mv a1, s7; li a2, 0; li a3, 0; j .Lbvgr_store_ret\n" ++
  ".Lbvgr_type_fail:\n" ++
  "  li a0, 3; mv a1, s7; addi a2, s8, 1; la t0, bvgr_tx_type; ld a3, 0(t0)\n" ++
  "  j .Lbvgr_store_ret\n" ++
  ".Lbvgr_extract_fail:\n" ++
  "  li a0, 4; mv a1, s7; addi a2, s8, 1; la t0, bvgr_tx_type; ld a3, 0(t0)\n" ++
  ".Lbvgr_store_ret:\n" ++
  "  la t0, bvgr_status; sd a0, 0(t0)\n" ++
  "  la t0, bvgr_count; sd a1, 0(t0)\n" ++
  "  la t0, bvgr_fail_index; sd a2, 0(t0)\n" ++
  "  la t0, bvgr_tx_type; sd a3, 0(t0)\n" ++
  ".Lbvgr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-! ## block_verdict_gas_result_arena_prepare

    Populate the block-verdict runtime gas-result arena.

    ABI:
      a0 = execution payload ptr
      a1 = runtime `gas_left` u64 array
      a2 = runtime `refund_counter` u64 array
      a3 = runtime `calldata_floor_gas_cost` u64 array
      a4 = runtime result count
      a5 = arena capacity

    Returns:
      a0 = status:
        0 ok
        1 tx gas-limit materialization failed
        2 runtime count does not match transaction count
        3 missing runtime array pointer for a non-empty transaction list
        4 invalid runtime gas result (`gas_left > tx.gas`)
      a1 = transaction count
      a2 = failing transaction index, 1-based; 0 if not transaction-specific
      a3 = substatus from the failing helper when available

    On success the following aligned arrays are populated for the later verdict
    gate:
      bvgr_tx_gas_limits, bvgr_gas_left, bvgr_refund_counter,
      bvgr_calldata_floor, bvgr_block_gas_increments,
      bvgr_receipt_gas_increments. -/
def blockVerdictGasResultArenaPrepareFunction : String :=
  "block_verdict_gas_result_arena_prepare:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # execution payload\n" ++
  "  mv s1, a1                   # runtime gas_left ptr\n" ++
  "  mv s2, a2                   # runtime refund_counter ptr\n" ++
  "  mv s3, a3                   # runtime calldata_floor ptr\n" ++
  "  mv s4, a4                   # runtime count\n" ++
  "  mv s5, a5                   # arena capacity\n" ++
  "  la t0, bvgr_arena_status; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_arena_tx_count; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_arena_runtime_count; sd s4, 0(t0)\n" ++
  "  la t0, bvgr_arena_fail_index; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_arena_substatus; sd zero, 0(t0)\n" ++
  "  la a1, bvgr_tx_gas_limits\n" ++
  "  mv a2, s5\n" ++
  "  mv a0, s0\n" ++
  "  jal ra, block_verdict_tx_gas_limits\n" ++
  "  bnez a0, .Lbvgr_arena_tx_fail\n" ++
  "  mv s6, a1                   # transaction count\n" ++
  "  la t0, bvgr_arena_tx_count; sd s6, 0(t0)\n" ++
  "  bne s4, s6, .Lbvgr_arena_count_mismatch\n" ++
  "  beqz s6, .Lbvgr_arena_ok\n" ++
  "  beqz s1, .Lbvgr_arena_missing_runtime\n" ++
  "  beqz s2, .Lbvgr_arena_missing_runtime\n" ++
  "  beqz s3, .Lbvgr_arena_missing_runtime\n" ++
  "  mv s7, zero                 # index\n" ++
  ".Lbvgr_arena_loop:\n" ++
  "  beq s7, s6, .Lbvgr_arena_ok\n" ++
  "  slli t0, s7, 3\n" ++
  "  la t1, bvgr_tx_gas_limits; add t1, t1, t0; ld s8, 0(t1)\n" ++
  "  add t1, s1, t0; ld s9, 0(t1)\n" ++
  "  add t1, s2, t0; ld s10, 0(t1)\n" ++
  "  add t1, s3, t0; ld s11, 0(t1)\n" ++
  "  la t1, bvgr_gas_left; add t1, t1, t0; sd s9, 0(t1)\n" ++
  "  la t1, bvgr_refund_counter; add t1, t1, t0; sd s10, 0(t1)\n" ++
  "  la t1, bvgr_calldata_floor; add t1, t1, t0; sd s11, 0(t1)\n" ++
  "  mv a0, s8; mv a1, s9; mv a2, s10; mv a3, s11\n" ++
  "  jal ra, tx_gas_result_increments\n" ++
  "  bnez a0, .Lbvgr_arena_bad_result\n" ++
  "  slli t0, s7, 3\n" ++
  "  la t1, bvgr_block_gas_increments; add t1, t1, t0; sd a1, 0(t1)\n" ++
  "  la t1, bvgr_receipt_gas_increments; add t1, t1, t0; sd a2, 0(t1)\n" ++
  "  la t1, bvgr_before_refund; add t1, t1, t0; sd a3, 0(t1)\n" ++
  "  la t1, bvgr_applied_refund; add t1, t1, t0; sd a4, 0(t1)\n" ++
  "  addi s7, s7, 1\n" ++
  "  j .Lbvgr_arena_loop\n" ++
  ".Lbvgr_arena_ok:\n" ++
  "  li a0, 0; mv a1, s6; li a2, 0; li a3, 0; j .Lbvgr_arena_store_ret\n" ++
  ".Lbvgr_arena_tx_fail:\n" ++
  "  mv t0, a0; mv t1, a1; mv t2, a2\n" ++
  "  li a0, 1; mv a1, t1; mv a2, t2; mv a3, t0; j .Lbvgr_arena_store_ret\n" ++
  ".Lbvgr_arena_count_mismatch:\n" ++
  "  li a0, 2; mv a1, s6; li a2, 0; mv a3, s4; j .Lbvgr_arena_store_ret\n" ++
  ".Lbvgr_arena_missing_runtime:\n" ++
  "  li a0, 3; mv a1, s6; li a2, 0; li a3, 0; j .Lbvgr_arena_store_ret\n" ++
  ".Lbvgr_arena_bad_result:\n" ++
  "  mv t0, a0\n" ++
  "  li a0, 4; mv a1, s6; addi a2, s7, 1; mv a3, t0\n" ++
  ".Lbvgr_arena_store_ret:\n" ++
  "  la t0, bvgr_arena_status; sd a0, 0(t0)\n" ++
  "  la t0, bvgr_arena_tx_count; sd a1, 0(t0)\n" ++
  "  la t0, bvgr_arena_fail_index; sd a2, 0(t0)\n" ++
  "  la t0, bvgr_arena_substatus; sd a3, 0(t0)\n" ++
  ".Lbvgr_arena_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_block_verdict_tx_gas_limits`: focused probe for materializing
    transaction gas limits from an execution payload.

    Input: an execution payload byte array at `INPUT_ADDR + 8`. Output:
      +0  status
      +8  count
      +16 fail index
      +24 last/failed tx type
      +32 first gas limit
      +40 second gas limit -/
def ziskBlockVerdictTxGasLimitsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000008\n" ++
  "  la a1, bvgr_tx_gas_limits\n" ++
  "  li a2, 16\n" ++
  "  jal ra, block_verdict_tx_gas_limits\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0); sd a1, 8(t0); sd a2, 16(t0); sd a3, 24(t0)\n" ++
  "  la t1, bvgr_tx_gas_limits; ld t2, 0(t1); sd t2, 32(t0); ld t2, 8(t1); sd t2, 40(t0)\n" ++
  "  j .Lbvgr_probe_done\n" ++
  bgvU32leFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  blockVerdictTxGasLimitsFunction ++ "\n" ++
  ".Lbvgr_probe_done:"

def ziskBlockVerdictTxGasLimitsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "bvgr_status:\n  .zero 8\n" ++
  "bvgr_count:\n  .zero 8\n" ++
  "bvgr_fail_index:\n  .zero 8\n" ++
  "bvgr_tx_type:\n  .zero 8\n" ++
  "bvgr_tx_inner:\n  .zero 8\n" ++
  "bvgr_nonce:\n  .zero 8\n" ++
  "bvgr_gas:\n  .zero 8\n" ++
  "bvgr_tx_gas_limits:\n  .zero 128\n"

def ziskBlockVerdictTxGasLimitsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockVerdictTxGasLimitsPrologue
  dataAsm     := ziskBlockVerdictTxGasLimitsDataSection
}

/-- `zisk_block_verdict_gas_result_arena`: focused probe for the runtime
    gas-result arena ABI. Input places the execution payload at `INPUT_ADDR+8`
    and runtime result arrays at `INPUT_ADDR+0x1008`:
      +0   count
      +8   gas_left[16]
      +136 refund_counter[16]
      +264 calldata_floor_gas_cost[16]
      +392 block_gas_limit

    Output:
      +0  arena status
      +8  tx count
      +16 runtime count
      +24 fail index
      +32 substatus
      +40 first tx gas
      +48 first block increment
      +56 first receipt increment
      +64 EIP-7778 status
      +72 EIP-7778 failing index
      +80 EIP-7778 used/final-used value
      +88 receipt materializer status
      +96 receipt record count -/
def ziskBlockVerdictGasResultArenaPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40001008\n" ++
  "  li a0, 0x40000008\n" ++
  "  addi a1, s0, 8\n" ++
  "  addi a2, s0, 136\n" ++
  "  addi a3, s0, 264\n" ++
  "  ld a4, 0(s0)\n" ++
  "  li a5, 16\n" ++
  "  jal ra, block_verdict_gas_result_arena_prepare\n" ++
  "  li s1, 0xa0010000\n" ++
  "  sd a0, 0(s1); sd a1, 8(s1)\n" ++
  "  la t0, bvgr_arena_runtime_count; ld t1, 0(t0); sd t1, 16(s1)\n" ++
  "  sd a2, 24(s1); sd a3, 32(s1)\n" ++
  "  la t0, bvgr_tx_gas_limits; ld t1, 0(t0); sd t1, 40(s1)\n" ++
  "  la t0, bvgr_block_gas_increments; ld t1, 0(t0); sd t1, 48(s1)\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t1, 0(t0); sd t1, 56(s1)\n" ++
  "  bnez a0, .Lbvgr_arena_probe_skip_consumers\n" ++
  "  ld a0, 392(s0)              # block_gas_limit\n" ++
  "  la a1, bvgr_tx_gas_limits\n" ++
  "  la a2, bvgr_gas_left\n" ++
  "  la a3, bvgr_refund_counter\n" ++
  "  la a4, bvgr_calldata_floor\n" ++
  "  la t0, bvgr_arena_tx_count; ld a5, 0(t0)\n" ++
  "  la a6, bvgr_block_gas_increments\n" ++
  "  jal ra, eip7778_remaining_block_gas_from_results\n" ++
  "  sd a0, 64(s1); sd a1, 72(s1); sd a2, 80(s1)\n" ++
  "  li a0, 0x40000008\n" ++
  "  la a1, bvgr_receipt_gas_increments\n" ++
  "  la t0, bvgr_arena_tx_count; ld a2, 0(t0)\n" ++
  "  jal ra, block_receipt_records_materialize\n" ++
  "  la t0, brr_status; ld t1, 0(t0); sd t1, 88(s1)\n" ++
  "  la t0, brr_control; ld t1, 0(t0); sd t1, 96(s1)\n" ++
  "  j .Lbvgr_arena_probe_done\n" ++
  ".Lbvgr_arena_probe_skip_consumers:\n" ++
  "  li t0, 255; sd t0, 64(s1); sd t0, 88(s1)\n" ++
  "  j .Lbvgr_arena_probe_done\n" ++
  bgvU32leFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txGasResultIncrementsFunction ++ "\n" ++
  eip7778RemainingBlockGasCheckFunction ++ "\n" ++
  eip7778RemainingBlockGasFromResultsFunction ++ "\n" ++
  receiptRecordsFunction ++ "\n" ++
  blockReceiptRecordsMaterializeFunction ++ "\n" ++
  blockVerdictTxGasLimitsFunction ++ "\n" ++
  blockVerdictGasResultArenaPrepareFunction ++ "\n" ++
  ".Lbvgr_arena_probe_done:"

def ziskBlockVerdictGasResultArenaDataSection : String :=
  ziskBlockVerdictTxGasLimitsDataSection ++
  "bvgr_arena_status:\n  .zero 8\n" ++
  "bvgr_arena_tx_count:\n  .zero 8\n" ++
  "bvgr_arena_runtime_count:\n  .zero 8\n" ++
  "bvgr_arena_fail_index:\n  .zero 8\n" ++
  "bvgr_arena_substatus:\n  .zero 8\n" ++
  "bvgr_gas_left:\n  .zero 128\n" ++
  "bvgr_refund_counter:\n  .zero 128\n" ++
  "bvgr_calldata_floor:\n  .zero 128\n" ++
  "bvgr_block_gas_increments:\n  .zero 128\n" ++
  "bvgr_receipt_gas_increments:\n  .zero 128\n" ++
  "bvgr_before_refund:\n  .zero 128\n" ++
  "bvgr_applied_refund:\n  .zero 128\n" ++
  "brr_status:\n  .zero 8\n" ++
  "brr_append_status:\n  .zero 8\n" ++
  "brr_tx_type:\n  .zero 8\n" ++
  "brr_tx_inner:\n  .zero 8\n" ++
  "brr_tx_gas:\n  .zero 8\n" ++
  "brr_receipt_gas_ptr:\n  .zero 8\n" ++
  "brr_receipt_gas_count:\n  .zero 8\n" ++
  "brr_control:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "brr_records:\n  .zero 1024\n"

def ziskBlockVerdictGasResultArenaProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockVerdictGasResultArenaPrologue
  dataAsm     := ziskBlockVerdictGasResultArenaDataSection
}

end EvmAsm.Codegen
