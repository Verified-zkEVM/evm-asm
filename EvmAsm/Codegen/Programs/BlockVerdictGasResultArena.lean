/-
  EvmAsm.Codegen.Programs.BlockVerdictGasResultArena

  Transaction gas-result helpers for the stateless block verdict path.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.BlockGasRemaining
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords
import EvmAsm.Codegen.Programs.TxExtract

import EvmAsm.Codegen.Programs.BlockVerdictTxGasLimits

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

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
def blockVerdictGasResultArenaPrepare_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
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
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .AUIPC .x5 (laHi GuestAddrs.bvgr_arena_status (GuestAddrs.block_verdict_gas_result_arena_prepare + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_arena_status (GuestAddrs.block_verdict_gas_result_arena_prepare + 80)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_arena_tx_count (GuestAddrs.block_verdict_gas_result_arena_prepare + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_arena_tx_count (GuestAddrs.block_verdict_gas_result_arena_prepare + 92)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_arena_runtime_count (GuestAddrs.block_verdict_gas_result_arena_prepare + 104)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_arena_runtime_count (GuestAddrs.block_verdict_gas_result_arena_prepare + 104)),
    .SD .x5 .x20 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_arena_fail_index (GuestAddrs.block_verdict_gas_result_arena_prepare + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_arena_fail_index (GuestAddrs.block_verdict_gas_result_arena_prepare + 116)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_arena_substatus (GuestAddrs.block_verdict_gas_result_arena_prepare + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_arena_substatus (GuestAddrs.block_verdict_gas_result_arena_prepare + 128)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.bvgr_tx_gas_limits (GuestAddrs.block_verdict_gas_result_arena_prepare + 140)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bvgr_tx_gas_limits (GuestAddrs.block_verdict_gas_result_arena_prepare + 140)),
    .MV .x12 .x21,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.block_verdict_tx_gas_limits (GuestAddrs.block_verdict_gas_result_arena_prepare + 156)),
    .BNE .x10 .x0 (brOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 420) (GuestAddrs.block_verdict_gas_result_arena_prepare + 160)),
    .MV .x22 .x11,
    .AUIPC .x5 (laHi GuestAddrs.bvgr_arena_tx_count (GuestAddrs.block_verdict_gas_result_arena_prepare + 168)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_arena_tx_count (GuestAddrs.block_verdict_gas_result_arena_prepare + 168)),
    .SD .x5 .x22 (0 : BitVec 12),
    .BNE .x20 .x22 (brOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 452) (GuestAddrs.block_verdict_gas_result_arena_prepare + 180)),
    .BEQ .x22 .x0 (brOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 400) (GuestAddrs.block_verdict_gas_result_arena_prepare + 184)),
    .BEQ .x9 .x0 (brOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 472) (GuestAddrs.block_verdict_gas_result_arena_prepare + 188)),
    .BEQ .x18 .x0 (brOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 472) (GuestAddrs.block_verdict_gas_result_arena_prepare + 192)),
    .BEQ .x19 .x0 (brOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 472) (GuestAddrs.block_verdict_gas_result_arena_prepare + 196)),
    .MV .x23 .x0,
    .BEQ .x23 .x22 (brOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 400) (GuestAddrs.block_verdict_gas_result_arena_prepare + 204)),
    .SLLI .x5 .x23 (3 : BitVec 6),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_tx_gas_limits (GuestAddrs.block_verdict_gas_result_arena_prepare + 212)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_tx_gas_limits (GuestAddrs.block_verdict_gas_result_arena_prepare + 212)),
    .ADD .x6 .x6 .x5,
    .LD .x24 .x6 (0 : BitVec 12),
    .ADD .x6 .x9 .x5,
    .LD .x25 .x6 (0 : BitVec 12),
    .ADD .x6 .x18 .x5,
    .LD .x26 .x6 (0 : BitVec 12),
    .ADD .x6 .x19 .x5,
    .LD .x27 .x6 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_gas_left (GuestAddrs.block_verdict_gas_result_arena_prepare + 252)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_gas_left (GuestAddrs.block_verdict_gas_result_arena_prepare + 252)),
    .ADD .x6 .x6 .x5,
    .SD .x6 .x25 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_refund_counter (GuestAddrs.block_verdict_gas_result_arena_prepare + 268)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_refund_counter (GuestAddrs.block_verdict_gas_result_arena_prepare + 268)),
    .ADD .x6 .x6 .x5,
    .SD .x6 .x26 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_calldata_floor (GuestAddrs.block_verdict_gas_result_arena_prepare + 284)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_calldata_floor (GuestAddrs.block_verdict_gas_result_arena_prepare + 284)),
    .ADD .x6 .x6 .x5,
    .SD .x6 .x27 (0 : BitVec 12),
    .MV .x10 .x24,
    .MV .x11 .x25,
    .MV .x12 .x26,
    .MV .x13 .x27,
    .JAL .x1 (jalOff GuestAddrs.tx_gas_result_increments (GuestAddrs.block_verdict_gas_result_arena_prepare + 316)),
    .BNE .x10 .x0 (brOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 492) (GuestAddrs.block_verdict_gas_result_arena_prepare + 320)),
    .SLLI .x5 .x23 (3 : BitVec 6),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_block_gas_increments (GuestAddrs.block_verdict_gas_result_arena_prepare + 328)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_block_gas_increments (GuestAddrs.block_verdict_gas_result_arena_prepare + 328)),
    .ADD .x6 .x6 .x5,
    .SD .x6 .x11 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_receipt_gas_increments (GuestAddrs.block_verdict_gas_result_arena_prepare + 344)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_receipt_gas_increments (GuestAddrs.block_verdict_gas_result_arena_prepare + 344)),
    .ADD .x6 .x6 .x5,
    .SD .x6 .x12 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_before_refund (GuestAddrs.block_verdict_gas_result_arena_prepare + 360)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_before_refund (GuestAddrs.block_verdict_gas_result_arena_prepare + 360)),
    .ADD .x6 .x6 .x5,
    .SD .x6 .x13 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_applied_refund (GuestAddrs.block_verdict_gas_result_arena_prepare + 376)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_applied_refund (GuestAddrs.block_verdict_gas_result_arena_prepare + 376)),
    .ADD .x6 .x6 .x5,
    .SD .x6 .x14 (0 : BitVec 12),
    .ADDI .x23 .x23 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 204) (GuestAddrs.block_verdict_gas_result_arena_prepare + 396)),
    .LI .x10 (0 : Word),
    .MV .x11 .x22,
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 512) (GuestAddrs.block_verdict_gas_result_arena_prepare + 416)),
    .MV .x5 .x10,
    .MV .x6 .x11,
    .MV .x7 .x12,
    .LI .x10 (1 : Word),
    .MV .x11 .x6,
    .MV .x12 .x7,
    .MV .x13 .x5,
    .JAL .x0 (jalOff (GuestAddrs.block_verdict_gas_result_arena_prepare + 512) (GuestAddrs.block_verdict_gas_result_arena_prepare + 448)),
    .LI .x10 (2 : Word),
    .MV .x11 .x22,
    .LI .x12 (0 : Word),
    .MV .x13 .x20,
    .JAL .x0 (44 : BitVec 21),
    .LI .x10 (3 : Word),
    .MV .x11 .x22,
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .MV .x5 .x10,
    .LI .x10 (4 : Word),
    .MV .x11 .x22,
    .ADDI .x12 .x23 (1 : BitVec 12),
    .MV .x13 .x5,
    .AUIPC .x5 (laHi GuestAddrs.bvgr_arena_status (GuestAddrs.block_verdict_gas_result_arena_prepare + 512)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_arena_status (GuestAddrs.block_verdict_gas_result_arena_prepare + 512)),
    .SD .x5 .x10 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_arena_tx_count (GuestAddrs.block_verdict_gas_result_arena_prepare + 524)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_arena_tx_count (GuestAddrs.block_verdict_gas_result_arena_prepare + 524)),
    .SD .x5 .x11 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_arena_fail_index (GuestAddrs.block_verdict_gas_result_arena_prepare + 536)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_arena_fail_index (GuestAddrs.block_verdict_gas_result_arena_prepare + 536)),
    .SD .x5 .x12 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_arena_substatus (GuestAddrs.block_verdict_gas_result_arena_prepare + 548)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_arena_substatus (GuestAddrs.block_verdict_gas_result_arena_prepare + 548)),
    .SD .x5 .x13 (0 : BitVec 12),
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
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockVerdictGasResultArenaPrepare_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockVerdictGasResultArenaPrepare_relocs : RelocTable :=
  [ (20, .la .x5 "bvgr_arena_status"),
    (23, .la .x5 "bvgr_arena_tx_count"),
    (26, .la .x5 "bvgr_arena_runtime_count"),
    (29, .la .x5 "bvgr_arena_fail_index"),
    (32, .la .x5 "bvgr_arena_substatus"),
    (35, .la .x11 "bvgr_tx_gas_limits"),
    (39, .jal .x1 "block_verdict_tx_gas_limits"),
    (42, .la .x5 "bvgr_arena_tx_count"),
    (53, .la .x6 "bvgr_tx_gas_limits"),
    (63, .la .x6 "bvgr_gas_left"),
    (67, .la .x6 "bvgr_refund_counter"),
    (71, .la .x6 "bvgr_calldata_floor"),
    (79, .jal .x1 "tx_gas_result_increments"),
    (82, .la .x6 "bvgr_block_gas_increments"),
    (86, .la .x6 "bvgr_receipt_gas_increments"),
    (90, .la .x6 "bvgr_before_refund"),
    (94, .la .x6 "bvgr_applied_refund"),
    (128, .la .x5 "bvgr_arena_status"),
    (131, .la .x5 "bvgr_arena_tx_count"),
    (134, .la .x5 "bvgr_arena_fail_index"),
    (137, .la .x5 "bvgr_arena_substatus") ]

def blockVerdictGasResultArenaPrepareFunction : String :=
  "block_verdict_gas_result_arena_prepare:\n" ++ emitProgramR blockVerdictGasResultArenaPrepare_prog blockVerdictGasResultArenaPrepare_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockVerdictGasResultArenaPrepare_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockVerdictGasResultArenaPrepareFunction_eq_prog :
    blockVerdictGasResultArenaPrepareFunction = "block_verdict_gas_result_arena_prepare:\n" ++ emitProgramR blockVerdictGasResultArenaPrepare_prog blockVerdictGasResultArenaPrepare_relocs := rfl

#guard blockVerdictGasResultArenaPrepareFunction.startsWith "block_verdict_gas_result_arena_prepare:\n"
#guard blockVerdictGasResultArenaPrepare_prog.length = 155
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
  "  li a5, " ++ toString bmvFixtureTxCapacity ++ "\n" ++
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
  "  li a7, 0                    # .6.5.2: probe consumer -> legacy 1D (no intrinsic_state array)\n" ++
  "  jal ra, eip7778_remaining_block_gas_from_results\n" ++
  "  sd a0, 64(s1); sd a1, 72(s1); sd a2, 80(s1)\n" ++
  "  li a0, 0x40000008\n" ++
  "  la a1, bvgr_receipt_gas_increments\n" ++
  "  la t0, bvgr_arena_tx_count; ld a2, 0(t0)\n" ++
  "  li a3, 0\n" ++   -- gas-only probe: record every tx as successful
  "  li a4, 0\n" ++   -- gas-only probe: empty log windows
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
  "bvgr_gas_left:\n  .zero " ++ toString bmvFixtureU64PerTxArenaBytes ++ "\n" ++
  "bvgr_refund_counter:\n  .zero " ++ toString bmvFixtureU64PerTxArenaBytes ++ "\n" ++
  "bvgr_calldata_floor:\n  .zero " ++ toString bmvFixtureU64PerTxArenaBytes ++ "\n" ++
  "bvgr_block_gas_increments:\n  .zero " ++ toString bmvFixtureU64PerTxArenaBytes ++ "\n" ++
  "bvgr_receipt_gas_increments:\n  .zero " ++ toString bmvFixtureU64PerTxArenaBytes ++ "\n" ++
  "bvgr_before_refund:\n  .zero " ++ toString bmvFixtureU64PerTxArenaBytes ++ "\n" ++
  "bvgr_applied_refund:\n  .zero " ++ toString bmvFixtureU64PerTxArenaBytes ++ "\n" ++
  "brr_status:\n  .zero 8\n" ++
  "brr_append_status:\n  .zero 8\n" ++
  "brr_tx_type:\n  .zero 8\n" ++
  "brr_tx_inner:\n  .zero 8\n" ++
  "brr_tx_gas:\n  .zero 8\n" ++
  "brr_receipt_gas_ptr:\n  .zero 8\n" ++
  "brr_tx_status_ptr:\n  .zero 8\n" ++
  "brr_tx_window_ptr:\n  .zero 8\n" ++
  "brr_receipt_gas_count:\n  .zero 8\n" ++
  "brr_control:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "brr_records:\n  .zero 1024\n"


end EvmAsm.Codegen
