/-
  EvmAsm.Codegen.Programs.BlockVerdictTxGasLimits

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
def blockVerdictTxGasLimits_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.bvgr_status (GuestAddrs.block_verdict_tx_gas_limits + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_status (GuestAddrs.block_verdict_tx_gas_limits + 68)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_count (GuestAddrs.block_verdict_tx_gas_limits + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_count (GuestAddrs.block_verdict_tx_gas_limits + 80)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_fail_index (GuestAddrs.block_verdict_tx_gas_limits + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_fail_index (GuestAddrs.block_verdict_tx_gas_limits + 92)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 104)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 104)),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x10 .x8 (504 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_gas_limits + 120)),
    .MV .x19 .x10,
    .ADDI .x10 .x8 (508 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_gas_limits + 132)),
    .MV .x20 .x10,
    .BGEU .x19 .x20 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 392) (GuestAddrs.block_verdict_tx_gas_limits + 140)),
    .ADD .x21 .x8 .x19,
    .SUB .x22 .x20 .x19,
    .LI .x5 (4 : Word),
    .BLTU .x22 .x5 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 440) (GuestAddrs.block_verdict_tx_gas_limits + 156)),
    .MV .x10 .x21,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_gas_limits + 164)),
    .ANDI .x5 .x10 (3 : BitVec 12),
    .BNE .x5 .x0 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 440) (GuestAddrs.block_verdict_tx_gas_limits + 172)),
    .BLTU .x22 .x10 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 440) (GuestAddrs.block_verdict_tx_gas_limits + 176)),
    .SRLI .x23 .x10 (2 : BitVec 6),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_count (GuestAddrs.block_verdict_tx_gas_limits + 184)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_count (GuestAddrs.block_verdict_tx_gas_limits + 184)),
    .SD .x5 .x23 (0 : BitVec 12),
    .BLTU .x18 .x23 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 460) (GuestAddrs.block_verdict_tx_gas_limits + 196)),
    .BEQ .x23 .x0 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 396) (GuestAddrs.block_verdict_tx_gas_limits + 200)),
    .MV .x24 .x0,
    .SLLI .x27 .x23 (2 : BitVec 6),
    .BEQ .x24 .x23 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 396) (GuestAddrs.block_verdict_tx_gas_limits + 212)),
    .SLLI .x5 .x24 (2 : BitVec 6),
    .ADD .x10 .x21 .x5,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_gas_limits + 224)),
    .MV .x25 .x10,
    .BLTU .x25 .x27 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 424) (GuestAddrs.block_verdict_tx_gas_limits + 232)),
    .BLTU .x22 .x25 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 424) (GuestAddrs.block_verdict_tx_gas_limits + 236)),
    .ADDI .x5 .x24 (1 : BitVec 12),
    .BEQ .x5 .x23 (24 : BitVec 13),
    .SLLI .x6 .x5 (2 : BitVec 6),
    .ADD .x10 .x21 .x6,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.block_verdict_tx_gas_limits + 256)),
    .MV .x26 .x10,
    .JAL .x0 (8 : BitVec 21),
    .MV .x26 .x22,
    .BLTU .x26 .x25 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 424) (GuestAddrs.block_verdict_tx_gas_limits + 272)),
    .BLTU .x22 .x26 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 424) (GuestAddrs.block_verdict_tx_gas_limits + 276)),
    .ADD .x5 .x21 .x25,
    .SUB .x6 .x26 .x25,
    .MV .x10 .x5,
    .MV .x11 .x6,
    .AUIPC .x12 (laHi GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 296)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 296)),
    .AUIPC .x13 (laHi GuestAddrs.bvgr_tx_inner (GuestAddrs.block_verdict_tx_gas_limits + 304)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bvgr_tx_inner (GuestAddrs.block_verdict_tx_gas_limits + 304)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.block_verdict_tx_gas_limits + 312)),
    .BNE .x10 .x0 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 480) (GuestAddrs.block_verdict_tx_gas_limits + 316)),
    .ADD .x5 .x21 .x25,
    .SUB .x6 .x26 .x25,
    .MV .x10 .x5,
    .MV .x11 .x6,
    .AUIPC .x12 (laHi GuestAddrs.bvgr_nonce (GuestAddrs.block_verdict_tx_gas_limits + 336)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bvgr_nonce (GuestAddrs.block_verdict_tx_gas_limits + 336)),
    .AUIPC .x13 (laHi GuestAddrs.bvgr_gas (GuestAddrs.block_verdict_tx_gas_limits + 344)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bvgr_gas (GuestAddrs.block_verdict_tx_gas_limits + 344)),
    .JAL .x1 (jalOff GuestAddrs.tx_extract_nonce_and_gas (GuestAddrs.block_verdict_tx_gas_limits + 352)),
    .BNE .x10 .x0 (brOff (GuestAddrs.block_verdict_tx_gas_limits + 508) (GuestAddrs.block_verdict_tx_gas_limits + 356)),
    .SLLI .x5 .x24 (3 : BitVec 6),
    .ADD .x6 .x9 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bvgr_gas (GuestAddrs.block_verdict_tx_gas_limits + 368)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bvgr_gas (GuestAddrs.block_verdict_tx_gas_limits + 368)),
    .LD .x28 .x7 (0 : BitVec 12),
    .SD .x6 .x28 (0 : BitVec 12),
    .ADDI .x24 .x24 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.block_verdict_tx_gas_limits + 212) (GuestAddrs.block_verdict_tx_gas_limits + 388)),
    .MV .x23 .x0,
    .LI .x10 (0 : Word),
    .MV .x11 .x23,
    .LI .x12 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 408)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 408)),
    .LD .x13 .x5 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.block_verdict_tx_gas_limits + 532) (GuestAddrs.block_verdict_tx_gas_limits + 420)),
    .ADDI .x12 .x24 (1 : BitVec 12),
    .LI .x10 (1 : Word),
    .MV .x11 .x23,
    .JAL .x0 (jalOff (GuestAddrs.block_verdict_tx_gas_limits + 532) (GuestAddrs.block_verdict_tx_gas_limits + 436)),
    .LI .x10 (1 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.block_verdict_tx_gas_limits + 532) (GuestAddrs.block_verdict_tx_gas_limits + 456)),
    .LI .x10 (2 : Word),
    .MV .x11 .x23,
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .JAL .x0 (56 : BitVec 21),
    .LI .x10 (3 : Word),
    .MV .x11 .x23,
    .ADDI .x12 .x24 (1 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 492)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 492)),
    .LD .x13 .x5 (0 : BitVec 12),
    .JAL .x0 (28 : BitVec 21),
    .LI .x10 (4 : Word),
    .MV .x11 .x23,
    .ADDI .x12 .x24 (1 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 520)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 520)),
    .LD .x13 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_status (GuestAddrs.block_verdict_tx_gas_limits + 532)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_status (GuestAddrs.block_verdict_tx_gas_limits + 532)),
    .SD .x5 .x10 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_count (GuestAddrs.block_verdict_tx_gas_limits + 544)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_count (GuestAddrs.block_verdict_tx_gas_limits + 544)),
    .SD .x5 .x11 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_fail_index (GuestAddrs.block_verdict_tx_gas_limits + 556)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_fail_index (GuestAddrs.block_verdict_tx_gas_limits + 556)),
    .SD .x5 .x12 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 568)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_tx_type (GuestAddrs.block_verdict_tx_gas_limits + 568)),
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

/-- Reloc side-table for `blockVerdictTxGasLimits_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockVerdictTxGasLimits_relocs : RelocTable :=
  [ (17, .la .x5 "bvgr_status"),
    (20, .la .x5 "bvgr_count"),
    (23, .la .x5 "bvgr_fail_index"),
    (26, .la .x5 "bvgr_tx_type"),
    (30, .jal .x1 "bgv_u32le"),
    (33, .jal .x1 "bgv_u32le"),
    (41, .jal .x1 "bgv_u32le"),
    (46, .la .x5 "bvgr_count"),
    (56, .jal .x1 "bgv_u32le"),
    (64, .jal .x1 "bgv_u32le"),
    (74, .la .x12 "bvgr_tx_type"),
    (76, .la .x13 "bvgr_tx_inner"),
    (78, .jal .x1 "tx_type_dispatch"),
    (84, .la .x12 "bvgr_nonce"),
    (86, .la .x13 "bvgr_gas"),
    (88, .jal .x1 "tx_extract_nonce_and_gas"),
    (92, .la .x7 "bvgr_gas"),
    (102, .la .x5 "bvgr_tx_type"),
    (123, .la .x5 "bvgr_tx_type"),
    (130, .la .x5 "bvgr_tx_type"),
    (133, .la .x5 "bvgr_status"),
    (136, .la .x5 "bvgr_count"),
    (139, .la .x5 "bvgr_fail_index"),
    (142, .la .x5 "bvgr_tx_type") ]

def blockVerdictTxGasLimitsFunction : String :=
  "block_verdict_tx_gas_limits:\n" ++ emitProgramR blockVerdictTxGasLimits_prog blockVerdictTxGasLimits_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockVerdictTxGasLimits_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockVerdictTxGasLimitsFunction_eq_prog :
    blockVerdictTxGasLimitsFunction = "block_verdict_tx_gas_limits:\n" ++ emitProgramR blockVerdictTxGasLimits_prog blockVerdictTxGasLimits_relocs := rfl

#guard blockVerdictTxGasLimitsFunction.startsWith "block_verdict_tx_gas_limits:\n"
#guard blockVerdictTxGasLimits_prog.length = 160
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
  "  li a2, " ++ toString bmvFixtureTxCapacity ++ "\n" ++
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
  "bvgr_tx_gas_limits:\n  .zero " ++ toString bmvFixtureU64PerTxArenaBytes ++ "\n"

def ziskBlockVerdictTxGasLimitsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockVerdictTxGasLimitsPrologue
  dataAsm     := ziskBlockVerdictTxGasLimitsDataSection
}


end EvmAsm.Codegen
