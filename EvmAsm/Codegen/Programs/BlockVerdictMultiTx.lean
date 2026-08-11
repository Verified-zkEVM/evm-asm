/-
  EvmAsm.Codegen.Programs.BlockVerdictMultiTx

  Per-INDEX transaction context extractor for the multi-transaction dispatch
  spine (evm-asm-fhsxz.2.4.2.57.11.6). `simple_transfer_tx_context` only
  supports a single-transaction block (it bails when bv_tx_count != 1). This
  helper extracts the i-th transaction of an N-transaction SSZ transaction
  list, materializing the same 192-byte per-transaction context record so a
  multi-tx dispatch loop can run each transaction through the runtime.

  The SSZ `transactions` list is a list of variable-length elements: a u32
  little-endian offset table (4 bytes per element) followed by the concatenated
  element bytes. The element count is offset[0] / 4, and element i spans
  [offset[i], offset[i+1]) (the final element ends at the list length). This is
  the same encoding walked by block_receipt_records_materialize
  (BlockVerdictReceiptRecords.lean). Once tx[i]'s [ptr,len) is located, the
  extraction tail is identical to simple_transfer_tx_context.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## multi_tx_nth_context

    Extract the i-th transaction of the SSZ transaction list prepared by
    block_verdict into a 192-byte per-transaction context record.

    Calling convention:
      a0 = output record ptr (same 192-byte layout as simple_transfer_tx_context;
           see BlockVerdictSimpleTransfer.lean for field offsets)
      a1 = transaction index i

    Reads bv_tx_list_ptr / bv_tx_list_len. Unlike simple_transfer_tx_context it
    does NOT read bv_tx_count / bv_tx_item_start / bv_public_keys_* / bv_exec_p:
    sender public key (record +24) and base_fee (record +32) are per-call inputs
    supplied by the multi-tx dispatch loop, so this helper leaves them zero and
    populates only the transaction-intrinsic fields.

    Status (record +0):
      0  ok: classified creation or non-creation, legacy/2930/1559/blob/7702 tx
      3  malformed transaction list (too short / offset table not 4-aligned /
         offset out of range)
      4  transaction item is empty
      5  index >= transaction count
      20 type dispatch or nonce/gas extraction failed
      21 type inner offset exceeds tx length
      30 to-address extraction failed
      40 value extraction failed
      50 data-section extraction failed
      60 reserved (formerly contract creation transaction)
      61 reserved (formerly non-empty calldata/initcode)
      62 reserved (formerly EIP-4844 blob unsupported)
      63 reserved (formerly EIP-7702 set-code unsupported) -/
def multiTxNthContext_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x20 .x11,
    .MV .x5 .x8,
    .LI .x6 (24 : Word),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.bv_tx_list_ptr (GuestAddrs.multi_tx_nth_context + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_tx_list_ptr (GuestAddrs.multi_tx_nth_context + 72)),
    .LD .x9 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_tx_list_len (GuestAddrs.multi_tx_nth_context + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_tx_list_len (GuestAddrs.multi_tx_nth_context + 84)),
    .LD .x18 .x5 (0 : BitVec 12),
    .LI .x5 (4 : Word),
    .BLTU .x18 .x5 (brOff (GuestAddrs.multi_tx_nth_context + 476) (GuestAddrs.multi_tx_nth_context + 100)),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.multi_tx_nth_context + 108)),
    .ANDI .x5 .x10 (3 : BitVec 12),
    .BNE .x5 .x0 (brOff (GuestAddrs.multi_tx_nth_context + 476) (GuestAddrs.multi_tx_nth_context + 116)),
    .SRLI .x19 .x10 (2 : BitVec 6),
    .BGEU .x20 .x19 (brOff (GuestAddrs.multi_tx_nth_context + 488) (GuestAddrs.multi_tx_nth_context + 124)),
    .SLLI .x5 .x20 (2 : BitVec 6),
    .ADD .x10 .x9 .x5,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.multi_tx_nth_context + 136)),
    .MV .x21 .x10,
    .ADDI .x5 .x20 (1 : BitVec 12),
    .BEQ .x5 .x19 (24 : BitVec 13),
    .SLLI .x6 .x5 (2 : BitVec 6),
    .ADD .x10 .x9 .x6,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.multi_tx_nth_context + 160)),
    .MV .x22 .x10,
    .JAL .x0 (8 : BitVec 21),
    .MV .x22 .x18,
    .SLLI .x5 .x19 (2 : BitVec 6),
    .BLTU .x21 .x5 (brOff (GuestAddrs.multi_tx_nth_context + 476) (GuestAddrs.multi_tx_nth_context + 180)),
    .BLTU .x22 .x21 (brOff (GuestAddrs.multi_tx_nth_context + 476) (GuestAddrs.multi_tx_nth_context + 184)),
    .BLTU .x18 .x22 (brOff (GuestAddrs.multi_tx_nth_context + 476) (GuestAddrs.multi_tx_nth_context + 188)),
    .ADD .x9 .x9 .x21,
    .SUB .x18 .x22 .x21,
    .BEQ .x18 .x0 (brOff (GuestAddrs.multi_tx_nth_context + 500) (GuestAddrs.multi_tx_nth_context + 200)),
    .SD .x8 .x9 (8 : BitVec 12),
    .SD .x8 .x18 (16 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .AUIPC .x12 (laHi GuestAddrs.tea_type (GuestAddrs.multi_tx_nth_context + 220)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tea_type (GuestAddrs.multi_tx_nth_context + 220)),
    .AUIPC .x13 (laHi GuestAddrs.tea_inner_off (GuestAddrs.multi_tx_nth_context + 228)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tea_inner_off (GuestAddrs.multi_tx_nth_context + 228)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.multi_tx_nth_context + 236)),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (20 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.multi_tx_nth_context + 520) (GuestAddrs.multi_tx_nth_context + 252)),
    .AUIPC .x5 (laHi GuestAddrs.tea_type (GuestAddrs.multi_tx_nth_context + 256)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tea_type (GuestAddrs.multi_tx_nth_context + 256)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x8 .x6 (160 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tea_inner_off (GuestAddrs.multi_tx_nth_context + 272)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tea_inner_off (GuestAddrs.multi_tx_nth_context + 272)),
    .LD .x28 .x5 (0 : BitVec 12),
    .SD .x8 .x28 (168 : BitVec 12),
    .BLTU .x18 .x28 (brOff (GuestAddrs.multi_tx_nth_context + 512) (GuestAddrs.multi_tx_nth_context + 288)),
    .ADD .x29 .x9 .x28,
    .SD .x8 .x29 (176 : BitVec 12),
    .SUB .x29 .x18 .x28,
    .SD .x8 .x29 (184 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .AUIPC .x12 (laHi GuestAddrs.sttc_nonce (GuestAddrs.multi_tx_nth_context + 316)),
    .ADDI .x12 .x12 (laLo GuestAddrs.sttc_nonce (GuestAddrs.multi_tx_nth_context + 316)),
    .ADDI .x13 .x8 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_extract_nonce_and_gas (GuestAddrs.multi_tx_nth_context + 328)),
    .SD .x8 .x10 (128 : BitVec 12),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (20 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.multi_tx_nth_context + 520) (GuestAddrs.multi_tx_nth_context + 348)),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .ADDI .x12 .x8 (72 : BitVec 12),
    .ADDI .x13 .x8 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_extract_to_address (GuestAddrs.multi_tx_nth_context + 368)),
    .SD .x8 .x10 (136 : BitVec 12),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (30 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.multi_tx_nth_context + 520) (GuestAddrs.multi_tx_nth_context + 388)),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .ADDI .x12 .x8 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_extract_value (GuestAddrs.multi_tx_nth_context + 404)),
    .SD .x8 .x10 (144 : BitVec 12),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (40 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.multi_tx_nth_context + 520) (GuestAddrs.multi_tx_nth_context + 424)),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .ADDI .x12 .x8 (56 : BitVec 12),
    .ADDI .x13 .x8 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_extract_data_section (GuestAddrs.multi_tx_nth_context + 444)),
    .SD .x8 .x10 (152 : BitVec 12),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (50 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (56 : BitVec 21),
    .SD .x8 .x0 (0 : BitVec 12),
    .JAL .x0 (48 : BitVec 21),
    .LI .x5 (3 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (36 : BitVec 21),
    .LI .x5 (5 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (24 : BitVec 21),
    .LI .x5 (4 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .LI .x5 (21 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `multiTxNthContext_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def multiTxNthContext_relocs : RelocTable :=
  [ (18, .la .x5 "bv_tx_list_ptr"),
    (21, .la .x5 "bv_tx_list_len"),
    (27, .jal .x1 "bgv_u32le"),
    (34, .jal .x1 "bgv_u32le"),
    (40, .jal .x1 "bgv_u32le"),
    (55, .la .x12 "tea_type"),
    (57, .la .x13 "tea_inner_off"),
    (59, .jal .x1 "tx_type_dispatch"),
    (64, .la .x5 "tea_type"),
    (68, .la .x5 "tea_inner_off"),
    (79, .la .x12 "sttc_nonce"),
    (82, .jal .x1 "tx_extract_nonce_and_gas"),
    (92, .jal .x1 "tx_extract_to_address"),
    (101, .jal .x1 "tx_extract_value"),
    (111, .jal .x1 "tx_extract_data_section") ]

def multiTxNthContextFunction : String :=
  "multi_tx_nth_context:\n" ++ emitProgramR multiTxNthContext_prog multiTxNthContext_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `multiTxNthContext_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem multiTxNthContextFunction_eq_prog :
    multiTxNthContextFunction = "multi_tx_nth_context:\n" ++ emitProgramR multiTxNthContext_prog multiTxNthContext_relocs := rfl

#guard multiTxNthContextFunction.startsWith "multi_tx_nth_context:\n"
#guard multiTxNthContext_prog.length = 140
/-- `zisk_multi_tx_nth_context`: focused probe for the per-index extractor.
    Input at INPUT_ADDR (0x40000000):
      +8   tx_list_len
      +16  transaction index i
      +640 SSZ transaction-list bytes (u32 offset table + concatenated txs)
    Output at 0xa0010000: the 192-byte multi_tx_nth_context record. -/
def ziskMultiTxNthContextPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  addi t0, s0, 640; la t1, bv_tx_list_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 8(s0); la t1, bv_tx_list_len; sd t0, 0(t1)\n" ++
  "  ld a1, 16(s0)               # transaction index\n" ++
  "  li a0, 0xa0010000\n" ++
  "  jal ra, multi_tx_nth_context\n" ++
  "  j .Lmtxp_done\n" ++
  bgvU32leFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txExtractValueFunction ++ "\n" ++
  txExtractDataSectionFunction ++ "\n" ++
  multiTxNthContextFunction ++ "\n" ++
  ".Lmtxp_done:"

def ziskMultiTxNthContextDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bv_tx_list_ptr:\n  .zero 8\n" ++
  "bv_tx_list_len:\n  .zero 8\n" ++
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  blockVerdictSimpleTransferDataSection

def ziskMultiTxNthContextProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMultiTxNthContextPrologue
  dataAsm     := ziskMultiTxNthContextDataSection
}

end EvmAsm.Codegen
