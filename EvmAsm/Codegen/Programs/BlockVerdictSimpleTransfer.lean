/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer

  Shared extraction helper for the parse-supported one-transaction simple
  value-transfer path used by block_verdict.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- #10685: `simple_transfer_tx_context` unlinked from guest (0 inbound, prev ends
    `jalr x0,0(x1)`). Probe-only Program keeps local address placeholders so
    `laHi`/`laLo`/`jalOff` still elaborate; drift is covered by
    `simpleTransferTxContextFunction_eq_prog`. Entry is a dummy PC; data/callee
    addrs match the current guest TSV (still live for MTx string paths). -/
private def simpleTransferTxContextPc : Nat := 0x80000000
private def sttc_bv_tx_count : Nat := 0xa5ca03f0
private def sttc_bv_public_keys_len : Nat := 0xa5ca0410
private def sttc_bv_public_keys_ptr : Nat := 0xa5ca0408
private def sttc_bv_tx_item_start : Nat := 0xa5ca0400
private def sttc_bv_tx_list_ptr : Nat := 0xa5ca03e0
private def sttc_bv_tx_list_len : Nat := 0xa5ca03e8
private def sttc_bv_exec_p : Nat := 0xa5ca02b0
private def sttc_sttc_nonce : Nat := 0xab960788
private def sttc_sttc_base_fee_be : Nat := 0xab960840
private def sttc_tea_type : Nat := 0xab960790
private def sttc_tea_inner_off : Nat := 0xab960798
private def sttc_tx_extract_data_section : Nat := 0x8001d038
private def sttc_tx_extract_value : Nat := 0x8001cdc0
private def sttc_tx_extract_to_address : Nat := 0x8001cb68
private def sttc_tx_extract_nonce_and_gas : Nat := 0x8002d29c
private def sttc_tx_type_dispatch : Nat := 0x8001c37c


/-! ## simple_transfer_tx_context

    Read the transaction-list/public-key globals prepared by block_verdict and
    materialize the stable per-transaction context needed by later BAL
    descriptor writers.

    Calling convention:
      a0 = output ptr

    Reads:
      bv_tx_count, bv_tx_list_ptr, bv_tx_list_len, bv_tx_item_start,
      bv_public_keys_ptr, bv_public_keys_len, bv_exec_p.

    Output:
      +0   status
             0  ok: single tx, 65-byte pubkey, classified creation or non-creation,
                legacy/2930/1559/blob/7702 tx
             1  transaction count is not exactly one
             2  public key bundle is not exactly 65 bytes
             3  tx item start exceeds tx list length
             4  tx item is empty
             20 nonce/gas extraction failed
             21 type inner offset exceeds tx length
             30 to-address extraction failed
             40 value extraction failed
             50 data-section extraction failed
             60 reserved (formerly contract creation transaction)
             61 reserved (formerly non-empty calldata/initcode)
             62 reserved (formerly EIP-4844 blob unsupported)
             63 reserved (formerly EIP-7702 set-code unsupported)
      +8   tx ptr
      +16  tx len
      +24  selected pubkey ptr (64-byte x||y tail)
      +32  base_fee_per_gas ptr (32-byte BE scratch)
      +40  tx gas limit u64
      +48  is_creation flag
      +56  data ptr
      +64  data len
      +72  recipient address, 20 bytes
      +96  value, 32-byte BE
      +128 nonce/gas extractor status
      +136 to-address extractor status
      +144 value extractor status
      +152 data-section extractor status
      +160 tx type (0 legacy, 1 EIP-2930, 2 EIP-1559, 3 EIP-4844,
           4 EIP-7702)
      +168 tx inner offset
      +176 tx inner ptr
      +184 tx inner len
-/
def simpleTransferTxContext_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .SD .x8 .x0 (0 : BitVec 12),
    .SD .x8 .x0 (8 : BitVec 12),
    .SD .x8 .x0 (16 : BitVec 12),
    .SD .x8 .x0 (24 : BitVec 12),
    .SD .x8 .x0 (32 : BitVec 12),
    .SD .x8 .x0 (40 : BitVec 12),
    .SD .x8 .x0 (48 : BitVec 12),
    .SD .x8 .x0 (56 : BitVec 12),
    .SD .x8 .x0 (64 : BitVec 12),
    .SD .x8 .x0 (72 : BitVec 12),
    .SD .x8 .x0 (80 : BitVec 12),
    .SD .x8 .x0 (88 : BitVec 12),
    .SD .x8 .x0 (96 : BitVec 12),
    .SD .x8 .x0 (104 : BitVec 12),
    .SD .x8 .x0 (112 : BitVec 12),
    .SD .x8 .x0 (120 : BitVec 12),
    .SD .x8 .x0 (128 : BitVec 12),
    .SD .x8 .x0 (136 : BitVec 12),
    .SD .x8 .x0 (144 : BitVec 12),
    .SD .x8 .x0 (152 : BitVec 12),
    .SD .x8 .x0 (160 : BitVec 12),
    .SD .x8 .x0 (168 : BitVec 12),
    .SD .x8 .x0 (176 : BitVec 12),
    .SD .x8 .x0 (184 : BitVec 12),
    .AUIPC .x5 (laHi sttc_bv_tx_count (simpleTransferTxContextPc + 128)),
    .ADDI .x5 .x5 (laLo sttc_bv_tx_count (simpleTransferTxContextPc + 128)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .BEQ .x6 .x7 (16 : BitVec 13),
    .LI .x5 (1 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (484 : BitVec 21),
    .AUIPC .x5 (laHi sttc_bv_public_keys_len (simpleTransferTxContextPc + 160)),
    .ADDI .x5 .x5 (laLo sttc_bv_public_keys_len (simpleTransferTxContextPc + 160)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (65 : Word),
    .BEQ .x6 .x7 (16 : BitVec 13),
    .LI .x5 (2 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (452 : BitVec 21),
    .AUIPC .x5 (laHi sttc_bv_tx_list_ptr (simpleTransferTxContextPc + 192)),
    .ADDI .x5 .x5 (laLo sttc_bv_tx_list_ptr (simpleTransferTxContextPc + 192)),
    .LD .x9 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi sttc_bv_tx_list_len (simpleTransferTxContextPc + 204)),
    .ADDI .x5 .x5 (laLo sttc_bv_tx_list_len (simpleTransferTxContextPc + 204)),
    .LD .x18 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi sttc_bv_tx_item_start (simpleTransferTxContextPc + 216)),
    .ADDI .x5 .x5 (laLo sttc_bv_tx_item_start (simpleTransferTxContextPc + 216)),
    .LD .x19 .x5 (0 : BitVec 12),
    .BLTU .x18 .x19 (380 : BitVec 13),
    .BEQ .x18 .x19 (388 : BitVec 13),
    .ADD .x9 .x9 .x19,
    .SUB .x18 .x18 .x19,
    .SD .x8 .x9 (8 : BitVec 12),
    .SD .x8 .x18 (16 : BitVec 12),
    .AUIPC .x5 (laHi sttc_bv_public_keys_ptr (simpleTransferTxContextPc + 252)),
    .ADDI .x5 .x5 (laLo sttc_bv_public_keys_ptr (simpleTransferTxContextPc + 252)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x8 .x6 (24 : BitVec 12),
    .AUIPC .x5 (laHi sttc_bv_exec_p (simpleTransferTxContextPc + 272)),
    .ADDI .x5 .x5 (laLo sttc_bv_exec_p (simpleTransferTxContextPc + 272)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (440 : BitVec 12),
    .AUIPC .x7 (laHi sttc_sttc_base_fee_be (simpleTransferTxContextPc + 288)),
    .ADDI .x7 .x7 (laLo sttc_sttc_base_fee_be (simpleTransferTxContextPc + 288)),
    .LI .x28 (0 : Word),
    .LI .x29 (32 : Word),
    .BEQ .x28 .x29 (36 : BitVec 13),
    .SUB .x30 .x29 .x28,
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .ADD .x30 .x6 .x30,
    .LBU .x31 .x30 (0 : BitVec 12),
    .ADD .x30 .x7 .x28,
    .SB .x30 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .SD .x8 .x7 (32 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .AUIPC .x12 (laHi sttc_tea_type (simpleTransferTxContextPc + 352)),
    .ADDI .x12 .x12 (laLo sttc_tea_type (simpleTransferTxContextPc + 352)),
    .AUIPC .x13 (laHi sttc_tea_inner_off (simpleTransferTxContextPc + 360)),
    .ADDI .x13 .x13 (laLo sttc_tea_inner_off (simpleTransferTxContextPc + 360)),
    .JAL .x1 (jalOff sttc_tx_type_dispatch (simpleTransferTxContextPc + 368)),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (20 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (256 : BitVec 21),
    .AUIPC .x5 (laHi sttc_tea_type (simpleTransferTxContextPc + 388)),
    .ADDI .x5 .x5 (laLo sttc_tea_type (simpleTransferTxContextPc + 388)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x8 .x6 (160 : BitVec 12),
    .AUIPC .x5 (laHi sttc_tea_inner_off (simpleTransferTxContextPc + 404)),
    .ADDI .x5 .x5 (laLo sttc_tea_inner_off (simpleTransferTxContextPc + 404)),
    .LD .x28 .x5 (0 : BitVec 12),
    .SD .x8 .x28 (168 : BitVec 12),
    .BLTU .x18 .x28 (212 : BitVec 13),
    .ADD .x29 .x9 .x28,
    .SD .x8 .x29 (176 : BitVec 12),
    .SUB .x29 .x18 .x28,
    .SD .x8 .x29 (184 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .AUIPC .x12 (laHi sttc_sttc_nonce (simpleTransferTxContextPc + 448)),
    .ADDI .x12 .x12 (laLo sttc_sttc_nonce (simpleTransferTxContextPc + 448)),
    .ADDI .x13 .x8 (40 : BitVec 12),
    .JAL .x1 (jalOff sttc_tx_extract_nonce_and_gas (simpleTransferTxContextPc + 460)),
    .SD .x8 .x10 (128 : BitVec 12),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (20 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (160 : BitVec 21),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .ADDI .x12 .x8 (72 : BitVec 12),
    .ADDI .x13 .x8 (48 : BitVec 12),
    .JAL .x1 (jalOff sttc_tx_extract_to_address (simpleTransferTxContextPc + 500)),
    .SD .x8 .x10 (136 : BitVec 12),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (30 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (120 : BitVec 21),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .ADDI .x12 .x8 (96 : BitVec 12),
    .JAL .x1 (jalOff sttc_tx_extract_value (simpleTransferTxContextPc + 536)),
    .SD .x8 .x10 (144 : BitVec 12),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (40 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (84 : BitVec 21),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .ADDI .x12 .x8 (56 : BitVec 12),
    .ADDI .x13 .x8 (64 : BitVec 12),
    .JAL .x1 (jalOff sttc_tx_extract_data_section (simpleTransferTxContextPc + 576)),
    .SD .x8 .x10 (152 : BitVec 12),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .LI .x5 (50 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .JAL .x0 (44 : BitVec 21),
    .SD .x8 .x0 (0 : BitVec 12),
    .JAL .x0 (36 : BitVec 21),
    .LI .x5 (3 : Word),
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
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `simpleTransferTxContext_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def simpleTransferTxContext_relocs : RelocTable :=
  [ (32, .la .x5 "bv_tx_count"),
    (40, .la .x5 "bv_public_keys_len"),
    (48, .la .x5 "bv_tx_list_ptr"),
    (51, .la .x5 "bv_tx_list_len"),
    (54, .la .x5 "bv_tx_item_start"),
    (63, .la .x5 "bv_public_keys_ptr"),
    (68, .la .x5 "bv_exec_p"),
    (72, .la .x7 "sttc_base_fee_be"),
    (88, .la .x12 "tea_type"),
    (90, .la .x13 "tea_inner_off"),
    (92, .jal .x1 "tx_type_dispatch"),
    (97, .la .x5 "tea_type"),
    (101, .la .x5 "tea_inner_off"),
    (112, .la .x12 "sttc_nonce"),
    (115, .jal .x1 "tx_extract_nonce_and_gas"),
    (125, .jal .x1 "tx_extract_to_address"),
    (134, .jal .x1 "tx_extract_value"),
    (144, .jal .x1 "tx_extract_data_section") ]

def simpleTransferTxContextFunction : String :=
  "simple_transfer_tx_context:\n" ++ emitProgramR simpleTransferTxContext_prog simpleTransferTxContext_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `simpleTransferTxContext_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem simpleTransferTxContextFunction_eq_prog :
    simpleTransferTxContextFunction = "simple_transfer_tx_context:\n" ++ emitProgramR simpleTransferTxContext_prog simpleTransferTxContext_relocs := rfl

#guard simpleTransferTxContextFunction.startsWith "simple_transfer_tx_context:\n"
#guard simpleTransferTxContext_prog.length = 168
def blockVerdictSimpleTransferDataSection : String :=
  ".balign 8\n" ++
  "sttc_nonce:\n  .zero 8\n" ++
  "tea_type:\n  .zero 8\n" ++
  "tea_inner_off:\n  .zero 8\n" ++
  "tea_field_off:\n  .zero 8\n" ++
  "tea_field_len:\n  .zero 8\n" ++
  -- g8zeq.1.4.2: tx_intrinsic_state_gas scratch (per-tx is_creation/type/auth parse).
  "tis_to_buf:\n  .zero 32\n" ++
  "tis_is_creation:\n  .zero 8\n" ++
  "tis_type:\n  .zero 8\n" ++
  "tis_inner_off:\n  .zero 8\n" ++
  "tis_auth_off:\n  .zero 8\n" ++
  "tis_auth_len:\n  .zero 8\n" ++
  "tis_auth_count:\n  .zero 8\n" ++
  "tev_type:\n  .zero 8\n" ++
  "tev_inner_off:\n  .zero 8\n" ++
  "teds_type:\n  .zero 8\n" ++
  "teds_inner_off:\n  .zero 8\n" ++
  "teds_field_off:\n  .zero 8\n" ++
  "teds_field_len:\n  .zero 8\n" ++
  "t48_offset:\n  .zero 8\n" ++
  "t48_length:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "sttc_base_fee_be:\n  .zero 32\n"
  -- #10685 PR2: bv_simple_transfer_tx (.zero 192) deleted with bv_emit_single_tx_tl7708.
  -- SPIKE_WATCH hits=0 on cell; sole producer never filled; emit early-exits on zero.

def blockVerdictTxGasPrechargeDataSection : String :=
  ".balign 8\n" ++
  "tgsbl_tmp_off:\n  .zero 8\n" ++
  "tgsbl_tmp_len:\n  .zero 8\n" ++
  "tgsbl_count:\n  .zero 8\n" ++
  "tgsbl_row_off:\n  .zero 8\n" ++
  "tgsbl_row_len:\n  .zero 8\n" ++
  "tgsbl_addr_off:\n  .zero 8\n" ++
  "tgsbl_addr_len:\n  .zero 8\n" ++
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "tegp_type:\n  .zero 8\n" ++
  "tegp_inner_off:\n  .zero 8\n" ++
  blockVerdictSimpleTransferDataSection ++
  ".balign 32\n" ++
  "tefgp_max_priority:\n  .zero 32\n" ++
  "tefgp_max_fee:\n  .zero 32\n" ++
  "tefgp_tmp:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "txup_nonce:\n  .zero 8\n" ++
  "txup_gas_limit:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "txup_effective_gas_price:\n  .zero 32\n" ++
  "txup_priority_fee:\n  .zero 32\n" ++
  "acpg_gas_fee:\n  .zero 32\n" ++
  "tgbpv_balance:\n  .zero 32\n" ++
  "tgbpv_refund:\n  .zero 32\n" ++
  "tgbpv_expected_balance:\n  .zero 32\n" ++
  "tgbpv_post_balance:\n  .zero 32\n" ++
  "tgbpv_value:\n  .zero 32\n" ++
  "tgbpv_blob_debit:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "tgbpv_nonce:\n  .zero 8\n" ++
  "tgbpv_simple_transfer_gas_used:\n  .zero 8\n" ++
  "tgbpv_skip_value:\n  .zero 8\n" ++
  "tgbpv_direct_floor:\n  .zero 8\n" ++
  "tgbpv_direct_oog:\n  .zero 8\n" ++
  "tgbpv_failed_oog:\n  .zero 8\n" ++
  "tgbpv_top_state_gas:\n  .zero 8\n" ++
  "tgbpv_tx_type:\n  .zero 8\n" ++
  "tgbpv_inner_off:\n  .zero 8\n" ++
  "tgbpv_blob_count:\n  .zero 8\n" ++
  "tgbpv_t48:\n  .zero 248\n" ++
  "tgbpv_to_addr:\n  .zero 24\n" ++
  "tgbpv_is_creation:\n  .zero 8\n" ++
  "tgbpv_lookup:\n  .zero 168\n" ++
  "tgbpv_records:\n  .zero 4096\n" ++
  "bv_tx_gas_precharge:\n  .zero 224\n"

/- Probe input:
      +8   tx_list_len
      +16  tx_item_start
      +24  tx_count
      +32  public_keys_len
      +64  fake execution payload (base_fee starts at +440, SSZ little-endian)
      +320 public keys blob
      +640 transaction-list bytes

   Output is the 192-byte simple_transfer_tx_context record.
-/
def ziskSimpleTransferTxContextPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  addi t0, s0, 64; la t1, bv_exec_p; sd t0, 0(t1)\n" ++
  "  addi t0, s0, 320; la t1, bv_public_keys_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 32(s0); la t1, bv_public_keys_len; sd t0, 0(t1)\n" ++
  "  addi t0, s0, 640; la t1, bv_tx_list_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 8(s0); la t1, bv_tx_list_len; sd t0, 0(t1)\n" ++
  "  ld t0, 16(s0); la t1, bv_tx_item_start; sd t0, 0(t1)\n" ++
  "  ld t0, 24(s0); la t1, bv_tx_count; sd t0, 0(t1)\n" ++
  "  li a0, 0xa0010000\n" ++
  "  jal ra, simple_transfer_tx_context\n" ++
  "  j .Lsttcp_done\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txExtractValueFunction ++ "\n" ++
  txExtractDataSectionFunction ++ "\n" ++
  simpleTransferTxContextFunction ++ "\n" ++
  ".Lsttcp_done:"

def ziskSimpleTransferTxContextDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bv_exec_p:\n  .zero 8\n" ++
  "bv_tx_list_ptr:\n  .zero 8\n" ++
  "bv_tx_list_len:\n  .zero 8\n" ++
  "bv_tx_count:\n  .zero 8\n" ++
  "bv_tx_item_start:\n  .zero 8\n" ++
  "bv_public_keys_ptr:\n  .zero 8\n" ++
  "bv_public_keys_len:\n  .zero 8\n" ++
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  blockVerdictSimpleTransferDataSection

def ziskSimpleTransferTxContextProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSimpleTransferTxContextPrologue
  dataAsm     := ziskSimpleTransferTxContextDataSection
}

end EvmAsm.Codegen
