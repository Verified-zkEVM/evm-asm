/-
  EvmAsm.Codegen.Programs.TxGasSenderBalLookup

  Sender BAL pre-state lookup for transaction upfront gas checks.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.AccountFieldExtract
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.BalAccountPostFields
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## tx_gas_sender_bal_lookup

    Locate the BAL row and pre-state account fields for a selected tx sender.

    Calling convention:
      a0 = tx ptr
      a1 = tx len
      a2 = selected sender public key ptr (64 B x||y)
      a3 = BAL AccountChanges list ptr
      a4 = BAL AccountChanges list len
      a5 = pre-account record array ptr, 24 B per BAL row:
           +0 account_rlp_ptr, +8 account_rlp_len, +16 flags
      a6 = output ptr

    Output:
      +0   status
             0 ok
             1 malformed tx/envelope
             2 malformed BAL row/list
             3 sender BAL row not found
             4 pre-account parse failed
             5 post-field parse failed
      +8   BAL row index, or UINT64_MAX on failure before match
      +16  sender address (20 B, then zero padding)
      +48  pre balance, u256 BE
      +80  pre nonce, u64 LE
      +88  post balance byte length, UINT64_MAX when absent
      +96  post balance bytes, capacity 32
      +128 post nonce byte length, UINT64_MAX when absent
      +136 post nonce bytes, capacity 32
-/
def txGasSenderBalLookup_prog : Program :=
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
    .MV .x22 .x16,
    .SD .x22 .x0 (0 : BitVec 12),
    .SD .x22 .x0 (16 : BitVec 12),
    .SD .x22 .x0 (24 : BitVec 12),
    .SD .x22 .x0 (32 : BitVec 12),
    .SD .x22 .x0 (40 : BitVec 12),
    .SD .x22 .x0 (48 : BitVec 12),
    .SD .x22 .x0 (56 : BitVec 12),
    .SD .x22 .x0 (64 : BitVec 12),
    .SD .x22 .x0 (72 : BitVec 12),
    .SD .x22 .x0 (80 : BitVec 12),
    .SD .x22 .x0 (96 : BitVec 12),
    .SD .x22 .x0 (104 : BitVec 12),
    .SD .x22 .x0 (112 : BitVec 12),
    .SD .x22 .x0 (136 : BitVec 12),
    .SD .x22 .x0 (144 : BitVec 12),
    .SD .x22 .x0 (152 : BitVec 12),
    .SD .x22 .x0 (160 : BitVec 12),
    .LI .x5 (-1 : Word),
    .SD .x22 .x5 (8 : BitVec 12),
    .SD .x22 .x5 (88 : BitVec 12),
    .SD .x22 .x5 (128 : BitVec 12),
    .BEQ .x9 .x0 (468 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .LI .x6 (128 : Word),
    .BLTU .x5 .x6 (44 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.tgsbl_tmp_off (GuestAddrs.tx_gas_sender_bal_lookup + 196)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tgsbl_tmp_off (GuestAddrs.tx_gas_sender_bal_lookup + 196)),
    .AUIPC .x14 (laHi GuestAddrs.tgsbl_tmp_len (GuestAddrs.tx_gas_sender_bal_lookup + 204)),
    .ADDI .x14 .x14 (laLo GuestAddrs.tgsbl_tmp_len (GuestAddrs.tx_gas_sender_bal_lookup + 204)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.tx_gas_sender_bal_lookup + 212)),
    .BNE .x10 .x0 (420 : BitVec 13),
    .JAL .x0 (60 : BitVec 21),
    .BEQ .x5 .x0 (412 : BitVec 13),
    .LI .x6 (4 : Word),
    .BLTU .x6 .x5 (404 : BitVec 13),
    .LI .x6 (2 : Word),
    .BLTU .x9 .x6 (396 : BitVec 13),
    .ADDI .x10 .x8 (1 : BitVec 12),
    .ADDI .x11 .x9 (-1 : BitVec 12),
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.tgsbl_tmp_off (GuestAddrs.tx_gas_sender_bal_lookup + 256)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tgsbl_tmp_off (GuestAddrs.tx_gas_sender_bal_lookup + 256)),
    .AUIPC .x14 (laHi GuestAddrs.tgsbl_tmp_len (GuestAddrs.tx_gas_sender_bal_lookup + 264)),
    .ADDI .x14 .x14 (laLo GuestAddrs.tgsbl_tmp_len (GuestAddrs.tx_gas_sender_bal_lookup + 264)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.tx_gas_sender_bal_lookup + 272)),
    .BNE .x10 .x0 (360 : BitVec 13),
    .MV .x10 .x18,
    .ADDI .x11 .x22 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.address_from_pubkey (GuestAddrs.tx_gas_sender_bal_lookup + 288)),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .AUIPC .x12 (laHi GuestAddrs.tgsbl_count (GuestAddrs.tx_gas_sender_bal_lookup + 300)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tgsbl_count (GuestAddrs.tx_gas_sender_bal_lookup + 300)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.tx_gas_sender_bal_lookup + 308)),
    .BNE .x10 .x0 (332 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tgsbl_count (GuestAddrs.tx_gas_sender_bal_lookup + 316)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tgsbl_count (GuestAddrs.tx_gas_sender_bal_lookup + 316)),
    .LD .x24 .x5 (0 : BitVec 12),
    .LI .x25 (0 : Word),
    .BGEU .x25 .x24 (320 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .MV .x12 .x25,
    .AUIPC .x13 (laHi GuestAddrs.tgsbl_row_off (GuestAddrs.tx_gas_sender_bal_lookup + 348)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tgsbl_row_off (GuestAddrs.tx_gas_sender_bal_lookup + 348)),
    .AUIPC .x14 (laHi GuestAddrs.tgsbl_row_len (GuestAddrs.tx_gas_sender_bal_lookup + 356)),
    .ADDI .x14 .x14 (laLo GuestAddrs.tgsbl_row_len (GuestAddrs.tx_gas_sender_bal_lookup + 356)),
    .JAL .x1 (jalOff GuestAddrs.rlp_item_span (GuestAddrs.tx_gas_sender_bal_lookup + 364)),
    .BNE .x10 .x0 (276 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tgsbl_row_off (GuestAddrs.tx_gas_sender_bal_lookup + 372)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tgsbl_row_off (GuestAddrs.tx_gas_sender_bal_lookup + 372)),
    .LD .x5 .x5 (0 : BitVec 12),
    .ADD .x26 .x19 .x5,
    .AUIPC .x5 (laHi GuestAddrs.tgsbl_row_len (GuestAddrs.tx_gas_sender_bal_lookup + 388)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tgsbl_row_len (GuestAddrs.tx_gas_sender_bal_lookup + 388)),
    .LD .x27 .x5 (0 : BitVec 12),
    .MV .x10 .x26,
    .MV .x11 .x27,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.tgsbl_addr_off (GuestAddrs.tx_gas_sender_bal_lookup + 412)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tgsbl_addr_off (GuestAddrs.tx_gas_sender_bal_lookup + 412)),
    .AUIPC .x14 (laHi GuestAddrs.tgsbl_addr_len (GuestAddrs.tx_gas_sender_bal_lookup + 420)),
    .ADDI .x14 .x14 (laLo GuestAddrs.tgsbl_addr_len (GuestAddrs.tx_gas_sender_bal_lookup + 420)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.tx_gas_sender_bal_lookup + 428)),
    .BNE .x10 .x0 (212 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tgsbl_addr_len (GuestAddrs.tx_gas_sender_bal_lookup + 436)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tgsbl_addr_len (GuestAddrs.tx_gas_sender_bal_lookup + 436)),
    .LD .x5 .x5 (0 : BitVec 12),
    .LI .x6 (20 : Word),
    .BNE .x5 .x6 (192 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tgsbl_addr_off (GuestAddrs.tx_gas_sender_bal_lookup + 456)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tgsbl_addr_off (GuestAddrs.tx_gas_sender_bal_lookup + 456)),
    .LD .x5 .x5 (0 : BitVec 12),
    .ADD .x5 .x26 .x5,
    .ADDI .x6 .x22 (16 : BitVec 12),
    .LI .x7 (20 : Word),
    .BEQ .x7 .x0 (40 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .BNE .x28 .x29 (20 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .JAL .x0 (-184 : BitVec 21),
    .SD .x22 .x25 (8 : BitVec 12),
    .SLLI .x5 .x25 (4 : BitVec 6),
    .SLLI .x6 .x25 (3 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .ADD .x5 .x21 .x5,
    .LD .x10 .x5 (0 : BitVec 12),
    .LD .x11 .x5 (8 : BitVec 12),
    .ADDI .x12 .x22 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_extract_balance (GuestAddrs.tx_gas_sender_bal_lookup + 552)),
    .BNE .x10 .x0 (104 : BitVec 13),
    .SLLI .x5 .x25 (4 : BitVec 6),
    .SLLI .x6 .x25 (3 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .ADD .x5 .x21 .x5,
    .LD .x10 .x5 (0 : BitVec 12),
    .LD .x11 .x5 (8 : BitVec 12),
    .ADDI .x12 .x22 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_extract_nonce (GuestAddrs.tx_gas_sender_bal_lookup + 588)),
    .BNE .x10 .x0 (68 : BitVec 13),
    .MV .x10 .x26,
    .MV .x11 .x27,
    .ADDI .x12 .x22 (96 : BitVec 12),
    .ADDI .x13 .x22 (88 : BitVec 12),
    .ADDI .x14 .x22 (136 : BitVec 12),
    .ADDI .x15 .x22 (128 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_account_post_fields (GuestAddrs.tx_gas_sender_bal_lookup + 620)),
    .BNE .x10 .x0 (44 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (40 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (3 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (4 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (5 : Word),
    .SD .x22 .x10 (0 : BitVec 12),
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

/-- Reloc side-table for `txGasSenderBalLookup_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txGasSenderBalLookup_relocs : RelocTable :=
  [ (49, .la .x13 "tgsbl_tmp_off"),
    (51, .la .x14 "tgsbl_tmp_len"),
    (53, .jal .x1 "rlp_list_nth_item"),
    (64, .la .x13 "tgsbl_tmp_off"),
    (66, .la .x14 "tgsbl_tmp_len"),
    (68, .jal .x1 "rlp_list_nth_item"),
    (72, .jal .x1 "address_from_pubkey"),
    (75, .la .x12 "tgsbl_count"),
    (77, .jal .x1 "rlp_list_count_items"),
    (79, .la .x5 "tgsbl_count"),
    (87, .la .x13 "tgsbl_row_off"),
    (89, .la .x14 "tgsbl_row_len"),
    (91, .jal .x1 "rlp_item_span"),
    (93, .la .x5 "tgsbl_row_off"),
    (97, .la .x5 "tgsbl_row_len"),
    (103, .la .x13 "tgsbl_addr_off"),
    (105, .la .x14 "tgsbl_addr_len"),
    (107, .jal .x1 "rlp_list_nth_item"),
    (109, .la .x5 "tgsbl_addr_len"),
    (114, .la .x5 "tgsbl_addr_off"),
    (138, .jal .x1 "account_extract_balance"),
    (147, .jal .x1 "account_extract_nonce"),
    (155, .jal .x1 "bal_account_post_fields") ]

def txGasSenderBalLookupFunction : String :=
  "tx_gas_sender_bal_lookup:\n" ++ emitProgramR txGasSenderBalLookup_prog txGasSenderBalLookup_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txGasSenderBalLookup_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txGasSenderBalLookupFunction_eq_prog :
    txGasSenderBalLookupFunction = "tx_gas_sender_bal_lookup:\n" ++ emitProgramR txGasSenderBalLookup_prog txGasSenderBalLookup_relocs := rfl

#guard txGasSenderBalLookupFunction.startsWith "tx_gas_sender_bal_lookup:\n"
#guard txGasSenderBalLookup_prog.length = 184
/-- Probe input:
      +8  tx_len
      +16 BAL len
      +24 account count
      +32 pubkey64
      +96 tx bytes
      align8, BAL bytes
      align8, account length table (u64 each), account RLP blobs align8 each.
-/
def ziskTxGasSenderBalLookupPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # tx_len\n" ++
  "  ld s2, 16(s0)               # BAL len\n" ++
  "  ld s3, 24(s0)               # account count\n" ++
  "  addi s4, s0, 32             # pubkey ptr\n" ++
  "  addi s5, s0, 96             # tx ptr\n" ++
  "  add t0, s5, s1; addi t0, t0, 7; li t1, -8; and s6, t0, t1 # BAL ptr\n" ++
  "  add t0, s6, s2; addi t0, t0, 7; li t1, -8; and s7, t0, t1 # length table\n" ++
  "  slli t0, s3, 3; add s8, s7, t0   # account blob cursor\n" ++
  "  la s9, tgsbl_records\n" ++
  "  li s10, 0\n" ++
  ".Ltgsblp_records:\n" ++
  "  bgeu s10, s3, .Ltgsblp_call\n" ++
  "  slli t0, s10, 3; add t1, s7, t0; ld t2, 0(t1) # account len\n" ++
  "  slli t3, s10, 4; add t4, t3, t0; add t4, s9, t4\n" ++
  "  sd s8, 0(t4); sd t2, 8(t4); sd zero, 16(t4)\n" ++
  "  add s8, s8, t2; addi s8, s8, 7; li t5, -8; and s8, s8, t5\n" ++
  "  addi s10, s10, 1\n" ++
  "  j .Ltgsblp_records\n" ++
  ".Ltgsblp_call:\n" ++
  "  mv a0, s5; mv a1, s1; mv a2, s4; mv a3, s6; mv a4, s2; mv a5, s9\n" ++
  "  li a6, 0xa0010000\n" ++
  "  jal ra, tx_gas_sender_bal_lookup\n" ++
  "  j .Ltgsblp_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  -- cursor-walk helpers (account_extract_nonce/_balance decode via RlpWalk)
  rlpWalkHelpersClosure ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountExtractNonceFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  txGasSenderBalLookupFunction ++ "\n" ++
  ".Ltgsblp_done:"

def ziskTxGasSenderBalLookupDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tgsbl_tmp_off:\n  .zero 8\n" ++
  "tgsbl_tmp_len:\n  .zero 8\n" ++
  "tgsbl_count:\n  .zero 8\n" ++
  "tgsbl_row_off:\n  .zero 8\n" ++
  "tgsbl_row_len:\n  .zero 8\n" ++
  "tgsbl_addr_off:\n  .zero 8\n" ++
  "tgsbl_addr_len:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "bpf_list_off:\n  .zero 8\n" ++
  "bpf_list_len:\n  .zero 8\n" ++
  "bpf_list_ptr:\n  .zero 8\n" ++
  "bpf_count:\n  .zero 8\n" ++
  "bpf_item_off:\n  .zero 8\n" ++
  "bpf_item_len:\n  .zero 8\n" ++
  "bpf_item_ptr:\n  .zero 8\n" ++
  "bpf_val_off:\n  .zero 8\n" ++
  "bpf_val_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "afp_digest:\n  .zero 32\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 8\n" ++
  "tgsbl_records:\n  .zero 4096"

def ziskTxGasSenderBalLookupProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxGasSenderBalLookupPrologue
  dataAsm     := ziskTxGasSenderBalLookupDataSection
}

end EvmAsm.Codegen
