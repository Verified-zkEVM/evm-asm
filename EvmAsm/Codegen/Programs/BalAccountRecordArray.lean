/-
  EvmAsm.Codegen.Programs.BalAccountRecordArray

  Derive a pre-account record table for BAL replay callers:
  for each BAL AccountChanges item, walk the pre-state trie to find the account
  RLP, or use the canonical empty-account RLP when the account is absent.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.BalAccountHasStateChange
import EvmAsm.Codegen.Programs.BalAccountPath
import EvmAsm.Codegen.Programs.BalModeledSystem
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptSet

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_record_array -- BAL list -> pre-account records

    a0 = root_hash ptr        a1 = witness ptr       a2 = witness length
    a3 = BAL list ptr         a4 = BAL list length   a5 = n records/items
    a6 = records out ptr      a7 = account arena out ptr
    a0 (output) = 0 ok / 1 conservative failure.

    Record layout matches `bal_account_descriptor_array`:
      +0 account_ptr | +8 account_len | +16 is_insert.

    Found accounts are copied into the caller-provided arena with is_insert=0.
    Missing accounts use the canonical empty account RLP with is_insert=1.
    Read-only BAL rows are recorded as the canonical empty account RLP with
    is_insert=3 so descriptor construction can skip re-classifying them.

    If `bara_skip_modeled_system` is nonzero, EIP-2935/EIP-4788 rows are also
    recorded with is_insert=3 because the verdict path has already replayed
    those system writes explicitly. The flag defaults to zero for standalone
    BAL state-root callers. -/
def balAccountRecordArray_prog : Program :=
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
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x23 .x17,
    .ADD .x5 .x19 .x20,
    .AUIPC .x6 (laHi GuestAddrs.bara_bal_end (GuestAddrs.bal_account_record_array + 84)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bara_bal_end (GuestAddrs.bal_account_record_array + 84)),
    .SD .x6 .x5 (0 : BitVec 12),
    .BGEU .x19 .x5 (brOff (GuestAddrs.bal_account_record_array + 568) (GuestAddrs.bal_account_record_array + 96)),
    .LBU .x7 .x19 (0 : BitVec 12),
    .LI .x28 (192 : Word),
    .BLTU .x7 .x28 (brOff (GuestAddrs.bal_account_record_array + 568) (GuestAddrs.bal_account_record_array + 108)),
    .LI .x28 (248 : Word),
    .BLTU .x7 .x28 (24 : BitVec 13),
    .LI .x28 (247 : Word),
    .SUB .x29 .x7 .x28,
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADD .x25 .x19 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x25 .x19 (1 : BitVec 12),
    .LI .x24 (0 : Word),
    .BEQ .x24 .x21 (brOff (GuestAddrs.bal_account_record_array + 560) (GuestAddrs.bal_account_record_array + 148)),
    .AUIPC .x5 (laHi GuestAddrs.bara_bal_end (GuestAddrs.bal_account_record_array + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bara_bal_end (GuestAddrs.bal_account_record_array + 152)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BGEU .x25 .x5 (brOff (GuestAddrs.bal_account_record_array + 568) (GuestAddrs.bal_account_record_array + 164)),
    .MV .x10 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_item_size (GuestAddrs.bal_account_record_array + 172)),
    .MV .x31 .x10,
    .ADD .x5 .x25 .x31,
    .AUIPC .x6 (laHi GuestAddrs.bara_bal_end (GuestAddrs.bal_account_record_array + 184)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bara_bal_end (GuestAddrs.bal_account_record_array + 184)),
    .LD .x6 .x6 (0 : BitVec 12),
    .BLTU .x6 .x5 (brOff (GuestAddrs.bal_account_record_array + 568) (GuestAddrs.bal_account_record_array + 196)),
    .AUIPC .x6 (laHi GuestAddrs.bara_next_item (GuestAddrs.bal_account_record_array + 200)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bara_next_item (GuestAddrs.bal_account_record_array + 200)),
    .SD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bara_item_len (GuestAddrs.bal_account_record_array + 212)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bara_item_len (GuestAddrs.bal_account_record_array + 212)),
    .SD .x6 .x31 (0 : BitVec 12),
    .MV .x10 .x25,
    .MV .x11 .x31,
    .JAL .x1 (jalOff GuestAddrs.bal_account_has_state_change (GuestAddrs.bal_account_record_array + 232)),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (28 : BitVec 13),
    .BNE .x10 .x0 (brOff (GuestAddrs.bal_account_record_array + 568) (GuestAddrs.bal_account_record_array + 244)),
    .AUIPC .x25 (laHi GuestAddrs.bara_empty_account (GuestAddrs.bal_account_record_array + 248)),
    .ADDI .x25 .x25 (laLo GuestAddrs.bara_empty_account (GuestAddrs.bal_account_record_array + 248)),
    .LI .x6 (70 : Word),
    .LI .x7 (3 : Word),
    .JAL .x0 (jalOff (GuestAddrs.bal_account_record_array + 484) (GuestAddrs.bal_account_record_array + 264)),
    .AUIPC .x5 (laHi GuestAddrs.bara_skip_modeled_system (GuestAddrs.bal_account_record_array + 268)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bara_skip_modeled_system (GuestAddrs.bal_account_record_array + 268)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (44 : BitVec 13),
    .MV .x10 .x25,
    .AUIPC .x5 (laHi GuestAddrs.bara_item_len (GuestAddrs.bal_account_record_array + 288)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bara_item_len (GuestAddrs.bal_account_record_array + 288)),
    .LD .x11 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_account_is_modeled_system (GuestAddrs.bal_account_record_array + 300)),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.bal_account_record_array + 468) (GuestAddrs.bal_account_record_array + 308)),
    .LI .x5 (2 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.bal_account_record_array + 468) (GuestAddrs.bal_account_record_array + 316)),
    .BNE .x10 .x0 (brOff (GuestAddrs.bal_account_record_array + 568) (GuestAddrs.bal_account_record_array + 320)),
    .MV .x10 .x25,
    .AUIPC .x5 (laHi GuestAddrs.bara_item_len (GuestAddrs.bal_account_record_array + 328)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bara_item_len (GuestAddrs.bal_account_record_array + 328)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.bara_path (GuestAddrs.bal_account_record_array + 340)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bara_path (GuestAddrs.bal_account_record_array + 340)),
    .JAL .x1 (jalOff GuestAddrs.bal_account_path (GuestAddrs.bal_account_record_array + 348)),
    .BNE .x10 .x0 (brOff (GuestAddrs.bal_account_record_array + 568) (GuestAddrs.bal_account_record_array + 352)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.bara_path (GuestAddrs.bal_account_record_array + 368)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bara_path (GuestAddrs.bal_account_record_array + 368)),
    .LI .x14 (64 : Word),
    .AUIPC .x15 (laHi GuestAddrs.bara_acct (GuestAddrs.bal_account_record_array + 380)),
    .ADDI .x15 .x15 (laLo GuestAddrs.bara_acct (GuestAddrs.bal_account_record_array + 380)),
    .AUIPC .x16 (laHi GuestAddrs.bara_acct_len (GuestAddrs.bal_account_record_array + 388)),
    .ADDI .x16 .x16 (laLo GuestAddrs.bara_acct_len (GuestAddrs.bal_account_record_array + 388)),
    .JAL .x1 (jalOff GuestAddrs.mpt_walk (GuestAddrs.bal_account_record_array + 396)),
    .BEQ .x10 .x0 (32 : BitVec 13),
    .LI .x5 (1 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.bal_account_record_array + 568) (GuestAddrs.bal_account_record_array + 408)),
    .AUIPC .x25 (laHi GuestAddrs.bara_empty_account (GuestAddrs.bal_account_record_array + 412)),
    .ADDI .x25 .x25 (laLo GuestAddrs.bara_empty_account (GuestAddrs.bal_account_record_array + 412)),
    .LI .x6 (70 : Word),
    .LI .x7 (1 : Word),
    .JAL .x0 (56 : BitVec 21),
    .AUIPC .x25 (laHi GuestAddrs.bara_acct (GuestAddrs.bal_account_record_array + 432)),
    .ADDI .x25 .x25 (laLo GuestAddrs.bara_acct (GuestAddrs.bal_account_record_array + 432)),
    .AUIPC .x5 (laHi GuestAddrs.bara_acct_len (GuestAddrs.bal_account_record_array + 440)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bara_acct_len (GuestAddrs.bal_account_record_array + 440)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x5 (256 : Word),
    .BLTU .x5 .x6 (brOff (GuestAddrs.bal_account_record_array + 568) (GuestAddrs.bal_account_record_array + 456)),
    .LI .x7 (0 : Word),
    .JAL .x0 (20 : BitVec 21),
    .AUIPC .x25 (laHi GuestAddrs.bara_empty_account (GuestAddrs.bal_account_record_array + 468)),
    .ADDI .x25 .x25 (laLo GuestAddrs.bara_empty_account (GuestAddrs.bal_account_record_array + 468)),
    .LI .x6 (70 : Word),
    .LI .x7 (3 : Word),
    .MV .x10 .x23,
    .MV .x11 .x25,
    .MV .x12 .x6,
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.bal_account_record_array + 496)),
    .SLLI .x5 .x24 (4 : BitVec 6),
    .SLLI .x28 .x24 (3 : BitVec 6),
    .ADD .x5 .x5 .x28,
    .ADD .x5 .x22 .x5,
    .SD .x5 .x23 (0 : BitVec 12),
    .SD .x5 .x6 (8 : BitVec 12),
    .SD .x5 .x7 (16 : BitVec 12),
    .ADD .x23 .x23 .x6,
    .ADDI .x23 .x23 (7 : BitVec 12),
    .ANDI .x23 .x23 (-8 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bara_next_item (GuestAddrs.bal_account_record_array + 540)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bara_next_item (GuestAddrs.bal_account_record_array + 540)),
    .LD .x25 .x5 (0 : BitVec 12),
    .ADDI .x24 .x24 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_account_record_array + 148) (GuestAddrs.bal_account_record_array + 556)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
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
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountRecordArray_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountRecordArray_relocs : RelocTable :=
  [ (21, .la .x6 "bara_bal_end"),
    (38, .la .x5 "bara_bal_end"),
    (43, .jal .x1 "rlp_item_size"),
    (46, .la .x6 "bara_bal_end"),
    (50, .la .x6 "bara_next_item"),
    (53, .la .x6 "bara_item_len"),
    (58, .jal .x1 "bal_account_has_state_change"),
    (62, .la .x25 "bara_empty_account"),
    (67, .la .x5 "bara_skip_modeled_system"),
    (72, .la .x5 "bara_item_len"),
    (75, .jal .x1 "bal_account_is_modeled_system"),
    (82, .la .x5 "bara_item_len"),
    (85, .la .x12 "bara_path"),
    (87, .jal .x1 "bal_account_path"),
    (92, .la .x13 "bara_path"),
    (95, .la .x15 "bara_acct"),
    (97, .la .x16 "bara_acct_len"),
    (99, .jal .x1 "mpt_walk"),
    (103, .la .x25 "bara_empty_account"),
    (108, .la .x25 "bara_acct"),
    (110, .la .x5 "bara_acct_len"),
    (117, .la .x25 "bara_empty_account"),
    (124, .jal .x1 "mset_memcpy"),
    (135, .la .x5 "bara_next_item") ]

def balAccountRecordArrayFunction : String :=
  "bal_account_record_array:\n" ++ emitProgramR balAccountRecordArray_prog balAccountRecordArray_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountRecordArray_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountRecordArrayFunction_eq_prog :
    balAccountRecordArrayFunction = "bal_account_record_array:\n" ++ emitProgramR balAccountRecordArray_prog balAccountRecordArray_relocs := rfl

#guard balAccountRecordArrayFunction.startsWith "bal_account_record_array:\n"
#guard balAccountRecordArray_prog.length = 156
/-- `zisk_bal_account_record_array`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  witness length (u64)
      +16 n (u64)
      +24 BAL list length (u64)
      +32 root hash (32 bytes)
      +64 BAL AccountChanges list bytes, padded to 8 bytes
      then witness section
    Output layout:
      OUTPUT+0  = status
      OUTPUT+8  = records
      OUTPUT+64 = account arena. -/
def ziskBalAccountRecordArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness len\n" ++
  "  ld a5, 16(t0)               # n\n" ++
  "  ld a4, 24(t0)               # BAL list len\n" ++
  "  addi a0, t0, 32             # root hash ptr\n" ++
  "  addi a3, t0, 64             # BAL list ptr\n" ++
  "  add t1, a3, a4; addi t1, t1, 7; andi t1, t1, -8\n" ++
  "  mv a1, t1                   # witness ptr\n" ++
  "  li a6, 0xa0010008           # records out\n" ++
  "  li a7, 0xa0010040           # account arena out\n" ++
  "  jal ra, bal_account_record_array\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lbara_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  balAccountHasStateChangeFunction ++ "\n" ++
  balAccountIsModeledSystemFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  balAccountRecordArrayFunction ++ "\n" ++
  ".Lbara_pdone:"

def ziskBalAccountRecordArrayDataSection : String :=
  ziskMptWalkDataSection ++ "\n" ++
  ziskBalAccountHasStateChangeDataSection ++ "\n" ++
  ziskBalAccountIsModeledSystemDataSection ++ "\n" ++
  ".balign 8\n" ++
  -- CONVERGENCE DEPENDENCY (#10765): paired with the skip in
  -- bal_all_accounts_storage_consistent. This flag is load-bearing until a
  -- rebuilt BAL has BAI-0 system rows; per-tx rows cannot replace explicit replay.
  "bara_skip_modeled_system:\n  .zero 8\n" ++
  "bara_item_off:\n  .zero 8\n" ++
  "bara_item_len:\n  .zero 8\n" ++
  "bara_acct_len:\n  .zero 8\n" ++
  "bara_bal_end:\n  .zero 8\n" ++
  "bara_next_item:\n  .zero 8\n" ++
  "bacp_off:\n  .zero 8\n" ++
  "bacp_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bacp_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bara_path:\n  .zero 64\n" ++
  "bara_acct:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "bara_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 8\n" ++
  "bara_pad:\n  .zero 8"

def ziskBalAccountRecordArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountRecordArrayPrologue
  dataAsm     := ziskBalAccountRecordArrayDataSection
}

end EvmAsm.Codegen
