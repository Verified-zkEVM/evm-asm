/-
  EvmAsm.Codegen.Programs.CommittedStorageLookup

  Bounded reader for the canonical block-level `storage_writes` map.
  It prepares the recipient/slot query exactly like the execution path and
  scans the canonical map's populated prefix.  Canonical rows store their
  value at byte offset 64; the execution log has a different row layout, so
  this reader deliberately does not reuse the execution-log leaf.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## storage_writes_block_latest_value
    a0 = recipient ptr (20B, block context address)
    a1 = slotKey ptr (32B big-endian BAL key)
    a2 = canonical block storage-writes map base (128B entries)
    a3 = map count
    a4 = map capacity
    a5 = out value ptr (32B; written on match)
    a6 = recipient scratch ptr (32B)
    a7 = slot scratch ptr (32B)
    returns:
      a0 = 0 no match, 1 found, 2 count exceeds capacity

    The helper normalizes the query key and scans 128-byte canonical rows.
    The canonical upsert path updates an existing key in place, so a match
    returns the current row value at offset 64. -/
def storageWritesBlockLatestValue_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .BLTU .x14 .x13 (276 : BitVec 13),
    .MV .x8 .x15,
    .MV .x9 .x16,
    .MV .x18 .x17,
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .LI .x5 (0 : Word),
    .LI .x6 (20 : Word),
    .BEQ .x5 .x6 (28 : BitVec 13),
    .ADD .x7 .x10 .x5,
    .LBU .x28 .x7 (0 : BitVec 12),
    .ADD .x7 .x9 .x5,
    .SB .x7 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x5 .x11 (31 : BitVec 12),
    .MV .x6 .x18,
    .LI .x7 (32 : Word),
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x5 (0 : Word),
    .BEQ .x5 .x13 (156 : BitVec 13),
    .SLLI .x6 .x5 (7 : BitVec 6),
    .ADD .x7 .x12 .x6,
    .LD .x28 .x7 (0 : BitVec 12),
    .LD .x29 .x9 (0 : BitVec 12),
    .BNE .x28 .x29 (128 : BitVec 13),
    .LD .x28 .x7 (8 : BitVec 12),
    .LD .x29 .x9 (8 : BitVec 12),
    .BNE .x28 .x29 (116 : BitVec 13),
    .LD .x28 .x7 (16 : BitVec 12),
    .LD .x29 .x9 (16 : BitVec 12),
    .BNE .x28 .x29 (104 : BitVec 13),
    .LD .x28 .x7 (24 : BitVec 12),
    .LD .x29 .x9 (24 : BitVec 12),
    .BNE .x28 .x29 (92 : BitVec 13),
    .LD .x28 .x7 (32 : BitVec 12),
    .LD .x29 .x18 (0 : BitVec 12),
    .BNE .x28 .x29 (80 : BitVec 13),
    .LD .x28 .x7 (40 : BitVec 12),
    .LD .x29 .x18 (8 : BitVec 12),
    .BNE .x28 .x29 (68 : BitVec 13),
    .LD .x28 .x7 (48 : BitVec 12),
    .LD .x29 .x18 (16 : BitVec 12),
    .BNE .x28 .x29 (56 : BitVec 13),
    .LD .x28 .x7 (56 : BitVec 12),
    .LD .x29 .x18 (24 : BitVec 12),
    .BNE .x28 .x29 (44 : BitVec 13),
    .LD .x28 .x7 (64 : BitVec 12),
    .SD .x8 .x28 (0 : BitVec 12),
    .LD .x28 .x7 (72 : BitVec 12),
    .SD .x8 .x28 (8 : BitVec 12),
    .LD .x28 .x7 (80 : BitVec 12),
    .SD .x8 .x28 (16 : BitVec 12),
    .LD .x28 .x7 (88 : BitVec 12),
    .SD .x8 .x28 (24 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (28 : BitVec 21),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-152 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (4 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def storageWritesBlockLatestValue_relocs : RelocTable := []

def storageWritesBlockLatestValueFunction : String :=
  "storage_writes_block_latest_value:\n" ++
    emitProgramR storageWritesBlockLatestValue_prog storageWritesBlockLatestValue_relocs

theorem storageWritesBlockLatestValueFunction_eq_prog :
    storageWritesBlockLatestValueFunction =
      "storage_writes_block_latest_value:\n" ++
        emitProgramR storageWritesBlockLatestValue_prog storageWritesBlockLatestValue_relocs := rfl

#guard storageWritesBlockLatestValueFunction.startsWith "storage_writes_block_latest_value:\n"
#guard storageWritesBlockLatestValue_prog.length = 82

/-! ## Focused ABI probe

    The probe uses a local table because the helper's ABI is intentionally
    independent of the guest's fixed arena address. -/
def ziskStorageWritesBlockLookupPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li t6, 0x40000000; ld s1, 8(t6)\n" ++
  "  la t0, swbl_recipient; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++
  "  la t0, swbl_key_be; li t1, 7; sb t1, 31(t0)\n" ++
  "  la t0, swbl_out; li t1, 0xEE; sd t1, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t0, swbl_table\n" ++
  "  li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0); li t1, 9; sd t1, 32(t0); li t1, 0x55; sd t1, 64(t0)\n" ++
  "  addi t0, t0, 128; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0); li t1, 7; sd t1, 32(t0); li t1, 0x11; sd t1, 64(t0)\n" ++
  "  li a3, 0; li a4, 16384\n" ++
  "  beqz s1, .Lswbl_call\n" ++
  "  li t0, 1; beq s1, t0, .Lswbl_no_match\n" ++
  "  li a3, 2; j .Lswbl_call\n" ++
  ".Lswbl_no_match:\n  li a3, 1\n" ++
  ".Lswbl_call:\n" ++
  "  la a0, swbl_recipient; la a1, swbl_key_be; la a2, swbl_table; la a5, swbl_out; la a6, swbl_recip_scratch; la a7, swbl_slot_scratch\n" ++
  "  jal ra, storage_writes_block_latest_value\n" ++
  "  sd a0, 0(s0); la t0, swbl_out; ld t1, 0(t0); sd t1, 8(s0)\n" ++
  "  j .Lswbl_done\n" ++
  storageWritesBlockLatestValueFunction ++ "\n" ++
  ".Lswbl_done:"

def ziskStorageWritesBlockLookupDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "swbl_table:\n  .zero 256\n" ++
  "swbl_recipient:\n  .zero 32\n" ++
  "swbl_key_be:\n  .zero 32\n" ++
  "swbl_out:\n  .zero 32\n" ++
  "swbl_recip_scratch:\n  .zero 32\n" ++
  "swbl_slot_scratch:\n  .zero 32\n"


end EvmAsm.Codegen
