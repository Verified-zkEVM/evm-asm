/-
  EvmAsm.Codegen.Programs.CommittedStorageSnapshot

  Leaf helper for cross-transaction committed-storage threading. After a tx
  executes, the multi-tx verdict loop snapshots that tx's live storage exec-log
  entries into `bv_mtx_committed`, re-keying `addrHash` to the tx recipient so a
  later tx can preload the latest already-committed value for the same account.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bv_mtx_committed_snapshot_append
    a0 = recipient ptr (20B)
    a1 = live storage log base (128B entries)
    a2 = live storage log entry count
    a3 = committed table base (128B entries)
    a4 = committed table count
    a5 = committed table capacity
    a6 = overflow status ptr (u64; set to 1 on overflow)
    returns:
      a0 = new committed table count
      a1 = status (0 ok, 1 overflow)

    For each live entry, append a 128-byte committed entry with addrHash zeroed
    then recipient[0..20] copied into bytes 0..20. Slot/original/current payload
    bytes are copied from the live entry. Overflow is checked before each append,
    so the first out-of-capacity entry leaves table memory untouched. -/
def bvMtxCommittedSnapshotAppend_prog : Program :=
  [ .LI .x5 (0 : Word),
    .BEQ .x5 .x12 (204 : BitVec 13),
    .BGEU .x14 .x15 (180 : BitVec 13),
    .SLLI .x6 .x5 (7 : BitVec 6),
    .ADD .x6 .x11 .x6,
    .SLLI .x7 .x14 (7 : BitVec 6),
    .ADD .x7 .x13 .x7,
    .SD .x7 .x0 (0 : BitVec 12),
    .SD .x7 .x0 (8 : BitVec 12),
    .SD .x7 .x0 (16 : BitVec 12),
    .SD .x7 .x0 (24 : BitVec 12),
    .LI .x28 (0 : Word),
    .LI .x29 (20 : Word),
    .BEQ .x28 .x29 (28 : BitVec 13),
    .ADD .x30 .x10 .x28,
    .LBU .x31 .x30 (0 : BitVec 12),
    .ADD .x30 .x7 .x28,
    .SB .x30 .x31 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x28 .x6 (32 : BitVec 12),
    .SD .x7 .x28 (32 : BitVec 12),
    .LD .x28 .x6 (40 : BitVec 12),
    .SD .x7 .x28 (40 : BitVec 12),
    .LD .x28 .x6 (48 : BitVec 12),
    .SD .x7 .x28 (48 : BitVec 12),
    .LD .x28 .x6 (56 : BitVec 12),
    .SD .x7 .x28 (56 : BitVec 12),
    .LD .x28 .x6 (64 : BitVec 12),
    .SD .x7 .x28 (64 : BitVec 12),
    .LD .x28 .x6 (72 : BitVec 12),
    .SD .x7 .x28 (72 : BitVec 12),
    .LD .x28 .x6 (80 : BitVec 12),
    .SD .x7 .x28 (80 : BitVec 12),
    .LD .x28 .x6 (88 : BitVec 12),
    .SD .x7 .x28 (88 : BitVec 12),
    .LD .x28 .x6 (96 : BitVec 12),
    .SD .x7 .x28 (96 : BitVec 12),
    .LD .x28 .x6 (104 : BitVec 12),
    .SD .x7 .x28 (104 : BitVec 12),
    .LD .x28 .x6 (112 : BitVec 12),
    .SD .x7 .x28 (112 : BitVec 12),
    .LD .x28 .x6 (120 : BitVec 12),
    .SD .x7 .x28 (120 : BitVec 12),
    .ADDI .x14 .x14 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-180 : BitVec 21),
    .LI .x5 (1 : Word),
    .SD .x16 .x5 (0 : BitVec 12),
    .MV .x10 .x14,
    .LI .x11 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .MV .x10 .x14,
    .LI .x11 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def committedStorageSnapshotAppendFunction : String :=
  "bv_mtx_committed_snapshot_append:\n" ++ emitProgram bvMtxCommittedSnapshotAppend_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bvMtxCommittedSnapshotAppend_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem committedStorageSnapshotAppendFunction_eq_prog :
    committedStorageSnapshotAppendFunction = "bv_mtx_committed_snapshot_append:\n" ++ emitProgram bvMtxCommittedSnapshotAppend_prog := rfl

#guard committedStorageSnapshotAppendFunction.startsWith "bv_mtx_committed_snapshot_append:\n"
#guard bvMtxCommittedSnapshotAppend_prog.length = 55
/-- `zisk_mtx_committed_snapshot_append`: focused probe.
    Input after ziskemu's length wrapper:
      +8  mode: 0 zero-live, 1 one-entry, 2 two-entry, 3 overflow
    Output:
      +0  returned count
      +8  returned status
      +16 stored overflow status
      +24 entry0 addrHash low byte
      +32 entry0 slotKey low byte
      +40 entry0 original low byte
      +48 entry0 current low byte
      +56 entry1 addrHash low byte
      +64 entry1 slotKey low byte
      +72 entry1 current low byte
      +80 sentinel entry3 current low byte, proving overflow did not write past capacity -/
def ziskCommittedStorageSnapshotPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li t6, 0x40000000; ld s1, 8(t6)\n" ++
  "  la t0, cssa_recipient; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++
  "  la t0, cssa_status; sd zero, 0(t0)\n" ++
  "  la t0, cssa_table; li t1, 0xEE; sd t1, 480(t0)\n" ++
  "  la t0, cssa_live\n" ++
  "  li t1, 0x07; sd t1, 32(t0); li t1, 0x42; sd t1, 64(t0); li t1, 0x11; sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; li t1, 0x09; sd t1, 32(t0); li t1, 0x44; sd t1, 64(t0); li t1, 0x33; sd t1, 96(t0)\n" ++
  "  mv a2, zero; li a4, 0; li a5, 3\n" ++
  "  beqz s1, .Lcssap_call\n" ++
  "  li t0, 1; beq s1, t0, .Lcssap_one\n" ++
  "  li t0, 2; beq s1, t0, .Lcssap_two\n" ++
  "  li a2, 2; li a4, 2; li a5, 3; j .Lcssap_call\n" ++
  ".Lcssap_one:\n  li a2, 1; j .Lcssap_call\n" ++
  ".Lcssap_two:\n  li a2, 2\n" ++
  ".Lcssap_call:\n" ++
  "  la a0, cssa_recipient; la a1, cssa_live; la a3, cssa_table; la a6, cssa_status\n" ++
  "  jal ra, bv_mtx_committed_snapshot_append\n" ++
  "  sd a0, 0(s0); sd a1, 8(s0); la t0, cssa_status; ld t1, 0(t0); sd t1, 16(s0)\n" ++
  "  la t0, cssa_table\n" ++
  "  ld t1, 0(t0);   sd t1, 24(s0); ld t1, 32(t0);  sd t1, 32(s0); ld t1, 64(t0);  sd t1, 40(s0); ld t1, 96(t0);  sd t1, 48(s0)\n" ++
  "  ld t1, 128(t0); sd t1, 56(s0); ld t1, 160(t0); sd t1, 64(s0); ld t1, 224(t0); sd t1, 72(s0); ld t1, 480(t0); sd t1, 80(s0)\n" ++
  "  j .Lcssap_done\n" ++
  committedStorageSnapshotAppendFunction ++ "\n" ++
  ".Lcssap_done:"


/-! ## bv_mtx_committed_snapshot_upsert
    a0 = recipient ptr (20B)
    a1 = live storage log base (128B entries)
    a2 = live storage log entry count
    a3 = committed table base (128B entries)
    a4 = committed table count
    a5 = committed table capacity
    a6 = overflow status ptr (u64; set to 1 on overflow)
    returns:
      a0 = new committed table count
      a1 = status (0 ok, 1 overflow)

    For each live entry, find an existing committed entry with the same
    re-keyed recipient bytes and slotKey. Matches update that entry in place,
    preserving latest-write-wins without growing the table. Non-matches append a
    new committed entry, and overflow is reported only when a new unique key
    cannot fit. -/
def bvMtxCommittedSnapshotUpsert_prog : Program :=
  [ .LI .x5 (0 : Word),
    .BEQ .x5 .x12 (320 : BitVec 13),
    .SLLI .x6 .x5 (7 : BitVec 6),
    .ADD .x6 .x11 .x6,
    .LI .x7 (0 : Word),
    .BEQ .x7 .x14 (112 : BitVec 13),
    .SLLI .x28 .x7 (7 : BitVec 6),
    .ADD .x28 .x13 .x28,
    .LI .x29 (0 : Word),
    .LI .x30 (20 : Word),
    .BEQ .x29 .x30 (32 : BitVec 13),
    .ADD .x30 .x10 .x29,
    .LBU .x30 .x30 (0 : BitVec 12),
    .ADD .x31 .x28 .x29,
    .LBU .x31 .x31 (0 : BitVec 12),
    .BNE .x30 .x31 (64 : BitVec 13),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LD .x30 .x6 (32 : BitVec 12),
    .LD .x31 .x28 (32 : BitVec 12),
    .BNE .x30 .x31 (44 : BitVec 13),
    .LD .x30 .x6 (40 : BitVec 12),
    .LD .x31 .x28 (40 : BitVec 12),
    .BNE .x30 .x31 (32 : BitVec 13),
    .LD .x30 .x6 (48 : BitVec 12),
    .LD .x31 .x28 (48 : BitVec 12),
    .BNE .x30 .x31 (20 : BitVec 13),
    .LD .x30 .x6 (56 : BitVec 12),
    .LD .x31 .x28 (56 : BitVec 12),
    .BNE .x30 .x31 (8 : BitVec 13),
    .JAL .x0 (80 : BitVec 21),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-108 : BitVec 21),
    .BGEU .x14 .x15 (172 : BitVec 13),
    .SLLI .x28 .x14 (7 : BitVec 6),
    .ADD .x28 .x13 .x28,
    .SD .x28 .x0 (0 : BitVec 12),
    .SD .x28 .x0 (8 : BitVec 12),
    .SD .x28 .x0 (16 : BitVec 12),
    .SD .x28 .x0 (24 : BitVec 12),
    .LI .x29 (0 : Word),
    .LI .x30 (20 : Word),
    .BEQ .x29 .x30 (28 : BitVec 13),
    .ADD .x30 .x10 .x29,
    .LBU .x31 .x30 (0 : BitVec 12),
    .ADD .x30 .x28 .x29,
    .SB .x30 .x31 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x14 .x14 (1 : BitVec 12),
    .LD .x29 .x6 (32 : BitVec 12),
    .SD .x28 .x29 (32 : BitVec 12),
    .LD .x29 .x6 (40 : BitVec 12),
    .SD .x28 .x29 (40 : BitVec 12),
    .LD .x29 .x6 (48 : BitVec 12),
    .SD .x28 .x29 (48 : BitVec 12),
    .LD .x29 .x6 (56 : BitVec 12),
    .SD .x28 .x29 (56 : BitVec 12),
    .LD .x29 .x6 (64 : BitVec 12),
    .SD .x28 .x29 (64 : BitVec 12),
    .LD .x29 .x6 (72 : BitVec 12),
    .SD .x28 .x29 (72 : BitVec 12),
    .LD .x29 .x6 (80 : BitVec 12),
    .SD .x28 .x29 (80 : BitVec 12),
    .LD .x29 .x6 (88 : BitVec 12),
    .SD .x28 .x29 (88 : BitVec 12),
    .LD .x29 .x6 (96 : BitVec 12),
    .SD .x28 .x29 (96 : BitVec 12),
    .LD .x29 .x6 (104 : BitVec 12),
    .SD .x28 .x29 (104 : BitVec 12),
    .LD .x29 .x6 (112 : BitVec 12),
    .SD .x28 .x29 (112 : BitVec 12),
    .LD .x29 .x6 (120 : BitVec 12),
    .SD .x28 .x29 (120 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-296 : BitVec 21),
    .LI .x5 (1 : Word),
    .SD .x16 .x5 (0 : BitVec 12),
    .MV .x10 .x14,
    .LI .x11 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .MV .x10 .x14,
    .LI .x11 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def committedStorageSnapshotUpsertFunction : String :=
  "bv_mtx_committed_snapshot_upsert:\n" ++ emitProgram bvMtxCommittedSnapshotUpsert_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bvMtxCommittedSnapshotUpsert_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem committedStorageSnapshotUpsertFunction_eq_prog :
    committedStorageSnapshotUpsertFunction = "bv_mtx_committed_snapshot_upsert:\n" ++ emitProgram bvMtxCommittedSnapshotUpsert_prog := rfl

#guard committedStorageSnapshotUpsertFunction.startsWith "bv_mtx_committed_snapshot_upsert:\n"
#guard bvMtxCommittedSnapshotUpsert_prog.length = 84
/-- `zisk_mtx_committed_snapshot_upsert`: focused probe.
    Input after ziskemu's length wrapper:
      +8  mode: 0 zero-live, 1 insert, 2 duplicate, 3 duplicate-plus-new,
          4 overflow for a new unique key, 5 high duplicate-write collapse
    Output matches the append probe shape:
      +0  returned count
      +8  returned status
      +16 stored overflow status
      +24 entry0 addrHash low byte
      +32 entry0 slotKey low byte
      +40 entry0 original low byte
      +48 entry0 current low byte
      +56 entry1 addrHash low byte
      +64 entry1 slotKey low byte
      +72 entry1 current low byte
      +80 sentinel entry3 current low byte, proving overflow did not write past capacity -/
def ziskCommittedStorageSnapshotUpsertPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li t6, 0x40000000; ld s1, 8(t6)\n" ++
  "  la t0, cssu_recipient; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++
  "  la t0, cssu_status; sd zero, 0(t0)\n" ++
  "  la t0, cssu_table; li t1, 0xEE; sd t1, 480(t0)\n" ++
  "  la t0, cssu_live\n" ++
  "  li t1, 0x07; sd t1, 32(t0); li t1, 0x42; sd t1, 64(t0); li t1, 0x11; sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; li t1, 0x07; sd t1, 32(t0); li t1, 0x42; sd t1, 64(t0); li t1, 0x33; sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; li t1, 0x09; sd t1, 32(t0); li t1, 0x44; sd t1, 64(t0); li t1, 0x55; sd t1, 96(t0)\n" ++
  "  mv a2, zero; li a4, 0; li a5, 3\n" ++
  "  beqz s1, .Lcssup_call\n" ++
  "  li t0, 1; beq s1, t0, .Lcssup_one\n" ++
  "  li t0, 2; beq s1, t0, .Lcssup_duplicate\n" ++
  "  li t0, 3; beq s1, t0, .Lcssup_mixed\n" ++
  "  li t0, 4; beq s1, t0, .Lcssup_overflow\n" ++
  "  la t0, cssu_live; li t2, 0\n" ++
  ".Lcssup_highdup_loop:\n" ++
  "  li t3, 130; beq t2, t3, .Lcssup_highdup_done\n" ++
  "  li t1, 0x07; sd t1, 32(t0); li t1, 0x42; sd t1, 64(t0); addi t1, t2, 1; sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; addi t2, t2, 1; j .Lcssup_highdup_loop\n" ++
  ".Lcssup_highdup_done:\n" ++
  "  li a2, 130; li a4, 0; li a5, 128; j .Lcssup_call\n" ++
  ".Lcssup_overflow:\n" ++
  "  li a2, 1; li a4, 3; li a5, 3; j .Lcssup_call\n" ++
  ".Lcssup_one:\n  li a2, 1; j .Lcssup_call\n" ++
  ".Lcssup_duplicate:\n  li a2, 2; j .Lcssup_call\n" ++
  ".Lcssup_mixed:\n  li a2, 3\n" ++
  ".Lcssup_call:\n" ++
  "  la a0, cssu_recipient; la a1, cssu_live; la a3, cssu_table; la a6, cssu_status\n" ++
  "  jal ra, bv_mtx_committed_snapshot_upsert\n" ++
  "  sd a0, 0(s0); sd a1, 8(s0); la t0, cssu_status; ld t1, 0(t0); sd t1, 16(s0)\n" ++
  "  la t0, cssu_table\n" ++
  "  ld t1, 0(t0);   sd t1, 24(s0); ld t1, 32(t0);  sd t1, 32(s0); ld t1, 64(t0);  sd t1, 40(s0); ld t1, 96(t0);  sd t1, 48(s0)\n" ++
  "  ld t1, 128(t0); sd t1, 56(s0); ld t1, 160(t0); sd t1, 64(s0); ld t1, 224(t0); sd t1, 72(s0); ld t1, 480(t0); sd t1, 80(s0)\n" ++
  "  j .Lcssup_done\n" ++
  committedStorageSnapshotUpsertFunction ++ "\n" ++
  ".Lcssup_done:"

def ziskCommittedStorageSnapshotUpsertDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "cssu_live:\n  .zero 16640\n" ++
  "cssu_table:\n  .zero 512\n" ++
  "cssu_recipient:\n  .zero 32\n" ++
  "cssu_status:\n  .zero 8\n"

def ziskCommittedStorageSnapshotUpsertProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCommittedStorageSnapshotUpsertPrologue
  dataAsm     := ziskCommittedStorageSnapshotUpsertDataSection
}


/-! ## bv_mtx_committed_chunked_snapshot_upsert
    a0 = recipient ptr (20B)
    a1 = live storage log base (128B entries)
    a2 = live storage log entry count
    a3 = chunked committed table base (128B entries, contiguous pages)
    a4 = committed table count across all chunks
    a5 = committed table total capacity
    a6 = overflow status ptr (u64; set to 1 on overflow)
    returns:
      a0 = new committed table count
      a1 = status (0 ok, 1 overflow)

    The chunked helper keeps the same 128-byte entry layout as the current
    upsert helper, but its ABI treats a4/a5 as global counts over the contiguous
    chunk pages. Existing keys update in place across page boundaries; new
    unique keys append at the global count and overflow only when total chunked
    capacity is exhausted. -/
def bvMtxCommittedChunkedSnapshotUpsert_prog : Program :=
  [ .LI .x5 (0 : Word),
    .BEQ .x5 .x12 (320 : BitVec 13),
    .SLLI .x6 .x5 (7 : BitVec 6),
    .ADD .x6 .x11 .x6,
    .LI .x7 (0 : Word),
    .BEQ .x7 .x14 (112 : BitVec 13),
    .SLLI .x28 .x7 (7 : BitVec 6),
    .ADD .x28 .x13 .x28,
    .LI .x29 (0 : Word),
    .LI .x30 (20 : Word),
    .BEQ .x29 .x30 (32 : BitVec 13),
    .ADD .x30 .x10 .x29,
    .LBU .x30 .x30 (0 : BitVec 12),
    .ADD .x31 .x28 .x29,
    .LBU .x31 .x31 (0 : BitVec 12),
    .BNE .x30 .x31 (64 : BitVec 13),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LD .x30 .x6 (32 : BitVec 12),
    .LD .x31 .x28 (32 : BitVec 12),
    .BNE .x30 .x31 (44 : BitVec 13),
    .LD .x30 .x6 (40 : BitVec 12),
    .LD .x31 .x28 (40 : BitVec 12),
    .BNE .x30 .x31 (32 : BitVec 13),
    .LD .x30 .x6 (48 : BitVec 12),
    .LD .x31 .x28 (48 : BitVec 12),
    .BNE .x30 .x31 (20 : BitVec 13),
    .LD .x30 .x6 (56 : BitVec 12),
    .LD .x31 .x28 (56 : BitVec 12),
    .BNE .x30 .x31 (8 : BitVec 13),
    .JAL .x0 (80 : BitVec 21),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-108 : BitVec 21),
    .BGEU .x14 .x15 (172 : BitVec 13),
    .SLLI .x28 .x14 (7 : BitVec 6),
    .ADD .x28 .x13 .x28,
    .SD .x28 .x0 (0 : BitVec 12),
    .SD .x28 .x0 (8 : BitVec 12),
    .SD .x28 .x0 (16 : BitVec 12),
    .SD .x28 .x0 (24 : BitVec 12),
    .LI .x29 (0 : Word),
    .LI .x30 (20 : Word),
    .BEQ .x29 .x30 (28 : BitVec 13),
    .ADD .x30 .x10 .x29,
    .LBU .x31 .x30 (0 : BitVec 12),
    .ADD .x30 .x28 .x29,
    .SB .x30 .x31 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x14 .x14 (1 : BitVec 12),
    .LD .x29 .x6 (32 : BitVec 12),
    .SD .x28 .x29 (32 : BitVec 12),
    .LD .x29 .x6 (40 : BitVec 12),
    .SD .x28 .x29 (40 : BitVec 12),
    .LD .x29 .x6 (48 : BitVec 12),
    .SD .x28 .x29 (48 : BitVec 12),
    .LD .x29 .x6 (56 : BitVec 12),
    .SD .x28 .x29 (56 : BitVec 12),
    .LD .x29 .x6 (64 : BitVec 12),
    .SD .x28 .x29 (64 : BitVec 12),
    .LD .x29 .x6 (72 : BitVec 12),
    .SD .x28 .x29 (72 : BitVec 12),
    .LD .x29 .x6 (80 : BitVec 12),
    .SD .x28 .x29 (80 : BitVec 12),
    .LD .x29 .x6 (88 : BitVec 12),
    .SD .x28 .x29 (88 : BitVec 12),
    .LD .x29 .x6 (96 : BitVec 12),
    .SD .x28 .x29 (96 : BitVec 12),
    .LD .x29 .x6 (104 : BitVec 12),
    .SD .x28 .x29 (104 : BitVec 12),
    .LD .x29 .x6 (112 : BitVec 12),
    .SD .x28 .x29 (112 : BitVec 12),
    .LD .x29 .x6 (120 : BitVec 12),
    .SD .x28 .x29 (120 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-296 : BitVec 21),
    .LI .x5 (1 : Word),
    .SD .x16 .x5 (0 : BitVec 12),
    .MV .x10 .x14,
    .LI .x11 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .MV .x10 .x14,
    .LI .x11 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def committedStorageChunkedSnapshotUpsertFunction : String :=
  "bv_mtx_committed_chunked_snapshot_upsert:\n" ++ emitProgram bvMtxCommittedChunkedSnapshotUpsert_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bvMtxCommittedChunkedSnapshotUpsert_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem committedStorageChunkedSnapshotUpsertFunction_eq_prog :
    committedStorageChunkedSnapshotUpsertFunction = "bv_mtx_committed_chunked_snapshot_upsert:\n" ++ emitProgram bvMtxCommittedChunkedSnapshotUpsert_prog := rfl

#guard committedStorageChunkedSnapshotUpsertFunction.startsWith "bv_mtx_committed_chunked_snapshot_upsert:\n"
#guard bvMtxCommittedChunkedSnapshotUpsert_prog.length = 84
/-- `zisk_mtx_committed_chunked_snapshot_upsert`: focused probe.
    Input after ziskemu's length wrapper:
      +8 mode: 0 zero-live, 1 129 unique inserts, 2 duplicate update across
          chunk boundary, 3 exact full-capacity fill, 4 overflow one unique
          beyond full capacity
    Output:
      +0 returned count
      +8 returned status
      +16 stored overflow status
      +24 entry0 slotKey low byte
      +32 entry0 current low byte
      +40 entry128 slotKey low byte
      +48 entry128 current low byte
      +56 entry511 current low byte
      +64 sentinel word after capacity -/
def ziskCommittedStorageChunkedSnapshotUpsertPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li t6, 0x40000000; ld s1, 8(t6)\n" ++
  "  la t0, cscsu_recipient; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++
  "  la t0, cscsu_status; sd zero, 0(t0)\n" ++
  "  la t0, cscsu_table; li t1, 0xEE; li t2, 65536; add t0, t0, t2; sd t1, 0(t0)\n" ++
  "  la t0, cscsu_live; li t2, 0\n" ++
  ".Lcscsup_seed_live_loop:\n" ++
  "  li t3, 129; beq t2, t3, .Lcscsup_seed_live_done\n" ++
  "  addi t1, t2, 1; sd t1, 32(t0); sd t1, 64(t0); sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; addi t2, t2, 1; j .Lcscsup_seed_live_loop\n" ++
  ".Lcscsup_seed_live_done:\n" ++
  "  li a2, 0; li a4, 0; li a5, 512\n" ++
  "  beqz s1, .Lcscsup_call\n" ++
  "  li t0, 1; beq s1, t0, .Lcscsup_129_unique\n" ++
  "  li t0, 2; beq s1, t0, .Lcscsup_cross_duplicate\n" ++
  "  li t0, 3; beq s1, t0, .Lcscsup_full_fill\n" ++
  "  j .Lcscsup_overflow\n" ++
  ".Lcscsup_129_unique:\n  li a2, 129; j .Lcscsup_call\n" ++
  ".Lcscsup_cross_duplicate:\n" ++
  "  la t0, cscsu_table; li t2, 0\n" ++
  ".Lcscsup_seed_table_loop:\n" ++
  "  li t3, 130; beq t2, t3, .Lcscsup_seed_table_done\n" ++
  "  li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0); addi t1, t2, 1; sd t1, 32(t0); sd t1, 64(t0); sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; addi t2, t2, 1; j .Lcscsup_seed_table_loop\n" ++
  ".Lcscsup_seed_table_done:\n" ++
  "  la t0, cscsu_live; li t1, 129; sd t1, 32(t0); sd t1, 64(t0); li t1, 0x77; sd t1, 96(t0)\n" ++
  "  li a2, 1; li a4, 130; j .Lcscsup_call\n" ++
  ".Lcscsup_full_fill:\n" ++
  "  la t0, cscsu_live; li t1, 512; sd t1, 32(t0); sd t1, 64(t0); li t1, 0x66; sd t1, 96(t0)\n" ++
  "  li a2, 1; li a4, 511; j .Lcscsup_call\n" ++
  ".Lcscsup_overflow:\n" ++
  "  la t0, cscsu_live; li t1, 513; sd t1, 32(t0); sd t1, 64(t0); li t1, 0x55; sd t1, 96(t0)\n" ++
  "  li a2, 1; li a4, 512\n" ++
  ".Lcscsup_call:\n" ++
  "  la a0, cscsu_recipient; la a1, cscsu_live; la a3, cscsu_table; la a6, cscsu_status\n" ++
  "  jal ra, bv_mtx_committed_chunked_snapshot_upsert\n" ++
  "  sd a0, 0(s0); sd a1, 8(s0); la t0, cscsu_status; ld t1, 0(t0); sd t1, 16(s0)\n" ++
  "  la t0, cscsu_table\n" ++
  "  ld t1, 32(t0); sd t1, 24(s0); ld t1, 96(t0); sd t1, 32(s0)\n" ++
  "  li t2, 16384; add t3, t0, t2; ld t1, 32(t3); sd t1, 40(s0); ld t1, 96(t3); sd t1, 48(s0)\n" ++
  "  li t2, 65408; add t3, t0, t2; ld t1, 96(t3); sd t1, 56(s0)\n" ++
  "  li t2, 65536; add t3, t0, t2; ld t1, 0(t3); sd t1, 64(s0)\n" ++
  "  j .Lcscsup_done\n" ++
  committedStorageChunkedSnapshotUpsertFunction ++ "\n" ++
  ".Lcscsup_done:"

def ziskCommittedStorageChunkedSnapshotUpsertDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "cscsu_live:\n  .zero 16640\n" ++
  "cscsu_table:\n  .zero 65544\n" ++
  "cscsu_recipient:\n  .zero 32\n" ++
  "cscsu_status:\n  .zero 8\n"

def ziskCommittedStorageChunkedSnapshotUpsertProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCommittedStorageChunkedSnapshotUpsertPrologue
  dataAsm     := ziskCommittedStorageChunkedSnapshotUpsertDataSection
}

def ziskCommittedStorageSnapshotDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "cssa_live:\n  .zero 256\n" ++
  "cssa_table:\n  .zero 512\n" ++
  "cssa_recipient:\n  .zero 32\n" ++
  "cssa_status:\n  .zero 8\n"

def ziskCommittedStorageSnapshotProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCommittedStorageSnapshotPrologue
  dataAsm     := ziskCommittedStorageSnapshotDataSection
}

end EvmAsm.Codegen
