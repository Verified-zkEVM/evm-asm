/-
  EvmAsm.Codegen.Programs.CommittedStorageSnapshot

  Leaf helper for cross-transaction committed-storage threading. After a tx
  executes, the multi-tx verdict loop snapshots that tx's live storage exec-log
  entries into `bv_mtx_committed`, re-keying `addrHash` to the tx recipient so a
  later tx can preload the latest already-committed value for the same account.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictParams

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
def committedStorageSnapshotAppendFunction : String :=
  "bv_mtx_committed_snapshot_append:\n" ++
  "  li t0, 0                      # j = 0\n" ++
  ".Lcssa_loop:\n" ++
  "  beq t0, a2, .Lcssa_done\n" ++
  "  bgeu a4, a5, .Lcssa_overflow\n" ++
  "  slli t1, t0, 7; add t1, a1, t1   # src = live[j]\n" ++
  "  slli t2, a4, 7; add t2, a3, t2   # dst = table[count]\n" ++
  "  sd zero, 0(t2); sd zero, 8(t2); sd zero, 16(t2); sd zero, 24(t2)\n" ++
  "  li t3, 0\n" ++
  ".Lcssa_addr:\n" ++
  "  li t4, 20; beq t3, t4, .Lcssa_addr_done\n" ++
  "  add t5, a0, t3; lbu t6, 0(t5); add t5, t2, t3; sb t6, 0(t5); addi t3, t3, 1; j .Lcssa_addr\n" ++
  ".Lcssa_addr_done:\n" ++
  "  ld t3, 32(t1);  sd t3, 32(t2);  ld t3, 40(t1);  sd t3, 40(t2)\n" ++
  "  ld t3, 48(t1);  sd t3, 48(t2);  ld t3, 56(t1);  sd t3, 56(t2)\n" ++
  "  ld t3, 64(t1);  sd t3, 64(t2);  ld t3, 72(t1);  sd t3, 72(t2)\n" ++
  "  ld t3, 80(t1);  sd t3, 80(t2);  ld t3, 88(t1);  sd t3, 88(t2)\n" ++
  "  ld t3, 96(t1);  sd t3, 96(t2);  ld t3, 104(t1); sd t3, 104(t2)\n" ++
  "  ld t3, 112(t1); sd t3, 112(t2); ld t3, 120(t1); sd t3, 120(t2)\n" ++
  "  addi a4, a4, 1; addi t0, t0, 1; j .Lcssa_loop\n" ++
  ".Lcssa_overflow:\n" ++
  "  li t0, 1; sd t0, 0(a6); mv a0, a4; li a1, 1; ret\n" ++
  ".Lcssa_done:\n" ++
  "  mv a0, a4; li a1, 0; ret"

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
def committedStorageSnapshotUpsertFunction : String :=
  "bv_mtx_committed_snapshot_upsert:\n" ++
  "  li t0, 0                      # j = 0\n" ++
  ".Lcssu_loop:\n" ++
  "  beq t0, a2, .Lcssu_done\n" ++
  "  slli t1, t0, 7; add t1, a1, t1   # src = live[j]\n" ++
  "  li t2, 0                      # i = 0\n" ++
  ".Lcssu_scan:\n" ++
  "  beq t2, a4, .Lcssu_no_match\n" ++
  "  slli t3, t2, 7; add t3, a3, t3   # entry = table[i]\n" ++
  "  li t4, 0\n" ++
  ".Lcssu_addr_cmp:\n" ++
  "  li t5, 20; beq t4, t5, .Lcssu_slot_cmp\n" ++
  "  add t5, a0, t4; lbu t5, 0(t5); add t6, t3, t4; lbu t6, 0(t6); bne t5, t6, .Lcssu_next_entry\n" ++
  "  addi t4, t4, 1; j .Lcssu_addr_cmp\n" ++
  ".Lcssu_slot_cmp:\n" ++
  "  ld t5, 32(t1);  ld t6, 32(t3);  bne t5, t6, .Lcssu_next_entry\n" ++
  "  ld t5, 40(t1);  ld t6, 40(t3);  bne t5, t6, .Lcssu_next_entry\n" ++
  "  ld t5, 48(t1);  ld t6, 48(t3);  bne t5, t6, .Lcssu_next_entry\n" ++
  "  ld t5, 56(t1);  ld t6, 56(t3);  bne t5, t6, .Lcssu_next_entry\n" ++
  "  j .Lcssu_store_payload\n" ++
  ".Lcssu_next_entry:\n" ++
  "  addi t2, t2, 1; j .Lcssu_scan\n" ++
  ".Lcssu_no_match:\n" ++
  "  bgeu a4, a5, .Lcssu_overflow\n" ++
  "  slli t3, a4, 7; add t3, a3, t3   # dst = table[count]\n" ++
  "  sd zero, 0(t3); sd zero, 8(t3); sd zero, 16(t3); sd zero, 24(t3)\n" ++
  "  li t4, 0\n" ++
  ".Lcssu_addr_copy:\n" ++
  "  li t5, 20; beq t4, t5, .Lcssu_store_payload_append\n" ++
  "  add t5, a0, t4; lbu t6, 0(t5); add t5, t3, t4; sb t6, 0(t5); addi t4, t4, 1; j .Lcssu_addr_copy\n" ++
  ".Lcssu_store_payload_append:\n" ++
  "  addi a4, a4, 1\n" ++
  ".Lcssu_store_payload:\n" ++
  "  ld t4, 32(t1);  sd t4, 32(t3);  ld t4, 40(t1);  sd t4, 40(t3)\n" ++
  "  ld t4, 48(t1);  sd t4, 48(t3);  ld t4, 56(t1);  sd t4, 56(t3)\n" ++
  "  ld t4, 64(t1);  sd t4, 64(t3);  ld t4, 72(t1);  sd t4, 72(t3)\n" ++
  "  ld t4, 80(t1);  sd t4, 80(t3);  ld t4, 88(t1);  sd t4, 88(t3)\n" ++
  "  ld t4, 96(t1);  sd t4, 96(t3);  ld t4, 104(t1); sd t4, 104(t3)\n" ++
  "  ld t4, 112(t1); sd t4, 112(t3); ld t4, 120(t1); sd t4, 120(t3)\n" ++
  "  addi t0, t0, 1; j .Lcssu_loop\n" ++
  ".Lcssu_overflow:\n" ++
  "  li t0, 1; sd t0, 0(a6); mv a0, a4; li a1, 1; ret\n" ++
  ".Lcssu_done:\n" ++
  "  mv a0, a4; li a1, 0; ret"

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
