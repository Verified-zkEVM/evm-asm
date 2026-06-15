/-
  EvmAsm.Codegen.Programs.CommittedStorageLookup

  Bounded consumer-side helper for the cross-transaction committed-storage table.
  It prepares the recipient/slot query exactly like the previous inline
  dispatch path, rejects counts above the named capacity, and delegates the
  last-match scan to `exec_log_latest_value`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.ExecLogLatestValue

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bv_mtx_committed_latest_value
    a0 = recipient ptr (20B, block context address)
    a1 = slotKey ptr (32B big-endian BAL key)
    a2 = committed table base (128B entries)
    a3 = committed table count
    a4 = committed table capacity
    a5 = out value ptr (32B; written on match)
    a6 = recipient scratch ptr (32B)
    a7 = slot scratch ptr (32B)
    returns:
      a0 = 0 no match, 1 found, 2 count exceeds capacity

    The helper zero-pads the 20-byte recipient into a 32-byte exec-log addrHash,
    byte-reverses the BAL big-endian slot key into the little-endian-limb order
    used by runtime SLOAD/SSTORE entries, then scans at most the named committed
    table count. Duplicate matches preserve `exec_log_latest_value` last-wins
    semantics. -/
def committedStorageLatestValueFunction : String :=
  "bv_mtx_committed_latest_value:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  bgtu a3, a4, .Lcslookup_overflow\n" ++
  "  mv s0, a5                    # out value ptr\n" ++
  "  mv s1, a6                    # recipient scratch\n" ++
  "  mv s2, a7                    # LE slot scratch\n" ++
  "  sd zero, 0(s1); sd zero, 8(s1); sd zero, 16(s1); sd zero, 24(s1)\n" ++
  "  li t0, 0\n" ++
  ".Lcslookup_rkey:\n" ++
  "  li t1, 20; beq t0, t1, .Lcslookup_rkey_done\n" ++
  "  add t2, a0, t0; lbu t3, 0(t2); add t2, s1, t0; sb t3, 0(t2); addi t0, t0, 1; j .Lcslookup_rkey\n" ++
  ".Lcslookup_rkey_done:\n" ++
  "  addi t0, a1, 31; mv t1, s2; li t2, 32\n" ++
  ".Lcslookup_slot_rev:\n" ++
  "  beqz t2, .Lcslookup_call\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; j .Lcslookup_slot_rev\n" ++
  ".Lcslookup_call:\n" ++
  "  mv a0, s1; mv a1, s2; mv a4, s0\n" ++
  "  jal ra, exec_log_latest_value\n" ++
  "  beqz a0, .Lcslookup_no_match\n" ++
  "  li a0, 1; j .Lcslookup_ret\n" ++
  ".Lcslookup_no_match:\n" ++
  "  li a0, 0; j .Lcslookup_ret\n" ++
  ".Lcslookup_overflow:\n" ++
  "  li a0, 2\n" ++
  ".Lcslookup_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_mtx_committed_latest_value`: focused probe.
    Input after ziskemu's length wrapper:
      +8 mode: 0 empty, 1 no-match, 2 one-match, 3 duplicate latest, 4 over-capacity
    Output:
      +0 returned status
      +8 output value low word
      +16 recipient scratch low word
      +24 slot scratch low word -/
def ziskCommittedStorageLookupPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li t6, 0x40000000; ld s1, 8(t6)\n" ++
  "  la t0, csl_recipient; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0)\n" ++
  "  la t0, csl_key_be; li t1, 7; sb t1, 31(t0)\n" ++
  "  la t0, csl_out; li t1, 0xEE; sd t1, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t0, csl_table\n" ++
  "  li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0); li t1, 9; sd t1, 32(t0); li t1, 0x55; sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0); li t1, 7; sd t1, 32(t0); li t1, 0x11; sd t1, 96(t0)\n" ++
  "  addi t0, t0, 128; li t1, 0xAA; sb t1, 0(t0); li t1, 0xBB; sb t1, 19(t0); li t1, 7; sd t1, 32(t0); li t1, 0x33; sd t1, 96(t0)\n" ++
  "  li a3, 0; li a4, 3\n" ++
  "  beqz s1, .Lcsl_call\n" ++
  "  li t0, 1; beq s1, t0, .Lcsl_no_match\n" ++
  "  li t0, 2; beq s1, t0, .Lcsl_one_match\n" ++
  "  li t0, 3; beq s1, t0, .Lcsl_duplicate\n" ++
  "  li a3, 4; j .Lcsl_call\n" ++
  ".Lcsl_no_match:\n  li a3, 1; j .Lcsl_call\n" ++
  ".Lcsl_one_match:\n  li a3, 2; j .Lcsl_call\n" ++
  ".Lcsl_duplicate:\n  li a3, 3\n" ++
  ".Lcsl_call:\n" ++
  "  la a0, csl_recipient; la a1, csl_key_be; la a2, csl_table; la a5, csl_out; la a6, csl_recip_scratch; la a7, csl_slot_scratch\n" ++
  "  jal ra, bv_mtx_committed_latest_value\n" ++
  "  sd a0, 0(s0); la t0, csl_out; ld t1, 0(t0); sd t1, 8(s0); la t0, csl_recip_scratch; ld t1, 0(t0); sd t1, 16(s0); la t0, csl_slot_scratch; ld t1, 0(t0); sd t1, 24(s0)\n" ++
  "  j .Lcsl_done\n" ++
  committedStorageLatestValueFunction ++ "\n" ++
  execLogLatestValueFunction ++ "\n" ++
  ".Lcsl_done:"

def ziskCommittedStorageLookupDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "csl_table:\n  .zero 512\n" ++
  "csl_recipient:\n  .zero 32\n" ++
  "csl_key_be:\n  .zero 32\n" ++
  "csl_out:\n  .zero 32\n" ++
  "csl_recip_scratch:\n  .zero 32\n" ++
  "csl_slot_scratch:\n  .zero 32\n"

def ziskCommittedStorageLookupProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCommittedStorageLookupPrologue
  dataAsm     := ziskCommittedStorageLookupDataSection
}

end EvmAsm.Codegen
