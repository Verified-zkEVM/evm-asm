/-
  EvmAsm.Codegen.Programs.BalStorageReadsExecLog

  `bal_storage_reads_in_exec_log` (bead bmvmx.1.6.7) — verify a BAL account's
  `storage_reads` (AccountChanges item 2) against execution. EIP-7928 records
  storage_reads (slots accessed but not net-changed) and commits them via the block
  access-list hash — but reads do NOT affect the state root, so this is NOT covered
  by the post-state-root comparison. Checking it against the persistent exec log
  (which records every SLOAD) catches a BAL that fabricates a read of a slot the
  account never accessed.

  Direction (forward): every BAL storage_read slot must appear in the exec log keyed
  on the account. (The converse — every exec access is a BAL read-or-change — is a
  follow-up.) Single-tx scope; the multi-tx (block_access_index) tuple layer is
  bmvmx.1.6.6.

  Exec-log entry (Storage.lean): 128 B = addrHash@0, slotKey@32, original@64,
  current@96. storage_reads keys are RLP-minimal big-endian U256; this byte-reverses
  them into EVM-stack order (4 LE u64 limbs) to match the exec-log slotKey.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_storage_reads_in_exec_log

    Calling convention:
      a0 = account address ptr (32-byte addrHash, as keyed in the exec log)
      a1 = AccountChanges RLP ptr   a2 = AccountChanges RLP length
      a3 = exec storage-log base    a4 = exec storage-log length (entry count)
    Returns:
      a0 = 0 if every storage_read slot the BAL claims for the account appears in the
           exec log keyed on the account; 1 on any claimed read absent from the log
           (or parse failure → conservative reject). An empty/absent storage_reads
           list trivially returns 0. -/
def balStorageReadsInExecLogFunction : String :=
  "bal_storage_reads_in_exec_log:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                    # account addr ptr (addrHash)\n" ++
  "  mv s1, a3                    # log base\n" ++
  "  mv s2, a4                    # log length\n" ++
  "  mv s6, a1                    # AccountChanges ptr\n" ++
  -- storage_reads = AccountChanges item 2.
  "  mv a0, a1; mv a1, a2; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbsre_reject        # malformed AccountChanges -> conservative\n" ++
  "  mv s6, a1                    # AccountChanges end\n" ++
  "  jal ra, rlp_walk_next        # item 0 = address\n" ++
  "  bnez a1, .Lbsre_reject\n" ++
  "  mv a1, s6; jal ra, rlp_walk_next          # item 1 = storage_changes\n" ++
  "  bnez a1, .Lbsre_reject\n" ++
  "  mv a1, s6; jal ra, rlp_walk_next          # item 2 = storage_reads\n" ++
  "  bnez a1, .Lbsre_reject\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbsre_reject\n" ++
  "  mv s3, a0                    # storage_reads cursor\n" ++
  "  mv s4, a1                    # storage_reads end\n" ++
  ".Lbsre_loop:\n" ++
  "  beq s3, s4, .Lbsre_match\n" ++
  -- Next read key (a canonical minimal big-endian U256 byte string).
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbsre_reject\n" ++
  "  mv s3, a0\n" ++
  "  sub t1, a0, a2                                   # content ptr (BE, MSB first)\n" ++
  "  mv t2, a2                                        # content length\n" ++
  "  li t0, 32; bgtu t2, t0, .Lbsre_reject\n" ++
  "  beqz t2, .Lbsre_key_canon\n" ++
  "  lbu t0, 0(t1); beqz t0, .Lbsre_reject             # non-canonical scalar\n" ++
  ".Lbsre_key_canon:\n" ++
  -- Build the stack-word key in bsr_krev: zero 32 B, then for the klen content bytes
  -- (big-endian at s3+koff) write reversed into the low bytes (LE limbs).
  "  la t0, bsr_krev\n" ++
  "  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  add t3, t1, t2; addi t3, t3, -1                   # last content byte (LSB)\n" ++
  "  mv t4, t0                                          # dst = bsr_krev (low byte first)\n" ++
  "  mv t5, t2\n" ++
  ".Lbsre_rev:\n" ++
  "  beqz t5, .Lbsre_revd\n  lbu a5, 0(t3); sb a5, 0(t4); addi t3, t3, -1; addi t4, t4, 1; addi t5, t5, -1; j .Lbsre_rev\n" ++
  ".Lbsre_revd:\n" ++
  -- Scan the exec log for (addrHash == s0, slotKey == bsr_krev).
  "  mv t2, s2\n" ++
  "  beqz t2, .Lbsre_reject        # empty log but a read claimed\n" ++
  "  slli t3, t2, 7; add t3, s1, t3      # past last entry\n" ++
  "  la t6, bsr_krev\n" ++
  ".Lbsre_scan:\n" ++
  "  addi t3, t3, -128            # entry ptr\n" ++
  "  ld t4, 0(t3);  ld t5, 0(s0);  bne t4, t5, .Lbsre_next\n" ++
  "  ld t4, 8(t3);  ld t5, 8(s0);  bne t4, t5, .Lbsre_next\n" ++
  "  ld t4, 16(t3); ld t5, 16(s0); bne t4, t5, .Lbsre_next\n" ++
  "  ld t4, 24(t3); ld t5, 24(s0); bne t4, t5, .Lbsre_next\n" ++
  "  ld t4, 32(t3); ld t5, 0(t6);  bne t4, t5, .Lbsre_next\n" ++
  "  ld t4, 40(t3); ld t5, 8(t6);  bne t4, t5, .Lbsre_next\n" ++
  "  ld t4, 48(t3); ld t5, 16(t6); bne t4, t5, .Lbsre_next\n" ++
  "  ld t4, 56(t3); ld t5, 24(t6); bne t4, t5, .Lbsre_next\n" ++
  "  j .Lbsre_advance              # this read slot was accessed -> next read\n" ++
  ".Lbsre_next:\n" ++
  "  mv t4, s1; bne t3, t4, .Lbsre_scan   # not yet at the first entry -> keep scanning\n" ++
  "  j .Lbsre_reject               # scanned whole log, slot never accessed\n" ++
  ".Lbsre_advance:\n" ++
  "  j .Lbsre_loop\n" ++
  ".Lbsre_match:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbsre_ret\n" ++
  ".Lbsre_reject:\n" ++
  "  li a0, 1\n" ++
  ".Lbsre_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- Scratch for `bal_storage_reads_in_exec_log`. -/
def balStorageReadsInExecLogData : String :=
  ".balign 8\n" ++
  ".balign 32\n" ++
  "bsr_krev:\n  .zero 32\n"

/-- `zisk_bal_storage_reads_in_exec_log`: probe. Exec log (addrHash A=0xAA): slot 7
    accessed (read), slot 9 accessed. AccountChanges with storage_reads [7, 9]:
      +0  both reads present                -> 0
      +8  storage_reads [7, 0x0b] (0x0b absent from the log) -> 1 -/
def ziskBalStorageReadsExecLogPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- 2-entry exec log: (A, slot7, _, _), (A, slot9, _, _).
  "  la t0, bsre_log\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x07; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  sd x0, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  sd x0, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++
  "  addi t0, t0, 128\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x09; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  sd x0, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  sd x0, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++
  "  la t0, bsre_addr; li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  -- AccountChanges: f8 LL  94 <20 zero>  c0(storage_changes)  c2 07 09(storage_reads)  c0 c0 c0
  -- content: addr(21) + c0(1) + [c2 07 09](3) + c0 c0 c0(3) = 28 -> 0xf8 0x1c.
  "  la t0, bsre_acct\n" ++
  "  li t1, 0xf8; sb t1, 0(t0); li t1, 0x1c; sb t1, 1(t0); li t1, 0x94; sb t1, 2(t0)\n" ++
  "  li t2, 20; addi t3, t0, 3\n" ++
  "1:\n  beqz t2, 2f\n  sb zero, 0(t3); addi t3, t3, 1; addi t2, t2, -1; j 1b\n" ++
  "2:\n" ++
  "  li t1, 0xc0; sb t1, 23(t0)\n" ++                          -- storage_changes = []
  "  li t1, 0xc2; sb t1, 24(t0); li t1, 0x07; sb t1, 25(t0); li t1, 0x09; sb t1, 26(t0)\n" ++  -- storage_reads = [7,9]
  "  li t1, 0xc0; sb t1, 27(t0); sb t1, 28(t0); sb t1, 29(t0)\n" ++   -- balance/nonce/code = []
  -- stash AccountChanges ptr for the helper.
  "  la a0, bsre_addr; la a1, bsre_acct; li a2, 30; la a3, bsre_log; li a4, 2\n" ++
  "  jal ra, bal_storage_reads_in_exec_log\n" ++
  "  sd a0, 0(s0)\n" ++
  -- Scenario 2: storage_reads = [7, 0x0b] (0x0b absent) -> reject.
  "  la t0, bsre_acct; li t1, 0x0b; sb t1, 26(t0)\n" ++         -- change second read key 0x09 -> 0x0b
  "  la a0, bsre_addr; la a1, bsre_acct; li a2, 30; la a3, bsre_log; li a4, 2\n" ++
  "  jal ra, bal_storage_reads_in_exec_log\n" ++
  "  sd a0, 8(s0)\n" ++
  "  j .Lbsre_done\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  balStorageReadsInExecLogFunction ++ "\n" ++
  ".Lbsre_done:"

def ziskBalStorageReadsExecLogDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bsre_log:\n  .zero 512\n" ++
  "bsre_addr:\n  .zero 32\n" ++
  "bsre_acct:\n  .zero 64\n" ++
  balStorageReadsInExecLogData

def ziskBalStorageReadsExecLogProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalStorageReadsExecLogPrologue
  dataAsm     := ziskBalStorageReadsExecLogDataSection
}

end EvmAsm.Codegen
