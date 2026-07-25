/-
  EvmAsm.Codegen.Programs.BalStorageMatchesExecLog

  `bal_storage_matches_exec_log` (bead bmvmx.1.6.2) — the core of the
  execution-vs-BAL storage consistency check. Given one account's BAL
  AccountChanges and the execution-time persistent storage log, verify that EVERY
  storage change the BAL claims for that account was actually produced by
  execution with the matching final value. A mismatch means the prover-supplied
  BAL is NOT what execution produced — the verdict rejects (succ=0).

  This composes `bal_storage_change_values` (the BAL post-value parser, 1.6.1) and
  a SLOAD-style scan of the exec log (per-contract `addrHash` keying, last-write-
  wins). It is a self-contained, unit-probeable helper; the verdict wiring (call
  it after the contract dispatch and branch to a reject on mismatch) is a small
  follow-up that also depends on the recipient storage-preload re-tag (#8561) so
  the exec log's recipient entries are keyed on the recipient address.

  Exec-log entry layout (Storage.lean): 128 bytes = addrHash@0, slotKey@32,
  original@64, current@96.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalStorageChangeValues
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_storage_matches_exec_log

    Calling convention:
      a0 = account address ptr (32-byte addrHash, as keyed in the exec log)
      a1 = AccountChanges RLP ptr   a2 = AccountChanges RLP length
      a3 = exec storage-log base    a4 = exec storage-log length (entry count)
    Returns:
      a0 = 0 if every BAL storage_change for the account is reproduced by the exec
           log with the matching final value; 1 on ANY mismatch (claimed change
           absent from the log, or present with a different final value) or on BAL
           parse failure (conservative reject).

    Direction: BAL ⊆ execution (every claimed change must be produced). The
    converse (execution produced a change the BAL omits) is a follow-up. -/
def balStorageMatchesExecLogFunction : String :=
  "bal_storage_matches_exec_log:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                    # account addr ptr (addrHash)\n" ++
  "  mv s1, a3                    # log base\n" ++
  "  mv s2, a4                    # log length\n" ++
  -- Parse the BAL storage_changes into (keys, post-values).
  "  mv a0, a1; mv a1, a2; la a2, bsme_keys; la a3, bsme_vals\n" ++
  "  jal ra, bal_storage_change_values\n" ++
  "  mv s3, a0                    # change count\n" ++
  "  beqz s3, .Lbsme_match        # no claimed changes -> trivially consistent\n" ++
  "  mv s4, zero                  # i\n" ++
  ".Lbsme_loop:\n" ++
  "  beq s4, s3, .Lbsme_match\n" ++
  "  slli t0, s4, 5\n" ++
  "  la t1, bsme_keys; add s5, t1, t0    # key ptr (big-endian)\n" ++
  "  la t1, bsme_vals; add s6, t1, t0    # BAL post-value ptr (big-endian)\n" ++
  -- The BAL key/value are big-endian (RLP); the exec log stores slotKey/current
  -- in EVM-stack order (LE u64 limbs, low first). Byte-reverse the BAL key and
  -- value into the contiguous scratch (bsme_krev @+0, bsme_vrev @+32) so the
  -- limb compares below match the exec-log layout.
  "  la t1, bsme_krev; addi t2, s5, 31; li t0, 32\n" ++
  ".Lbsme_revk:\n" ++
  "  beqz t0, .Lbsme_revkd\n  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t0, t0, -1; j .Lbsme_revk\n" ++
  ".Lbsme_revkd:\n" ++
  "  la t1, bsme_vrev; addi t2, s6, 31; li t0, 32\n" ++
  ".Lbsme_revv:\n" ++
  "  beqz t0, .Lbsme_revvd\n  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t0, t0, -1; j .Lbsme_revv\n" ++
  ".Lbsme_revvd:\n" ++
  "  la t6, bsme_krev                    # t6 = reversed key (krev@+0, vrev@+32)\n" ++
  -- lv44p: FIRST consult the captured system-call SSTORE log (bv_system_storage_log,
  -- count = bv_system_storage_log_count). Those rows are the ACTUAL end-of-block
  -- EIP-7002/7251 system-transaction storage writes (queue head/tail/slot-count
  -- dequeues) that the per-tx exec log does NOT record (the verdict restores the
  -- exec-log count after the system-call replay; the writes are captured into this
  -- side arena instead — BlockVerdictStateRoot capture). They are the GENUINELY LAST
  -- writes for the predeploy's slots, so when the BAL's declared (addr,slot) appears
  -- in the system log, that captured value IS the final value to compare against. This
  -- closes the bv34/37 false-rejects on the 7002/7251 predeploys WITHOUT skipping any
  -- account: a forged BAL value still mismatches the captured actual value -> reject.
  -- Same 128-byte row layout (addrHash@0, slotKey@32, original@64, current@96). In the
  -- focused probes bv_system_storage_log_count = 0, so this scan is inert there.
  "  la t0, bv_system_storage_log_count; ld t2, 0(t0)\n" ++
  "  beqz t2, .Lbsme_uarena_scan # no captured system rows -> user side arena\n" ++
  "  la t1, bv_system_storage_log; slli t3, t2, 7; add t3, t1, t3   # past last system entry\n" ++
  ".Lbsme_sys_scan:\n" ++
  "  addi t3, t3, -128\n" ++
  "  ld t4, 0(t3);  ld t5, 0(s0);  bne t4, t5, .Lbsme_sys_next\n" ++
  "  ld t4, 8(t3);  ld t5, 8(s0);  bne t4, t5, .Lbsme_sys_next\n" ++
  "  ld t4, 16(t3); ld t5, 16(s0); bne t4, t5, .Lbsme_sys_next\n" ++
  "  ld t4, 24(t3); ld t5, 24(s0); bne t4, t5, .Lbsme_sys_next\n" ++
  "  ld t4, 32(t3); ld t5, 0(t6);  bne t4, t5, .Lbsme_sys_next\n" ++
  "  ld t4, 40(t3); ld t5, 8(t6);  bne t4, t5, .Lbsme_sys_next\n" ++
  "  ld t4, 48(t3); ld t5, 16(t6); bne t4, t5, .Lbsme_sys_next\n" ++
  "  ld t4, 56(t3); ld t5, 24(t6); bne t4, t5, .Lbsme_sys_next\n" ++
  -- System log has the (addr,slot): this captured value is the final write.
  "  ld t4, 96(t3);  ld t5, 32(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  ld t4, 104(t3); ld t5, 40(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  ld t4, 112(t3); ld t5, 48(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  ld t4, 120(t3); ld t5, 56(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  j .Lbsme_advance             # captured final value matches -> next change\n" ++
  ".Lbsme_sys_next:\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lbsme_sys_scan     # not this row -> earlier system row\n" ++
  -- bmvmx.5.5.10 PR-2: THEN consult the per-tx USER-write side arena
  -- (bv_user_storage_log, captured after each mtx dispatch; the live exec log only
  -- holds the LAST dispatch's rows). Backward scan = last-write-wins across txs.
  -- These rows precede the end-of-block system writes (block_access_index 1..N <
  -- N+1), so this scan runs only after the system scan missed. Same 128-byte row
  -- layout. On single-tx lanes the count is 0 (never populated) and this is inert.
  "  la t0, bv_user_storage_log_count; ld t2, 0(t0)\n" ++
  "  beqz t2, .Lbsme_user_scan    # no captured user rows -> live exec log\n" ++
  "  la t1, bv_user_storage_log; slli t3, t2, 7; add t3, t1, t3   # past last user entry\n" ++
  ".Lbsme_uarena_scan:\n" ++
  "  addi t3, t3, -128\n" ++
  "  ld t4, 0(t3);  ld t5, 0(s0);  bne t4, t5, .Lbsme_uarena_next\n" ++
  "  ld t4, 8(t3);  ld t5, 8(s0);  bne t4, t5, .Lbsme_uarena_next\n" ++
  "  ld t4, 16(t3); ld t5, 16(s0); bne t4, t5, .Lbsme_uarena_next\n" ++
  "  ld t4, 24(t3); ld t5, 24(s0); bne t4, t5, .Lbsme_uarena_next\n" ++
  "  ld t4, 32(t3); ld t5, 0(t6);  bne t4, t5, .Lbsme_uarena_next\n" ++
  "  ld t4, 40(t3); ld t5, 8(t6);  bne t4, t5, .Lbsme_uarena_next\n" ++
  "  ld t4, 48(t3); ld t5, 16(t6); bne t4, t5, .Lbsme_uarena_next\n" ++
  "  ld t4, 56(t3); ld t5, 24(t6); bne t4, t5, .Lbsme_uarena_next\n" ++
  -- User side arena has the (addr,slot): this captured value is the final write.
  "  ld t4, 96(t3);  ld t5, 32(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  ld t4, 104(t3); ld t5, 40(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  ld t4, 112(t3); ld t5, 48(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  ld t4, 120(t3); ld t5, 56(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  j .Lbsme_advance             # captured final value matches -> next change\n" ++
  ".Lbsme_uarena_next:\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lbsme_uarena_scan  # not this row -> earlier user row\n" ++
  -- Scan the user exec log from the end (last write wins) for (addrHash==s0, key==krev).
  ".Lbsme_user_scan:\n" ++
  "  mv t2, s2\n" ++
  "  beqz t2, .Lbsme_mismatch     # empty log but BAL claims a change\n" ++
  "  slli t3, t2, 7; add t3, s1, t3      # past last entry\n" ++
  ".Lbsme_scan:\n" ++
  "  addi t3, t3, -128            # entry ptr\n" ++
  -- addrHash (entry+0..32) vs account addr (s0).
  "  ld t4, 0(t3);  ld t5, 0(s0);  bne t4, t5, .Lbsme_next\n" ++
  "  ld t4, 8(t3);  ld t5, 8(s0);  bne t4, t5, .Lbsme_next\n" ++
  "  ld t4, 16(t3); ld t5, 16(s0); bne t4, t5, .Lbsme_next\n" ++
  "  ld t4, 24(t3); ld t5, 24(s0); bne t4, t5, .Lbsme_next\n" ++
  -- slotKey (entry+32..64) vs key (s5).
  "  ld t4, 32(t3); ld t5, 0(t6);  bne t4, t5, .Lbsme_next\n" ++
  "  ld t4, 40(t3); ld t5, 8(t6);  bne t4, t5, .Lbsme_next\n" ++
  "  ld t4, 48(t3); ld t5, 16(t6); bne t4, t5, .Lbsme_next\n" ++
  "  ld t4, 56(t3); ld t5, 24(t6); bne t4, t5, .Lbsme_next\n" ++
  -- Match: the LAST write for this (addr,slot). Compare current (entry+96..128)
  -- vs the BAL post-value (s6).
  "  ld t4, 96(t3);  ld t5, 32(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  ld t4, 104(t3); ld t5, 40(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  ld t4, 112(t3); ld t5, 48(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  ld t4, 120(t3); ld t5, 56(t6); bne t4, t5, .Lbsme_mismatch\n" ++
  "  j .Lbsme_advance             # this change reproduced -> next change\n" ++
  ".Lbsme_next:\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lbsme_scan\n" ++
  "  j .Lbsme_mismatch            # scanned whole log, key not found\n" ++
  ".Lbsme_advance:\n" ++
  -- Temporary differential trace for a matching row (same layout as mismatch).
  "  li t0, 0xa0010100\n" ++
  "  ld t1, 0(s0); sd t1, 0(t0); ld t1, 8(s0); sd t1, 8(t0); ld t1, 16(s0); sd t1, 16(t0); ld t1, 24(s0); sd t1, 24(t0)\n" ++
  "  ld t1, 0(t6); sd t1, 32(t0); ld t1, 8(t6); sd t1, 40(t0); ld t1, 16(t6); sd t1, 48(t0); ld t1, 24(t6); sd t1, 56(t0)\n" ++
  "  ld t1, 32(t6); sd t1, 64(t0); ld t1, 40(t6); sd t1, 72(t0); ld t1, 48(t6); sd t1, 80(t0); ld t1, 56(t6); sd t1, 88(t0)\n" ++
  "  ld t1, 96(t3); sd t1, 96(t0); ld t1, 104(t3); sd t1, 104(t0); ld t1, 112(t3); sd t1, 112(t0); ld t1, 120(t3); sd t1, 120(t0)\n" ++
  "  addi s4, s4, 1; j .Lbsme_loop\n" ++
  ".Lbsme_match:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbsme_ret\n" ++
  ".Lbsme_mismatch:\n" ++
  -- Temporary direct verdict-debug trace for AccountState convergence: persist the
  -- failing BAL tuple and the last candidate exec-log row outside the 112-byte
  -- result window.  The epilogue preserves these offsets for post-run comparison.
  -- OUTPUT+128 account, +160 slot (LE), +192 BAL value (LE), +224 scanned row,
  -- +352 log base/count/index.  Diagnostic only; remove after 00199 root pin.
  "  li t0, 0xa0010100\n" ++
  "  ld t1, 0(s0); sd t1, 0(t0); ld t1, 8(s0); sd t1, 8(t0); ld t1, 16(s0); sd t1, 16(t0); ld t1, 24(s0); sd t1, 24(t0)\n" ++
  "  ld t1, 0(t6); sd t1, 32(t0); ld t1, 8(t6); sd t1, 40(t0); ld t1, 16(t6); sd t1, 48(t0); ld t1, 24(t6); sd t1, 56(t0)\n" ++
  "  ld t1, 32(t6); sd t1, 64(t0); ld t1, 40(t6); sd t1, 72(t0); ld t1, 48(t6); sd t1, 80(t0); ld t1, 56(t6); sd t1, 88(t0)\n" ++
  "  ld t1, 96(t3); sd t1, 96(t0); ld t1, 104(t3); sd t1, 104(t0); ld t1, 112(t3); sd t1, 112(t0); ld t1, 120(t3); sd t1, 120(t0)\n" ++
  "  li a0, 1\n" ++
  ".Lbsme_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- Scratch for `bal_storage_matches_exec_log` (BAL parse output buffers). -/
def balStorageMatchesExecLogData : String :=
  ".balign 8\n" ++
  "bsme_keys:\n  .zero " ++ toString (bsrAccountSlotCap * 32) ++ "\n" ++
  "bsme_vals:\n  .zero " ++ toString (bsrAccountSlotCap * 32) ++ "\n" ++
  "bsme_krev:\n  .zero 32\n" ++
  "bsme_vrev:\n  .zero 32\n"

/-- `zisk_bal_storage_matches_exec_log`: probe over a synthetic exec log + BAL.
    Exec log (addrHash A=0xAA): slot 0x07 current 0x22, slot 0x09 current 0x33.
    BAL AccountChanges: slot 0x07->0x22, slot 0x09->0x33.
    Output:
      +0  match for the consistent BAL          (expect 0)
      +8  match after corrupting BAL slot7->0x99 (expect 1, value mismatch)
      +16 match for a BAL claiming slot 0x0b     (expect 1, key absent in log) -/
def ziskBalStorageMatchesExecLogPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Build a 2-entry exec log at bsme_log: (A,7,_,0x22), (A,9,_,0x33).
  "  la t0, bsme_log\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++   -- e0 addrHash A
  "  li t1, 0x07; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++  -- e0 slot 7
  "  sd x0, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++                -- e0 original
  "  li t1, 0x22; sd t1, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++ -- e0 current 0x22
  "  addi t0, t0, 128\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++   -- e1 addrHash A
  "  li t1, 0x09; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++  -- e1 slot 9
  "  sd x0, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  li t1, 0x33; sd t1, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++ -- e1 current 0x33
  -- account addr A = 0xAA (32-byte addrHash).
  "  la t0, bsme_addr; li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  -- AccountChanges (same hand-encoding as the 1.6.1 probe): slot7->[[0,11],[1,22]], slot9->[[0,33]].
  "  la t0, bsme_acct\n" ++
  "  li t1, 0xf8; sb t1, 0(t0); li t1, 0x29; sb t1, 1(t0); li t1, 0x94; sb t1, 2(t0)\n" ++
  "  li t2, 20; addi t3, t0, 3\n" ++
  "1:\n  beqz t2, 2f\n  sb zero, 0(t3); addi t3, t3, 1; addi t2, t2, -1; j 1b\n" ++
  "2:\n" ++
  -- storage_changes blob at +23 (16 bytes): cf c8 07 c6 c2 80 11 c2 01 22 c5 09 c3 c2 80 33
  "  addi t3, t0, 23\n" ++
  "  li t1, 0xcf; sb t1, 0(t3); li t1, 0xc8; sb t1, 1(t3); li t1, 0x07; sb t1, 2(t3)\n" ++
  "  li t1, 0xc6; sb t1, 3(t3); li t1, 0xc2; sb t1, 4(t3); li t1, 0x80; sb t1, 5(t3)\n" ++
  "  li t1, 0x11; sb t1, 6(t3); li t1, 0xc2; sb t1, 7(t3); li t1, 0x01; sb t1, 8(t3)\n" ++
  "  li t1, 0x22; sb t1, 9(t3); li t1, 0xc5; sb t1, 10(t3); li t1, 0x09; sb t1, 11(t3)\n" ++
  "  li t1, 0xc3; sb t1, 12(t3); li t1, 0xc2; sb t1, 13(t3); li t1, 0x80; sb t1, 14(t3)\n" ++
  "  li t1, 0x33; sb t1, 15(t3)\n" ++
  "  li t1, 0xc0; sb t1, 39(t0); sb t1, 40(t0); sb t1, 41(t0); sb t1, 42(t0)\n" ++
  -- Scenario 1: consistent BAL -> expect match (0).
  "  la a0, bsme_addr; la a1, bsme_acct; li a2, 43; la a3, bsme_log; li a4, 2\n" ++
  "  jal ra, bal_storage_matches_exec_log\n" ++
  "  sd a0, 0(s0)\n" ++
  -- Scenario 2: corrupt the exec-log slot7 current 0x22 -> 0x99, re-run -> mismatch (1).
  "  la t0, bsme_log; li t1, 0x99; sd t1, 96(t0)\n" ++
  "  la a0, bsme_addr; la a1, bsme_acct; li a2, 43; la a3, bsme_log; li a4, 2\n" ++
  "  jal ra, bal_storage_matches_exec_log\n" ++
  "  sd a0, 8(s0)\n" ++
  -- Scenario 3: shrink log to 1 entry (slot 7 only) so the BAL's slot 9 is absent -> mismatch (1).
  "  la a0, bsme_addr; la a1, bsme_acct; li a2, 43; la a3, bsme_log; li a4, 1\n" ++
  "  jal ra, bal_storage_matches_exec_log\n" ++
  "  sd a0, 16(s0)\n" ++
  "  j .Lbsme_probe_done\n" ++
  balStorageChangeValuesFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  balStorageMatchesExecLogFunction ++ "\n" ++
  ".Lbsme_probe_done:"

def ziskBalStorageMatchesExecLogDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bsme_log:\n  .zero 512\n" ++
  "bsme_addr:\n  .zero 32\n" ++
  "bsme_acct:\n  .zero 128\n" ++
  balStorageChangeValuesData ++
  balStorageMatchesExecLogData ++
   -- lv44p: empty captured-system-log stub so the focused probe links the function's
   -- bv_system_storage_log scan (count 0 -> inert; the verdict links the real globals).
   ".balign 8\n" ++
   "bv_system_storage_log_count:\n  .zero 8\n" ++
   ".balign 32\n" ++
   "bv_system_storage_log:\n  .zero 128\n" ++
   -- bmvmx.5.5.10 PR-2: same inert stub for the per-tx user-write side arena scan.
   ".balign 8\n" ++
   "bv_user_storage_log_count:\n  .zero 8\n" ++
   ".balign 32\n" ++
   "bv_user_storage_log:\n  .zero 128\n"

def ziskBalStorageMatchesExecLogProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalStorageMatchesExecLogPrologue
  dataAsm     := ziskBalStorageMatchesExecLogDataSection
}

end EvmAsm.Codegen
