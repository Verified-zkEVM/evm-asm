/-
  EvmAsm.Codegen.Programs.BalStorageCoversExecLog

  `bal_storage_covers_exec_log` (bead bmvmx.1.6.5) — the CONVERSE of
  `bal_storage_matches_exec_log` (1.6.2). 1.6.2 verifies BAL ⊆ execution (every
  claimed change was produced); this verifies execution ⊆ BAL (every change
  EXECUTION made for the account is CLAIMED by the BAL). It catches a prover that
  OMITS a storage write from the BAL to hide state. Together they pin the
  recipient's BAL storage_changes to EXACTLY what execution produced.

  For each exec-log entry that is the LAST write for its (addr, slot) and a net
  change (entry.current != entry.original — `original` is the slot's preserved
  pre-tx value, Storage.lean), the BAL storage_changes must claim that slot with
  a final value equal to entry.current; otherwise reject. SLOAD / preload / write-
  back-to-original entries have current==original and need no BAL entry.

  Exec-log entry layout (Storage.lean): 128 bytes = addrHash@0, slotKey@32,
  original@64, current@96.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalStorageChangeValues
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_storage_covers_exec_log

    Calling convention:
      a0 = account address ptr (32-byte addrHash, as keyed in the exec log)
      a1 = AccountChanges RLP ptr   a2 = AccountChanges RLP length
      a3 = exec storage-log base    a4 = exec storage-log length (entry count)
    Returns:
      a0 = 0 if every net storage change the exec log records for the account is
           claimed by the BAL storage_changes with the matching final value;
           1 on ANY omission (a net change absent from the BAL) or value mismatch
           (or BAL parse failure — conservative reject).

    Direction: execution ⊆ BAL (the converse of bal_storage_matches_exec_log). -/
def balStorageCoversExecLogFunction : String :=
  "bal_storage_covers_exec_log:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0                    # account addr ptr (addrHash)\n" ++
  "  mv s1, a3                    # log base\n" ++
  "  mv s2, a4                    # log length\n" ++
  -- Parse the BAL storage_changes into (keys, post-values), both big-endian.
  "  mv a0, a1; mv a1, a2; la a2, bsce_keys; la a3, bsce_vals\n" ++
  "  jal ra, bal_storage_change_values\n" ++
  "  li s8, 0                     # lv44p: phase marker (0 = user reverse pass; set AFTER the call, which does not preserve s8)\n" ++
  "  mv s3, a0                    # BAL change count\n" ++
  "  mv s4, zero                  # i (exec entry index)\n" ++
  ".Lbsce_loop:\n" ++
  "  beq s4, s2, .Lbsce_sys_phase\n" ++   -- lv44p: after the user log, run the captured-system-log reverse pass
  "  slli t0, s4, 7; add s5, s1, t0       # entry_i ptr\n" ++
  -- recipient entries only: addrHash (entry+0..32) == s0.
  "  ld t1, 0(s5);  ld t2, 0(s0);  bne t1, t2, .Lbsce_next\n" ++
  "  ld t1, 8(s5);  ld t2, 8(s0);  bne t1, t2, .Lbsce_next\n" ++
  "  ld t1, 16(s5); ld t2, 16(s0); bne t1, t2, .Lbsce_next\n" ++
  "  ld t1, 24(s5); ld t2, 24(s0); bne t1, t2, .Lbsce_next\n" ++
  -- last write for this (addr, slot)? scan entries j>i for a later same-slot write.
  "  addi s6, s4, 1\n" ++
  ".Lbsce_later:\n" ++
  "  beq s6, s2, .Lbsce_user_islast_chk\n" ++
  "  slli t0, s6, 7; add t3, s1, t0       # entry_j ptr\n" ++
  "  ld t1, 0(t3);  ld t2, 0(s0);  bne t1, t2, .Lbsce_later_next\n" ++
  "  ld t1, 8(t3);  ld t2, 8(s0);  bne t1, t2, .Lbsce_later_next\n" ++
  "  ld t1, 16(t3); ld t2, 16(s0); bne t1, t2, .Lbsce_later_next\n" ++
  "  ld t1, 24(t3); ld t2, 24(s0); bne t1, t2, .Lbsce_later_next\n" ++
  "  ld t1, 32(t3); ld t2, 32(s5); bne t1, t2, .Lbsce_later_next\n" ++
  "  ld t1, 40(t3); ld t2, 40(s5); bne t1, t2, .Lbsce_later_next\n" ++
  "  ld t1, 48(t3); ld t2, 48(s5); bne t1, t2, .Lbsce_later_next\n" ++
  "  ld t1, 56(t3); ld t2, 56(s5); bne t1, t2, .Lbsce_later_next\n" ++
  "  j .Lbsce_next                        # later user write exists -> entry_i not last\n" ++
  ".Lbsce_later_next:\n" ++
  "  addi s6, s6, 1; j .Lbsce_later\n" ++
  ".Lbsce_user_islast_chk:\n" ++
  -- lv44p: a per-tx exec entry that is the last in the USER log is NOT the genuine
  -- final write if a captured system-call SSTORE (bv_system_storage_log) later wrote
  -- the same (addr, slot) (the end-of-block EIP-7002/7251 system tx runs after all
  -- user txs). Such an entry is superseded -> its (stale) value must NOT drive a BAL
  -- coverage requirement (that is the bv34/37 false-reject). The system row's own
  -- (original,current) net change is required by the system reverse pass below, so
  -- anti-omission stays intact. If the (addr,slot) is absent from the system log this
  -- entry is the genuine last write and proceeds normally. (Probe: count 0 -> inert.)
  "  la t0, bv_system_storage_log_count; ld t4, 0(t0); beqz t4, .Lbsce_is_last\n" ++
  "  la t6, bv_system_storage_log; slli t0, t4, 7; add t6, t6, t0   # past last system row\n" ++
  ".Lbsce_user_sys_chk:\n" ++
  "  addi t6, t6, -128\n" ++
  "  ld t1, 0(t6);  ld t2, 0(s0);  bne t1, t2, .Lbsce_user_sys_next\n" ++
  "  ld t1, 8(t6);  ld t2, 8(s0);  bne t1, t2, .Lbsce_user_sys_next\n" ++
  "  ld t1, 16(t6); ld t2, 16(s0); bne t1, t2, .Lbsce_user_sys_next\n" ++
  "  ld t1, 24(t6); ld t2, 24(s0); bne t1, t2, .Lbsce_user_sys_next\n" ++
  "  ld t1, 32(t6); ld t2, 32(s5); bne t1, t2, .Lbsce_user_sys_next\n" ++
  "  ld t1, 40(t6); ld t2, 40(s5); bne t1, t2, .Lbsce_user_sys_next\n" ++
  "  ld t1, 48(t6); ld t2, 48(s5); bne t1, t2, .Lbsce_user_sys_next\n" ++
  "  ld t1, 56(t6); ld t2, 56(s5); bne t1, t2, .Lbsce_user_sys_next\n" ++
  "  j .Lbsce_next                        # system superseded this (addr,slot) -> skip user entry\n" ++
  ".Lbsce_user_sys_next:\n" ++
  "  addi t4, t4, -1; bnez t4, .Lbsce_user_sys_chk\n" ++
  ".Lbsce_is_last:\n" ++
  -- net change? current (entry+96..128) != original (entry+64..96).
  "  ld t1, 96(s5);  ld t2, 64(s5); bne t1, t2, .Lbsce_netchange\n" ++
  "  ld t1, 104(s5); ld t2, 72(s5); bne t1, t2, .Lbsce_netchange\n" ++
  "  ld t1, 112(s5); ld t2, 80(s5); bne t1, t2, .Lbsce_netchange\n" ++
  "  ld t1, 120(s5); ld t2, 88(s5); bne t1, t2, .Lbsce_netchange\n" ++
  "  j .Lbsce_next                        # no net change -> not required in the BAL\n" ++
  ".Lbsce_netchange:\n" ++
  -- A contract created and SELFDESTRUCTed in the same transaction does not commit
  -- constructor storage writes. The raw exec log still records them, but EIP-7928
  -- exposes those touched slots as storage_reads, not storage_changes. Failed
  -- CREATE/CREATE2 initcode can leave the same noncommitting storage trace when it
  -- reaches the target account and then OOGs before deployment: the account is
  -- accessed, but no deployed-code effect is produced. Restrict the demotion to the
  -- user pass and require execution evidence from the nonstorage/code-effect logs.
  "  bnez s8, .Lbsce_require_storage_change\n" ++
  "  la t0, exec_nonstorage_effect_count; ld t4, 0(t0); beqz t4, .Lbsce_require_storage_change\n" ++
  "  la t5, exec_nonstorage_effect_log\n" ++
  "  mv t0, zero\n" ++
  ".Lbsce_deleted_scan:\n" ++
  "  beq t0, t4, .Lbsce_require_storage_change\n" ++
  "  li t1, 112; mul t2, t0, t1; add t3, t5, t2\n" ++
  "  li t1, 0\n" ++
  ".Lbsce_deleted_addr_cmp:\n" ++
  "  li t2, 20; beq t1, t2, .Lbsce_deleted_addr_match\n" ++
  "  add t6, t3, t1; lbu t6, 0(t6)\n" ++
  "  li t2, 19; sub t2, t2, t1; add t2, s0, t2; lbu t2, 0(t2)\n" ++
  "  bne t6, t2, .Lbsce_deleted_next\n" ++
  "  addi t1, t1, 1; j .Lbsce_deleted_addr_cmp\n" ++
  ".Lbsce_deleted_addr_match:\n" ++
  "  ld t1, 64(t3); ld t2, 72(t3); or t1, t1, t2\n" ++
  "  ld t2, 80(t3); or t1, t1, t2\n" ++
  "  ld t2, 88(t3); or t1, t1, t2\n" ++
  "  bnez t1, .Lbsce_deleted_next\n" ++
  "  ld t1, 104(t3); beqz t1, .Lbsce_deleted_demote\n" ++
  "  li t2, 2; bne t1, t2, .Lbsce_deleted_next\n" ++
  "  la t1, exec_code_effect_overflow; ld t1, 0(t1); bnez t1, .Lbsce_require_storage_change\n" ++
  "  la t1, exec_code_effect_count; ld t2, 0(t1); beqz t2, .Lbsce_deleted_demote\n" ++
  "  sd t0, 80(sp)\n" ++
  "  la t1, exec_code_effect_log\n" ++
  "  mv t6, zero\n" ++
  ".Lbsce_failed_create_code_scan:\n" ++
  "  beq t6, t2, .Lbsce_failed_create_no_code\n" ++
  "  li t4, 0\n" ++
  ".Lbsce_failed_create_code_addr_cmp:\n" ++
  "  li t5, 20; beq t4, t5, .Lbsce_failed_create_has_code\n" ++
  "  add t5, t1, t4; lbu t5, 0(t5)\n" ++
  "  li t3, 19; sub t3, t3, t4; add t3, s0, t3; lbu t3, 0(t3)\n" ++
  "  bne t5, t3, .Lbsce_failed_create_code_next\n" ++
  "  addi t4, t4, 1; j .Lbsce_failed_create_code_addr_cmp\n" ++
  ".Lbsce_failed_create_code_next:\n" ++
  "  ld t4, 40(t1); addi t4, t4, 55; andi t4, t4, -8; add t1, t1, t4\n" ++
  "  addi t6, t6, 1; j .Lbsce_failed_create_code_scan\n" ++
  ".Lbsce_failed_create_has_code:\n" ++
  "  ld t0, 80(sp); j .Lbsce_require_storage_change\n" ++
  ".Lbsce_failed_create_no_code:\n" ++
  "  ld t0, 80(sp)\n" ++
  ".Lbsce_deleted_demote:\n" ++
  "  j .Lbsce_next                        # noncommitting create/deleted-account storage writes demoted to reads\n" ++
  ".Lbsce_deleted_next:\n" ++
  "  la t5, exec_nonstorage_effect_log\n" ++
  "  la t2, exec_nonstorage_effect_count; ld t4, 0(t2)\n" ++
  "  addi t0, t0, 1; j .Lbsce_deleted_scan\n" ++
  ".Lbsce_require_storage_change:\n" ++
  -- The exec slot/current are stack-word order (LE u64 limbs); the BAL keys/vals
  -- are big-endian (RLP). Byte-reverse the exec slot (32..64) and current (96..128)
  -- into bsce_slotrev / bsce_currev (big-endian) to match the BAL side.
  "  addi t2, s5, 63; la t1, bsce_slotrev; li t0, 32\n" ++
  ".Lbsce_revs:\n" ++
  "  beqz t0, .Lbsce_revsd\n  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t0, t0, -1; j .Lbsce_revs\n" ++
  ".Lbsce_revsd:\n" ++
  "  addi t2, s5, 127; la t1, bsce_currev; li t0, 32\n" ++
  ".Lbsce_revc:\n" ++
  "  beqz t0, .Lbsce_revcd\n  lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t0, t0, -1; j .Lbsce_revc\n" ++
  ".Lbsce_revcd:\n" ++
  -- Search the BAL keys (big-endian) for this slot.
  "  mv s7, zero                  # k (BAL entry index)\n" ++
  ".Lbsce_ksearch:\n" ++
  "  beq s7, s3, .Lbsce_mismatch          # slot not claimed by the BAL -> omission\n" ++
  "  slli t0, s7, 5; la t1, bsce_keys; add t5, t1, t0\n" ++
  "  la t6, bsce_slotrev\n" ++
  "  ld t1, 0(t5);  ld t2, 0(t6);  bne t1, t2, .Lbsce_ksearch_next\n" ++
  "  ld t1, 8(t5);  ld t2, 8(t6);  bne t1, t2, .Lbsce_ksearch_next\n" ++
  "  ld t1, 16(t5); ld t2, 16(t6); bne t1, t2, .Lbsce_ksearch_next\n" ++
  "  ld t1, 24(t5); ld t2, 24(t6); bne t1, t2, .Lbsce_ksearch_next\n" ++
  -- Key matches: the BAL final value must equal entry.current.
  "  slli t0, s7, 5; la t1, bsce_vals; add t5, t1, t0\n" ++
  "  la t6, bsce_currev\n" ++
  "  ld t1, 0(t5);  ld t2, 0(t6);  bne t1, t2, .Lbsce_mismatch\n" ++
  "  ld t1, 8(t5);  ld t2, 8(t6);  bne t1, t2, .Lbsce_mismatch\n" ++
  "  ld t1, 16(t5); ld t2, 16(t6); bne t1, t2, .Lbsce_mismatch\n" ++
  "  ld t1, 24(t5); ld t2, 24(t6); bne t1, t2, .Lbsce_mismatch\n" ++
  "  j .Lbsce_after_cover                 # this net change is claimed -> continue active phase\n" ++
  ".Lbsce_ksearch_next:\n" ++
  "  addi s7, s7, 1; j .Lbsce_ksearch\n" ++
  ".Lbsce_after_cover:\n" ++
  -- lv44p: dispatch back to whichever phase invoked the netchange coverage check.
  -- s8 = 0 user phase, 1 system phase (set on entry to each phase).
  "  bnez s8, .Lbsce_sys_next\n" ++
  ".Lbsce_next:\n" ++
  "  addi s4, s4, 1; j .Lbsce_loop\n" ++
  -- lv44p: SYSTEM reverse pass. Every captured system-call SSTORE that is the genuine
  -- last write for its (addr,slot) AND a net change (current@96 != original@64 — the
  -- value the dispatcher read at the start of the system tx vs after it) must be CLAIMED
  -- by the BAL with the matching final value, or the prover OMITTED a system storage
  -- update (the state-root recompute APPLIES only declared storage, so a forged matching
  -- root would otherwise hide the omission -> false-accept). Mirrors the user pass; the
  -- captured rows are the ACTUAL end-of-block system replay, so this only ADDS coverage
  -- requirements (never weakens). Probe: bv_system_storage_log_count = 0 -> inert.
  ".Lbsce_sys_phase:\n" ++
  "  li s8, 1                     # system phase marker\n" ++
  "  la t0, bv_system_storage_log_count; ld t0, 0(t0); la t1, bsce_sys_count; sd t0, 0(t1)\n" ++
  "  beqz t0, .Lbsce_covered\n" ++
  "  mv s4, zero                  # j (system entry index, reuse s4)\n" ++
  ".Lbsce_sys_loop:\n" ++
  "  la t0, bsce_sys_count; ld t0, 0(t0); beq s4, t0, .Lbsce_covered\n" ++
  "  slli t0, s4, 7; la t1, bv_system_storage_log; add s5, t1, t0   # system entry_j ptr\n" ++
  "  ld t1, 0(s5);  ld t2, 0(s0);  bne t1, t2, .Lbsce_sys_next\n" ++
  "  ld t1, 8(s5);  ld t2, 8(s0);  bne t1, t2, .Lbsce_sys_next\n" ++
  "  ld t1, 16(s5); ld t2, 16(s0); bne t1, t2, .Lbsce_sys_next\n" ++
  "  ld t1, 24(s5); ld t2, 24(s0); bne t1, t2, .Lbsce_sys_next\n" ++
  -- last SYSTEM write for this (addr, slot)? scan later system entries.
  "  addi s6, s4, 1\n" ++
  ".Lbsce_sys_later:\n" ++
  "  la t0, bsce_sys_count; ld t0, 0(t0); beq s6, t0, .Lbsce_sys_islast\n" ++
  "  slli t0, s6, 7; la t1, bv_system_storage_log; add t3, t1, t0\n" ++
  "  ld t1, 0(t3);  ld t2, 0(s0);  bne t1, t2, .Lbsce_sys_later_next\n" ++
  "  ld t1, 8(t3);  ld t2, 8(s0);  bne t1, t2, .Lbsce_sys_later_next\n" ++
  "  ld t1, 16(t3); ld t2, 16(s0); bne t1, t2, .Lbsce_sys_later_next\n" ++
  "  ld t1, 24(t3); ld t2, 24(s0); bne t1, t2, .Lbsce_sys_later_next\n" ++
  "  ld t1, 32(t3); ld t2, 32(s5); bne t1, t2, .Lbsce_sys_later_next\n" ++
  "  ld t1, 40(t3); ld t2, 40(s5); bne t1, t2, .Lbsce_sys_later_next\n" ++
  "  ld t1, 48(t3); ld t2, 48(s5); bne t1, t2, .Lbsce_sys_later_next\n" ++
  "  ld t1, 56(t3); ld t2, 56(s5); bne t1, t2, .Lbsce_sys_later_next\n" ++
  "  j .Lbsce_sys_next                    # later system write exists -> not last\n" ++
  ".Lbsce_sys_later_next:\n" ++
  "  addi s6, s6, 1; j .Lbsce_sys_later\n" ++
  ".Lbsce_sys_islast:\n" ++
  -- net change? current (entry+96..128) != original (entry+64..96).
  "  ld t1, 96(s5);  ld t2, 64(s5); bne t1, t2, .Lbsce_netchange\n" ++
  "  ld t1, 104(s5); ld t2, 72(s5); bne t1, t2, .Lbsce_netchange\n" ++
  "  ld t1, 112(s5); ld t2, 80(s5); bne t1, t2, .Lbsce_netchange\n" ++
  "  ld t1, 120(s5); ld t2, 88(s5); bne t1, t2, .Lbsce_netchange\n" ++
  ".Lbsce_sys_next:\n" ++
  "  addi s4, s4, 1; j .Lbsce_sys_loop\n" ++
  ".Lbsce_covered:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbsce_ret\n" ++
  ".Lbsce_mismatch:\n" ++
  "  li a0, 1\n" ++
  ".Lbsce_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- Scratch for `bal_storage_covers_exec_log` (BAL parse output + reversed exec slot/value). -/
def balStorageCoversExecLogData : String :=
  ".balign 8\n" ++
  "bsce_keys:\n  .zero " ++ toString (bsrAccountSlotCap * 32) ++ "\n" ++
  "bsce_vals:\n  .zero " ++ toString (bsrAccountSlotCap * 32) ++ "\n" ++
  "bsce_slotrev:\n  .zero 32\n" ++
  "bsce_currev:\n  .zero 32\n" ++
  "bsce_sys_count:\n  .zero 8\n"

/-- `zisk_bal_storage_covers_exec_log`: probe over a synthetic exec log + one BAL.
    BAL AccountChanges (same encoding as the 1.6.1/1.6.2 probes): slot 7 -> 0x22,
    slot 9 -> 0x33. The exec log is varied per scenario (addrHash A=0xAA):
      (1) S7 (0x11 then 0x22), S9 0x33, SB read no-op -> all net changes claimed -> 0
      (2) + S5 net change 0x44 not in the BAL                            -> 1 (omission)
      (3) S7 last current 0x99 (BAL claims 0x22)                         -> 1 (mismatch) -/
def ziskBalStorageCoversExecLogPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Build base exec log at bsce_log. Helper to set an entry is inline below.
  -- e0: (A, S7, orig 0, cur 0x11)
  "  la t0, bsce_log\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x07; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  sd x0, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  li t1, 0x11; sd t1, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++
  -- e1: (A, S9, orig 0, cur 0x33)
  "  addi t0, t0, 128\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x09; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  sd x0, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  li t1, 0x33; sd t1, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++
  -- e2: (A, SB, orig 0x55, cur 0x55) read no-op
  "  addi t0, t0, 128\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x0b; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  li t1, 0x55; sd t1, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  li t1, 0x55; sd t1, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++
  -- e3: (A, S7, orig 0, cur 0x22) — the LAST write to S7
  "  addi t0, t0, 128\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x07; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  sd x0, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  li t1, 0x22; sd t1, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++
  -- e4 (scenario 2 only): (A, S5, orig 0, cur 0x44) net change absent from the BAL
  "  addi t0, t0, 128\n" ++
  "  li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  li t1, 0x05; sd t1, 32(t0); sd x0, 40(t0); sd x0, 48(t0); sd x0, 56(t0)\n" ++
  "  sd x0, 64(t0); sd x0, 72(t0); sd x0, 80(t0); sd x0, 88(t0)\n" ++
  "  li t1, 0x44; sd t1, 96(t0); sd x0, 104(t0); sd x0, 112(t0); sd x0, 120(t0)\n" ++
  -- account addr A = 0xAA (32-byte addrHash).
  "  la t0, bsce_addr; li t1, 0xAA; sd t1, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  -- AccountChanges (1.6.2 encoding): slot7->[[0,11],[1,22]] (post 0x22), slot9->[[0,33]].
  "  la t0, bsce_acct\n" ++
  "  li t1, 0xf8; sb t1, 0(t0); li t1, 0x29; sb t1, 1(t0); li t1, 0x94; sb t1, 2(t0)\n" ++
  "  li t2, 20; addi t3, t0, 3\n" ++
  "1:\n  beqz t2, 2f\n  sb zero, 0(t3); addi t3, t3, 1; addi t2, t2, -1; j 1b\n" ++
  "2:\n" ++
  "  addi t3, t0, 23\n" ++
  "  li t1, 0xcf; sb t1, 0(t3); li t1, 0xc8; sb t1, 1(t3); li t1, 0x07; sb t1, 2(t3)\n" ++
  "  li t1, 0xc6; sb t1, 3(t3); li t1, 0xc2; sb t1, 4(t3); li t1, 0x80; sb t1, 5(t3)\n" ++
  "  li t1, 0x11; sb t1, 6(t3); li t1, 0xc2; sb t1, 7(t3); li t1, 0x01; sb t1, 8(t3)\n" ++
  "  li t1, 0x22; sb t1, 9(t3); li t1, 0xc5; sb t1, 10(t3); li t1, 0x09; sb t1, 11(t3)\n" ++
  "  li t1, 0xc3; sb t1, 12(t3); li t1, 0xc2; sb t1, 13(t3); li t1, 0x80; sb t1, 14(t3)\n" ++
  "  li t1, 0x33; sb t1, 15(t3)\n" ++
  "  li t1, 0xc0; sb t1, 39(t0); sb t1, 40(t0); sb t1, 41(t0); sb t1, 42(t0)\n" ++
  -- Scenario 1: 4-entry log (e0..e3), all net changes claimed -> covered (0).
  "  la a0, bsce_addr; la a1, bsce_acct; li a2, 43; la a3, bsce_log; li a4, 4\n" ++
  "  jal ra, bal_storage_covers_exec_log\n" ++
  "  sd a0, 0(s0)\n" ++
  -- Scenario 2: 5-entry log (include e4 S5->0x44) -> S5 omitted from the BAL -> 1.
  "  la a0, bsce_addr; la a1, bsce_acct; li a2, 43; la a3, bsce_log; li a4, 5\n" ++
  "  jal ra, bal_storage_covers_exec_log\n" ++
  "  sd a0, 8(s0)\n" ++
  -- Scenario 3: corrupt e3's S7 current 0x22 -> 0x99 (BAL claims 0x22) -> mismatch (1).
  "  la t0, bsce_log; li t1, 0x99; sd t1, 480(t0)\n" ++   -- e3 current low limb @ 3*128+96 = 480
  "  la a0, bsce_addr; la a1, bsce_acct; li a2, 43; la a3, bsce_log; li a4, 4\n" ++
  "  jal ra, bal_storage_covers_exec_log\n" ++
  "  sd a0, 16(s0)\n" ++
  "  j .Lbsce_probe_done\n" ++
  balStorageChangeValuesFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  balStorageCoversExecLogFunction ++ "\n" ++
  ".Lbsce_probe_done:"

def ziskBalStorageCoversExecLogDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bsce_log:\n  .zero 768\n" ++
  "bsce_addr:\n  .zero 32\n" ++
  "bsce_acct:\n  .zero 128\n" ++
  balStorageChangeValuesData ++
  balStorageCoversExecLogData ++
  -- lv44p: empty captured-system-log stub so the focused probe links the function's
  -- bv_system_storage_log scan (count 0 -> inert; the verdict links the real globals).
  ".balign 8\n" ++
  "bv_system_storage_log_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_system_storage_log:\n  .zero 128\n" ++
  ".balign 8\n" ++
  "exec_nonstorage_effect_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "exec_nonstorage_effect_log:\n  .zero 112\n" ++
  ".balign 8\n" ++
  "exec_code_effect_count:\n  .zero 8\n" ++
  "exec_code_effect_overflow:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "exec_code_effect_log:\n  .zero 48\n"

def ziskBalStorageCoversExecLogProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalStorageCoversExecLogPrologue
  dataAsm     := ziskBalStorageCoversExecLogDataSection
}

end EvmAsm.Codegen
