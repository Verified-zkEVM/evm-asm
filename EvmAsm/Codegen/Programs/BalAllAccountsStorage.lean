/-
  EvmAsm.Codegen.Programs.BalAllAccountsStorage

  bmvmx.1.6.4.3: all-accounts storage exec-vs-BAL forward+reverse consistency.

  Wraps the two per-account comparators (claude-c1's bal_storage_matches_exec_log
  #8564 forward / bal_storage_covers_exec_log #8569 reverse) over EVERY account in
  the block_access_list, so a block is rejected if any account's BAL storage_changes
  disagree with what execution actually wrote.

  Per claude-c1's handoff (the exec-log key SPLITS by depth):
    - the TOP-LEVEL RECIPIENT is keyed on env.ADDRESS = tx.to BIG-ENDIAN and is
      already verified inside block_verdict (#8566), so this wrapper SKIPS it;
    - NESTED CALLEES are keyed on the address BYTE-REVERSED (LE stack-word), so the
      callee key is produced via bal_addr_to_exec_log_key (#8575) from the BAL
      account's 20-byte big-endian address.

  Conservative: any parse failure or per-account mismatch/omission returns 1 (reject).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.BalStorageChangeValues
import EvmAsm.Codegen.Programs.BalStorageMatchesExecLog
import EvmAsm.Codegen.Programs.BalStorageCoversExecLog
import EvmAsm.Codegen.Programs.BalAddrExecLogKey
import EvmAsm.Codegen.Programs.BalModeledSystem

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_all_accounts_storage_consistent

    Calling convention:
      a0 = BAL section RLP ptr (list of AccountChanges)
      a1 = BAL section RLP length
      a2 = exec storage-log base
      a3 = exec storage-log length (entry count)
      a4 = recipient 20-byte big-endian address ptr (SKIPPED — checked elsewhere)
      ra = return
      a0 (output) :
        0 : every non-recipient BAL account's storage_changes are both reproduced
            (forward) by and cover (reverse) the exec log for that account
        1 : any parse failure / mismatch / omission (conservative reject)

    A BAL account whose address item is not exactly 20 bytes is skipped (system /
    malformed entries are not callee storage accounts). -/
def balAllAccountsStorageConsistentFunction : String :=
  "bal_all_accounts_storage_consistent:\n" ++
  "  li a5, 1                    # legacy ABI: one skipped recipient\n" ++
  "  j bal_all_accounts_storage_consistent_skip_list\n" ++
  "bal_all_accounts_storage_consistent_skip_list:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # BAL section ptr\n" ++
  "  mv s1, a1                   # BAL section len\n" ++
  "  mv s2, a2                   # exec log base\n" ++
  "  mv s3, a3                   # exec log entry count\n" ++
  "  mv s4, a4                   # skip-list ptr (32-byte-strided 20B BE entries)\n" ++
  "  mv s8, a5                   # skip-list count\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc2baas_fail\n" ++
  "  mv s5, a0                   # BAL cursor\n" ++
  "  mv s6, a1                   # BAL end\n" ++
  ".Lc2baas_loop:\n" ++
  "  beq s5, s6, .Lc2baas_ok\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc2baas_fail\n" ++
  "  mv s5, a0; sub s7, a0, a2; mv s9, a2   # AccountChanges ptr/len\n" ++
  "  mv a0, s7; mv a1, s9; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc2baas_fail\n" ++
  "  jal ra, rlp_walk_next                 # item 0 = address\n" ++
  "  bnez a1, .Lc2baas_fail\n" ++
  "  li t2, 20; bne a2, t2, .Lc2baas_next   # not 20B -> skip\n" ++
  "  sub s10, a0, a2              # addr ptr (20B BE)\n" ++
  "  li t4, 0                    # skip-list index\n" ++
  ".Lc2baas_skip_outer:\n" ++
  "  beq t4, s8, .Lc2baas_check  # not in skip-list -> check it\n" ++
  "  slli t5, t4, 5; add t5, s4, t5\n" ++
  "  li t6, 0                    # byte index\n" ++
  ".Lc2baas_skip_cmp:\n" ++
  "  li a0, 20; beq t6, a0, .Lc2baas_next      # all 20 bytes equal skip entry -> skip\n" ++
  "  add a0, s10, t6; lbu a1, 0(a0)\n" ++
  "  add a0, t5, t6; lbu a2, 0(a0)\n" ++
  "  bne a1, a2, .Lc2baas_skip_advance\n" ++
  "  addi t6, t6, 1; j .Lc2baas_skip_cmp\n" ++
  ".Lc2baas_skip_advance:\n" ++
  "  addi t4, t4, 1; j .Lc2baas_skip_outer\n" ++

  ".Lc2baas_check:\n" ++
  "  mv a0, s10                              # addr ptr (20B BE)\n" ++
  "  la a1, c2bal_key\n" ++
  "  jal ra, bal_addr_to_exec_log_key           # c2bal_key = addr byte-reversed (LE callee key)\n" ++
  "  la a0, c2bal_key; mv a1, s7; mv a2, s9; mv a3, s2; mv a4, s3\n" ++
  "  jal ra, bal_storage_matches_exec_log        # forward: BAL changes reproduced by exec\n" ++
  "  bnez a0, .Lc2baas_fail\n" ++
  "  la a0, c2bal_key; mv a1, s7; mv a2, s9; mv a3, s2; mv a4, s3\n" ++
  "  jal ra, bal_storage_covers_exec_log         # reverse: exec net changes claimed by BAL\n" ++
  "  bnez a0, .Lc2baas_fail\n" ++
  ".Lc2baas_next:\n" ++
  "  j .Lc2baas_loop\n" ++
  ".Lc2baas_ok:\n" ++
  "  li a0, 0; j .Lc2baas_ret\n" ++
  ".Lc2baas_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lc2baas_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_bal_all_accounts_storage_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL section length
      bytes 16..24 : exec log entry count
      bytes 24..56 : recipient address (20B BE in the low bytes, padded to 32)
      bytes 56..    : exec log (count * 128B), then the BAL section
    Output:
      bytes 0..8 : status (0 consistent / 1 mismatch) -/
def ziskBalAllAccountsStorageConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # BAL section len\n" ++
  "  ld a3, 16(a5)               # exec log entry count\n" ++
  "  addi a4, a5, 24             # recipient ptr\n" ++
  "  addi a2, a5, 56             # exec log base\n" ++
  "  slli t0, a3, 7              # count * 128\n" ++
  "  add a0, a2, t0              # BAL section ptr = log_base + 128*count\n" ++
  "  jal ra, bal_all_accounts_storage_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lc2baas_pdone\n" ++
  balAllAccountsStorageConsistentFunction ++ "\n" ++
  balAccountIsModeledSystemFunction ++ "\n" ++   -- .57.11.6.5.1: modeled-system skip dep
  balStorageMatchesExecLogFunction ++ "\n" ++
  balStorageCoversExecLogFunction ++ "\n" ++
  balStorageChangeValuesFunction ++ "\n" ++
  balAddrToExecLogKeyFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lc2baas_pdone:"

/-- Scratch for `bal_all_accounts_storage_consistent` (account-loop state + the LE
    per-account exec-log key). Shared by the probe data section and the verdict data
    section so the verdict can link the wrapper (single source of truth). -/
def balAllAccountsStorageConsistentData : String :=
  ".balign 32\n" ++
  "c2bal_key:\n  .zero 32\n"

/-- `zisk_bal_all_accounts_storage_consistent_skip_list`: probe for the new skip-list ABI.
    Input after the ziskemu length wrapper:
      +8  BAL section length, +16 exec-log entry count, +24 skip count,
      +32 skip list (32-byte-strided), then exec log, then BAL section. -/
def ziskBalAllAccountsStorageConsistentSkipListPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # BAL section len\n" ++
  "  ld a3, 16(t6)               # exec log entry count\n" ++
  "  ld a5, 24(t6)               # skip-list count\n" ++
  "  addi a4, t6, 32             # skip-list base\n" ++
  "  slli t0, a5, 5; add a2, a4, t0   # exec log base\n" ++
  "  slli t0, a3, 7; add a0, a2, t0   # BAL section ptr\n" ++
  "  jal ra, bal_all_accounts_storage_consistent_skip_list\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lc2baas_sl_pdone\n" ++
  balAllAccountsStorageConsistentFunction ++ "\n" ++
  balAccountIsModeledSystemFunction ++ "\n" ++
  balStorageMatchesExecLogFunction ++ "\n" ++
  balStorageCoversExecLogFunction ++ "\n" ++
  balStorageChangeValuesFunction ++ "\n" ++
  balAddrToExecLogKeyFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lc2baas_sl_pdone:"

def ziskBalAllAccountsStorageConsistentDataSection : String :=
  ".section .data\n" ++
  balAllAccountsStorageConsistentData ++
  balStorageChangeValuesData ++
  balStorageMatchesExecLogData ++
  balStorageCoversExecLogData ++
  ziskBalAccountIsModeledSystemDataSection ++   -- .57.11.6.5.1: bams_* for the modeled-system skip
  -- lv44p: empty captured-system-log stub so the focused probe links the bsme/bsce
  -- bv_system_storage_log scan (count 0 -> inert; the verdict links the real globals).
  ".balign 8\n" ++
  "bv_system_storage_log_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_system_storage_log:\n  .zero " ++ toString bvStorageLogRowBytes ++ "\n" ++
  -- bmvmx.5.5.10 PR-2: empty user-arena stubs (count 0 -> inert; the verdict links
  -- the real globals from BlockVerdictDataSection).  One row each, sized from
  -- `bvStorageLogRowBytes` so the stubs cannot drift away from the real stride.
  ".balign 8\n" ++
  "bv_user_storage_log_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_user_storage_log:\n  .zero " ++ toString bvStorageLogRowBytes ++ "\n" ++
  ".balign 8\n" ++
  "exec_nonstorage_effect_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "exec_nonstorage_effect_log:\n  .zero 112\n"

def ziskBalAllAccountsStorageConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsStorageConsistentPrologue
  dataAsm     := ziskBalAllAccountsStorageConsistentDataSection
}

def ziskBalAllAccountsStorageConsistentSkipListProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsStorageConsistentSkipListPrologue
  dataAsm     := ziskBalAllAccountsStorageConsistentDataSection
}

end EvmAsm.Codegen
