/-
  EvmAsm.Codegen.Programs.BalAllAccountsNonstorage

  `bal_all_accounts_nonstorage_consistent` (bead i3djw / bmvmx.1.6.4.4 step .3a) —
  the all-accounts NON-storage FINAL wrapper, the non-storage analog of
  bal_all_accounts_storage_consistent (#8576). It runs the per-account non-storage
  comparator bal_account_nonstorage_consistent (#8586, step .2) over EVERY account in
  the block_access_list, so a block is rejected if any account's BAL balance/nonce
  finals disagree with what execution actually produced.

  Per-account execution-derived non-storage effect record (112 B, 8-byte aligned),
  one per touched account, keyed by the account's 20-byte big-endian address:
    +0   address      (20 B big-endian in the low bytes, padded to 32)
    +32  pre_balance  (32 B big-endian)
    +64  post_balance (32 B big-endian)
    +96  pre_nonce    (u64)
    +104 post_nonce   (u64)

  Keying note: unlike the storage exec-log (whose callee key is the address
  byte-reversed via bal_addr_to_exec_log_key #8575, an LE stack-word artifact), this
  fresh effect record is keyed by the plain 20-byte big-endian address, so the wrapper
  matches a BAL account to its record with a direct 20-byte compare (no keccak / no
  byte-reversal).

  DIRECTION — this is the FORWARD half (every BAL-declared non-storage change is
  reproduced by exec; via .2's per-account reverse, a matched account's exec changes
  must also be declared). The REVERSE-completeness half (an account exec net-changed
  but ENTIRELY ABSENT from the BAL) is step .3b. The top-level recipient is SKIPPED
  (its balance/nonce are checked on the gas/balance path — claude-c1's sender/recipient
  balance compare), exactly as #8576 skips the recipient for storage. Code changes stay
  out of scope until CREATE/SELFDESTRUCT exec (i3djw create/delete steps).

  Conservative: any parse failure, per-account mismatch, or a non-recipient BAL account
  that declares a balance/nonce/code change with no matching exec effect returns 1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.BalAccountNonstorageConsistent

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_all_accounts_nonstorage_consistent
    a0 = BAL section RLP ptr (list of AccountChanges)   a1 = BAL section RLP length
    a2 = exec non-storage effect array base             a3 = effect record count
    a4 = recipient 20-byte big-endian address ptr (SKIPPED — checked on the gas path)
    a0 (output) = 0 consistent / 1 inconsistent (conservative reject).

    A BAL account whose address item is not exactly 20 bytes is skipped. -/
def balAllAccountsNonstorageConsistentFunction : String :=
  "bal_all_accounts_nonstorage_consistent:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                   # BAL section ptr\n" ++
  "  mv s1, a1                   # BAL section len\n" ++
  "  mv s2, a2                   # effect array base\n" ++
  "  mv s3, a3                   # effect record count\n" ++
  "  mv s4, a4                   # recipient 20B BE addr ptr\n" ++
  "  mv a0, s0; mv a1, s1; la a2, c3ns_acct_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lc3ns_fail\n" ++
  "  la t0, c3ns_acct_count; ld s6, 0(t0)   # account count\n" ++
  "  li s5, 0                    # account index\n" ++
  ".Lc3ns_loop:\n" ++
  "  beq s5, s6, .Lc3ns_ok\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5; la a3, c3ns_acct_off; la a4, c3ns_acct_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lc3ns_fail\n" ++
  "  la t0, c3ns_acct_off; ld t1, 0(t0); add s7, s0, t1   # AccountChanges ptr\n" ++
  "  la t0, c3ns_acct_len; ld s8, 0(t0)                   # AccountChanges len\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 0; la a3, c3ns_addr_off; la a4, c3ns_addr_len\n" ++
  "  jal ra, rlp_list_nth_item                            # item 0 = address\n" ++
  "  bnez a0, .Lc3ns_fail\n" ++
  "  la t0, c3ns_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lc3ns_next   # not 20B -> skip\n" ++
  "  la t0, c3ns_addr_off; ld t1, 0(t0); add s9, s7, t1   # addr ptr (20B BE)\n" ++
  "  # --- skip the top-level recipient (checked on the gas/balance path) ---\n" ++
  "  li t4, 0\n" ++
  ".Lc3ns_rcmp:\n" ++
  "  li t5, 20; beq t4, t5, .Lc3ns_next      # all 20 bytes equal recipient -> skip\n" ++
  "  add t5, s9, t4; lbu t6, 0(t5)\n" ++
  "  add t5, s4, t4; lbu a0, 0(t5)\n" ++
  "  bne t6, a0, .Lc3ns_find                  # differs from recipient -> a callee\n" ++
  "  addi t4, t4, 1; j .Lc3ns_rcmp\n" ++
  ".Lc3ns_find:\n" ++
  "  # --- find this callee's exec effect record by 20-byte address ---\n" ++
  "  li t4, 0                                 # effect index\n" ++
  ".Lc3ns_find_loop:\n" ++
  "  beq t4, s3, .Lc3ns_notfound              # scanned all effects, none match\n" ++
  "  slli t5, t4, 7; slli t6, t4, 4; sub t5, t5, t6; add t5, s2, t5   # effect[t4] ptr (t4*112)\n" ++
  "  li a6, 0\n" ++
  ".Lc3ns_find_cmp:\n" ++
  "  li a7, 20; beq a6, a7, .Lc3ns_found\n" ++
  "  add a0, s9, a6; lbu a1, 0(a0)\n" ++
  "  add a0, t5, a6; lbu a2, 0(a0)\n" ++
  "  bne a1, a2, .Lc3ns_find_adv\n" ++
  "  addi a6, a6, 1; j .Lc3ns_find_cmp\n" ++
  ".Lc3ns_find_adv:\n" ++
  "  addi t4, t4, 1; j .Lc3ns_find_loop\n" ++
  ".Lc3ns_found:\n" ++
  "  mv a0, s7; mv a1, s8; mv a2, t5\n" ++
  "  jal ra, bal_account_nonstorage_consistent   # .2: 0 consistent / 1 / 2 -> reject if != 0\n" ++
  "  bnez a0, .Lc3ns_fail\n" ++
  "  j .Lc3ns_next\n" ++
  ".Lc3ns_notfound:\n" ++
  "  # no exec effect for this callee: only a problem if the BAL declares a non-storage change\n" ++
  "  mv a0, s7; mv a1, s8; la a2, c2nsc_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lc3ns_fail                     # parse failure -> reject\n" ++
  "  la t0, c2nsc_finals\n" ++
  "  ld t1, 0(t0);  bnez t1, .Lc3ns_fail      # has_balance declared but no exec effect -> reject\n" ++
  "  ld t1, 40(t0); bnez t1, .Lc3ns_fail      # has_nonce\n" ++
  "  ld t1, 56(t0); bnez t1, .Lc3ns_fail      # has_code\n" ++
  "  # declares no non-storage change (storage-only callee) -> nothing to check here\n" ++
  ".Lc3ns_next:\n" ++
  "  addi s5, s5, 1; j .Lc3ns_loop\n" ++
  ".Lc3ns_ok:\n" ++
  "  li a0, 0; j .Lc3ns_ret\n" ++
  ".Lc3ns_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lc3ns_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_bal_all_accounts_nonstorage_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL section length
      bytes 16..24 : exec effect record count
      bytes 24..56 : recipient address (20B BE in the low bytes, padded to 32)
      bytes 56..    : effect array (count * 112B), then the BAL section
    Output: bytes 0..8 = status (0 consistent / 1 reject). -/
def ziskBalAllAccountsNonstorageConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # BAL section len\n" ++
  "  ld a3, 16(a5)               # effect record count\n" ++
  "  addi a4, a5, 24             # recipient ptr\n" ++
  "  addi a2, a5, 56             # effect array base (0x40000038, 8-aligned)\n" ++
  "  slli t0, a3, 7; slli t1, a3, 4; sub t0, t0, t1   # effect_count * 112\n" ++
  "  add a0, a2, t0              # BAL section ptr = effect_base + 112*count\n" ++
  "  jal ra, bal_all_accounts_nonstorage_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lc3ns_pdone\n" ++
  balAllAccountsNonstorageConsistentFunction ++ "\n" ++
  balAccountNonstorageConsistentFunction ++ "\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lc3ns_pdone:"

def ziskBalAllAccountsNonstorageConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "c3ns_acct_count:\n  .zero 8\n" ++
  "c3ns_acct_off:\n  .zero 8\n" ++
  "c3ns_acct_len:\n  .zero 8\n" ++
  "c3ns_addr_off:\n  .zero 8\n" ++
  "c3ns_addr_len:\n  .zero 8\n" ++
  ziskBalAccountNonstorageConsistentDataSection  -- c2nsc_finals + c2nsf_* + rfu scratch

def ziskBalAllAccountsNonstorageConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsNonstorageConsistentPrologue
  dataAsm     := ziskBalAllAccountsNonstorageConsistentDataSection
}

end EvmAsm.Codegen
