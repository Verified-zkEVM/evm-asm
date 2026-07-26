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
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.BalAccountNonstorageConsistent
import EvmAsm.Codegen.Programs.NonstorageEffectLog

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_all_accounts_nonstorage_consistent
    a0 = BAL section RLP ptr (list of AccountChanges)   a1 = BAL section RLP length
    a2 = exec non-storage effect array base             a3 = effect record count
    a4 = skip-list ptr (array of 32-byte-padded 20-byte addresses to SKIP — the
         gas/value-coupled accounts {sender, recipient, coinbase}, checked on the gas path)
    a5 = skip-list count
    a0 (output) = 0 consistent / 1 inconsistent (conservative reject).

    A BAL account whose address item is not exactly 20 bytes is skipped. -/
def balAllAccountsNonstorageConsistentFunction : String :=
  "bal_all_accounts_nonstorage_consistent:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # BAL section ptr\n" ++
  "  mv s1, a1                   # BAL section len\n" ++
  "  mv s2, a2                   # effect array base\n" ++
  "  mv s3, a3                   # effect record count\n" ++
  "  mv s4, a4                   # skip-list ptr\n" ++
  "  mv s10, a5                  # skip-list count\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc3ns_fail\n" ++
  "  sd a0, 96(sp); sd a1, 104(sp)\n" ++
  "  li s5, 0                    # account index\n" ++
  ".Lc3ns_loop:\n" ++
  "  ld t0, 96(sp); ld t1, 104(sp); beq t0, t1, .Lc3ns_ok\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc3ns_fail\n" ++
  "  sd a0, 96(sp); sub s7, a0, a2; mv s8, a2   # AccountChanges ptr/len\n" ++
  "  mv a0, s7; mv a1, s8; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc3ns_fail\n" ++
  "  jal ra, rlp_walk_next                            # item 0 = address\n" ++
  "  bnez a1, .Lc3ns_fail\n" ++
  "  li t2, 20; bne a2, t2, .Lc3ns_next   # not 20B -> skip\n" ++
  "  sub s9, a0, a2   # addr ptr (20B BE)\n" ++
  "  # --- skip gas/value-coupled accounts {sender,recipient,coinbase} (checked on the gas path) ---\n" ++
  "  li t4, 0                                 # skip-list entry index\n" ++
  ".Lc3ns_skloop:\n" ++
  "  beq t4, s10, .Lc3ns_find                 # not in skip-list -> a callee, check it\n" ++
  "  slli t5, t4, 5; add t5, s4, t5           # skip entry ptr (32B strided)\n" ++
  "  li t6, 0\n" ++
  ".Lc3ns_skcmp:\n" ++
  "  li a0, 20; beq t6, a0, .Lc3ns_next       # all 20 bytes equal a skip entry -> skip account\n" ++
  "  add a0, s9, t6; lbu a1, 0(a0)\n" ++
  "  add a0, t5, t6; lbu a2, 0(a0)\n" ++
  "  bne a1, a2, .Lc3ns_skadv\n" ++
  "  addi t6, t6, 1; j .Lc3ns_skcmp\n" ++
  ".Lc3ns_skadv:\n" ++
  "  addi t4, t4, 1; j .Lc3ns_skloop\n" ++
  ".Lc3ns_find:\n" ++
  "  # --- find this callee's exec effect record by 20-byte address. bmvmx.5.5.7.3: the effect agg\n" ++
  "  # is now SORTED by address (every caller routes through nonstorage_effect_aggregate), so BINARY\n" ++
  "  # SEARCH it (O(log agg) per account) instead of the old O(agg) linear scan -- removes the\n" ++
  "  # O(BAL*agg) barrier blocking the effect-log cap lift. Addresses are 20-byte big-endian; compare\n" ++
  "  # byte 0 (MSB) first, matching the helper's ascending sort. Mirrors b1_sender_table_find. The\n" ++
  "  # agg is deduplicated (one record per address) so there is exactly one match. CONTRACT: callers\n" ++
  "  # MUST pass a sorted (e.g. aggregated) effect array. ---\n" ++
  "  li t4, 0                                 # lo\n" ++
  "  mv a3, s3                                # hi = effect count\n" ++
  ".Lc3ns_bs:\n" ++
  "  bgeu t4, a3, .Lc3ns_notfound             # lo >= hi -> absent\n" ++
  "  add a4, t4, a3; srli a4, a4, 1           # mid = (lo+hi)/2\n" ++
  "  slli t5, a4, 7; slli t6, a4, 4; sub t5, t5, t6; add t5, s2, t5   # &agg[mid] (mid*112)\n" ++
  "  li a6, 0\n" ++
  ".Lc3ns_bscmp:\n" ++
  "  li a7, 20; beq a6, a7, .Lc3ns_found      # 20 bytes equal -> found (t5 = record)\n" ++
  "  add a0, t5, a6; lbu a1, 0(a0)            # agg[mid].addr[a6]\n" ++
  "  add a0, s9, a6; lbu a2, 0(a0)            # target.addr[a6]\n" ++
  "  bltu a1, a2, .Lc3ns_bslo                 # agg[mid] < target -> upper half\n" ++
  "  bltu a2, a1, .Lc3ns_bshi                 # agg[mid] > target -> lower half\n" ++
  "  addi a6, a6, 1; j .Lc3ns_bscmp\n" ++
  ".Lc3ns_bslo:\n" ++
  "  addi t4, a4, 1; j .Lc3ns_bs              # lo = mid+1\n" ++
  ".Lc3ns_bshi:\n" ++
  "  mv a3, a4; j .Lc3ns_bs                   # hi = mid\n" ++
  ".Lc3ns_found:\n" ++
  "  mv a0, s7; mv a1, s8; mv a2, t5\n" ++
  "  jal ra, bal_account_nonstorage_consistent   # .2: 0 consistent / 1 / 2 -> reject if != 0\n" ++
  "  bnez a0, .Lc3ns_fail\n" ++
  -- The effect format mirrors execution-specs' independently-emitted fields.
  -- If a component is absent from the execution record, a BAL declaration for
  -- that component has no producer and must reject rather than being silently
  -- accepted by the legacy triple comparator.
  "  lbu t0, 20(t5); li t1, " ++ toString nonstorageEffectHasBalance ++ "; and t1, t0, t1; bnez t1, .Lc3ns_mask_nonce; mv a0, s7; mv a1, s8; la a2, c2nsc_finals; jal ra, bal_account_nonstorage_finals; bnez a0, .Lc3ns_fail; ld t1, 0(a2); bnez t1, .Lc3ns_fail\n" ++
  ".Lc3ns_mask_nonce:\n" ++
  "  li t1, " ++ toString nonstorageEffectHasNonce ++ "; and t1, t0, t1; bnez t1, .Lc3ns_next; mv a0, s7; mv a1, s8; la a2, c2nsc_finals; jal ra, bal_account_nonstorage_finals; bnez a0, .Lc3ns_fail; ld t1, 40(a2); bnez t1, .Lc3ns_fail\n" ++
  "  j .Lc3ns_next\n" ++
  ".Lc3ns_notfound:\n" ++
  "  # no exec effect for this callee: only a problem if the BAL declares a non-storage change\n" ++
  "  mv a0, s7; mv a1, s8; la a2, c2nsc_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lc3ns_fail                     # parse failure -> reject\n" ++
  "  la t0, c2nsc_finals\n" ++
  "  ld t1, 0(t0);  bnez t1, .Lc3ns_fail      # has_balance declared but no exec effect -> reject\n" ++
  "  ld t1, 56(t0); beqz t1, .Lc3ns_no_7702_code\n" ++
  "  # EIP-7702 set_delegation installs 0xef0100||target directly from authorization,\n" ++
  "  # so an authority account can have BAL nonce/code changes without a CALL/CREATE exec effect.\n" ++
  "  ld t2, 72(t0); li t3, 23; bne t2, t3, .Lc3ns_fail\n" ++
  "  ld t2, 64(t0); add t2, s7, t2\n" ++
  "  lbu t3, 0(t2); li t4, 0xef; bne t3, t4, .Lc3ns_fail\n" ++
  "  lbu t3, 1(t2); li t4, 0x01; bne t3, t4, .Lc3ns_fail\n" ++
  "  lbu t3, 2(t2); bnez t3, .Lc3ns_fail\n" ++
  "  j .Lc3ns_next\n" ++
  ".Lc3ns_no_7702_code:\n" ++
  "  ld t1, 40(t0); bnez t1, .Lc3ns_fail      # has_nonce\n" ++
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
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_bal_all_accounts_nonstorage_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL section length
      bytes 16..24 : exec effect record count
      bytes 24..32 : skip-list count
      bytes 32..    : skip-list (count * 32B), then effect array (count * 112B), then the BAL section
    Output: bytes 0..8 = status (0 consistent / 1 reject). -/
def ziskBalAllAccountsNonstorageConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # BAL section len\n" ++
  "  ld a3, 16(t6)               # effect record count\n" ++
  "  ld a5, 24(t6)               # skip-list count\n" ++
  "  addi a4, t6, 32             # skip-list base (0x40000020, 8-aligned)\n" ++
  "  slli t0, a5, 5; add a2, a4, t0           # effect base = skip_base + skip_count*32\n" ++
  "  slli t0, a3, 7; slli t1, a3, 4; sub t0, t0, t1   # effect_count * 112\n" ++
  "  add a0, a2, t0              # BAL section ptr = effect_base + 112*count\n" ++
  "  jal ra, bal_all_accounts_nonstorage_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lc3ns_pdone\n" ++
  balAllAccountsNonstorageConsistentFunction ++ "\n" ++
  balAccountNonstorageConsistentFunction ++ "\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lc3ns_pdone:"

def ziskBalAllAccountsNonstorageConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  ziskBalAccountNonstorageConsistentDataSection  -- c2nsc_finals + c2nsf_* + rfu scratch

def ziskBalAllAccountsNonstorageConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsNonstorageConsistentPrologue
  dataAsm     := ziskBalAllAccountsNonstorageConsistentDataSection
}

end EvmAsm.Codegen
