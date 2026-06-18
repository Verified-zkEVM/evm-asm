/-
  EvmAsm.Codegen.Programs.BalAllAccountsNonstorageCovers

  `bal_all_accounts_nonstorage_covers` (bead i3djw / bmvmx.1.6.4.4 step .3b) — the
  REVERSE-completeness half of the all-accounts non-storage exec-vs-BAL check, the
  companion of bal_all_accounts_nonstorage_consistent (#8588, step .3a, forward) and
  the non-storage analog of bal_storage_covers_exec_log (#8569).

  Where .3a iterates BAL accounts and checks each declared final is reproduced by exec,
  .3b iterates the execution-derived non-storage effect array and checks that every
  account exec NET-CHANGED (post != pre, for balance or nonce) is PRESENT in the
  block_access_list — catching the soundness-critical case of an account exec changed
  but ENTIRELY ABSENT from the BAL (a producer hiding a balance/nonce movement).

  Effect record (112 B, 8-byte aligned), keyed by 20-byte big-endian address:
    +0 address (20B→32) | +32 pre_balance (32B BE) | +64 post_balance (32B BE)
    | +96 pre_nonce (u64) | +104 post_nonce (u64)

  The top-level recipient is SKIPPED (its balance/nonce are checked on the gas/balance
  path — claude-c1's sender/recipient balance compare), as in .3a / #8576. An effect
  with no net change (pre == post) imposes no obligation. A net-changed non-recipient
  effect that matches no BAL account returns 1 (conservative reject). This verifies only
  PRESENCE; the matched account's finals are verified by .3a. Code is out of scope until
  CREATE/SELFDESTRUCT exec.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.NonstorageEffectLog

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_all_accounts_nonstorage_covers
    a0 = BAL section RLP ptr (list of AccountChanges)   a1 = BAL section RLP length
    a2 = exec non-storage effect array base             a3 = effect record count
    a4 = skip-list ptr (array of 32-byte-padded 20-byte addresses to SKIP — the
         gas/value-coupled accounts {sender, recipient, coinbase}, checked on the gas path)
    a5 = skip-list count
    a0 (output) = 0 every net-changed effect is present in the BAL / 1 reject. -/
def balAllAccountsNonstorageCoversFunction : String :=
  "bal_all_accounts_nonstorage_covers:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # BAL section ptr\n" ++
  "  mv s1, a1                   # BAL section len\n" ++
  "  mv s2, a2                   # effect array base (SORTED, deduplicated agg)\n" ++
  "  mv s3, a3                   # effect record count\n" ++
  "  mv s4, a4                   # skip-list ptr\n" ++
  "  mv s10, a5                  # skip-list count\n" ++
  "  mv a0, s0; mv a1, s1; la a2, c3cov_acct_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lc3cov_fail\n" ++
  "  la t0, c3cov_acct_count; ld s5, 0(t0)   # BAL account count\n" ++
  "  # bmvmx.5.5.7.3 step c: LINEARIZED via a matched-bitmap, removing the old O(BAL*agg) inner\n" ++
  "  # BAL scan (the last O(N^2) barrier blocking the effect-log cap lift). The effect agg is now\n" ++
  "  # SORTED + deduplicated (every caller routes through nonstorage_effect_aggregate), so:\n" ++
  "  #   Phase 1: iterate BAL accounts ONCE; binary-search the sorted agg for each (O(log agg),\n" ++
  "  #            mirrors the forward .Lc3ns_bs); on a hit, set covered[mid]=1.\n" ++
  "  #   Phase 2: iterate agg entries ONCE; a net-changed non-skip effect with covered[j]==0 was\n" ++
  "  #            reproduced by exec but is ENTIRELY ABSENT from the BAL -> reject.\n" ++
  "  # Total O((BAL+agg)*log agg) instead of O(BAL*agg). covered[] is sized to nonstorageEffectLogCap\n" ++
  "  # bytes and indexed by agg index, so it stays valid as the cap is lifted. Semantics are\n" ++
  "  # byte-identical to the prior linear-scan covers.\n" ++
  "  # --- Phase 0: clear covered[0..count) ---\n" ++
  "  la t0, c3cov_covered; li t1, 0\n" ++
  ".Lc3cov_clr:\n" ++
  "  beq t1, s3, .Lc3cov_clrdone\n" ++
  "  add t2, t0, t1; sb x0, 0(t2)\n" ++
  "  addi t1, t1, 1; j .Lc3cov_clr\n" ++
  ".Lc3cov_clrdone:\n" ++
  "  # --- Phase 1: mark each agg entry that some BAL account's address binary-searches to ---\n" ++
  "  li s8, 0                    # BAL account index k\n" ++
  ".Lc3cov_mloop:\n" ++
  "  beq s8, s5, .Lc3cov_mdone\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s8; la a3, c3cov_acct_off; la a4, c3cov_acct_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lc3cov_fail       # malformed BAL list -> reject\n" ++
  "  la t0, c3cov_acct_off; ld t1, 0(t0); add s9, s0, t1   # AccountChanges[k] ptr\n" ++
  "  mv a0, s9; la t0, c3cov_acct_len; ld a1, 0(t0); li a2, 0; la a3, c3cov_addr_off; la a4, c3cov_addr_len\n" ++
  "  jal ra, rlp_list_nth_item                              # item 0 = address\n" ++
  "  bnez a0, .Lc3cov_fail       # malformed account -> reject\n" ++
  "  la t0, c3cov_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lc3cov_madv   # not 20B -> covers nothing\n" ++
  "  la t0, c3cov_addr_off; ld t1, 0(t0); add s7, s9, t1    # BAL addr ptr (20B BE) = search target\n" ++
  "  li t4, 0                                 # lo\n" ++
  "  mv a3, s3                                # hi = effect count\n" ++
  ".Lc3cov_bs:\n" ++
  "  bgeu t4, a3, .Lc3cov_madv                # lo >= hi -> agg has no entry for this BAL account\n" ++
  "  add a4, t4, a3; srli a4, a4, 1           # mid = (lo+hi)/2\n" ++
  "  slli t5, a4, 7; slli t6, a4, 4; sub t5, t5, t6; add t5, s2, t5   # &agg[mid] (mid*112)\n" ++
  "  li a6, 0\n" ++
  ".Lc3cov_bscmp:\n" ++
  "  li a7, 20; beq a6, a7, .Lc3cov_bsfound   # 20 bytes equal -> covered[mid]=1\n" ++
  "  add a0, t5, a6; lbu a1, 0(a0)            # agg[mid].addr[a6]\n" ++
  "  add a0, s7, a6; lbu a2, 0(a0)            # target.addr[a6]\n" ++
  "  bltu a1, a2, .Lc3cov_bslo                # agg[mid] < target -> upper half\n" ++
  "  bltu a2, a1, .Lc3cov_bshi                # agg[mid] > target -> lower half\n" ++
  "  addi a6, a6, 1; j .Lc3cov_bscmp\n" ++
  ".Lc3cov_bslo:\n" ++
  "  addi t4, a4, 1; j .Lc3cov_bs             # lo = mid+1\n" ++
  ".Lc3cov_bshi:\n" ++
  "  mv a3, a4; j .Lc3cov_bs                  # hi = mid\n" ++
  ".Lc3cov_bsfound:\n" ++
  "  la t0, c3cov_covered; add t0, t0, a4; li t1, 1; sb t1, 0(t0)   # covered[mid] = 1\n" ++
  ".Lc3cov_madv:\n" ++
  "  addi s8, s8, 1; j .Lc3cov_mloop\n" ++
  ".Lc3cov_mdone:\n" ++
  "  # --- Phase 2: every net-changed non-skip agg entry must be covered ---\n" ++
  "  li s6, 0                    # effect index j\n" ++
  ".Lc3cov_eloop:\n" ++
  "  beq s6, s3, .Lc3cov_ok\n" ++
  "  slli t0, s6, 7; slli t1, s6, 4; sub t0, t0, t1; add s7, s2, t0   # effect[j] ptr (j*112)\n" ++
  "  # --- net change? balance (32B) or nonce (u64) ---\n" ++
  "  addi t2, s7, 32; addi t3, s7, 64\n" ++
  "  ld t4, 0(t2);  ld t5, 0(t3);  bne t4, t5, .Lc3cov_changed\n" ++
  "  ld t4, 8(t2);  ld t5, 8(t3);  bne t4, t5, .Lc3cov_changed\n" ++
  "  ld t4, 16(t2); ld t5, 16(t3); bne t4, t5, .Lc3cov_changed\n" ++
  "  ld t4, 24(t2); ld t5, 24(t3); bne t4, t5, .Lc3cov_changed\n" ++
  "  ld t4, 96(s7); ld t5, 104(s7); bne t4, t5, .Lc3cov_changed\n" ++
  "  j .Lc3cov_enext             # no net change -> no obligation\n" ++
  ".Lc3cov_changed:\n" ++
  "  # --- skip gas/value-coupled accounts {sender,recipient,coinbase} (gas-path checked) ---\n" ++
  "  li t4, 0                                 # skip-list entry index\n" ++
  ".Lc3cov_skloop:\n" ++
  "  beq t4, s10, .Lc3cov_check               # not in skip-list -> must be present in BAL\n" ++
  "  slli t5, t4, 5; add t5, s4, t5           # skip entry ptr (32B strided)\n" ++
  "  li t6, 0\n" ++
  ".Lc3cov_skcmp:\n" ++
  "  li a0, 20; beq t6, a0, .Lc3cov_enext     # effect addr equals a skip entry -> skip\n" ++
  "  add a0, s7, t6; lbu a1, 0(a0)            # effect addr byte\n" ++
  "  add a0, t5, t6; lbu a2, 0(a0)            # skip entry byte\n" ++
  "  bne a1, a2, .Lc3cov_skadv\n" ++
  "  addi t6, t6, 1; j .Lc3cov_skcmp\n" ++
  ".Lc3cov_skadv:\n" ++
  "  addi t4, t4, 1; j .Lc3cov_skloop\n" ++
  ".Lc3cov_check:\n" ++
  "  la t0, c3cov_covered; add t0, t0, s6; lbu t1, 0(t0)\n" ++
  "  beqz t1, .Lc3cov_fail       # net-changed non-skip exec effect absent from BAL -> reject\n" ++
  ".Lc3cov_enext:\n" ++
  "  addi s6, s6, 1; j .Lc3cov_eloop\n" ++
  ".Lc3cov_ok:\n" ++
  "  li a0, 0; j .Lc3cov_ret\n" ++
  ".Lc3cov_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lc3cov_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_bal_all_accounts_nonstorage_covers`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL section length
      bytes 16..24 : exec effect record count
      bytes 24..32 : skip-list count
      bytes 32..    : skip-list (count * 32B), then effect array (count * 112B), then the BAL section
    Output: bytes 0..8 = status (0 covered / 1 reject). -/
def ziskBalAllAccountsNonstorageCoversPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # BAL section len\n" ++
  "  ld a3, 16(t6)               # effect record count\n" ++
  "  ld a5, 24(t6)               # skip-list count\n" ++
  "  addi a4, t6, 32             # skip-list base (0x40000020, 8-aligned)\n" ++
  "  slli t0, a5, 5; add a2, a4, t0           # effect base = skip_base + skip_count*32\n" ++
  "  slli t0, a3, 7; slli t1, a3, 4; sub t0, t0, t1   # effect_count * 112\n" ++
  "  add a0, a2, t0              # BAL section ptr = effect_base + 112*count\n" ++
  "  jal ra, bal_all_accounts_nonstorage_covers\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lc3cov_pdone\n" ++
  balAllAccountsNonstorageCoversFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  ".Lc3cov_pdone:"

def ziskBalAllAccountsNonstorageCoversDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "c3cov_acct_count:\n  .zero 8\n" ++
  "c3cov_acct_off:\n  .zero 8\n" ++
  "c3cov_acct_len:\n  .zero 8\n" ++
  "c3cov_addr_off:\n  .zero 8\n" ++
  "c3cov_addr_len:\n  .zero 8\n" ++
  -- bmvmx.5.5.7.3 step c: per-agg-entry "covered by some BAL account" bitmap (1 byte/entry),
  -- indexed by agg index, so it MUST be at least nonstorageEffectLogCap bytes.
  "c3cov_covered:\n  .zero " ++ toString nonstorageEffectLogCap ++ "\n"

def ziskBalAllAccountsNonstorageCoversProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsNonstorageCoversPrologue
  dataAsm     := ziskBalAllAccountsNonstorageCoversDataSection
}

end EvmAsm.Codegen
