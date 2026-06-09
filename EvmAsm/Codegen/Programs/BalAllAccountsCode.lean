/-
  EvmAsm.Codegen.Programs.BalAllAccountsCode

  `bal_all_accounts_code_consistent` (bead i3djw / bmvmx.1.6.4.4 — the all-accounts CODE
  forward wrapper) — runs the per-account code comparator bal_account_code_consistent
  (#8591) over every block_access_list account, completing the all-accounts non-storage
  surface (balance/nonce via #8588/#8589, code here).

  An account's code only changes via CREATE/CREATE2/SELFDESTRUCT, so each created/destroyed
  account has an execution-derived code-effect record keyed by its 20-byte big-endian
  address (per c2#5/c2#11 coordination). Because the deployed code is variable-length, the
  effect array is VARIABLE-STRIDE — one record:
    +0   address (20B BE in the low bytes, padded to 32)   <- key
    +32  has_code_change (u64)
    +40  code_len (u64)
    +48  code bytes (code_len, padded to 8 so the next record's address stays 8-aligned)
  i.e. record size = 48 + roundup8(code_len). The wrapper passes a2 = record+32 to
  bal_account_code_consistent (whose effect layout is `[has_code_change | code_len | code]`).

  DIRECTION — FORWARD: every BAL account that declares a code change must have a matching
  exec code-effect with identical bytes (and `bal_account_code_consistent`'s own per-account
  reverse rejects a matched account whose exec changed code the BAL omitted). A non-matched
  account that declares a code change is rejected; one that declares none is skipped. The
  account-level REVERSE (an exec code-effect for an account ENTIRELY ABSENT from the BAL) is
  a follow-up, analogous to .3b. No skip-list is needed: code never changes for the
  gas/value accounts {sender,recipient,coinbase} via the gas path.

  IMPORTANT (per c1#9/c2#11): this must only be wired once execution emits the code-effect
  records (.8b) — before that, removing CREATE from the self-contained gate (.8c) would leave
  a self-contained CREATE with no effect record, and the forward direction would false-reject.

  Conservative: any parse failure, per-account mismatch, or a code-declaring account with no
  matching exec code-effect returns 1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.BalAccountCodeConsistent

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_all_accounts_code_consistent
    a0 = BAL section RLP ptr (list of AccountChanges)   a1 = BAL section RLP length
    a2 = exec code-effect array base (variable-stride; layout above)   a3 = record count
    a0 (output) = 0 consistent / 1 reject. -/
def balAllAccountsCodeConsistentFunction : String :=
  "bal_all_accounts_code_consistent:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0                   # BAL section ptr\n" ++
  "  mv s1, a1                   # BAL section len\n" ++
  "  mv s2, a2                   # code-effect array base\n" ++
  "  mv s3, a3                   # record count\n" ++
  "  mv a0, s0; mv a1, s1; la a2, baac_acct_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbaac_fail\n" ++
  "  la t0, baac_acct_count; ld s4, 0(t0)   # account count\n" ++
  "  li s5, 0                    # account index\n" ++
  ".Lbaac_loop:\n" ++
  "  beq s5, s4, .Lbaac_ok\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5; la a3, baac_acct_off; la a4, baac_acct_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaac_fail\n" ++
  "  la t0, baac_acct_off; ld t1, 0(t0); add s6, s0, t1   # AccountChanges ptr\n" ++
  "  la t0, baac_acct_len; ld s7, 0(t0)                   # AccountChanges len\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 0; la a3, baac_addr_off; la a4, baac_addr_len\n" ++
  "  jal ra, rlp_list_nth_item                            # item 0 = address\n" ++
  "  bnez a0, .Lbaac_fail\n" ++
  "  la t0, baac_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lbaac_next   # not 20B -> skip\n" ++
  "  la t0, baac_addr_off; ld t1, 0(t0); add s8, s6, t1   # addr ptr (20B BE)\n" ++
  "  # --- find this account's code-effect by 20-byte address (variable-stride scan) ---\n" ++
  "  mv t0, s2                    # rec_ptr = effect base\n" ++
  "  li t1, 0                     # record index k\n" ++
  ".Lbaac_find:\n" ++
  "  beq t1, s3, .Lbaac_notfound  # scanned all records, none match\n" ++
  "  li t2, 0\n" ++
  ".Lbaac_cmp:\n" ++
  "  li t3, 20; beq t2, t3, .Lbaac_found\n" ++
  "  add t3, s8, t2; lbu t4, 0(t3)\n" ++
  "  add t3, t0, t2; lbu t5, 0(t3)\n" ++
  "  bne t4, t5, .Lbaac_adv\n" ++
  "  addi t2, t2, 1; j .Lbaac_cmp\n" ++
  ".Lbaac_adv:\n" ++
  "  ld t2, 40(t0)                # code_len\n" ++
  "  addi t2, t2, 7; andi t2, t2, -8   # roundup8(code_len)\n" ++
  "  addi t2, t2, 48              # + header (addr 32 + has_code_change 8 + code_len 8)\n" ++
  "  add t0, t0, t2               # rec_ptr += record size\n" ++
  "  addi t1, t1, 1; j .Lbaac_find\n" ++
  ".Lbaac_found:\n" ++
  "  mv a0, s6; mv a1, s7; addi a2, t0, 32   # effect = record+32 ([has_code_change|code_len|code])\n" ++
  "  jal ra, bal_account_code_consistent     # 0 consistent / 1 / 2 -> reject if != 0\n" ++
  "  bnez a0, .Lbaac_fail\n" ++
  "  j .Lbaac_next\n" ++
  ".Lbaac_notfound:\n" ++
  "  # no code-effect for this account: only a problem if the BAL declares a code change\n" ++
  "  mv a0, s6; mv a1, s7; la a2, bacc_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lbaac_fail                     # parse failure -> reject\n" ++
  "  la t0, bacc_finals; ld t1, 56(t0); bnez t1, .Lbaac_fail   # has_code declared but no effect -> reject\n" ++
  "  # declares no code change -> nothing to check here\n" ++
  ".Lbaac_next:\n" ++
  "  addi s5, s5, 1; j .Lbaac_loop\n" ++
  ".Lbaac_ok:\n" ++
  "  li a0, 0; j .Lbaac_ret\n" ++
  ".Lbaac_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbaac_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_bal_all_accounts_code_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL section length
      bytes 16..24 : code-effect record count
      bytes 24..32 : code-effect array total byte length
      bytes 32..    : code-effect array (variable-stride), then the BAL section
    Output: bytes 0..8 = status (0 consistent / 1 reject). -/
def ziskBalAllAccountsCodeConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # BAL section len\n" ++
  "  ld a3, 16(t6)               # code-effect record count\n" ++
  "  ld t0, 24(t6)               # code-effect array total byte length\n" ++
  "  addi a2, t6, 32             # code-effect array base (0x40000020, 8-aligned)\n" ++
  "  add a0, a2, t0              # BAL section ptr = effect base + effect total length\n" ++
  "  jal ra, bal_all_accounts_code_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbaac_pdone\n" ++
  balAllAccountsCodeConsistentFunction ++ "\n" ++
  balAccountCodeConsistentFunction ++ "\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lbaac_pdone:"

def ziskBalAllAccountsCodeConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "baac_acct_count:\n  .zero 8\n" ++
  "baac_acct_off:\n  .zero 8\n" ++
  "baac_acct_len:\n  .zero 8\n" ++
  "baac_addr_off:\n  .zero 8\n" ++
  "baac_addr_len:\n  .zero 8\n" ++
  ziskBalAccountCodeConsistentDataSection  -- bacc_finals + c2nsf_* + rfu scratch

def ziskBalAllAccountsCodeConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsCodeConsistentPrologue
  dataAsm     := ziskBalAllAccountsCodeConsistentDataSection
}

end EvmAsm.Codegen
