/-
  EvmAsm.Codegen.Programs.BalAllAccountsCodeCovers

  `bal_all_accounts_code_covers` (bead i3djw / bmvmx.1.6.4.4 — the all-accounts CODE
  reverse wrapper) — the reverse-completeness companion of the forward code wrapper
  bal_all_accounts_code_consistent (#8600), analogous to .3b vs .3a for balance/nonce.

  Where the forward wrapper iterates BAL accounts and checks each declared code change
  is reproduced by exec, this iterates the execution-derived code-effect array and checks
  that every account exec changed code for (CREATE/CREATE2 deploy or SELFDESTRUCT clear,
  `has_code_change=1`) is PRESENT in the block_access_list — catching a producer that
  hides a created/destroyed contract by omitting its account from the BAL.

  It verifies PRESENCE only: a present account's code declaration is verified by the
  forward wrapper (bal_account_code_consistent's per-account direction rejects a present
  account whose exec changed code the BAL didn't declare). So the obligation here is just
  "the account is in the BAL"; an absent account with `has_code_change=1` is a reject.

  The code-effect array is VARIABLE-STRIDE (per c2#11): one record
    +0 address (20B→32) | +32 has_code_change (u64) | +40 code_len (u64) | +48 code bytes
  with size 48 + roundup8(code_len). Records with `has_code_change=0` impose no obligation.
  No skip-list: code never changes for the gas/value accounts {sender,recipient,coinbase}.

  Conservative: any parse failure, or a `has_code_change=1` record whose address matches no
  BAL account, returns 1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_all_accounts_code_covers
    a0 = BAL section RLP ptr (list of AccountChanges)   a1 = BAL section RLP length
    a2 = exec code-effect array base (variable-stride)   a3 = record count
    a0 (output) = 0 every changed code-effect's account is present in the BAL / 1 reject. -/
def balAllAccountsCodeCoversFunction : String :=
  "bal_all_accounts_code_covers:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # BAL section ptr\n" ++
  "  mv s1, a1                   # BAL section len\n" ++
  "  mv s2, a2                   # code-effect array base\n" ++
  "  mv s3, a3                   # record count\n" ++
  "  mv a0, s0; mv a1, s1; la a2, bacov_acct_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbacov_fail\n" ++
  "  la t0, bacov_acct_count; ld s4, 0(t0)   # BAL account count\n" ++
  "  mv s5, s2                    # rec_ptr = effect base\n" ++
  "  li s6, 0                     # record index k\n" ++
  ".Lbacov_eloop:\n" ++
  "  beq s6, s3, .Lbacov_ok\n" ++
  "  ld t0, 32(s5); beqz t0, .Lbacov_advance   # has_code_change == 0 -> no obligation\n" ++
  "  # changed: scan BAL accounts for one whose item-0 address == effect record address (s5+0)\n" ++
  "  li s7, 0                     # BAL account scan index\n" ++
  ".Lbacov_sloop:\n" ++
  "  beq s7, s4, .Lbacov_fail     # scanned all, no BAL account -> reject (omitted created/destroyed account)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s7; la a3, bacov_acct_off; la a4, bacov_acct_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbacov_fail        # malformed BAL list -> reject\n" ++
  "  la t0, bacov_acct_off; ld t1, 0(t0); add t2, s0, t1   # AccountChanges[scan] ptr\n" ++
  "  mv a0, t2; la t0, bacov_acct_len; ld a1, 0(t0); li a2, 0; la a3, bacov_addr_off; la a4, bacov_addr_len\n" ++
  "  jal ra, rlp_list_nth_item                              # item 0 = address\n" ++
  "  bnez a0, .Lbacov_fail        # malformed account -> reject\n" ++
  "  la t0, bacov_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lbacov_sadv   # not 20B -> not a match\n" ++
  "  la t0, bacov_acct_off; ld t1, 0(t0); add t2, s0, t1    # recompute AccountChanges ptr\n" ++
  "  la t0, bacov_addr_off; ld t1, 0(t0); add t2, t2, t1    # BAL addr ptr (20B BE)\n" ++
  "  li t3, 0\n" ++
  ".Lbacov_acmp:\n" ++
  "  li t4, 20; beq t3, t4, .Lbacov_advance   # all 20 equal -> account present -> obligation met\n" ++
  "  add t4, s5, t3; lbu t5, 0(t4)            # effect record address byte\n" ++
  "  add t4, t2, t3; lbu t6, 0(t4)            # BAL address byte\n" ++
  "  bne t5, t6, .Lbacov_sadv\n" ++
  "  addi t3, t3, 1; j .Lbacov_acmp\n" ++
  ".Lbacov_sadv:\n" ++
  "  addi s7, s7, 1; j .Lbacov_sloop\n" ++
  ".Lbacov_advance:\n" ++
  "  ld t0, 40(s5); addi t0, t0, 7; andi t0, t0, -8; addi t0, t0, 48   # record size = 48 + roundup8(code_len)\n" ++
  "  add s5, s5, t0\n" ++
  "  addi s6, s6, 1; j .Lbacov_eloop\n" ++
  ".Lbacov_ok:\n" ++
  "  li a0, 0; j .Lbacov_ret\n" ++
  ".Lbacov_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbacov_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_bal_all_accounts_code_covers`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL section length
      bytes 16..24 : code-effect record count
      bytes 24..32 : code-effect array total byte length
      bytes 32..    : code-effect array (variable-stride), then the BAL section
    Output: bytes 0..8 = status (0 covered / 1 reject). -/
def ziskBalAllAccountsCodeCoversPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # BAL section len\n" ++
  "  ld a3, 16(t6)               # code-effect record count\n" ++
  "  ld t0, 24(t6)               # code-effect array total byte length\n" ++
  "  addi a2, t6, 32             # code-effect array base (0x40000020, 8-aligned)\n" ++
  "  add a0, a2, t0              # BAL section ptr = effect base + effect total length\n" ++
  "  jal ra, bal_all_accounts_code_covers\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbacov_pdone\n" ++
  balAllAccountsCodeCoversFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  ".Lbacov_pdone:"

def ziskBalAllAccountsCodeCoversDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bacov_acct_count:\n  .zero 8\n" ++
  "bacov_acct_off:\n  .zero 8\n" ++
  "bacov_acct_len:\n  .zero 8\n" ++
  "bacov_addr_off:\n  .zero 8\n" ++
  "bacov_addr_len:\n  .zero 8\n"

def ziskBalAllAccountsCodeCoversProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsCodeCoversPrologue
  dataAsm     := ziskBalAllAccountsCodeCoversDataSection
}

end EvmAsm.Codegen
