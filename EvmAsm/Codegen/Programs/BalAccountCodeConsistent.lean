/-
  EvmAsm.Codegen.Programs.BalAccountCodeConsistent

  `bal_account_code_consistent` (bead i3djw / bmvmx.1.6.4.4 — the CODE field) — the
  per-account CODE exec-vs-BAL comparator, completing the non-storage field family
  alongside bal_account_nonstorage_consistent (#8586, balance + nonce). It uses the
  code field LOCATED by bal_account_nonstorage_finals (#8584, step .1) and compares
  the BAL's declared deployed code bytes against an execution-derived code effect,
  forward + reverse.

  An account's code only changes via CREATE/CREATE2 (deploy) or SELFDESTRUCT (clear),
  so this is the i3djw piece gated on CREATE/SELFDESTRUCT execution: the comparator is
  built + probe-tested now, wired once that exec produces code effects.

  Execution-derived code effect record:
    +0  has_code_change (u64; 1 if exec created/destroyed this account's code)
    +8  code_len        (u64; deployed code byte length)
    +16 code bytes      (the deployed bytecode)

  EIP-7928 code_changes carries the full new_code BYTES (not a hash), and exec has the
  deployed bytes at deploy time, so this compares bytes directly (no keccak): if the
  bytes match, the state code_hash = keccak(code) matches too.

  Direction: forward (BAL declares a code change => exec changed it AND bytes match) +
  reverse (exec changed code => BAL declares it, matching bytes). Conservative: parse
  failure returns 2, any mismatch/omission returns 1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_code_consistent
    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = exec code effect record ptr (layout above)
    a0 (output) = 0 consistent / 1 inconsistent / 2 BAL parse failure. -/
def balAccountCodeConsistentFunction : String :=
  "bal_account_code_consistent:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # AccountChanges ptr\n" ++
  "  mv s1, a2                   # exec code effect ptr\n" ++
  "  la s2, bacc_finals          # 88-byte finals scratch\n" ++
  "  mv a2, s2                   # finals out = scratch (a0/a1 still AccountChanges ptr/len)\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lbacc_parsefail   # BAL parse failure -> 2\n" ++
  "  ld t0, 56(s2)               # bal_declared = has_code\n" ++
  "  ld t1, 0(s1)                # exec_changed = has_code_change\n" ++
  "  bnez t1, .Lbacc_exec_changed\n" ++
  "  # exec did NOT change code\n" ++
  "  beqz t0, .Lbacc_ok          # BAL silent too -> consistent\n" ++
  "  j .Lbacc_bad                # BAL declares a code change exec didn't make -> reject\n" ++
  ".Lbacc_exec_changed:\n" ++
  "  beqz t0, .Lbacc_bad         # exec changed code but BAL silent -> reject\n" ++
  "  # both declare: lengths then bytes must match\n" ++
  "  ld t2, 72(s2)               # BAL code_len\n" ++
  "  ld t3, 8(s1)                # exec code_len\n" ++
  "  bne t2, t3, .Lbacc_bad\n" ++
  "  ld t4, 64(s2); add t4, s0, t4   # BAL code ptr = AccountChanges + code_off\n" ++
  "  addi t5, s1, 16             # exec code ptr\n" ++
  ".Lbacc_cmp:\n" ++
  "  beqz t2, .Lbacc_ok\n" ++
  "  lbu t6, 0(t4); lbu a0, 0(t5); bne t6, a0, .Lbacc_bad\n" ++
  "  addi t4, t4, 1; addi t5, t5, 1; addi t2, t2, -1; j .Lbacc_cmp\n" ++
  ".Lbacc_ok:\n" ++
  "  li a0, 0; j .Lbacc_ret\n" ++
  ".Lbacc_bad:\n" ++
  "  li a0, 1; j .Lbacc_ret\n" ++
  ".Lbacc_parsefail:\n" ++
  "  li a0, 2\n" ++
  ".Lbacc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_bal_account_code_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : AccountChanges byte length
      bytes 16..24 : exec code effect padded byte length
      bytes 24..    : exec code effect (has_code_change u64 | code_len u64 | code bytes),
                      padded to 8; then the AccountChanges RLP
    Output: bytes 0..8 = status (0 consistent / 1 inconsistent / 2 parse fail). -/
def ziskBalAccountCodeConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # AccountChanges len\n" ++
  "  ld t1, 16(a5)               # exec effect padded length\n" ++
  "  addi a2, a5, 24             # exec code effect ptr (0x40000018, 8-aligned)\n" ++
  "  add a0, a2, t1              # AccountChanges ptr = effect ptr + padded effect length\n" ++
  "  jal ra, bal_account_code_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbacc_pdone\n" ++
  balAccountCodeConsistentFunction ++ "\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lbacc_pdone:"

def ziskBalAccountCodeConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bacc_finals:\n  .zero 88\n" ++
  ziskBalAccountNonstorageFinalsDataSection  -- c2nsf_* + rfu scratch for the inlined finals helper

def ziskBalAccountCodeConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountCodeConsistentPrologue
  dataAsm     := ziskBalAccountCodeConsistentDataSection
}

end EvmAsm.Codegen
