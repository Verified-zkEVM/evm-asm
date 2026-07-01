/-
  EvmAsm.Codegen.Programs.BalAccountHasStateChange

  Cheap BAL AccountChanges classifier for post-state-root replay.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_has_state_change -- detect state-affecting BAL rows

    a0 = AccountChanges RLP ptr   a1 = AccountChanges length
    a0 (output) = 0 no post-state change / 1 has post-state change / 2 parse fail.

    AccountChanges fields:
      [address, storage_changes, storage_reads, balance_changes, nonce_changes, code_changes]
    `storage_reads` are read-only, so only fields 1, 3, 4, and 5 can affect the
    post-state root. -/
def balAccountHasStateChangeFunction : String :=
  "bal_account_has_state_change:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbahsc_parse_fail\n" ++
  "  mv s0, a0                    # AccountChanges cursor\n" ++
  "  mv s1, a1                    # AccountChanges end\n" ++
  "  jal ra, rlp_walk_next        # item 0: address\n" ++
  "  bnez a1, .Lbahsc_parse_fail\n" ++
  "  mv s0, a0\n" ++
  "  jal ra, .Lbahsc_check_next   # item 1: storage_changes\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next        # item 2: storage_reads (read-only)\n" ++
  "  bnez a1, .Lbahsc_parse_fail\n" ++
  "  mv s0, a0\n" ++
  "  jal ra, .Lbahsc_check_next   # item 3: balance_changes\n" ++
  "  jal ra, .Lbahsc_check_next   # item 4: nonce_changes\n" ++
  "  jal ra, .Lbahsc_check_next   # item 5: code_changes\n" ++
  "  li a0, 0; j .Lbahsc_ret\n" ++
  "# Consume the next AccountChanges field and return if its sub-list is empty.\n" ++
  "# Branches directly to changed/parse-fail for the non-empty/fail outcomes.\n" ++
  ".Lbahsc_check_next:\n" ++
  "  mv s2, ra\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbahsc_parse_fail\n" ++
  "  mv s0, a0                    # advance AccountChanges cursor\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbahsc_parse_fail\n" ++
  "  bne a0, a1, .Lbahsc_changed\n" ++
  "  mv ra, s2; ret\n" ++
  ".Lbahsc_changed:\n" ++
  "  li a0, 1; j .Lbahsc_ret\n" ++
  ".Lbahsc_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbahsc_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskBalAccountHasStateChangeDataSection : String :=
  ".balign 8\n"

end EvmAsm.Codegen
