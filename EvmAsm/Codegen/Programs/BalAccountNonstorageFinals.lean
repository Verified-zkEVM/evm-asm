/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinals

  `bal_account_nonstorage_finals` (bead i3djw / bmvmx.1.6.4.4 step .1) — parse a BAL
  AccountChanges' NON-storage fields into their per-account FINAL values, the
  value-bearing companion of bal_storage_change_values (#8564, which does storage).
  This is the BAL-side foundation for the all-accounts non-storage exec-vs-BAL
  consistency check (the analog of bal_all_accounts_storage_consistent #8576).

  AccountChanges = RLP `[address, storage_changes, storage_reads, balance_changes,
  nonce_changes, code_changes]` (EIP-7928). Each of balance_changes (item 3) /
  nonce_changes (item 4) / code_changes (item 5) is a list of `[block_access_index,
  value]` tuples; the account's FINAL value for that field is the `value` of the
  LAST (highest block_access_index) tuple. (The per-tx tuple SEQUENCE is verified
  separately once the exec log carries a tx index — bmvmx.1.6.6.)
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_nonstorage_finals
    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length   a2 = out ptr (88 B)
    a0 (output) = 0 ok / 1 parse failure (conservative).
    Output layout (all u64/native unless noted):
      +0  has_balance (1 if balance_changes non-empty)
      +8  post_balance (32-byte big-endian, right-aligned)
      +40 has_nonce
      +48 post_nonce (u64)
      +56 has_code
      +64 code_off  (offset of the final code field RELATIVE to a0; 0 if none)
      +72 code_len  (byte length of the final code field content) -/
def balAccountNonstorageFinalsFunction : String :=
  "bal_account_nonstorage_finals:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # AccountChanges ptr\n" ++
  "  mv s1, a1                   # AccountChanges len\n" ++
  "  mv s2, a2                   # out ptr\n" ++
  "  sd zero, 0(s2); sd zero, 40(s2); sd zero, 56(s2); sd zero, 64(s2); sd zero, 72(s2)\n" ++
  "  sd zero, 8(s2); sd zero, 16(s2); sd zero, 24(s2); sd zero, 32(s2); sd zero, 48(s2)\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc2nsf_fail\n" ++
  "  sd a0, 48(sp); sd a1, 56(sp)\n" ++
  "  # Skip address, storage_changes, storage_reads.\n" ++
  "  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 48(sp)\n" ++
  "  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 48(sp)\n" ++
  "  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 48(sp)\n" ++
  "  # --- balance_changes = item 3; final post_balance = item 1 of its last tuple ---\n" ++
  "  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc2nsf_fail\n" ++
  "  sd a0, 48(sp); sub s3, a0, a2; mv s4, a2\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc2nsf_fail\n" ++
  "  beq a0, a1, .Lc2nsf_nonce\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp)\n" ++
  ".Lc2nsf_balance_last_loop:\n" ++
  "  ld t0, 64(sp); ld t1, 72(sp); beq t0, t1, .Lc2nsf_balance_have_last\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc2nsf_fail\n" ++
  "  sd a0, 64(sp); sub s3, a0, a2; mv s4, a2\n" ++
  "  j .Lc2nsf_balance_last_loop\n" ++
  ".Lc2nsf_balance_have_last:\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc2nsf_fail\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp)\n" ++
  "  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 64(sp)\n" ++
  "  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc2nsf_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; addi a2, s2, 8; jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  li t0, 1; sd t0, 0(s2)\n" ++
  "  # --- nonce_changes = item 4; final new_nonce = item 1 of its last tuple (u64) ---\n" ++
  ".Lc2nsf_nonce:\n" ++
  "  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc2nsf_fail\n" ++
  "  sd a0, 48(sp); sub s3, a0, a2; mv s4, a2\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc2nsf_fail\n" ++
  "  beq a0, a1, .Lc2nsf_code\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp)\n" ++
  ".Lc2nsf_nonce_last_loop:\n" ++
  "  ld t0, 64(sp); ld t1, 72(sp); beq t0, t1, .Lc2nsf_nonce_have_last\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc2nsf_fail\n" ++
  "  sd a0, 64(sp); sub s3, a0, a2; mv s4, a2\n" ++
  "  j .Lc2nsf_nonce_last_loop\n" ++
  ".Lc2nsf_nonce_have_last:\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc2nsf_fail\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp)\n" ++
  "  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 64(sp)\n" ++
  "  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc2nsf_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lc2nsf_fail\n" ++
  "  sd a0, 48(s2)\n" ++
  "  li t0, 1; sd t0, 40(s2)\n" ++
  "  # --- code_changes = item 5; locate item 1 of its last tuple (no conversion) ---\n" ++
  ".Lc2nsf_code:\n" ++
  "  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc2nsf_fail\n" ++
  "  sub s3, a0, a2; mv s4, a2\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc2nsf_fail\n" ++
  "  beq a0, a1, .Lc2nsf_ok\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp)\n" ++
  ".Lc2nsf_code_last_loop:\n" ++
  "  ld t0, 64(sp); ld t1, 72(sp); beq t0, t1, .Lc2nsf_code_have_last\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc2nsf_fail\n" ++
  "  sd a0, 64(sp); sub s3, a0, a2; mv s4, a2\n" ++
  "  j .Lc2nsf_code_last_loop\n" ++
  ".Lc2nsf_code_have_last:\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lc2nsf_fail\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp)\n" ++
  "  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 64(sp)\n" ++
  "  ld t3, 64(sp); ld a1, 72(sp); mv a0, t3; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lc2nsf_fail\n" ++
  "  sub t4, a0, a2; sub t4, t4, s0; sd t4, 64(s2)\n" ++
  "  sd a2, 72(s2)\n" ++
  "  li t0, 1; sd t0, 56(s2)\n" ++
  ".Lc2nsf_ok:\n" ++
  "  li a0, 0; j .Lc2nsf_ret\n" ++
  ".Lc2nsf_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lc2nsf_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_bal_account_nonstorage_finals`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes 8..16 : AccountChanges byte length
      bytes 16..  : the AccountChanges RLP
    Output: bytes 0..8 status, then the 88-byte finals block (see ABI above). -/
def ziskBalAccountNonstorageFinalsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # AccountChanges len\n" ++
  "  addi a0, a5, 16             # AccountChanges ptr\n" ++
  "  li a2, 0xa0010008           # finals out (OUTPUT + 8)\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lc2nsf_pdone\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lc2nsf_pdone:"

def ziskBalAccountNonstorageFinalsDataSection : String :=
  ""

def ziskBalAccountNonstorageFinalsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountNonstorageFinalsPrologue
  dataAsm     := ziskBalAccountNonstorageFinalsDataSection
}

end EvmAsm.Codegen
