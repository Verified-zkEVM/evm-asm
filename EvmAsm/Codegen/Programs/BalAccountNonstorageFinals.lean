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
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

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
      +72 code_len  (byte length of the final code field, RLP-encoded form) -/
def balAccountNonstorageFinalsFunction : String :=
  "bal_account_nonstorage_finals:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # AccountChanges ptr\n" ++
  "  mv s1, a1                   # AccountChanges len\n" ++
  "  mv s2, a2                   # out ptr\n" ++
  "  sd zero, 0(s2); sd zero, 40(s2); sd zero, 56(s2); sd zero, 64(s2); sd zero, 72(s2)\n" ++
  "  sd zero, 8(s2); sd zero, 16(s2); sd zero, 24(s2); sd zero, 32(s2); sd zero, 48(s2)\n" ++
  "  # --- balance_changes = item 3; final post_balance = item 1 of its last tuple ---\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3; la a3, c2nsf_off; la a4, c2nsf_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  la t0, c2nsf_off; ld t1, 0(t0); add s3, s0, t1     # balance_changes ptr\n" ++
  "  la t0, c2nsf_len; ld s4, 0(t0)\n" ++
  "  mv a0, s3; mv a1, s4; la a2, c2nsf_cnt; jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  la t0, c2nsf_cnt; ld t1, 0(t0); beqz t1, .Lc2nsf_nonce\n" ++
  "  addi t1, t1, -1\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, t1; la a3, c2nsf_toff; la a4, c2nsf_tlen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  la t0, c2nsf_toff; ld t1, 0(t0); add a0, s3, t1    # last tuple ptr\n" ++
  "  la t0, c2nsf_tlen; ld a1, 0(t0)\n" ++
  "  li a2, 1; addi a3, s2, 8; jal ra, rlp_field_to_u256_be   # post_balance -> out+8\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  li t0, 1; sd t0, 0(s2)\n" ++
  "  # --- nonce_changes = item 4; final new_nonce = item 1 of its last tuple (u64) ---\n" ++
  ".Lc2nsf_nonce:\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4; la a3, c2nsf_off; la a4, c2nsf_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  la t0, c2nsf_off; ld t1, 0(t0); add s3, s0, t1     # nonce_changes ptr\n" ++
  "  la t0, c2nsf_len; ld s4, 0(t0)\n" ++
  "  mv a0, s3; mv a1, s4; la a2, c2nsf_cnt; jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  la t0, c2nsf_cnt; ld t1, 0(t0); beqz t1, .Lc2nsf_code\n" ++
  "  addi t1, t1, -1\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, t1; la a3, c2nsf_toff; la a4, c2nsf_tlen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  la t0, c2nsf_toff; ld t1, 0(t0); add a0, s3, t1\n" ++
  "  la t0, c2nsf_tlen; ld a1, 0(t0)\n" ++
  "  li a2, 1; addi a3, s2, 48; jal ra, rlp_field_to_u64    # post_nonce -> out+48\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  li t0, 1; sd t0, 40(s2)\n" ++
  "  # --- code_changes = item 5; locate item 1 of its last tuple (no conversion) ---\n" ++
  ".Lc2nsf_code:\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5; la a3, c2nsf_off; la a4, c2nsf_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  la t0, c2nsf_off; ld t1, 0(t0); add s3, s0, t1     # code_changes ptr\n" ++
  "  la t0, c2nsf_len; ld s4, 0(t0)\n" ++
  "  mv a0, s3; mv a1, s4; la a2, c2nsf_cnt; jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  la t0, c2nsf_cnt; ld t1, 0(t0); beqz t1, .Lc2nsf_ok\n" ++
  "  addi t1, t1, -1\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, t1; la a3, c2nsf_toff; la a4, c2nsf_tlen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  la t0, c2nsf_toff; ld t1, 0(t0); add t2, s3, t1    # last code tuple ptr\n" ++
  "  la t0, c2nsf_tlen; ld a1, 0(t0)\n" ++
  "  mv a0, t2; li a2, 1; la a3, c2nsf_coff; la a4, c2nsf_clen\n" ++
  "  jal ra, rlp_list_nth_item                          # code field within the tuple\n" ++
  "  bnez a0, .Lc2nsf_fail\n" ++
  "  la t0, c2nsf_coff; ld t3, 0(t0); add t3, t2, t3    # absolute code field ptr\n" ++
  "  sub t3, t3, s0                                      # offset relative to AccountChanges\n" ++
  "  sd t3, 64(s2)\n" ++
  "  la t0, c2nsf_clen; ld t3, 0(t0); sd t3, 72(s2)\n" ++
  "  li t0, 1; sd t0, 56(s2)\n" ++
  ".Lc2nsf_ok:\n" ++
  "  li a0, 0; j .Lc2nsf_ret\n" ++
  ".Lc2nsf_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lc2nsf_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
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
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lc2nsf_pdone:"

def ziskBalAccountNonstorageFinalsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "c2nsf_off:\n  .zero 8\n" ++
  "c2nsf_len:\n  .zero 8\n" ++
  "c2nsf_cnt:\n  .zero 8\n" ++
  "c2nsf_toff:\n  .zero 8\n" ++
  "c2nsf_tlen:\n  .zero 8\n" ++
  "c2nsf_coff:\n  .zero 8\n" ++
  "c2nsf_clen:\n  .zero 8\n" ++
  ziskRlpFieldToU64DataSection   -- rfu_offset/rfu_length scratch for rlp_field_to_u256_be/u64

def ziskBalAccountNonstorageFinalsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountNonstorageFinalsPrologue
  dataAsm     := ziskBalAccountNonstorageFinalsDataSection
}

end EvmAsm.Codegen
