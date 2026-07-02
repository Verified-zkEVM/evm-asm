/-
  EvmAsm.Codegen.Programs.EvmCodes

  EVM-opcode state-query programs carved out of `StateCompose.lean`
  to keep that file under the hard-cap line limit.  Imports
  `StateCompose` so it can reference the string-constant helpers
  defined there.
-/
import EvmAsm.Codegen.Programs.StateCompose

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## has_code_or_nonce_at_header_state_root  (EIP-684 CREATE collision)

    Witness-side predicate for the EIP-684 CREATE2 / CREATE
    collision check: given a parent header RLP, an address, and
    an SSZ `witness.state` list section, return 1 iff the
    account at the address has `code_hash != EMPTY_CODE_HASH`,
    `nonce > 0`, or a non-empty storage root, else 0.

    The check is what `apply_body` uses before letting a CREATE
    opcode place new code at an address: per EIP-684, a CREATE
    that would land on an account with non-zero nonce,
    non-trivial code, or non-empty storage is rejected up-front,
    so pre-existing account state can't be silently overwritten.

    Distinct from the EIP-1052 EXTCODEHASH empty-account rule
    (which ALSO requires `balance == 0`): EIP-684 considers an
    account collision-relevant when its nonce, code, or storage is
    non-empty; balance-only accounts remain deployable.

    Composes K201 `header_extract_state_root`, K28
    `account_at_address`, and an inline check on 1 u64 nonce +
    4 u64 storage_root compares + 4 u64 code_hash compares.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      ra (input)  : return

      a0 (output) :
        0 = success (`hcon_predicate` holds 0 or 1)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

    The probe BuildUnit copies `hcon_predicate` to OUTPUT + 8.
    On a "not in trie" miss, the predicate is 0 (no collision)
    and the status is 0 -- account absence is a valid spec-side
    outcome, not an error.
-/
def hasCodeOrNonceAtHeaderStateRootFunction : String :=
  "has_code_or_nonce_at_header_state_root:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  # Pre-zero predicate.\n" ++
  "  la t0, hcon_predicate\n" ++
  "  sd zero, 0(t0)\n" ++
  "  # Step 1: header.state_root -> hcon_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, hcon_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lhcon_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lhcon_ret\n" ++
  ".Lhcon_step2:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, hcon_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la s5, hcon_acct_struct\n" ++
  "  mv a5, s5\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lhcon_check\n" ++
  "  # status 1 (not in trie) -> predicate 0 (no collision), return 0.\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lhcon_zero\n" ++
  "  # status 2/3 -> propagate.\n" ++
  "  j .Lhcon_ret\n" ++
  ".Lhcon_zero:\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcon_ret\n" ++
  ".Lhcon_check:\n" ++
  "  # nonce != 0 ?\n" ++
  "  ld t1, 0(s5)\n" ++
  "  bnez t1, .Lhcon_collide\n" ++
  "  # storage_root != EMPTY_TRIE_ROOT ? (EIP-7610 create-collision)\n" ++
  "  la t0, hcon_empty_trie_root\n" ++
  "  ld t1,  0(t0); ld t2, 40(s5); bne t1, t2, .Lhcon_collide\n" ++
  "  ld t1,  8(t0); ld t2, 48(s5); bne t1, t2, .Lhcon_collide\n" ++
  "  ld t1, 16(t0); ld t2, 56(s5); bne t1, t2, .Lhcon_collide\n" ++
  "  ld t1, 24(t0); ld t2, 64(s5); bne t1, t2, .Lhcon_collide\n" ++
  "  # code_hash != EMPTY_CODE_HASH ?\n" ++
  "  la t0, hcon_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(s5); bne t1, t2, .Lhcon_collide\n" ++
  "  ld t1,  8(t0); ld t2, 80(s5); bne t1, t2, .Lhcon_collide\n" ++
  "  ld t1, 16(t0); ld t2, 88(s5); bne t1, t2, .Lhcon_collide\n" ++
  "  ld t1, 24(t0); ld t2, 96(s5); bne t1, t2, .Lhcon_collide\n" ++
  "  # nonce == 0 AND storage_root == EMPTY AND code_hash == EMPTY -> no collision.\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcon_ret\n" ++
  ".Lhcon_collide:\n" ++
  "  la t0, hcon_predicate\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  "  li a0, 0\n" ++
  ".Lhcon_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_has_code_or_nonce_at_header_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..44+H              : header_rlp
      bytes 44+H..44+H+WS         : witness.state
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4)
      bytes  8..16 : predicate (u64; 0 or 1) -/
def ziskHasCodeOrNonceAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  jal ra, has_code_or_nonce_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  la t1, hcon_predicate; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  j .Lhcon_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  hasCodeOrNonceAtHeaderStateRootFunction ++ "\n" ++
  ".Lhcon_pdone:"

def ziskHasCodeOrNonceAtHeaderStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "hcon_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hcon_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "hcon_predicate:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "hcon_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 32\n" ++
  "hcon_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskHasCodeOrNonceAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHasCodeOrNonceAtHeaderStateRootPrologue
  dataAsm     := ziskHasCodeOrNonceAtHeaderStateRootDataSection
}

end EvmAsm.Codegen
