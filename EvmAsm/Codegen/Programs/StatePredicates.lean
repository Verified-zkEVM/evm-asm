/-
  EvmAsm.Codegen.Programs.StatePredicates

  Account-level boolean predicates over a stateless witness +
  parent header. Distinct from `StateCompose.lean` (full-record
  composites returning the account struct or specific fields)
  in that each function here returns a u64 predicate (0 or 1)
  based on a single spec-defined check.

  Hosts probes for spec primitives such as `account_exists`
  (this PR), with room to grow for EIP-161 `account_is_empty`,
  `account_alive`, and similar one-bit checks.

  Each probe composes K201 `header_extract_state_root` and K28
  `account_at_address` from `State.lean`, then applies the
  spec-specific predicate to the resulting account struct or
  status code.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## account_exists_at_header_state_root

    Witness-side implementation of the spec's `account_exists`
    predicate: returns 1 iff the address has any record in the
    state trie referenced by the parent header's `state_root`,
    else 0.

    This is the most fundamental account-level predicate, used
    by the spec wherever `apply_body` distinguishes a fresh
    (never-touched) account from a previously-recorded one
    regardless of the account's contents. It does NOT inspect
    nonce, balance, code_hash, or storage_root -- it only asks
    "is the account in the trie?". That makes it distinct from:

      * EIP-1052 `extcodehash_at_header_state_root` -- returns
        0 for absent OR empty accounts but non-zero for
        non-empty ones (looks at contents).
      * EIP-684 `has_code_or_nonce_at_header_state_root` --
        looks at `nonce` and `code_hash` only.
      * EIP-161 `account_is_empty` -- returns 1 for both
        fully-empty AND absent accounts.

    The clean separation is on purpose: stateless verifiers that
    care about pure existence (e.g. SELFDESTRUCT-target
    accounting in some EIPs) need exactly this predicate, not
    one of the content-aware variants.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      ra (input)  : return

      a0 (output) :
        0 = success (`aex_predicate` holds 0 or 1)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

    The probe BuildUnit copies `aex_predicate` to OUTPUT + 8.
-/
def accountExistsAtHeaderStateRootFunction : String :=
  "account_exists_at_header_state_root:\n" ++
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
  "  la t0, aex_predicate\n" ++
  "  sd zero, 0(t0)\n" ++
  "  # Step 1: header.state_root -> aex_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, aex_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Laex_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Laex_ret\n" ++
  ".Laex_step2:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, aex_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la s5, aex_acct_struct\n" ++
  "  mv a5, s5\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Laex_found\n" ++
  "  # status 1 (not in trie) -> predicate 0, return 0.\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Laex_absent\n" ++
  "  # status 2/3 -> propagate.\n" ++
  "  j .Laex_ret\n" ++
  ".Laex_absent:\n" ++
  "  # predicate already 0.\n" ++
  "  li a0, 0\n" ++
  "  j .Laex_ret\n" ++
  ".Laex_found:\n" ++
  "  la t0, aex_predicate\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  "  li a0, 0\n" ++
  ".Laex_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_account_exists_at_header_state_root`: probe BuildUnit.
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
def ziskAccountExistsAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  jal ra, account_exists_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  la t1, aex_predicate; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  j .Laex_pdone\n" ++
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
  accountExistsAtHeaderStateRootFunction ++ "\n" ++
  ".Laex_pdone:"

def ziskAccountExistsAtHeaderStateRootDataSection : String :=
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
  "aex_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aex_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "aex_predicate:\n" ++
  "  .zero 8"

def ziskAccountExistsAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExistsAtHeaderStateRootPrologue
  dataAsm     := ziskAccountExistsAtHeaderStateRootDataSection
}

/-! ## account_is_empty_at_header_state_root  (EIP-161)

    Witness-side implementation of the EIP-161 `account_is_empty`
    predicate: returns 1 iff the account is present in the state
    trie AND has `nonce == 0` AND `balance == 0` AND
    `code_hash == EMPTY_CODE_HASH`.

    This is the predicate used by spec primitives that need
    EIP-161's notion of emptiness:
      * SELFDESTRUCT touched-account refund accounting.
      * SSTORE refund rules (EIP-2200 / Berlin).
      * CALL value-transfer "touch" semantics.

    Completes the boolean-predicate trio with:
      * `account_exists_at_header_state_root` (presence only;
        ignores contents).
      * `has_code_or_nonce_at_header_state_root` (EIP-684
        CREATE collision; nonce OR code, no balance).

    Spec-distinguishing rows (account_in_trie = present):

        | account contents             | exists | EIP-684 | EIP-161 |
        |------------------------------|--------|---------|---------|
        | fully empty                  |   1    |    0    |    1    |
        | balance only (n=0, c=EMPTY)  |   1    |    0    |    0    |
        | nonce only  (b=0, c=EMPTY)   |   1    |    1    |    0    |
        | contract    (c != EMPTY)     |   1    |    1    |    0    |
        | (not in trie)                |   0    |    0    |    0    |

    The `fully empty` row is where EIP-161 and EIP-684 give
    OPPOSITE results: EIP-161 says empty (1), EIP-684 says no
    collision (0). The `balance only` row is where EIP-161 and
    `account_exists` give opposite results (0 vs 1).

    Composes K201 `header_extract_state_root` + K28
    `account_at_address` + an inline 9 x u64 check (1 nonce + 4
    balance + 4 code_hash) against the baked-in EMPTY_CODE_HASH
    constant.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      ra (input)  : return

      a0 (output) :
        0 = success (`aie_predicate` holds 0 or 1)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

    Account-not-in-trie maps to predicate 0 (EIP-161 says empty
    only when account is PRESENT but trivially zero; an absent
    account is NOT empty per the strict spec read, because
    `state[addr]` is undefined rather than equal to the empty
    record). The probe BuildUnit copies `aie_predicate` to
    OUTPUT + 8.
-/
def accountIsEmptyAtHeaderStateRootFunction : String :=
  "account_is_empty_at_header_state_root:\n" ++
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
  "  la t0, aie_predicate\n" ++
  "  sd zero, 0(t0)\n" ++
  "  # Step 1: header.state_root -> aie_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, aie_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Laiehsr_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Laiehsr_ret\n" ++
  ".Laiehsr_step2:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, aie_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la s5, aie_acct_struct\n" ++
  "  mv a5, s5\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Laiehsr_check\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Laiehsr_absent\n" ++
  "  j .Laiehsr_ret\n" ++
  ".Laiehsr_absent:\n" ++
  "  # absent -> predicate 0 (already zero).\n" ++
  "  li a0, 0\n" ++
  "  j .Laiehsr_ret\n" ++
  ".Laiehsr_check:\n" ++
  "  # nonce == 0 ?\n" ++
  "  ld t1, 0(s5)\n" ++
  "  bnez t1, .Laiehsr_non_empty\n" ++
  "  # balance == 0 ?\n" ++
  "  ld t1,  8(s5); bnez t1, .Laiehsr_non_empty\n" ++
  "  ld t1, 16(s5); bnez t1, .Laiehsr_non_empty\n" ++
  "  ld t1, 24(s5); bnez t1, .Laiehsr_non_empty\n" ++
  "  ld t1, 32(s5); bnez t1, .Laiehsr_non_empty\n" ++
  "  # code_hash == EMPTY_CODE_HASH ?\n" ++
  "  la t0, aie_empty_code_hash\n" ++
  "  ld t1,  0(t0); ld t2, 72(s5); bne t1, t2, .Laiehsr_non_empty\n" ++
  "  ld t1,  8(t0); ld t2, 80(s5); bne t1, t2, .Laiehsr_non_empty\n" ++
  "  ld t1, 16(t0); ld t2, 88(s5); bne t1, t2, .Laiehsr_non_empty\n" ++
  "  ld t1, 24(t0); ld t2, 96(s5); bne t1, t2, .Laiehsr_non_empty\n" ++
  "  # All three empty-conditions hold; predicate := 1.\n" ++
  "  la t0, aie_predicate\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  "  li a0, 0\n" ++
  "  j .Laiehsr_ret\n" ++
  ".Laiehsr_non_empty:\n" ++
  "  # Predicate stays 0.\n" ++
  "  li a0, 0\n" ++
  ".Laiehsr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_account_is_empty_at_header_state_root`: probe BuildUnit.
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
def ziskAccountIsEmptyAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a0, t1, 44             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  jal ra, account_is_empty_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, aie_predicate; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  j .Laiehsr_pdone\n" ++
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
  accountIsEmptyAtHeaderStateRootFunction ++ "\n" ++
  ".Laiehsr_pdone:"

def ziskAccountIsEmptyAtHeaderStateRootDataSection : String :=
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
  "aie_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "aie_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "aie_predicate:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskAccountIsEmptyAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountIsEmptyAtHeaderStateRootPrologue
  dataAsm     := ziskAccountIsEmptyAtHeaderStateRootDataSection
}

end EvmAsm.Codegen
