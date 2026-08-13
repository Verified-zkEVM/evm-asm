/-
  EvmAsm.Codegen.Programs.AccountVerify

  Account verification primitives: given a parent header, an
  address, and an expected 104-byte account struct (matching
  `account_at_address`'s output layout), confirm that walking
  the state trie in the witness produces exactly the expected
  fields. Useful for stateless-guest harness validation where
  the caller wants to assert "this account record is what I
  expect" rather than just "what's at this address?".

  Currently hosts `verify_account_struct_matches`.

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

/-! ## verify_account_struct_matches

    Walk the state trie at `header.state_root` to the leaf for
    `address`, decode the account record into the 104-byte
    `account_at_address` struct layout, and bytewise-compare
    against a caller-supplied expected struct. Returns
    `is_match = 1` iff every field matches.

    The 104-byte struct layout (caller follows the same
    convention as `account_at_address`):
      offset  0..  8 : nonce (u64 LE)
      offset  8.. 40 : balance (u256 BE, left-zero-padded)
      offset 40.. 72 : storage_root (32 B)
      offset 72..104 : code_hash (32 B)

    Spec-side use case: a stateless-guest test harness wants
    to confirm that a witness encodes a specific genesis state
    -- i.e., the account at `address` has nonce X, balance Y,
    storage_root Z, code_hash W. Rather than calling all four
    field-getters and comparing each, this primitive does one
    state walk + 13 u64 compares.

    Distinct from `account_at_header_state_root` (which RETURNS
    the struct) and from `account_exists_at_header_state_root`
    (which only checks presence): this one checks the full
    record AGAINST a claim.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : expected_account_struct ptr (104 bytes,
                    layout above)
      a6 (input)  : u64 out (is_match)
      ra (input)  : return

      a0 (output) :
        0 = success (is_match holds 0 or 1)
        1 = account not in state trie  (is_match = 0)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail

      (No is_match-side flattening: is_match = 1 only when the
      walk succeeds AND every byte of the struct matches. A
      missing-account result is reported as status 1, with
      is_match = 0.)
-/
def verifyAccountStructMatchesFunction : String :=
  "verify_account_struct_matches:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # expected_struct ptr\n" ++
  "  mv s6, a6                  # is_match out ptr\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # Step 1: header.state_root -> vasm_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, vasm_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lvasm_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lvasm_ret\n" ++
  ".Lvasm_step2:\n" ++
  "  # Step 2: account_at_address -> vasm_walked_struct.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, vasm_state_root\n" ++
  "  mv a3, s3\n" ++
  "  mv a4, s4\n" ++
  "  la a5, vasm_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  bnez a0, .Lvasm_ret        # 1/2/3 propagate; is_match stays 0\n" ++
  "  # Step 3: compare vasm_walked_struct vs s5 (expected), 104 bytes.\n" ++
  "  # 13 u64 compares (104 / 8).\n" ++
  "  la t0, vasm_walked_struct\n" ++
  "  ld t1,   0(t0); ld t2,   0(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,   8(t0); ld t2,   8(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  16(t0); ld t2,  16(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  24(t0); ld t2,  24(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  32(t0); ld t2,  32(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  40(t0); ld t2,  40(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  48(t0); ld t2,  48(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  56(t0); ld t2,  56(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  64(t0); ld t2,  64(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  72(t0); ld t2,  72(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  80(t0); ld t2,  80(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  88(t0); ld t2,  88(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  ld t1,  96(t0); ld t2,  96(s5); bne t1, t2, .Lvasm_no_match\n" ++
  "  # All 13 compares passed -> is_match = 1.\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvasm_ret\n" ++
  ".Lvasm_no_match:\n" ++
  "  li a0, 0                   # status 0 (no error; just mismatch)\n" ++
  ".Lvasm_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_verify_account_struct_matches`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..44 : address (20 bytes)
      bytes 44..148: expected_account_struct (104 bytes)
      bytes 148..148+H            : header_rlp
      bytes 148+H..148+H+WS       : witness.state
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_match (u64; 0 or 1) -/
def ziskVerifyAccountStructMatchesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  addi a2, t1, 24             # address ptr\n" ++
  "  addi a5, t1, 44             # expected_struct ptr\n" ++
  "  addi a0, t1, 148            # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # witness.state ptr\n" ++
  "  mv a4, t3                   # witness_state_len\n" ++
  "  li a6, 0xa0010008           # is_match out\n" ++
  "  jal ra, verify_account_struct_matches\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvasm_pdone\n" ++
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
  verifyAccountStructMatchesFunction ++ "\n" ++
  ".Lvasm_pdone:"

def ziskVerifyAccountStructMatchesDataSection : String :=
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
  "vasm_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "vasm_walked_struct:\n" ++
  "  .zero 104"


end EvmAsm.Codegen
