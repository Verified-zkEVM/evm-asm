/-
  EvmAsm.Codegen.Programs.CodeVerify

  Code verification primitives. Given a parent header, an
  address, and a candidate code blob, verify that the code's
  keccak matches the account's `code_hash` field. End-to-end
  deployment / code-attestation check.

  Sibling of `AccountVerify.lean` (full struct equality) and
  `StorageVerify.lean` (slot value equality).

  Currently hosts `verify_code_hash_matches`.

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

/-! ## verify_code_hash_matches

    End-to-end deployment-verification primitive: given a parent
    header, an address, and a candidate code blob, verify that
    `keccak256(code) == account.code_hash` for the account at
    that address in the state trie.

    Spec-side use case: a stateless-guest test harness wants to
    confirm a specific contract is deployed at an address --
    "address X holds the contract whose bytecode I'm providing".
    Rather than letting the caller compute the hash separately,
    this primitive hashes the code in-place and compares against
    the on-trie `code_hash` field.

    Spec-defining edge case: the empty-code case. For an EOA
    or an account explicitly with no code, `account.code_hash`
    equals `EMPTY_CODE_HASH = keccak("")`. If the caller passes
    `expected_code_len = 0`, the function hashes the empty byte
    string and gets exactly `EMPTY_CODE_HASH`. The compare then
    matches the EOA's stored `code_hash`. Caller gets a clean
    `is_match = 1` without having to special-case "no code".

    Distinct from:
      * PR `code_at_header_state_root` (#7146) -- LOCATES the
        code in `witness.codes` by hash; doesn't verify content.
      * PR `verify_account_struct_matches` (#7187) -- requires
        the caller to pre-compute all 4 fields including the
        code_hash; this primitive lets the caller pass the raw
        code bytes instead.

    Composes K201 `header_extract_state_root` + K28
    `account_at_address` + `zkvm_keccak256` over the
    caller-supplied code bytes + 4 u64 compares against the
    account.code_hash field of the walked struct.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : expected_code ptr
      a4 (input)  : expected_code_len (u64; 0 ⇒ empty code)
      a5 (input)  : witness.state ptr
      a6 (input)  : witness.state len
      a7 (input)  : u64 out (is_match)
      ra (input)  : return

      a0 (output) :
        0 = success (is_match holds 0 or 1)
        1 = account not in state trie (is_match = 0)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
-/
def verifyCodeHashMatchesFunction : String :=
  "verify_code_hash_matches:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # expected_code ptr\n" ++
  "  mv s4, a4                  # expected_code_len\n" ++
  "  mv s5, a5                  # witness.state ptr\n" ++
  "  mv s6, a6                  # witness.state len\n" ++
  "  mv s7, a7                  # is_match out ptr\n" ++
  "  sd zero, 0(s7)\n" ++
  "  # Step 1: header.state_root -> vchm_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, vchm_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lvchm_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lvchm_ret\n" ++
  ".Lvchm_step2:\n" ++
  "  # Step 2: account_at_address -> vchm_acct_struct.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, vchm_state_root\n" ++
  "  mv a3, s5\n" ++
  "  mv a4, s6\n" ++
  "  la a5, vchm_acct_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  bnez a0, .Lvchm_ret        # 1/2/3 propagate\n" ++
  "  # Step 3: keccak256(expected_code) -> vchm_computed_hash.\n" ++
  "  mv a0, s3\n" ++
  "  mv a1, s4\n" ++
  "  la a2, vchm_computed_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 4: compare vchm_computed_hash vs acct.code_hash (struct + 72).\n" ++
  "  la t0, vchm_computed_hash\n" ++
  "  la t1, vchm_acct_struct\n" ++
  "  ld t2,  0(t0); ld t3, 72(t1); bne t2, t3, .Lvchm_no_match\n" ++
  "  ld t2,  8(t0); ld t3, 80(t1); bne t2, t3, .Lvchm_no_match\n" ++
  "  ld t2, 16(t0); ld t3, 88(t1); bne t2, t3, .Lvchm_no_match\n" ++
  "  ld t2, 24(t0); ld t3, 96(t1); bne t2, t3, .Lvchm_no_match\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s7)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvchm_ret\n" ++
  ".Lvchm_no_match:\n" ++
  "  li a0, 0\n" ++
  ".Lvchm_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_verify_code_hash_matches`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : expected_code_len (u64 LE)
      bytes 32..52 : address (20 bytes)
      bytes 52..52+H            : header_rlp
      bytes 52+H..52+H+CODE     : expected_code
      bytes 52+H+CODE..         : witness.state
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_match (u64; 0 or 1) -/
def ziskVerifyCodeHashMatchesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  ld t4, 24(t1)               # expected_code_len\n" ++
  "  addi a2, t1, 32             # address ptr\n" ++
  "  addi a0, t1, 52             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a3, a0, t2              # expected_code ptr\n" ++
  "  mv a4, t4                   # expected_code_len\n" ++
  "  add a5, a3, t4              # witness.state ptr\n" ++
  "  mv a6, t3                   # witness.state len\n" ++
  "  li a7, 0xa0010008           # is_match out\n" ++
  "  jal ra, verify_code_hash_matches\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvchm_pdone\n" ++
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
  verifyCodeHashMatchesFunction ++ "\n" ++
  ".Lvchm_pdone:"

def ziskVerifyCodeHashMatchesDataSection : String :=
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
  "vchm_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "vchm_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "vchm_computed_hash:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
