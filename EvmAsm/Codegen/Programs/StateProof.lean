/-
  EvmAsm.Codegen.Programs.StateProof

  State-proof verification primitives that operate on a
  caller-supplied state_root (rather than one extracted from
  a header). Useful for light-client / bridge proofs where the
  state_root comes from a trusted source other than the
  parent header chain.

  Currently hosts `state_account_inclusion_proof_verify`,
  the state-side analog of
  `storage_slot_inclusion_proof_verify` in StorageProof.lean.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## state_account_inclusion_proof_verify

    Light-client account-inclusion-proof primitive: given a
    trusted `state_root` (from a bridge contract / light-client
    snapshot rather than walked from a parent header), an
    address, an expected 104-byte account struct, and a
    `witness.state` SSZ list section, verify that walking the
    MPT from `state_root` with key `keccak256(address)` yields
    an account that matches the struct byte-for-byte.

    Spec-defining edge case: account-absent semantics. The
    Ethereum state-trie spec treats a non-existent address as
    the canonical empty account
      (nonce=0, balance=0, storage_root=EMPTY_TRIE_ROOT,
       code_hash=EMPTY_CODE_HASH).
    So an `expected = empty_account` with the address missing
    from the trie is reported as `is_match = 1` (struct
    agrees with spec default) AND status 1 (account wasn't
    actually in the trie). Callers caring about presence use
    status; those caring only about struct equality (i.e.
    "does the chain agree with the caller's snapshot of this
    account?") use `is_match` directly.

    Distinct from `verify_account_struct_matches` (PR #7187):
      * #7187 takes `(header, address, ...)` and walks the
        state trie to derive a state_root from header[3].
      * THIS primitive takes a trusted `state_root` directly.
        Useful when the state_root comes from a non-header
        source (bridge state oracle, sync-committee snapshot,
        etc.) and the caller doesn't have / want to involve
        the parent header.

    Mirrors PR #7191 (`storage_slot_inclusion_proof_verify`)
    on the state-trie side. Together they form a light-client
    inclusion-proof pair for (account, slot) on any trusted
    (state_root, storage_root).

    Composes K28 `account_at_address` + a 104-byte struct
    compare against the caller's expected struct (or, on
    miss, against the canonical empty-account default).

    Calling convention (8 args):
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : expected_struct ptr
                    (104 bytes: nonce u64 LE | balance 32 BE |
                     storage_root 32 BE | code_hash 32 BE)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : u64 out ptr (is_match)
      ra (input)  : return

      a0 (output) :
        0 = success (is_match valid; struct walked from trie
            matches expected byte-for-byte)
        1 = account not in trie (is_match = expected==empty_default)
        2 = mpt_walk parse error
        3 = account RLP decode failure
-/
def stateAccountInclusionProofVerifyFunction : String :=
  "state_account_inclusion_proof_verify:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a2                  # expected_struct ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # is_match out\n" ++
  "  sd zero, 0(s5)\n" ++
  "  # Step 1: account_at_address with the trusted state_root.\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s0                  # state_root ptr\n" ++
  "  mv a3, s3                  # witness.state ptr\n" ++
  "  mv a4, s4                  # witness.state len\n" ++
  "  la a5, saip_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  mv s6, a0                  # save K28 status\n" ++
  "  beqz a0, .Lsaip_compare_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsaip_compare_absent\n" ++
  "  # status 2/3 propagate; is_match stays 0.\n" ++
  "  j .Lsaip_ret\n" ++
  ".Lsaip_compare_present:\n" ++
  "  # account_at_address returned the walked struct in\n" ++
  "  # saip_walked_struct. 104-byte compare against caller's\n" ++
  "  # expected struct in s2.\n" ++
  "  la t0, saip_walked_struct\n" ++
  "  ld t2,  0(t0); ld t3,  0(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2,  8(t0); ld t3,  8(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 16(t0); ld t3, 16(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 24(t0); ld t3, 24(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 32(t0); ld t3, 32(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 40(t0); ld t3, 40(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 48(t0); ld t3, 48(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 56(t0); ld t3, 56(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 64(t0); ld t3, 64(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 72(t0); ld t3, 72(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 80(t0); ld t3, 80(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 88(t0); ld t3, 88(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  ld t2, 96(t0); ld t3, 96(s2); bne t2, t3, .Lsaip_no_match\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lsaip_no_match:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsaip_ret\n" ++
  ".Lsaip_compare_absent:\n" ++
  "  # Account missing from trie. Spec default is\n" ++
  "  # (nonce=0, balance=0, storage_root=EMPTY_TRIE_ROOT,\n" ++
  "  #  code_hash=EMPTY_CODE_HASH).\n" ++
  "  # is_match = 1 iff caller's expected matches that struct.\n" ++
  "  # nonce (8 B) at struct + 0 must be 0.\n" ++
  "  ld t2,  0(s2); bnez t2, .Lsaip_absent_no\n" ++
  "  # balance (32 B) at struct + 8 must be zero.\n" ++
  "  ld t2,  8(s2); bnez t2, .Lsaip_absent_no\n" ++
  "  ld t2, 16(s2); bnez t2, .Lsaip_absent_no\n" ++
  "  ld t2, 24(s2); bnez t2, .Lsaip_absent_no\n" ++
  "  ld t2, 32(s2); bnez t2, .Lsaip_absent_no\n" ++
  "  # storage_root (32 B) at struct + 40 must equal EMPTY_TRIE_ROOT.\n" ++
  "  la t1, saip_empty_trie_root\n" ++
  "  ld t2, 40(s2); ld t3,  0(t1); bne t2, t3, .Lsaip_absent_no\n" ++
  "  ld t2, 48(s2); ld t3,  8(t1); bne t2, t3, .Lsaip_absent_no\n" ++
  "  ld t2, 56(s2); ld t3, 16(t1); bne t2, t3, .Lsaip_absent_no\n" ++
  "  ld t2, 64(s2); ld t3, 24(t1); bne t2, t3, .Lsaip_absent_no\n" ++
  "  # code_hash (32 B) at struct + 72 must equal EMPTY_CODE_HASH.\n" ++
  "  la t1, saip_empty_code_hash\n" ++
  "  ld t2, 72(s2); ld t3,  0(t1); bne t2, t3, .Lsaip_absent_no\n" ++
  "  ld t2, 80(s2); ld t3,  8(t1); bne t2, t3, .Lsaip_absent_no\n" ++
  "  ld t2, 88(s2); ld t3, 16(t1); bne t2, t3, .Lsaip_absent_no\n" ++
  "  ld t2, 96(s2); ld t3, 24(t1); bne t2, t3, .Lsaip_absent_no\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lsaip_absent_no:\n" ++
  "  li a0, 1\n" ++
  ".Lsaip_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_state_account_inclusion_proof_verify`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes   0.. 8 : (ziskemu metadata)
      bytes   8..16 : witness_state_len (u64 LE)
      bytes  16..48 : state_root (32 bytes)
      bytes  48..68 : address (20 bytes)
      bytes  68..172: expected_struct (104 bytes)
      bytes 172..   : witness.state section bytes
    Output layout:
      bytes  0.. 8 : status (0=ok / 1=absent / 2=parse fail / 3=acct RLP fail)
      bytes  8..16 : is_match (u64; 0 or 1) -/
def ziskStateAccountInclusionProofVerifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a4, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # address ptr\n" ++
  "  addi a2, a6, 68             # expected_struct ptr\n" ++
  "  addi a3, a6, 172            # witness.state ptr\n" ++
  "  li a5, 0xa0010008           # is_match out\n" ++
  "  jal ra, state_account_inclusion_proof_verify\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsaip_pdone\n" ++
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
  stateAccountInclusionProofVerifyFunction ++ "\n" ++
  ".Lsaip_pdone:"

def ziskStateAccountInclusionProofVerifyDataSection : String :=
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
  ".balign 32\n" ++
  "saip_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "saip_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 32\n" ++
  "saip_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
