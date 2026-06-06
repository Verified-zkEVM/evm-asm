/-
  EvmAsm.Codegen.Programs.AccountFields

  Account-field equality predicates + 32-byte field extractors
  carved out of `EvmAsm.Codegen.Programs` per the file-size hard
  cap. Hosts:

    K98   account_validate_code_hash
    K119  account_extract_storage_root
    K122  account_extract_code_hash
    K131  account_has_empty_code
    K133  account_storage_root_is_empty
    K134  account_storage_root_eq
    K135  account_code_hash_eq
    K136  account_nonce_eq
    K137  account_is_eip161_empty

  All compose K20 `rlp_list_nth_item` + K47 `rlp_list_count_items`
  from `RlpRead.lean` plus `zkvm_keccak256` from `HashBridge.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpListCountProbe
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## account_validate_code_hash -- PR-K98

    Verify that an account's `code_hash` field matches the
    keccak256 of a claimed bytecode buffer:

      account.code_hash == keccak256(claimed_code)

    Used during witness validation to assert that the contract
    code supplied by the host matches the `code_hash` committed in
    the account trie leaf. EOAs (no contract) carry the canonical
    empty-code hash `EMPTY_CODE_HASH`:

      keccak256(b'') ==
        0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    A `claimed_code_len == 0` reproduces this exact value.

    Composes:
      - PR-K20 `rlp_list_nth_item` — extract field 3 (code_hash)
      - PR-K3  `zkvm_keccak256`    — compute claimed digest

    Account RLP layout (4 items):
      field 0 : nonce        (uint)
      field 1 : balance      (uint)
      field 2 : storage_root (32-byte string)
      field 3 : code_hash    (32-byte string)

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : claimed_code ptr (may be unused when len == 0)
      a3 (input)  : claimed_code byte length
      ra (input)  : return
      a0 (output) :
        0 : match
        1 : account RLP parse failure (field 3 not 32 B)
        2 : mismatch — both succeeded, digests differ

    Uses 64 bytes of `.data` scratch (`avch_claimed` 32 B +
    `avch_computed` 32 B), plus K20's offset/length slots. -/
def accountValidateCodeHashFunction : String :=
  "account_validate_code_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s2, a0                   # account_ptr (stash)\n" ++
  "  mv s3, a1                   # account_len (stash)\n" ++
  "  mv s0, a2                   # claimed_code ptr\n" ++
  "  mv s1, a3                   # claimed_code_len\n" ++
  "  # Step 1: extract account.code_hash (field 3, 32 B).\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s3\n" ++
  "  li a2, 3\n" ++
  "  la a3, avch_offset\n" ++
  "  la a4, avch_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lavch_fail\n" ++
  "  la t0, avch_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lavch_fail\n" ++
  "  # Copy 32 bytes from (account_ptr + offset) to avch_claimed.\n" ++
  "  la t0, avch_offset; ld t4, 0(t0)\n" ++
  "  add t3, s2, t4\n" ++
  "  la t5, avch_claimed\n" ++
  "  ld t0,  0(t3); sd t0,  0(t5)\n" ++
  "  ld t0,  8(t3); sd t0,  8(t5)\n" ++
  "  ld t0, 16(t3); sd t0, 16(t5)\n" ++
  "  ld t0, 24(t3); sd t0, 24(t5)\n" ++
  "  # Step 2: keccak256(claimed_code) → avch_computed.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, avch_computed\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 3: compare avch_claimed vs avch_computed.\n" ++
  "  la t0, avch_claimed\n" ++
  "  la t1, avch_computed\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lavch_diff\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lavch_diff\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lavch_diff\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lavch_diff\n" ++
  "  li a0, 0\n" ++
  "  j .Lavch_ret\n" ++
  ".Lavch_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lavch_ret\n" ++
  ".Lavch_diff:\n" ++
  "  li a0, 2\n" ++
  ".Lavch_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_validate_code_hash`: probe BuildUnit. Reads
    (account_len, code_len, account_rlp ‖ code_bytes) from host
    input, writes 8-byte status to OUTPUT.
    Input layout:
      bytes  0.. 8 : account_rlp_len
      bytes  8..16 : code_len
      bytes 16..   : account_rlp ‖ code_bytes -/
def ziskAccountValidateCodeHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # account_rlp_len\n" ++
  "  ld a3, 16(a4)               # code_len\n" ++
  "  addi a0, a4, 24             # account_rlp_ptr\n" ++
  "  add a2, a0, a1              # code_ptr = account_ptr + account_len\n" ++
  "  jal ra, account_validate_code_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lavch_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountValidateCodeHashFunction ++ "\n" ++
  ".Lavch_pdone:"

def ziskAccountValidateCodeHashDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "avch_offset:\n" ++
  "  .zero 8\n" ++
  "avch_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "avch_claimed:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "avch_computed:\n" ++
  "  .zero 32"

def ziskAccountValidateCodeHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountValidateCodeHashPrologue
  dataAsm     := ziskAccountValidateCodeHashDataSection
}

/-! ## account_storage_root_eq -- PR-K134

    Generic equality check on an account's `storage_root` field:
    does it equal the 32-byte hash passed in as `expected`?

    Used during witness validation to assert that the storage trie
    pointed at by an account matches a claimed root (e.g., the
    pre-state root in a stateless witness's account proof). The
    narrower PR-K133 `account_storage_root_is_empty` is the
    specialization where the expected value is `EMPTY_TRIE_ROOT`.

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 2 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : expected_root ptr (32 bytes)      a3 (input)  : u64 out ptr (1 if equal, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 32 -/
def accountStorageRootEqFunction : String :=
  "account_storage_root_eq:\n" ++  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # expected_root ptr\n" ++
  "  mv s3, a3                   # u64 out ptr\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, asre_offset; la a4, asre_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lasre_parse_fail\n" ++
  "  la t0, asre_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lasre_size_fail\n" ++
  "  la t0, asre_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t5,  0(t3); ld t6,  0(s2); bne t5, t6, .Lasre_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(s2); bne t5, t6, .Lasre_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(s2); bne t5, t6, .Lasre_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(s2); bne t5, t6, .Lasre_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lasre_ret\n" ++
  ".Lasre_neq:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lasre_ret\n" ++
  ".Lasre_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lasre_ret\n" ++
  ".Lasre_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lasre_ret:\n" ++  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_storage_root_eq`: probe BuildUnit. Reads
    (account_len, expected_root[32], account_bytes), writes
    (status, is_equal) to OUTPUT (16 bytes total).
    Input layout:
      bytes  0.. 8 : account_len
      bytes  8..40 : expected_root (32 bytes)
      bytes 40..   : account_rlp -/
def ziskAccountStorageRootEqPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # account_rlp_len\n" ++
  "  addi a2, a4, 16             # expected_root ptr\n" ++
  "  addi a0, a4, 48             # account_rlp ptr\n" ++
  "  li a3, 0xa0010008           # is_equal out\n" ++
  "  jal ra, account_storage_root_eq\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lasre_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountStorageRootEqFunction ++ "\n" ++
  ".Lasre_pdone:"

def ziskAccountStorageRootEqDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "asre_offset:\n" ++
  "  .zero 8\n" ++
  "asre_length:\n" ++
  "  .zero 8"

def ziskAccountStorageRootEqProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountStorageRootEqPrologue
  dataAsm     := ziskAccountStorageRootEqDataSection
}



/-! ## account_code_hash_eq -- PR-K135

    Generic equality check on an account's `code_hash` field:
    does it equal the 32-byte hash passed in as `expected`?

    PR-K98 `account_validate_code_hash` *computes* the expected
    digest from a bytecode buffer; K135 simply *compares* against
    a caller-supplied digest. Use K98 when the bytecode is known
    locally and we need an integrity check; use K135 when the
    expected hash is already in hand (e.g., from a code-DB lookup
    in a stateless witness, where the bytecode lives elsewhere).

    Companion to PR-K131 `account_has_empty_code` (the specialised
    EMPTY_CODE_HASH variant) and PR-K134
    `account_storage_root_eq` (the storage-side equivalent).

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 3 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : expected_hash ptr (32 bytes)      a3 (input)  : u64 out ptr (1 if equal, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 3 missing
        2 : field 3 length != 32 -/
def accountCodeHashEqFunction : String :=
  "account_code_hash_eq:\n" ++  "  addi sp, sp, -48\n" ++  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # expected_hash ptr\n" ++
  "  mv s3, a3                   # u64 out ptr\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, ache_offset; la a4, ache_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lache_parse_fail\n" ++
  "  la t0, ache_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lache_size_fail\n" ++
  "  la t0, ache_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t5,  0(t3); ld t6,  0(s2); bne t5, t6, .Lache_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(s2); bne t5, t6, .Lache_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(s2); bne t5, t6, .Lache_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(s2); bne t5, t6, .Lache_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lache_ret\n" ++
  ".Lache_neq:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lache_ret\n" ++
  ".Lache_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lache_ret\n" ++
  ".Lache_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lache_ret:\n" ++  "  ld ra,  0(sp)\n" ++  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_code_hash_eq`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : account_rlp_len
      bytes  8..40 : expected_hash (32 bytes)
      bytes 40..   : account_rlp -/
def ziskAccountCodeHashEqPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # account_rlp_len\n" ++
  "  addi a2, a4, 16             # expected_hash ptr\n" ++
  "  addi a0, a4, 48             # account_rlp ptr\n" ++
  "  li a3, 0xa0010008           # is_equal out\n" ++
  "  jal ra, account_code_hash_eq\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lache_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountCodeHashEqFunction ++ "\n" ++
  ".Lache_pdone:"

def ziskAccountCodeHashEqDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ache_offset:\n" ++
  "  .zero 8\n" ++
  "ache_length:\n" ++
  "  .zero 8"

def ziskAccountCodeHashEqProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountCodeHashEqPrologue
  dataAsm     := ziskAccountCodeHashEqDataSection
}

/-! ## account_nonce_eq -- PR-K136

    Narrow equality predicate on an account's `nonce` field:
    does `RLP-decoded(account.nonce) == expected_nonce` ?

    Field 0 of `[nonce, balance, storage_root, code_hash]` is the
    RLP-canonical big-endian encoding of the account nonce. EOA
    nonces fit comfortably in u64 — the RLP-canonical encoding
    omits leading zeros, so the encoded length is in `0..8` for any
    realistic account. K27 `account_decode` already big-endian-
    decodes this field to a u64 as part of full-record extraction;
    K136 is the narrower accessor for callers that only need the
    equality check and don't want to allocate the 96-byte struct.

    Used by:
      * sender-validation in `check_transaction` (asserts
        `tx.nonce == account.nonce` before charging gas)
      * EIP-7702 authorization-list checks
        (`authorization.nonce == account.nonce`)
      * post-tx state validation (asserts the post-state account
        has the bumped nonce)

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 0 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : expected_nonce (u64, native)      a3 (input)  : u64 out ptr (1 if equal, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 0 missing / nonce > 8 bytes -/
def accountNonceEqFunction : String :=
  "account_nonce_eq:\n" ++  "  addi sp, sp, -48\n" ++  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # expected_nonce\n" ++
  "  mv s3, a3                   # is_equal out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, ane_offset; la a4, ane_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lane_fail\n" ++
  "  la t0, ane_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Lane_fail      # nonce > 8 bytes\n" ++
  "  la t0, ane_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0                    # u64 accumulator\n" ++
  ".Lane_loop:\n" ++
  "  beqz t1, .Lane_done\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lane_loop\n" ++
  ".Lane_done:\n" ++
  "  bne t2, s2, .Lane_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lane_ret\n" ++
  ".Lane_neq:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lane_ret\n" ++
  ".Lane_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lane_ret:\n" ++  "  ld ra,  0(sp)\n" ++  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_nonce_eq`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : account_rlp_len
      bytes  8..16 : expected_nonce (u64 LE)
      bytes 16..   : account_rlp -/
def ziskAccountNonceEqPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # account_rlp_len\n" ++
  "  ld a2, 16(a4)               # expected_nonce\n" ++
  "  addi a0, a4, 24             # account_rlp ptr\n" ++
  "  li a3, 0xa0010008           # is_equal out\n" ++
  "  jal ra, account_nonce_eq\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lane_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountNonceEqFunction ++ "\n" ++
  ".Lane_pdone:"

def ziskAccountNonceEqDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ane_offset:\n" ++
  "  .zero 8\n" ++
  "ane_length:\n" ++
  "  .zero 8"

def ziskAccountNonceEqProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountNonceEqPrologue
  dataAsm     := ziskAccountNonceEqDataSection}
/-! ## account_is_eip161_empty -- PR-K137

    EIP-161 empty-account predicate:

      is_empty ⇐ nonce == 0
              ∧  balance == 0
              ∧  code_hash == EMPTY_CODE_HASH

    where

      EMPTY_CODE_HASH =
        0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    Drives EIP-161 deletion: an account that satisfies this
    predicate after a transaction is removed from the state trie
    (i.e., its slot in the state MPT is deleted, not retained
    with a zero-balance leaf). Also used by:
      * SELFDESTRUCT recipient handling (re-creation of an empty
        beneficiary)
      * fee-charging paths in apply_body that decide whether the
        sender account becomes empty post-tx and so must be
        removed from the trie.

    Strict reading of the EIP-161 spec compares Uint values, not
    RLP-canonical byte patterns. We therefore accept both
    canonical empty-byte and non-canonical zero-byte encodings:
      * nonce: length ≤ 8, BE-decoded value == 0
      * balance: length ≤ 32, all bytes == 0 (cheaper than full
        32-byte decode + compare)
      * code_hash: length == 32, bytes match EMPTY_CODE_HASH

    Companions:
      - PR-K131 `account_has_empty_code` (only the code_hash side)
      - PR-K133 `account_storage_root_is_empty`
      - PR-K136 `account_nonce_eq` (specialised to expected==0
        when caller knows the strict predicate)

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 0/1/3 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out ptr (1 if empty, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / nonce > 8 bytes / balance > 32 bytes
        2 : code_hash field length != 32 -/
def accountIsEip161EmptyFunction : String :=
  "account_is_eip161_empty:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # is_empty out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # ---- Field 0: nonce ---- BE-decode and check == 0\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, aie_offset; la a4, aie_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laie_fail\n" ++
  "  la t0, aie_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bgtu t1, t2, .Laie_fail      # nonce > 8 bytes\n" ++
  "  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  li t2, 0\n" ++
  ".Laie_nloop:\n" ++
  "  beqz t1, .Laie_ndone\n" ++
  "  slli t2, t2, 8\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  or t2, t2, t4\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Laie_nloop\n" ++
  ".Laie_ndone:\n" ++
  "  bnez t2, .Laie_not_empty     # nonce != 0\n" ++
  "  # ---- Field 1: balance ---- check all bytes == 0\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, aie_offset; la a4, aie_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laie_fail\n" ++
  "  la t0, aie_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Laie_fail      # balance > 32 bytes\n" ++
  "  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  ".Laie_bloop:\n" ++
  "  beqz t1, .Laie_bdone\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  bnez t4, .Laie_not_empty     # balance non-zero byte\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Laie_bloop\n" ++
  ".Laie_bdone:\n" ++
  "  # ---- Field 3: code_hash ---- length == 32 and bytes match\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, aie_offset; la a4, aie_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laie_fail\n" ++
  "  la t0, aie_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laie_sizefail\n" ++
  "  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t6, aie_empty_code_hash\n" ++
  "  ld t5,  0(t3); ld t4,  0(t6); bne t5, t4, .Laie_not_empty\n" ++
  "  ld t5,  8(t3); ld t4,  8(t6); bne t5, t4, .Laie_not_empty\n" ++
  "  ld t5, 16(t3); ld t4, 16(t6); bne t5, t4, .Laie_not_empty\n" ++
  "  ld t5, 24(t3); ld t4, 24(t6); bne t5, t4, .Laie_not_empty\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laie_ret\n" ++
  ".Laie_not_empty:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laie_ret\n" ++
  ".Laie_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Laie_ret\n" ++
  ".Laie_sizefail:\n" ++
  "  li a0, 2\n" ++
  ".Laie_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- `zisk_account_is_eip161_empty`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : account_rlp_len
      bytes  8..   : account_rlp -/
def ziskAccountIsEip161EmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # account_rlp_len\n" ++
  "  addi a0, a4, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_empty out\n" ++
  "  jal ra, account_is_eip161_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laie_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountIsEip161EmptyFunction ++ "\n" ++
  ".Laie_pdone:"

def ziskAccountIsEip161EmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "aie_offset:\n" ++
  "  .zero 8\n" ++
  "aie_length:\n" ++
  "  .zero 8\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70"

def ziskAccountIsEip161EmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountIsEip161EmptyPrologue
  dataAsm     := ziskAccountIsEip161EmptyDataSection
}

/-! ## account_extract_storage_root -- PR-K119

    Extract the 32-byte `storage_root` field (RLP field 2) from a
    fully RLP-encoded Ethereum account:

      account = [nonce, balance, storage_root, code_hash]

    The storage_root is the MPT root of this account's per-account
    storage trie (keccak256 of the empty trie's RLP encoding,
    a.k.a. `EMPTY_TRIE_ROOT`, for EOAs and unused contracts):

      EMPTY_TRIE_ROOT =
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421

    Direct input to per-account storage trie walks
    (`mpt_lookup_by_key` for SLOAD) and to state-root recomputation
    after SSTORE writes.

    K27 `account_decode` already extracts the full account record;
    K119 is the narrower accessor for callers that only need the
    storage root and don't want to allocate the 96-byte struct.

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 2 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 32

    Output zeroed on failure. Uses two 8-byte `.data` scratch slots
    (`aesr_offset`, `aesr_length`). -/
/-! ## account_extract_code_hash -- PR-K122

    Extract the 32-byte `code_hash` field (RLP field 3) from a
    fully RLP-encoded Ethereum account:

      account = [nonce, balance, storage_root, code_hash]

    The storage_root is the MPT root of this account's per-account
    storage trie (keccak256 of the empty trie's RLP encoding,
    a.k.a. `EMPTY_TRIE_ROOT`, for EOAs and unused contracts):

      EMPTY_TRIE_ROOT =
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421

    Direct input to per-account storage trie walks
    (`mpt_lookup_by_key` for SLOAD) and to state-root recomputation
    after SSTORE writes.

    K27 `account_decode` already extracts the full account record;
    K119 is the narrower accessor for callers that only need the
    storage root and don't want to allocate the 96-byte struct.

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 2 bounds
    The code_hash is the keccak256 of this account's bytecode.
    For EOAs and accounts that have never been touched as
    contracts, code_hash equals the canonical empty-code hash:

      EMPTY_CODE_HASH =
        0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    Direct input to:
    - EOA detection (compare against EMPTY_CODE_HASH)
    - EXTCODEHASH opcode evaluation
    - Per-account contract-code lookup (use code_hash as DB key)

    K98 `account_validate_code_hash` *verifies* this field against
    a claimed bytecode buffer (computing the keccak256 inline);
    K122 simply *returns* it. Use K98 when the bytecode is known
    and we want a yes/no integrity check; use K122 when we want to
    keep the hash for later use (e.g. as a code-DB index key).

    Completes the per-field accessor set for accounts (alongside
    PR-K119 storage_root, K120 balance, K121 nonce).

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 3 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 32

    Output zeroed on failure. Uses two 8-byte `.data` scratch slots
    (`aesr_offset`, `aesr_length`). -/
def accountExtractStorageRootFunction : String :=
  "account_extract_storage_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_rlp ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # 32B output ptr\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  # Extract field 2 (storage_root).\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, aesr_offset; la a4, aesr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laesr_parse_fail\n" ++
  "  la t0, aesr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laesr_size_fail\n" ++
  "  la t0, aesr_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laesr_ret\n" ++
  ".Laesr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Laesr_ret\n" ++
  ".Laesr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Laesr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def accountExtractCodeHashFunction : String :=
  "account_extract_code_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_rlp ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # 32B output ptr\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  # Extract field 2 (storage_root).\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, aesr_offset; la a4, aesr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laesr_parse_fail\n" ++
  "  la t0, aesr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laesr_size_fail\n" ++
  "  la t0, aesr_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  # Extract field 3 (code_hash).\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, aech_offset; la a4, aech_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laech_parse_fail\n" ++
  "  la t0, aech_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Laech_size_fail\n" ++
  "  la t0, aech_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Laesr_ret\n" ++
  ".Laesr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Laesr_ret\n" ++
  ".Laesr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Laesr_ret:\n" ++
  "  j .Laech_ret\n" ++
  ".Laech_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Laech_ret\n" ++
  ".Laech_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Laech_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_account_extract_storage_root`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, 32-byte
    storage_root) to OUTPUT (40 bytes total). -/
def ziskAccountExtractStorageRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # 32B output\n" ++
  "  jal ra, account_extract_storage_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laesr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountExtractStorageRootFunction ++ "\n" ++
  ".Laesr_pdone:"

def ziskAccountExtractStorageRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "aesr_offset:\n" ++
  "  .zero 8\n" ++
  "aesr_length:\n" ++
  "  .zero 8"

def ziskAccountExtractStorageRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExtractStorageRootPrologue
  dataAsm     := ziskAccountExtractStorageRootDataSection
}

/-- `zisk_account_extract_code_hash`: probe BuildUnit. Reads
    (account_len, account_bytes), writes (status, 32-byte
    code_hash) to OUTPUT (40 bytes). -/
def ziskAccountExtractCodeHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # 32B output\n" ++
  "  jal ra, account_extract_code_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Laech_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountExtractCodeHashFunction ++ "\n" ++
  ".Laech_pdone:"

def ziskAccountExtractCodeHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "aech_offset:\n" ++
  "  .zero 8\n" ++
  "aech_length:\n" ++
  "  .zero 8"

def ziskAccountExtractCodeHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountExtractCodeHashPrologue
  dataAsm     := ziskAccountExtractCodeHashDataSection
}

/-! ## account_has_empty_code -- PR-K131

    Predicate: does this account's `code_hash` field equal
    `EMPTY_CODE_HASH = keccak256(b'')`?

      EMPTY_CODE_HASH =
        0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    A `true` result means the account has no associated bytecode
    — i.e., it is an EOA (or an unfilled contract slot). Distinct
    from PR-K123 `account_is_empty`, which additionally requires
    `nonce == 0` and `balance == 0` per EIP-161.

    Used by:
    - CALL / DELEGATECALL / STATICCALL paths to detect EOA targets
      (no code → no execution, refund or fall-through)
    - EXTCODECOPY / EXTCODESIZE fast paths
    - state-tracker bookkeeping (touch behaviour differs for
      empty-code accounts)

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 3 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out ptr (1 if EOA, 0 if contract)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 3 missing
        2 : field 3 length != 32 -/
def accountHasEmptyCodeFunction : String :=
  "account_has_empty_code:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # u64 out ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, ahec_offset; la a4, ahec_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lahec_parse_fail\n" ++
  "  la t0, ahec_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lahec_size_fail\n" ++
  "  la t0, ahec_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, ahec_empty_code_hash\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lahec_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lahec_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lahec_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lahec_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lahec_ret\n" ++
  ".Lahec_neq:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lahec_ret\n" ++
  ".Lahec_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lahec_ret\n" ++
  ".Lahec_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lahec_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"
/-! ## rlp_list_count_items -- PR-K47
    The function body now lives in `EvmAsm/Codegen/Programs/RlpRead.lean`
    (see PR #5900). Only the zisk probe BuildUnit remains here. -/

/-- `zisk_account_has_empty_code`: probe BuildUnit. -/
def ziskAccountHasEmptyCodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_eoa out\n" ++
  "  jal ra, account_has_empty_code\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lahec_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountHasEmptyCodeFunction ++ "\n" ++
  ".Lahec_pdone:"

def ziskAccountHasEmptyCodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ahec_offset:\n" ++
  "  .zero 8\n" ++
  "ahec_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ahec_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskAccountHasEmptyCodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountHasEmptyCodePrologue
  dataAsm     := ziskAccountHasEmptyCodeDataSection
}

/-! ## account_storage_root_is_empty -- PR-K133

    Predicate: does this account's `storage_root` field equal
    `EMPTY_TRIE_ROOT = keccak256(rlp.encode(b''))`?

      EMPTY_TRIE_ROOT =
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421

    A `true` result means the account has no storage entries
    (its storage trie is empty). EOAs and untouched contracts
    carry this canonical empty value.

    Companion to PR-K131 `account_has_empty_code` (the code-side
    EOA predicate) and PR-K123 `account_is_empty` (the EIP-161
    nonce+balance+code variant — but explicitly *not* requiring
    empty storage).

    Composes:
      - PR-K20 `rlp_list_nth_item` — field 2 bounds

    Calling convention:
      a0 (input)  : account_rlp ptr
      a1 (input)  : account_rlp byte length
      a2 (input)  : u64 out ptr (1 if storage_root == EMPTY_TRIE_ROOT,
                                 0 otherwise)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 32 -/
def accountStorageRootIsEmptyFunction : String :=
  "account_storage_root_is_empty:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # account_ptr\n" ++
  "  mv s1, a1                   # account_len\n" ++
  "  mv s2, a2                   # u64 out ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, asrie_offset; la a4, asrie_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lasrie_parse_fail\n" ++
  "  la t0, asrie_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lasrie_size_fail\n" ++
  "  la t0, asrie_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, asrie_empty_trie_root\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lasrie_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lasrie_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lasrie_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lasrie_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lasrie_ret\n" ++
  ".Lasrie_neq:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lasrie_ret\n" ++
  ".Lasrie_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lasrie_ret\n" ++
  ".Lasrie_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lasrie_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_account_storage_root_is_empty`: probe BuildUnit. -/
def ziskAccountStorageRootIsEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # account_rlp_len\n" ++
  "  addi a0, a3, 16             # account_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_empty out\n" ++
  "  jal ra, account_storage_root_is_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lasrie_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  accountStorageRootIsEmptyFunction ++ "\n" ++
  ".Lasrie_pdone:"

def ziskAccountStorageRootIsEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "asrie_offset:\n" ++
  "  .zero 8\n" ++
  "asrie_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "asrie_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"

def ziskAccountStorageRootIsEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountStorageRootIsEmptyPrologue
  dataAsm     := ziskAccountStorageRootIsEmptyDataSection
}

end EvmAsm.Codegen
