/-
  EvmAsm.Codegen.Programs.TxSigningHash

  Transaction signing-hash family carved out of
  `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap. Hosts:

    K144  rlp_list_truncate_to_n_fields
    K145  tx_signing_hash
    K146  tx_signing_hash_legacy_eip155
    K147  eip7702_authorization_signing_hash

  K144 is the RLP list truncator used by the signing-hash
  variants to strip trailing fields before keccak. The signing
  hashes are inputs to ECDSA recovery for sender-recovery.

  Compose K20 `rlp_list_nth_item` + K28 `rlp_encode_list_prefix`
  + K30 `rlp_encode_uint_be` (RlpRead.lean) + `zkvm_keccak256`
  (HashBridge.lean).

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## rlp_list_truncate_to_n_fields -- PR-K144

    Given an RLP-encoded list and a count `n`, write a freshly
    re-encoded RLP list containing only the first `n` fields of
    the input. The child encodings are reused verbatim (RLP is
    context-free at child level); only the outer list prefix is
    re-emitted to reflect the smaller payload.

    Direct building block for transaction signing-hash computation:

      * Legacy pre-EIP-155 signing hash = `keccak256(rlp([nonce,
        gas_price, gas_limit, to, value, data]))` — i.e., the
        legacy tx's 9-field RLP truncated to its first 6 fields
        (dropping `v, r, s`).
      * EIP-1559 signing hash body = first 9 fields of the
        12-field inner list (dropping `y_parity, r, s`).
      * EIP-2930 signing hash body = first 8 fields of 11.
      * EIP-4844 signing hash body = first 11 fields of 14.
      * EIP-7702 signing hash body = first 10 fields of 13.
      * EIP-7702 authorization signing hash body = first 3 fields
        of the 6-field authorization tuple (dropping
        `y_parity, r, s`).

    Composes:
      - PR-K20 `rlp_list_nth_item`     — locate first / last fields
      - PR-K129 `rlp_encode_list_prefix` — new outer prefix

    Calling convention:
      a0 (input)  : input_rlp ptr (encoded list)
      a1 (input)  : input_rlp byte length
      a2 (input)  : n_fields (u64) — keep first n
      a3 (input)  : output buffer ptr (caller supplies
                    >= 9 + len(retained payload) bytes)
      a4 (input)  : u64 out_length ptr (receives total written
                    bytes, prefix + payload)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / input not a list
        2 : input has fewer than `n` fields
    Edge cases:
      * n == 0 → output is `0xc0` (empty list, 1 byte). -/
def rlpListTruncateToNFieldsFunction : String :=
  "rlp_list_truncate_to_n_fields:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # input_rlp ptr\n" ++
  "  mv s1, a1                   # input_rlp len\n" ++
  "  mv s2, a2                   # n_fields\n" ++
  "  mv s3, a3                   # output buffer ptr\n" ++
  "  mv s4, a4                   # out_length ptr\n" ++
  "  beqz s2, .Lrltn_empty       # n == 0 → emit `0xc0`\n" ++
  "  # ---- Parse the outer list prefix to get payload_start ----\n" ++
  "  # NOTE: we cannot use `rlp_list_nth_item(input, 0)` for this:\n" ++
  "  # K20 returns the *content* offset for byte-string items, which\n" ++
  "  # drops the field's RLP prefix byte. The truncation needs the\n" ++
  "  # *item* offset = start of the outer payload = byte after the\n" ++
  "  # outer list prefix.\n" ++
  "  beqz s1, .Lrltn_parse_fail\n" ++
  "  lbu t0, 0(s0)\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lrltn_parse_fail   # not an RLP list\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lrltn_short_list\n" ++
  "  # Long list: payload_start = 1 + (t0 - 0xf7)\n" ++
  "  addi s5, t0, -0xf7\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lrltn_have_start\n" ++
  ".Lrltn_short_list:\n" ++
  "  li s5, 1                          # payload_start = 1\n" ++
  ".Lrltn_have_start:\n" ++
  "  # ---- Locate field (n-1) to get end-of-payload ----\n" ++
  "  addi t0, s2, -1\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, t0\n" ++
  "  la a3, rltn_offset_hi; la a4, rltn_length_hi\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lrltn_too_few\n" ++
  "  la t0, rltn_offset_hi; ld t1, 0(t0)\n" ++
  "  la t0, rltn_length_hi; ld t2, 0(t0)\n" ++
  "  add t1, t1, t2                              # end-of-payload (after item n-1)\n" ++
  "  sub s6, t1, s5                              # new_payload_len\n" ++
  "  # ---- Write new outer list prefix ----\n" ++
  "  mv a0, s6; mv a1, s3\n" ++
  "  la a2, rltn_prefix_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, rltn_prefix_len; ld t1, 0(t0)        # prefix_len\n" ++
  "  # ---- Copy payload bytes ----\n" ++
  "  add t2, s3, t1                              # dst = output + prefix\n" ++
  "  add t3, s0, s5                              # src = input + payload_start\n" ++
  "  mv t4, s6                                   # remaining bytes\n" ++
  ".Lrltn_cploop:\n" ++
  "  beqz t4, .Lrltn_cpdone\n" ++
  "  lbu t5, 0(t3)\n" ++
  "  sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lrltn_cploop\n" ++
  ".Lrltn_cpdone:\n" ++
  "  add t1, t1, s6                              # out_len = prefix + payload\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lrltn_ret\n" ++
  ".Lrltn_empty:\n" ++
  "  li t0, 0xc0\n" ++
  "  sb t0, 0(s3)\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lrltn_ret\n" ++
  ".Lrltn_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lrltn_ret\n" ++
  ".Lrltn_too_few:\n" ++
  "  li a0, 2\n" ++
  ".Lrltn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_rlp_list_truncate_to_n_fields`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : input_rlp_len
      bytes  8..16 : n_fields (u64 LE)
      bytes 16..   : input_rlp
    Output layout (1 KiB ought to be plenty for fixtures):
      bytes  0.. 8 : status
      bytes  8..16 : out_length
      bytes 16..   : written RLP bytes (truncated to 256-byte
                     ziskemu cap; the fixture script reconstructs
                     the slice from the input and the expected
                     prefix). -/
def ziskRlpListTruncateToNFieldsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # input_rlp_len\n" ++
  "  ld a2, 16(a5)               # n_fields\n" ++
  "  addi a0, a5, 24             # input_rlp ptr\n" ++
  "  li a3, 0xa0010010           # output buffer\n" ++
  "  li a4, 0xa0010008           # out_length\n" ++
  "  jal ra, rlp_list_truncate_to_n_fields\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lrltn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  ".Lrltn_pdone:"

def ziskRlpListTruncateToNFieldsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rltn_offset_lo:\n" ++
  "  .zero 8\n" ++
  "rltn_length_lo:\n" ++
  "  .zero 8\n" ++
  "rltn_offset_hi:\n" ++
  "  .zero 8\n" ++
  "rltn_length_hi:\n" ++
  "  .zero 8\n" ++
  "rltn_prefix_len:\n" ++
  "  .zero 8"

def ziskRlpListTruncateToNFieldsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpListTruncateToNFieldsPrologue
  dataAsm     := ziskRlpListTruncateToNFieldsDataSection
}

/-! ## tx_signing_hash -- PR-K145

    Unified transaction signing-hash builder. Given a tx inner
    RLP, the number of fields to retain (everything before
    `y_parity, r, s`), and an optional type-prefix byte, compute

      keccak256( [type_prefix?] || rlp([first n fields]) )

    in a single call. This is the digest fed to
    `zkvm_secp256k1_ecrecover` together with the extracted
    `(y_parity, r, s)` to recover the tx sender's pubkey.

    Per-tx-type usage:

      type   | type_prefix | n  | description
      -------|-------------|----|-----------------------------
      legacy | 0           | 6  | pre-EIP-155 signing hash
      EIP-2930 | 0x01      | 8  | type-1 signing hash
      EIP-1559 | 0x02      | 9  | type-2 signing hash
      EIP-4844 | 0x03      | 11 | type-3 signing hash
      EIP-7702 | 0x04      | 10 | type-4 signing hash

    Legacy EIP-155 (chain_id-bearing) signing hash is **not**
    covered by this helper: it appends `(chain_id, 0, 0)` after
    the first 6 fields, which requires building a new 9-field
    list rather than just truncating. That variant lands as
    `tx_signing_hash_legacy_eip155` in a follow-up PR.

    EIP-7702 authorization signing hash is similarly out of scope
    (it computes over `MAGIC=0x05 || rlp([chain_id, address,
    nonce])` where the body is a 3-field list freshly built from
    the authorization tuple, not a truncation); follow-up.

    Composes:
      - PR-K144 `rlp_list_truncate_to_n_fields`  -- truncation
      - `zkvm_keccak256` (HashBridge)            -- hashing

    Calling convention:
      a0 (input)  : tx_inner_rlp ptr (caller has stripped any
                    leading type byte)
      a1 (input)  : tx_inner_rlp byte length
      a2 (input)  : n_fields (u64) -- fields to keep
      a3 (input)  : type_prefix (u8 in low bits; 0 = no prefix)
      a4 (input)  : 32-byte output hash ptr
      ra (input)  : return
      a0 (output) :
        0 : success -- hash written
        1 : truncation parse failure / fewer than n fields

    Uses two `.data` scratch buffers:
      * `tsh_buf` (128 KiB) -- holds `[optional type byte] ||
        rlp([first n fields])` immediately before the keccak
        call.
      * `zk3_state` (200 bytes) -- reused from the existing
        keccak bridge. -/
def txSigningHashFunction : String :=
  "tx_signing_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # inner_rlp ptr\n" ++
  "  mv s1, a1                   # inner_rlp len\n" ++
  "  mv s2, a2                   # n_fields\n" ++
  "  mv s3, a3                   # type_prefix (low byte)\n" ++
  "  mv s4, a4                   # output hash ptr (32 B)\n" ++
  "  # ---- Write optional type prefix at tsh_buf[0] ----\n" ++
  "  la t0, tsh_buf\n" ++
  "  beqz s3, .Ltsh_after_prefix\n" ++
  "  sb s3, 0(t0)\n" ++
  ".Ltsh_after_prefix:\n" ++
  "  # ---- Truncate inner_rlp into tsh_buf[1..] ----\n" ++
  "  # Capacity gate: the truncated payload is <= inner_rlp len, so gate on\n" ++
  "  # s1 against the 128 KiB staging buffer (overflow would smash the\n" ++
  "  # adjacent length cells -- the t155_prefix_len runaway, bead .11.3).\n" ++
  "  li t0, 131056\n" ++
  "  bgtu s1, t0, .Ltsh_fail\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  la a3, tsh_buf; addi a3, a3, 1\n" ++
  "  la a4, tsh_trunc_len\n" ++
  "  jal ra, rlp_list_truncate_to_n_fields\n" ++
  "  bnez a0, .Ltsh_fail\n" ++
  "  la t0, tsh_trunc_len; ld t1, 0(t0)        # trunc_len\n" ++
  "  # ---- Compute (hash_data_ptr, hash_data_len) ----\n" ++
  "  beqz s3, .Ltsh_no_prefix\n" ++
  "  la a0, tsh_buf                            # start at byte 0 (prefix)\n" ++
  "  addi a1, t1, 1                            # length = trunc_len + 1\n" ++
  "  j .Ltsh_do_hash\n" ++
  ".Ltsh_no_prefix:\n" ++
  "  la a0, tsh_buf; addi a0, a0, 1            # start at byte 1\n" ++
  "  mv a1, t1                                 # length = trunc_len\n" ++
  ".Ltsh_do_hash:\n" ++
  "  mv a2, s4                                 # output ptr\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Ltsh_ret\n" ++
  ".Ltsh_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltsh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_signing_hash`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : inner_rlp_len
      bytes  8..16 : n_fields (u64 LE)
      bytes 16..24 : type_prefix (u64 LE; low byte is the byte;
                     0 = no prefix)
      bytes 24..   : inner_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : 32-byte signing hash -/
def ziskTxSigningHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # inner_rlp_len\n" ++
  "  ld a2, 16(a5)               # n_fields\n" ++
  "  ld a3, 24(a5)               # type_prefix (u64; low byte)\n" ++
  "  addi a0, a5, 32             # inner_rlp ptr\n" ++
  "  li a4, 0xa0010008           # output hash ptr (32 B)\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltsh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  ".Ltsh_pdone:"

def ziskTxSigningHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "tsh_buf:\n" ++
  "  .zero 131072\n" ++
  "tsh_trunc_len:\n" ++
  "  .zero 8\n" ++
  -- Scratch labels owned by `rlp_list_truncate_to_n_fields` (K144);
  -- the truncate function references them at fixed offsets through
  -- `la`, so we re-declare them in this probe's `.data` section.
  "rltn_offset_lo:\n" ++
  "  .zero 8\n" ++
  "rltn_length_lo:\n" ++
  "  .zero 8\n" ++
  "rltn_offset_hi:\n" ++
  "  .zero 8\n" ++
  "rltn_length_hi:\n" ++
  "  .zero 8\n" ++
  "rltn_prefix_len:\n" ++
  "  .zero 8"

def ziskTxSigningHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxSigningHashPrologue
  dataAsm     := ziskTxSigningHashDataSection
}

/-! ## tx_signing_hash_legacy_eip155 -- PR-K146

    Legacy EIP-155 signing hash. Different from the typed-tx and
    pre-EIP-155 cases (PR-K145 `tx_signing_hash`) because the
    EIP-155 spec appends `(chain_id, 0, 0)` after the first six
    fields rather than just truncating:

      signing_hash = keccak256(rlp([nonce, gas_price, gas_limit,
                                    to, value, data,
                                    chain_id, 0, 0]))

    So we splice rather than truncate:

      new_payload = [old payload bytes of fields 0..5]
                 || [RLP-canonical-encoded chain_id]
                 || 0x80
                 || 0x80

      signing_hash = keccak256(new_outer_prefix || new_payload)

    Used by every post-Spurious-Dragon mainnet legacy tx; the
    pre-EIP-155 variant (`v ∈ {27, 28}`) is rare on modern
    chains. PR-K37 `derive_chain_id_from_v` distinguishes the
    two — caller routes here when `is_eip155 == 1`.

    Composes:
      - PR-K20 `rlp_list_nth_item`     -- locate fields 0 / 5
      - PR-K30 `rlp_encode_uint_be`    -- chain_id encoding
      - PR-K129 `rlp_encode_list_prefix` -- new outer prefix
      - `zkvm_keccak256` (HashBridge)  -- hashing

    Calling convention:
      a0 (input)  : legacy_tx_rlp ptr (9-field RLP with v,r,s)
      a1 (input)  : legacy_tx_rlp byte length
      a2 (input)  : chain_id (u64)
      a3 (input)  : 32-byte output hash ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fewer than 6 fields -/
def txSigningHashLegacyEip155Function : String :=
  "tx_signing_hash_legacy_eip155:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # tx_rlp ptr\n" ++
  "  mv s1, a1                   # tx_rlp len\n" ++
  "  mv s2, a2                   # chain_id\n" ++
  "  mv s3, a3                   # output hash ptr\n" ++
  "  # ---- Parse outer list prefix to get payload_start ----\n" ++
  "  # NOTE: K20 returns content offsets, not item-start offsets.\n" ++
  "  # We need the byte right after the outer list prefix.\n" ++
  "  beqz s1, .Lt155_fail\n" ++
  "  lbu t0, 0(s0)\n" ++
  "  li t1, 0xc0\n" ++
  "  bltu t0, t1, .Lt155_fail\n" ++
  "  li t1, 0xf8\n" ++
  "  bltu t0, t1, .Lt155_short_list\n" ++
  "  addi s4, t0, -0xf7\n" ++
  "  addi s4, s4, 1                              # payload_start\n" ++
  "  j .Lt155_have_start\n" ++
  ".Lt155_short_list:\n" ++
  "  li s4, 1\n" ++
  ".Lt155_have_start:\n" ++
  "  # ---- Locate field 5 to get end-of-body ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, t155_offset_hi; la a4, t155_length_hi\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt155_fail\n" ++
  "  la t0, t155_offset_hi; ld t1, 0(t0)\n" ++
  "  la t0, t155_length_hi; ld t2, 0(t0)\n" ++
  "  add t1, t1, t2                              # end-of-body\n" ++
  "  sub s5, t1, s4                              # body_len\n" ++
  "  # ---- Encode chain_id as canonical RLP into t155_chain_be ----\n" ++
  "  # Write chain_id as 8 BE bytes to t155_chain_be\n" ++
  "  la t0, t155_chain_be\n" ++
  "  li t1, 7\n" ++
  ".Lt155_chain_be_loop:\n" ++
  "  bltz t1, .Lt155_chain_be_done\n" ++
  "  slli t2, t1, 3\n" ++
  "  srl t3, s2, t2\n" ++
  "  andi t3, t3, 0xff\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt155_chain_be_loop\n" ++
  ".Lt155_chain_be_done:\n" ++
  "  la a0, t155_chain_be; li a1, 8\n" ++
  "  la a2, t155_chain_enc\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  mv t3, a0                                   # chain_id_enc_len\n" ++
  "  # tail_len = chain_id_enc_len + 2  (two 0x80 bytes for 0, 0)\n" ++
  "  addi t3, t3, 2\n" ++
  "  # new_payload_len = body_len + tail_len. Held in a callee-saved register\n" ++
  "  # (s6) because rlp_encode_list_prefix's long-list path (payload >= 56)\n" ++
  "  # clobbers t4; new_payload_len is reused below for the chain_id length and\n" ++
  "  # the final keccak length, so a t-reg would corrupt both for large txs.\n" ++
  "  add s6, s5, t3                              # new_payload_len\n" ++
  "  # ---- Write new outer list prefix into t155_buf[0..] ----\n" ++
  "  # .63.1.6.2.8 (e1s5z): NO 128 KiB capacity cap. The 6-field body is streamed\n" ++
  "  # IN PLACE from the input region via zkvm_keccak256_segments, so a legacy\n" ++
  "  # EIP-155 tx with arbitrarily large calldata (up to the block-gas bound,\n" ++
  "  # ~20 MB at 200M gas) hashes without a staging-buffer overflow. The old gate\n" ++
  "  # fail-closed at 128 KiB -> false-reject (bead .11.3); streaming is sound for\n" ++
  "  # any size with O(1) extra memory and no input mutation.\n" ++
  "  mv a0, s6; la a1, t155_buf\n" ++
  "  la a2, t155_prefix_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  # ---- Build suffix [chain_id_enc || 0x80 || 0x80] at t155_buf+64 ----\n" ++
  "  sub t2, s6, s5; addi t2, t2, -2             # chain_id_enc_len = new_payload - body - 2\n" ++
  "  la t0, t155_buf; addi t0, t0, 64            # suffix dst (small; prefix lives at +0)\n" ++
  "  la t1, t155_chain_enc\n" ++
  "  mv t3, t2\n" ++
  ".Lt155_suffix_cp:\n" ++
  "  beqz t3, .Lt155_suffix_tail\n" ++
  "  lbu t6, 0(t1); sb t6, 0(t0); addi t0, t0, 1; addi t1, t1, 1; addi t3, t3, -1; j .Lt155_suffix_cp\n" ++
  ".Lt155_suffix_tail:\n" ++
  "  li t6, 0x80; sb t6, 0(t0); sb t6, 1(t0)     # (0, 0) tail\n" ++
  "  addi t2, t2, 2                              # suffix_len = chain_id_enc_len + 2\n" ++
  "  # ---- Build 3-segment descriptor at t155_buf+128: prefix || body(in place) || suffix ----\n" ++
  "  la t4, t155_prefix_len; ld t4, 0(t4)        # prefix_len\n" ++
  "  la t5, t155_buf; addi t5, t5, 128           # &segs[0]\n" ++
  "  la t6, t155_buf; sd t6, 0(t5); sd t4, 8(t5)            # seg0 = (prefix, prefix_len)\n" ++
  "  add t6, s0, s4; sd t6, 16(t5); sd s5, 24(t5)           # seg1 = (input+payload_start, body_len) IN PLACE\n" ++
  "  la t6, t155_buf; addi t6, t6, 64; sd t6, 32(t5); sd t2, 40(t5)   # seg2 = (suffix, suffix_len)\n" ++
  "  mv a0, t5; li a1, 3; mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256_segments\n" ++
  "  li a0, 0\n" ++
  "  j .Lt155_ret\n" ++
  ".Lt155_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt155_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_tx_signing_hash_legacy_eip155`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : tx_rlp_len
      bytes  8..16 : chain_id (u64 LE)
      bytes 16..   : tx_rlp (full 9-field)
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : 32-byte signing hash -/
def ziskTxSigningHashLegacyEip155Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tx_rlp_len\n" ++
  "  ld a2, 16(a5)               # chain_id\n" ++
  "  addi a0, a5, 24             # tx_rlp ptr\n" ++
  "  li a3, 0xa0010008           # output hash ptr (32 B)\n" ++
  "  jal ra, tx_signing_hash_legacy_eip155\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lt155_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  ".Lt155_pdone:"

def ziskTxSigningHashLegacyEip155DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "t155_buf:\n" ++
  "  .zero 131072\n" ++
  "t155_offset_lo:\n" ++
  "  .zero 8\n" ++
  "t155_length_lo:\n" ++
  "  .zero 8\n" ++
  "t155_offset_hi:\n" ++
  "  .zero 8\n" ++
  "t155_length_hi:\n" ++
  "  .zero 8\n" ++
  "t155_chain_be:\n" ++
  "  .zero 8\n" ++
  "t155_chain_enc:\n" ++
  "  .zero 9\n" ++
  "t155_prefix_len:\n" ++
  "  .zero 8"

def ziskTxSigningHashLegacyEip155ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxSigningHashLegacyEip155Prologue
  dataAsm     := ziskTxSigningHashLegacyEip155DataSection
}

/-! ## eip7702_authorization_signing_hash -- PR-K147

    EIP-7702 per-authorization signing hash:

      signing_hash =
        keccak256(MAGIC || rlp([chain_id, address, nonce]))

    where `MAGIC = 0x05`. This is the digest a delegator signs to
    authorise their account to delegate execution to a target
    address at a specific nonce.

    Companion to PR-K143
    `eip7702_authorization_extract_signature` (which extracts the
    `(y_parity, r, s)` triple). Together, K143 + K147 + the
    upcoming `zkvm_secp256k1_ecrecover` wiring + K99
    `address_from_pubkey` recover the **delegator** address from
    an authorization tuple.

    The body operation is structurally identical to K145
    `tx_signing_hash` with `n = 3` and `type_prefix = 0x05`:
    truncate the 6-field authorization tuple to its first 3
    fields and keccak the prefix-extended result. K147 is a
    typed convenience wrapper -- callers don't need to remember
    the MAGIC byte or the field count -- and delegates to
    `tx_signing_hash` for the body.

    Composes:
      - PR-K145 `tx_signing_hash` (truncate + keccak)
        which in turn composes K144 + K129 + K20 + Keccak.

    Calling convention:
      a0 (input)  : authorization_tuple_rlp ptr
      a1 (input)  : authorization_tuple_rlp byte length
      a2 (input)  : 32-byte output hash ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / fewer than 3 fields -/
def eip7702AuthorizationSigningHashFunction : String :=
  "eip7702_authorization_signing_hash:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  # Forward to tx_signing_hash with n=3, type_prefix=0x05.\n" ++
  "  # a0 = inner_rlp ptr      (unchanged)\n" ++
  "  # a1 = inner_rlp byte len (unchanged)\n" ++
  "  # a2 = 32-byte output ptr (move to a4 per K145 ABI)\n" ++
  "  mv a4, a2\n" ++
  "  li a2, 3                  # n_fields\n" ++
  "  li a3, 0x05               # MAGIC type prefix\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  ld ra,  0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_eip7702_authorization_signing_hash`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : tuple_rlp_len
      bytes  8..   : tuple_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : 32-byte signing hash -/
def ziskEip7702AuthorizationSigningHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tuple_rlp_len\n" ++
  "  addi a0, a4, 16             # tuple_rlp ptr\n" ++
  "  li a2, 0xa0010008           # output hash ptr (32 B)\n" ++
  "  jal ra, eip7702_authorization_signing_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltash_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  eip7702AuthorizationSigningHashFunction ++ "\n" ++
  ".Ltash_pdone:"

/-- Reuse the same scratch labels as `ziskTxSigningHashDataSection`
    (`tsh_buf`, `tsh_trunc_len`, `rltn_*`, `zk3_state`). -/
def ziskEip7702AuthorizationSigningHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "tsh_buf:\n" ++
  "  .zero 131072\n" ++
  "tsh_trunc_len:\n" ++
  "  .zero 8\n" ++
  "rltn_offset_lo:\n" ++
  "  .zero 8\n" ++
  "rltn_length_lo:\n" ++
  "  .zero 8\n" ++
  "rltn_offset_hi:\n" ++
  "  .zero 8\n" ++
  "rltn_length_hi:\n" ++
  "  .zero 8\n" ++
  "rltn_prefix_len:\n" ++
  "  .zero 8"

def ziskEip7702AuthorizationSigningHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip7702AuthorizationSigningHashPrologue
  dataAsm     := ziskEip7702AuthorizationSigningHashDataSection
}


end EvmAsm.Codegen
