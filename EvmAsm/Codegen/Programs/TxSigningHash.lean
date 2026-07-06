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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
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
def rlpListTruncateToNFields_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .BEQ .x18 .x0 (204 : BitVec 13),
    .BEQ .x9 .x0 (224 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (212 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (16 : BitVec 13),
    .ADDI .x21 .x5 (-247 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x21 (1 : Word),
    .ADDI .x5 .x18 (-1 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x5,
    .AUIPC .x13 (laHi GuestAddrs.rltn_offset_hi (GuestAddrs.rlp_list_truncate_to_n_fields + 116)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rltn_offset_hi (GuestAddrs.rlp_list_truncate_to_n_fields + 116)),
    .AUIPC .x14 (laHi GuestAddrs.rltn_length_hi (GuestAddrs.rlp_list_truncate_to_n_fields + 124)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rltn_length_hi (GuestAddrs.rlp_list_truncate_to_n_fields + 124)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.rlp_list_truncate_to_n_fields + 132)),
    .BNE .x10 .x0 (156 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rltn_offset_hi (GuestAddrs.rlp_list_truncate_to_n_fields + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rltn_offset_hi (GuestAddrs.rlp_list_truncate_to_n_fields + 140)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.rltn_length_hi (GuestAddrs.rlp_list_truncate_to_n_fields + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rltn_length_hi (GuestAddrs.rlp_list_truncate_to_n_fields + 152)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x6 .x6 .x7,
    .SUB .x22 .x6 .x21,
    .MV .x10 .x22,
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.rltn_prefix_len (GuestAddrs.rlp_list_truncate_to_n_fields + 180)),
    .ADDI .x12 .x12 (laLo GuestAddrs.rltn_prefix_len (GuestAddrs.rlp_list_truncate_to_n_fields + 180)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.rlp_list_truncate_to_n_fields + 188)),
    .AUIPC .x5 (laHi GuestAddrs.rltn_prefix_len (GuestAddrs.rlp_list_truncate_to_n_fields + 192)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rltn_prefix_len (GuestAddrs.rlp_list_truncate_to_n_fields + 192)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x19 .x6,
    .ADD .x28 .x8 .x21,
    .MV .x29 .x22,
    .BEQ .x29 .x0 (28 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .SB .x7 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x6 .x6 .x22,
    .SD .x20 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (40 : BitVec 21),
    .LI .x5 (192 : Word),
    .SB .x19 .x5 (0 : BitVec 12),
    .LI .x5 (1 : Word),
    .SD .x20 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `rlpListTruncateToNFields_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def rlpListTruncateToNFields_relocs : RelocTable :=
  [ (29, .la .x13 "rltn_offset_hi"),
    (31, .la .x14 "rltn_length_hi"),
    (33, .jal .x1 "rlp_list_nth_item"),
    (35, .la .x5 "rltn_offset_hi"),
    (38, .la .x5 "rltn_length_hi"),
    (45, .la .x12 "rltn_prefix_len"),
    (47, .jal .x1 "rlp_encode_list_prefix"),
    (48, .la .x5 "rltn_prefix_len") ]

def rlpListTruncateToNFieldsFunction : String :=
  "rlp_list_truncate_to_n_fields:\n" ++ emitProgramR rlpListTruncateToNFields_prog rlpListTruncateToNFields_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `rlpListTruncateToNFields_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem rlpListTruncateToNFieldsFunction_eq_prog :
    rlpListTruncateToNFieldsFunction = "rlp_list_truncate_to_n_fields:\n" ++ emitProgramR rlpListTruncateToNFields_prog rlpListTruncateToNFields_relocs := rfl

#guard rlpListTruncateToNFieldsFunction.startsWith "rlp_list_truncate_to_n_fields:\n"
#guard rlpListTruncateToNFields_prog.length = 84
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
def txSigningHash_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .AUIPC .x5 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 56)),
    .SB .x5 .x19 (0 : BitVec 12),
    .BEQ .x9 .x0 (260 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (248 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (16 : BitVec 13),
    .ADDI .x21 .x5 (-247 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x21 (1 : Word),
    .LI .x22 (0 : Word),
    .BEQ .x18 .x0 (76 : BitVec 13),
    .ADDI .x5 .x18 (-1 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x5,
    .AUIPC .x13 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 132)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 132)),
    .ADDI .x13 .x13 (64 : BitVec 12),
    .AUIPC .x14 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 144)),
    .ADDI .x14 .x14 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 144)),
    .ADDI .x14 .x14 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.tx_signing_hash + 156)),
    .BNE .x10 .x0 (168 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 164)),
    .LD .x6 .x5 (64 : BitVec 12),
    .LD .x7 .x5 (72 : BitVec 12),
    .ADD .x6 .x6 .x7,
    .SUB .x22 .x6 .x21,
    .MV .x10 .x22,
    .AUIPC .x11 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 192)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 192)),
    .ADDI .x11 .x11 (16 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 204)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 204)),
    .ADDI .x12 .x12 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.tx_signing_hash + 216)),
    .AUIPC .x5 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 220)),
    .LD .x29 .x5 (80 : BitVec 12),
    .AUIPC .x30 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 232)),
    .ADDI .x30 .x30 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 232)),
    .ADDI .x30 .x30 (128 : BitVec 12),
    .LI .x5 (0 : Word),
    .BEQ .x19 .x0 (8 : BitVec 13),
    .LI .x5 (1 : Word),
    .AUIPC .x31 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 256)),
    .ADDI .x31 .x31 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 256)),
    .SD .x30 .x31 (0 : BitVec 12),
    .SD .x30 .x5 (8 : BitVec 12),
    .AUIPC .x31 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 272)),
    .ADDI .x31 .x31 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 272)),
    .ADDI .x31 .x31 (16 : BitVec 12),
    .SD .x30 .x31 (16 : BitVec 12),
    .SD .x30 .x29 (24 : BitVec 12),
    .ADD .x31 .x8 .x21,
    .SD .x30 .x31 (32 : BitVec 12),
    .SD .x30 .x22 (40 : BitVec 12),
    .MV .x10 .x30,
    .LI .x11 (3 : Word),
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256_segments (GuestAddrs.tx_signing_hash + 316)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txSigningHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txSigningHash_relocs : RelocTable :=
  [ (14, .la .x5 "tsh_buf"),
    (33, .la .x13 "tsh_buf"),
    (36, .la .x14 "tsh_buf"),
    (39, .jal .x1 "rlp_list_nth_item"),
    (41, .la .x5 "tsh_buf"),
    (48, .la .x11 "tsh_buf"),
    (51, .la .x12 "tsh_buf"),
    (54, .jal .x1 "rlp_encode_list_prefix"),
    (55, .la .x5 "tsh_buf"),
    (58, .la .x30 "tsh_buf"),
    (64, .la .x31 "tsh_buf"),
    (68, .la .x31 "tsh_buf"),
    (79, .jal .x1 "zkvm_keccak256_segments") ]

def txSigningHashFunction : String :=
  "tx_signing_hash:\n" ++ emitProgramR txSigningHash_prog txSigningHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txSigningHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txSigningHashFunction_eq_prog :
    txSigningHashFunction = "tx_signing_hash:\n" ++ emitProgramR txSigningHash_prog txSigningHash_relocs := rfl

#guard txSigningHashFunction.startsWith "tx_signing_hash:\n"
#guard txSigningHash_prog.length = 93
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
def txSigningHashLegacyEip155_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .BEQ .x9 .x0 (384 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (372 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (16 : BitVec 13),
    .ADDI .x20 .x5 (-247 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x20 (1 : Word),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (5 : Word),
    .AUIPC .x13 (laHi GuestAddrs.t155_offset_hi (GuestAddrs.tx_signing_hash_legacy_eip155 + 104)),
    .ADDI .x13 .x13 (laLo GuestAddrs.t155_offset_hi (GuestAddrs.tx_signing_hash_legacy_eip155 + 104)),
    .AUIPC .x14 (laHi GuestAddrs.t155_length_hi (GuestAddrs.tx_signing_hash_legacy_eip155 + 112)),
    .ADDI .x14 .x14 (laLo GuestAddrs.t155_length_hi (GuestAddrs.tx_signing_hash_legacy_eip155 + 112)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.tx_signing_hash_legacy_eip155 + 120)),
    .BNE .x10 .x0 (312 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.t155_offset_hi (GuestAddrs.tx_signing_hash_legacy_eip155 + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.t155_offset_hi (GuestAddrs.tx_signing_hash_legacy_eip155 + 128)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.t155_length_hi (GuestAddrs.tx_signing_hash_legacy_eip155 + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.t155_length_hi (GuestAddrs.tx_signing_hash_legacy_eip155 + 140)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x6 .x6 .x7,
    .SUB .x21 .x6 .x20,
    .AUIPC .x5 (laHi GuestAddrs.t155_chain_be (GuestAddrs.tx_signing_hash_legacy_eip155 + 160)),
    .ADDI .x5 .x5 (laLo GuestAddrs.t155_chain_be (GuestAddrs.tx_signing_hash_legacy_eip155 + 160)),
    .LI .x6 (7 : Word),
    .BLT .x6 .x0 (32 : BitVec 13),
    .SLLI .x7 .x6 (3 : BitVec 6),
    .SRL .x28 .x18 .x7,
    .ANDI .x28 .x28 (255 : BitVec 12),
    .SB .x5 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.t155_chain_be (GuestAddrs.tx_signing_hash_legacy_eip155 + 204)),
    .ADDI .x10 .x10 (laLo GuestAddrs.t155_chain_be (GuestAddrs.tx_signing_hash_legacy_eip155 + 204)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.t155_chain_enc (GuestAddrs.tx_signing_hash_legacy_eip155 + 216)),
    .ADDI .x12 .x12 (laLo GuestAddrs.t155_chain_enc (GuestAddrs.tx_signing_hash_legacy_eip155 + 216)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.tx_signing_hash_legacy_eip155 + 224)),
    .MV .x28 .x10,
    .ADDI .x28 .x28 (2 : BitVec 12),
    .ADD .x22 .x21 .x28,
    .MV .x10 .x22,
    .AUIPC .x11 (laHi GuestAddrs.t155_buf (GuestAddrs.tx_signing_hash_legacy_eip155 + 244)),
    .ADDI .x11 .x11 (laLo GuestAddrs.t155_buf (GuestAddrs.tx_signing_hash_legacy_eip155 + 244)),
    .AUIPC .x12 (laHi GuestAddrs.t155_prefix_len (GuestAddrs.tx_signing_hash_legacy_eip155 + 252)),
    .ADDI .x12 .x12 (laLo GuestAddrs.t155_prefix_len (GuestAddrs.tx_signing_hash_legacy_eip155 + 252)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.tx_signing_hash_legacy_eip155 + 260)),
    .SUB .x7 .x22 .x21,
    .ADDI .x7 .x7 (-2 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.t155_buf (GuestAddrs.tx_signing_hash_legacy_eip155 + 272)),
    .ADDI .x5 .x5 (laLo GuestAddrs.t155_buf (GuestAddrs.tx_signing_hash_legacy_eip155 + 272)),
    .ADDI .x5 .x5 (64 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.t155_chain_enc (GuestAddrs.tx_signing_hash_legacy_eip155 + 284)),
    .ADDI .x6 .x6 (laLo GuestAddrs.t155_chain_enc (GuestAddrs.tx_signing_hash_legacy_eip155 + 284)),
    .MV .x28 .x7,
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x31 .x6 (0 : BitVec 12),
    .SB .x5 .x31 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x31 (128 : Word),
    .SB .x5 .x31 (0 : BitVec 12),
    .SB .x5 .x31 (1 : BitVec 12),
    .ADDI .x7 .x7 (2 : BitVec 12),
    .AUIPC .x29 (laHi GuestAddrs.t155_prefix_len (GuestAddrs.tx_signing_hash_legacy_eip155 + 340)),
    .ADDI .x29 .x29 (laLo GuestAddrs.t155_prefix_len (GuestAddrs.tx_signing_hash_legacy_eip155 + 340)),
    .LD .x29 .x29 (0 : BitVec 12),
    .AUIPC .x30 (laHi GuestAddrs.t155_buf (GuestAddrs.tx_signing_hash_legacy_eip155 + 352)),
    .ADDI .x30 .x30 (laLo GuestAddrs.t155_buf (GuestAddrs.tx_signing_hash_legacy_eip155 + 352)),
    .ADDI .x30 .x30 (128 : BitVec 12),
    .AUIPC .x31 (laHi GuestAddrs.t155_buf (GuestAddrs.tx_signing_hash_legacy_eip155 + 364)),
    .ADDI .x31 .x31 (laLo GuestAddrs.t155_buf (GuestAddrs.tx_signing_hash_legacy_eip155 + 364)),
    .SD .x30 .x31 (0 : BitVec 12),
    .SD .x30 .x29 (8 : BitVec 12),
    .ADD .x31 .x8 .x20,
    .SD .x30 .x31 (16 : BitVec 12),
    .SD .x30 .x21 (24 : BitVec 12),
    .AUIPC .x31 (laHi GuestAddrs.t155_buf (GuestAddrs.tx_signing_hash_legacy_eip155 + 392)),
    .ADDI .x31 .x31 (laLo GuestAddrs.t155_buf (GuestAddrs.tx_signing_hash_legacy_eip155 + 392)),
    .ADDI .x31 .x31 (64 : BitVec 12),
    .SD .x30 .x31 (32 : BitVec 12),
    .SD .x30 .x7 (40 : BitVec 12),
    .MV .x10 .x30,
    .LI .x11 (3 : Word),
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256_segments (GuestAddrs.tx_signing_hash_legacy_eip155 + 424)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txSigningHashLegacyEip155_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txSigningHashLegacyEip155_relocs : RelocTable :=
  [ (26, .la .x13 "t155_offset_hi"),
    (28, .la .x14 "t155_length_hi"),
    (30, .jal .x1 "rlp_list_nth_item"),
    (32, .la .x5 "t155_offset_hi"),
    (35, .la .x5 "t155_length_hi"),
    (40, .la .x5 "t155_chain_be"),
    (51, .la .x10 "t155_chain_be"),
    (54, .la .x12 "t155_chain_enc"),
    (56, .jal .x1 "rlp_encode_uint_be"),
    (61, .la .x11 "t155_buf"),
    (63, .la .x12 "t155_prefix_len"),
    (65, .jal .x1 "rlp_encode_list_prefix"),
    (68, .la .x5 "t155_buf"),
    (71, .la .x6 "t155_chain_enc"),
    (85, .la .x29 "t155_prefix_len"),
    (88, .la .x30 "t155_buf"),
    (91, .la .x31 "t155_buf"),
    (98, .la .x31 "t155_buf"),
    (106, .jal .x1 "zkvm_keccak256_segments") ]

def txSigningHashLegacyEip155Function : String :=
  "tx_signing_hash_legacy_eip155:\n" ++ emitProgramR txSigningHashLegacyEip155_prog txSigningHashLegacyEip155_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txSigningHashLegacyEip155_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txSigningHashLegacyEip155Function_eq_prog :
    txSigningHashLegacyEip155Function = "tx_signing_hash_legacy_eip155:\n" ++ emitProgramR txSigningHashLegacyEip155_prog txSigningHashLegacyEip155_relocs := rfl

#guard txSigningHashLegacyEip155Function.startsWith "tx_signing_hash_legacy_eip155:\n"
#guard txSigningHashLegacyEip155_prog.length = 120
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
def eip7702AuthorizationSigningHash_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .MV .x14 .x12,
    .LI .x12 (3 : Word),
    .LI .x13 (5 : Word),
    .JAL .x1 (jalOff GuestAddrs.tx_signing_hash (GuestAddrs.eip7702_authorization_signing_hash + 20)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `eip7702AuthorizationSigningHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def eip7702AuthorizationSigningHash_relocs : RelocTable :=
  [ (5, .jal .x1 "tx_signing_hash") ]

def eip7702AuthorizationSigningHashFunction : String :=
  "eip7702_authorization_signing_hash:\n" ++ emitProgramR eip7702AuthorizationSigningHash_prog eip7702AuthorizationSigningHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `eip7702AuthorizationSigningHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem eip7702AuthorizationSigningHashFunction_eq_prog :
    eip7702AuthorizationSigningHashFunction = "eip7702_authorization_signing_hash:\n" ++ emitProgramR eip7702AuthorizationSigningHash_prog eip7702AuthorizationSigningHash_relocs := rfl

#guard eip7702AuthorizationSigningHashFunction.startsWith "eip7702_authorization_signing_hash:\n"
#guard eip7702AuthorizationSigningHash_prog.length = 9
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
