/-
  EvmAsm.Codegen.Programs.TxDecode

  EIP-typed-tx decoders + dispatcher carved out of
  `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap.
  Hosts:

    K41  tx_eip1559_decode   (12-field EIP-1559)
    K42  tx_eip2930_decode   (11-field EIP-2930)
    K44  tx_eip7702_decode   (13-field EIP-7702)
    K45  tx_eip4844_decode   (14-field EIP-4844)
    K87  tx_decode_dispatch  (legacy + typed)

  Each decoder splits the appropriate RLP shape into per-field
  offset / length pairs in a caller-supplied output table.
  K87 inspects the typed-tx prefix byte and dispatches to the
  matching specific decoder (legacy / 1559 / 2930 / 4844 /
  7702). Composes K34 / K35 / K20 + K36 (tx_legacy_decode) +
  K40 (tx_type_dispatch) which remain in `Programs/Tx.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxDecode1559

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## tx_eip2930_decode -- PR-K42 full 11-field EIP-2930 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-2930
    (type-1) access-list transaction into a flat 216-byte output
    struct. Inner RLP shape (11 fields):

      rlp([
        chain_id, nonce, gas_price, gas_limit,
        to, value, data, access_list,
        y_parity, r, s
      ])

    EIP-2930 is structurally simpler than EIP-1559: a single
    `gas_price` field (legacy-style) instead of the
    `(max_priority_fee_per_gas, max_fee_per_gas)` pair.

    Output struct (216 bytes):
       0..  8  chain_id              (u64 LE)
       8.. 16  nonce                 (u64 LE)
      16.. 48  gas_price             (u256 BE)
      48.. 56  gas_limit             (u64 LE)
      56.. 76  to (20-byte address; zero for creation)
      76.. 80  to_present (u32; 0 = creation, 1 = call)
      80..112  value                 (u256 BE)
     112..120  data_offset           (u64 within inner RLP)
     120..128  data_length           (u64)
     128..136  access_list_offset    (u64; whole encoded item incl. prefix)
     136..144  access_list_length    (u64; whole encoded item incl. prefix)
     144..152  y_parity              (u64; 0 or 1)
     152..184  r                     (u256 BE)
     184..216  s                     (u256 BE)

    Caller passes the inner RLP body -- after stripping the 0x01
    type byte that PR-K40 `tx_type_dispatch` reports via
    `inner_offset`. access_list semantics mirror PR-K41
    `tx_eip1559_decode`: the returned (offset, length) span the
    *full* encoded sub-list including its RLP prefix, so the
    caller can recurse into it.

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (216 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip2930DecodeFunction : String :=
  "tx_eip2930_decode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # inner_rlp ptr\n" ++
  "  mv s1, a1                  # inner_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: chain_id (u64 at offset 0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 1: nonce (u64 at offset 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 2: gas_price (u256 at offset 16)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 16\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 3: gas_limit (u64 at offset 48)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 48\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 4: to (0 or 20 bytes at offset 56; to_present u32 at 76)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  la a3, t29_offset; la a4, t29_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  la t0, t29_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lt29_to_creation\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lt29_fail\n" ++
  "  la t0, t29_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 56\n" ++
  "  ld t5,  0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t3); sd t5, 8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  li t5, 1\n" ++
  "  sw t5, 76(s2)              # to_present = 1\n" ++
  "  j .Lt29_after_to\n" ++
  ".Lt29_to_creation:\n" ++
  "  addi t4, s2, 56\n" ++
  "  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)\n" ++
  "  sw zero, 76(s2)            # to_present = 0\n" ++
  ".Lt29_after_to:\n" ++
  "  # Field 5: value (u256 at offset 80)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 6: data (offset+length at 112/120)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  la a3, t29_offset; la a4, t29_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  la t0, t29_offset; ld t1, 0(t0); sd t1, 112(s2)\n" ++
  "  la t0, t29_length; ld t1, 0(t0); sd t1, 120(s2)\n" ++
  "  # Field 7: access_list (offset+length at 128/136; full encoded item)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, t29_offset; la a4, t29_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  la t0, t29_offset; ld t1, 0(t0); sd t1, 128(s2)\n" ++
  "  la t0, t29_length; ld t1, 0(t0); sd t1, 136(s2)\n" ++
  "  # Field 8: y_parity (u64 at offset 144)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  addi a3, s2, 144\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 9: r (u256 at offset 152)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  addi a3, s2, 152\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 10: s (u256 at offset 184)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  addi a3, s2, 184\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lt29_ret\n" ++
  ".Lt29_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt29_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_eip2930_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x01 type byte. Writes (status, 216-byte struct)
    to OUTPUT (224 bytes total). -/
def ziskTxEip2930DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 216 bytes (27 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 27\n" ++
  ".Lt29_zinit:\n" ++
  "  beqz t1, .Lt29_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt29_zinit\n" ++
  ".Lt29_zdone:\n" ++
  "  jal ra, tx_eip2930_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt29_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip2930DecodeFunction ++ "\n" ++
  ".Lt29_pdone:"

def ziskTxEip2930DecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t29_offset:\n" ++
  "  .zero 8\n" ++
  "t29_length:\n" ++
  "  .zero 8"

def ziskTxEip2930DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip2930DecodePrologue
  dataAsm     := ziskTxEip2930DecodeDataSection
}

/-! ## tx_eip7702_decode -- PR-K44 full 13-field EIP-7702 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-7702
    (type-4) set-code transaction into a flat 240-byte output
    struct. Inner RLP shape (13 fields):

      rlp([
        chain_id, nonce,
        max_priority_fee_per_gas, max_fee_per_gas,
        gas_limit, to, value, data,
        access_list, authorization_list,
        y_parity, r, s
      ])

    Compared to PR-K41 EIP-1559 (12 fields), EIP-7702 inserts an
    `authorization_list` after `access_list` -- a list of
    (chain_id, address, nonce, y_parity, r, s) authorization
    tuples. The decoder records only its outer (offset, length)
    bounds; sub-decoding into individual authorization entries
    lands in a follow-up PR.

    Output struct (240 bytes; u32 offsets/lengths to fit the
    256-byte ziskemu output cap):

       0..  8  chain_id              (u64 LE)
       8.. 16  nonce                 (u64 LE)
      16.. 48  max_priority_fee_per_gas (u256 BE)
      48.. 80  max_fee_per_gas       (u256 BE)
      80.. 88  gas_limit             (u64 LE)
      88..108  to (20-byte address; zero for creation -- but
                  EIP-7702 spec requires `to` so empty paths
                  are still reported as creation status=1)
     108..112  to_present (u32; 0 = creation, 1 = call)
     112..144  value                 (u256 BE)
     144..148  data_offset           (u32)
     148..152  data_length           (u32)
     152..156  access_list_offset    (u32; whole encoded item)
     156..160  access_list_length    (u32; whole encoded item)
     160..164  auth_list_offset      (u32; whole encoded item)
     164..168  auth_list_length      (u32; whole encoded item)
     168..176  y_parity              (u64; 0 or 1)
     176..208  r                     (u256 BE)
     208..240  s                     (u256 BE)

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (240 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip7702DecodeFunction : String :=
  "tx_eip7702_decode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # inner_rlp ptr\n" ++
  "  mv s1, a1                  # inner_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: chain_id (u64 at offset 0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 1: nonce (u64 at offset 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 2: max_priority_fee_per_gas (u256 at offset 16)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 16\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 3: max_fee_per_gas (u256 at offset 48)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 48\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 4: gas_limit (u64 at offset 80)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 5: to (0 or 20 bytes at offset 88; to_present u32 at 108)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, t77_offset; la a4, t77_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  la t0, t77_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lt77_to_creation\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lt77_fail\n" ++
  "  la t0, t77_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 88\n" ++
  "  ld t5,  0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t3); sd t5, 8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  li t5, 1\n" ++
  "  sw t5, 108(s2)             # to_present = 1\n" ++
  "  j .Lt77_after_to\n" ++
  ".Lt77_to_creation:\n" ++
  "  addi t4, s2, 88\n" ++
  "  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)\n" ++
  "  sw zero, 108(s2)           # to_present = 0\n" ++
  ".Lt77_after_to:\n" ++
  "  # Field 6: value (u256 at offset 112)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  addi a3, s2, 112\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 7: data (offset+length u32 at 144/148)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, t77_offset; la a4, t77_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  la t0, t77_offset; ld t1, 0(t0); sw t1, 144(s2)\n" ++
  "  la t0, t77_length; ld t1, 0(t0); sw t1, 148(s2)\n" ++
  "  # Field 8: access_list (offset+length u32 at 152/156)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  la a3, t77_offset; la a4, t77_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  la t0, t77_offset; ld t1, 0(t0); sw t1, 152(s2)\n" ++
  "  la t0, t77_length; ld t1, 0(t0); sw t1, 156(s2)\n" ++
  "  # Field 9: authorization_list (offset+length u32 at 160/164)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  la a3, t77_offset; la a4, t77_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  la t0, t77_offset; ld t1, 0(t0); sw t1, 160(s2)\n" ++
  "  la t0, t77_length; ld t1, 0(t0); sw t1, 164(s2)\n" ++
  "  # Field 10: y_parity (u64 at offset 168)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  addi a3, s2, 168\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 11: r (u256 at offset 176)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 176\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  # Field 12: s (u256 at offset 208)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 12\n" ++
  "  addi a3, s2, 208\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt77_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lt77_ret\n" ++
  ".Lt77_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt77_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_eip7702_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x04 type byte. Writes (status, 240-byte struct)
    to OUTPUT (248 bytes total). -/
def ziskTxEip7702DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 240 bytes (30 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 30\n" ++
  ".Lt77_zinit:\n" ++
  "  beqz t1, .Lt77_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt77_zinit\n" ++
  ".Lt77_zdone:\n" ++
  "  jal ra, tx_eip7702_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt77_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip7702DecodeFunction ++ "\n" ++
  ".Lt77_pdone:"

def ziskTxEip7702DecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t77_offset:\n" ++
  "  .zero 8\n" ++
  "t77_length:\n" ++
  "  .zero 8"

def ziskTxEip7702DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip7702DecodePrologue
  dataAsm     := ziskTxEip7702DecodeDataSection
}

/-! ## tx_eip4844_decode -- PR-K45 full 14-field EIP-4844 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-4844
    (type-3) blob transaction into a flat 248-byte output struct.
    Inner RLP shape (14 fields):

      rlp([
        chain_id, nonce,
        max_priority_fee_per_gas, max_fee_per_gas,
        gas_limit, to, value, data,
        access_list,
        max_fee_per_blob_gas, blob_versioned_hashes,
        y_parity, r, s
      ])

    Compared to PR-K41 EIP-1559 (12 fields), EIP-4844 inserts
    `max_fee_per_blob_gas` (u256) and `blob_versioned_hashes`
    (list of 32-byte hashes) between `access_list` and `y_parity`.

    NOTE on max_fee_per_blob_gas: the spec type is u256, but
    real-world blob fees fit comfortably in u64 (mainnet typical
    range is 1 wei .. low gwei). To keep the struct within
    ziskemu's 256-byte output cap, this decoder stores the
    field as `u64` and rejects (status=1) any encoded value
    longer than 8 bytes. Callers needing the full u256 can
    re-extract via `rlp_field_to_u256_be` at field index 9.

    Output struct (248 bytes; u32 offsets/lengths):

       0..  8  chain_id                  (u64 LE)
       8.. 16  nonce                     (u64 LE)
      16.. 48  max_priority_fee_per_gas  (u256 BE)
      48.. 80  max_fee_per_gas           (u256 BE)
      80.. 88  gas_limit                 (u64 LE)
      88..108  to (20-byte address; zero for creation -- but
                  EIP-4844 spec disallows creation, so empty
                  to is just reported via to_present=0)
     108..112  to_present (u32; 0 = creation, 1 = call)
     112..144  value                     (u256 BE)
     144..148  data_offset               (u32)
     148..152  data_length               (u32)
     152..156  access_list_offset        (u32; whole encoded item)
     156..160  access_list_length        (u32; whole encoded item)
     160..168  max_fee_per_blob_gas      (u64 LE; rejects > 8 B BE)
     168..172  blob_versioned_hashes_off (u32; whole encoded item)
     172..176  blob_versioned_hashes_len (u32; whole encoded item)
     176..184  y_parity                  (u64; 0 or 1)
     184..216  r                         (u256 BE)
     216..248  s                         (u256 BE)

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (248 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (incl. blob fee > u64) -/
def txEip4844DecodeFunction : String :=
  "tx_eip4844_decode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # inner_rlp ptr\n" ++
  "  mv s1, a1                  # inner_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: chain_id\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 1: nonce\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 2: max_priority_fee_per_gas\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 16\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 3: max_fee_per_gas\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 48\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 4: gas_limit\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 5: to (0 or 20 B at 88; to_present u32 at 108)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, t48_offset; la a4, t48_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  la t0, t48_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lt48_to_creation\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lt48_fail\n" ++
  "  la t0, t48_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 88\n" ++
  "  ld t5,  0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t3); sd t5, 8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  li t5, 1\n" ++
  "  sw t5, 108(s2)             # to_present = 1\n" ++
  "  j .Lt48_after_to\n" ++
  ".Lt48_to_creation:\n" ++
  "  addi t4, s2, 88\n" ++
  "  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)\n" ++
  "  sw zero, 108(s2)           # to_present = 0\n" ++
  ".Lt48_after_to:\n" ++
  "  # Field 6: value\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  addi a3, s2, 112\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 7: data (u32 off+len at 144/148)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, t48_offset; la a4, t48_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  la t0, t48_offset; ld t1, 0(t0); sw t1, 144(s2)\n" ++
  "  la t0, t48_length; ld t1, 0(t0); sw t1, 148(s2)\n" ++
  "  # Field 8: access_list (u32 off+len at 152/156)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  la a3, t48_offset; la a4, t48_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  la t0, t48_offset; ld t1, 0(t0); sw t1, 152(s2)\n" ++
  "  la t0, t48_length; ld t1, 0(t0); sw t1, 156(s2)\n" ++
  "  # Field 9: max_fee_per_blob_gas (u64 at 160; rejects > 8B BE)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  addi a3, s2, 160\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 10: blob_versioned_hashes (u32 off+len at 168/172)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  la a3, t48_offset; la a4, t48_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  la t0, t48_offset; ld t1, 0(t0); sw t1, 168(s2)\n" ++
  "  la t0, t48_length; ld t1, 0(t0); sw t1, 172(s2)\n" ++
  "  # Field 11: y_parity (u64 at 176)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 176\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 12: r (u256 at 184)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 12\n" ++
  "  addi a3, s2, 184\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 13: s (u256 at 216)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 13\n" ++
  "  addi a3, s2, 216\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lt48_ret\n" ++
  ".Lt48_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt48_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_eip4844_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x03 type byte. Writes (status, 248-byte struct)
    to OUTPUT (256 bytes total). -/
def ziskTxEip4844DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 248 bytes (31 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 31\n" ++
  ".Lt48_zinit:\n" ++
  "  beqz t1, .Lt48_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt48_zinit\n" ++
  ".Lt48_zdone:\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt48_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  ".Lt48_pdone:"

def ziskTxEip4844DecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8"

def ziskTxEip4844DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip4844DecodePrologue
  dataAsm     := ziskTxEip4844DecodeDataSection
}

/-! ## tx_decode_dispatch -- PR-K87 unified tx decoder

    Dispatch on a tx envelope's type byte and route to the
    appropriate inner decoder. Mirrors Python's
    `decode_transaction`:

      byte 0 ≥ 0xc0     → legacy        → tx_legacy_decode    (K36)
      byte 0 == 0x01    → EIP-2930      → tx_eip2930_decode   (K42)
      byte 0 == 0x02    → EIP-1559      → tx_eip1559_decode   (K41)
      byte 0 == 0x03    → EIP-4844      → tx_eip4844_decode   (K45)
      byte 0 == 0x04    → EIP-7702      → tx_eip7702_decode   (K44)
      else              → status = type-unrecognized

    The decoded struct's size depends on the tx type:
      type 0 (legacy)   : 196 B
      type 1 (EIP-2930) : 216 B
      type 2 (EIP-1559) : 248 B
      type 3 (EIP-4844) : 248 B
      type 4 (EIP-7702) : 240 B

    Status encoding packs both the tx_type and sub-status:

      status = (tx_type << 8) | sub_status

      sub_status 0  : success
      sub_status 1  : type unrecognized (used with tx_type=0)
      sub_status 2  : sub-decoder returned non-zero

    Caller responsibilities:
      - Pre-zero the 248-byte struct_out buffer.
      - After success, infer struct_size from `tx_type` extracted
        as `(status >> 8) & 0xff`.

    Composes PR-K40 + each of K36, K41, K42, K44, K45.

    Calling convention:
      a0 (input)  : envelope ptr
      a1 (input)  : envelope_len
      a2 (input)  : struct_out ptr (must be ≥ 248 bytes, pre-zeroed)
      ra (input)  : return
      a0 (output) : packed status (see encoding above).

    Uses 8 bytes of `.data` scratch (`tdd_inner_off`) plus the
    inner-decoder scratches (rfu_offset/rfu_length etc.). -/
def txDecodeDispatchFunction : String :=
  "tx_decode_dispatch:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # envelope ptr\n" ++
  "  mv s1, a1                   # envelope_len\n" ++
  "  mv s2, a2                   # struct_out ptr\n" ++
  "  # tx_type_dispatch(envelope, len, type_out=tdd_type, inner_offset_out=tdd_inner_off)\n" ++
  "  la a2, tdd_type\n" ++
  "  la a3, tdd_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Ltdd_unrec\n" ++
  "  la t0, tdd_type; ld t1, 0(t0)\n" ++
  "  la t0, tdd_inner_off; ld t2, 0(t0)\n" ++
  "  add t3, s0, t2              # inner_ptr\n" ++
  "  sub t4, s1, t2              # inner_len\n" ++
  "  # Dispatch on tx_type (t1)\n" ++
  "  beqz t1, .Ltdd_legacy\n" ++
  "  li t5, 1\n" ++
  "  beq t1, t5, .Ltdd_2930\n" ++
  "  li t5, 2\n" ++
  "  beq t1, t5, .Ltdd_1559\n" ++
  "  li t5, 3\n" ++
  "  beq t1, t5, .Ltdd_4844\n" ++
  "  li t5, 4\n" ++
  "  beq t1, t5, .Ltdd_7702\n" ++
  "  j .Ltdd_unrec\n" ++
  ".Ltdd_legacy:\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  jal ra, tx_legacy_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_legacy\n" ++
  "  li a0, 0\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_2930:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip2930_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_2930\n" ++
  "  li a0, 0x0100\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_1559:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip1559_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_1559\n" ++
  "  li a0, 0x0200\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_4844:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_4844\n" ++
  "  li a0, 0x0300\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_7702:\n" ++
  "  mv a0, t3; mv a1, t4; mv a2, s2\n" ++
  "  jal ra, tx_eip7702_decode\n" ++
  "  bnez a0, .Ltdd_decode_fail_7702\n" ++
  "  li a0, 0x0400\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_unrec:\n" ++
  "  li a0, 0x0001\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_legacy:\n" ++
  "  li a0, 0x0002\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_2930:\n" ++
  "  li a0, 0x0102\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_1559:\n" ++
  "  li a0, 0x0202\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_4844:\n" ++
  "  li a0, 0x0302\n" ++
  "  j .Ltdd_ret\n" ++
  ".Ltdd_decode_fail_7702:\n" ++
  "  li a0, 0x0402\n" ++
  ".Ltdd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_tx_decode_dispatch`: probe BuildUnit. Reads (env_len,
    env_bytes) from host input; pre-zeros 248-byte struct slot
    at OUTPUT+8; calls helper; writes (packed status, struct)
    to OUTPUT (256 bytes total). -/
def ziskTxDecodeDispatchPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # env_len\n" ++
  "  addi a0, a3, 16             # env ptr\n" ++
  "  li a2, 0xa0010008           # struct slot at OUTPUT + 8\n" ++
  "  # Pre-zero 248 bytes (31 dwords).\n" ++
  "  mv t0, a2; li t1, 31\n" ++
  ".Ltdd_zout:\n" ++
  "  beqz t1, .Ltdd_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltdd_zout\n" ++
  ".Ltdd_zout_done:\n" ++
  "  jal ra, tx_decode_dispatch\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # packed status\n" ++
  "  j .Ltdd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txLegacyDecodeFunction ++ "\n" ++
  txEip2930DecodeFunction ++ "\n" ++
  txEip1559DecodeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  txEip7702DecodeFunction ++ "\n" ++
  txDecodeDispatchFunction ++ "\n" ++
  ".Ltdd_pdone:"

def ziskTxDecodeDispatchDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "txd_offset:\n" ++
  "  .zero 8\n" ++
  "txd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t1d_offset:\n" ++
  "  .zero 8\n" ++
  "t1d_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t29_offset:\n" ++
  "  .zero 8\n" ++
  "t29_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t77_offset:\n" ++
  "  .zero 8\n" ++
  "t77_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tdd_type:\n" ++
  "  .zero 8\n" ++
  "tdd_inner_off:\n" ++
  "  .zero 8"

def ziskTxDecodeDispatchProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxDecodeDispatchPrologue
  dataAsm     := ziskTxDecodeDispatchDataSection
}


/-! ## tx_eip4844_compute_blob_gas -- PR-K88

    Given an EIP-4844 (type 3) tx inner RLP body, decode it and
    compute the per-tx `blob_gas_used` field:

      blob_gas_used = len(tx.blob_versioned_hashes) × GAS_PER_BLOB

    Where `GAS_PER_BLOB = 131072` (mainnet Cancun); parameterized
    so the helper works across forks that adjust it.

    Composes:
      - PR-K45 `tx_eip4844_decode` — decode inner body → 248 B struct
      - PR-K64 `blob_gas_used_from_versioned_hashes` — count × gas_per_blob

    Useful for verifying that
    `header.blob_gas_used == sum(tx.blob_gas_used for tx in block)`.

    The K45 struct at offsets 168..172 (u32 LE) holds
    `blob_versioned_hashes_offset` (relative to `inner_ptr`), and
    offsets 172..176 hold `blob_versioned_hashes_length`. This
    helper reads those, computes the absolute pointer, and
    invokes K64.

    Calling convention:
      a0 (input)  : inner_rlp ptr (post-0x03 type byte)
      a1 (input)  : inner_rlp byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet)
      a3 (input)  : u64 out ptr (receives blob_gas_used)
      ra (input)  : return
      a0 (output) :
        0  : success
        1  : tx_eip4844_decode failed (parse error)
        2  : blob_gas_used_from_versioned_hashes failed (parse error)

    Uses 248 + 8 bytes of `.data` scratch (`tcbg_struct` for the
    decoded EIP-4844 struct, plus an inherited count scratch). -/
def txEip4844ComputeBlobGasFunction : String :=
  "tx_eip4844_compute_blob_gas:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # inner_rlp ptr\n" ++
  "  mv s1, a2                   # gas_per_blob\n" ++
  "  mv s2, a3                   # out ptr\n" ++
  "  # Step 1: K45 tx_eip4844_decode(inner, len, tcbg_struct)\n" ++
  "  la a2, tcbg_struct\n" ++
  "  # Pre-zero 248 bytes (31 dwords)\n" ++
  "  mv t0, a2; li t1, 31\n" ++
  ".Ltcbg_zinit:\n" ++
  "  beqz t1, .Ltcbg_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltcbg_zinit\n" ++
  ".Ltcbg_zdone:\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Ltcbg_decode_fail\n" ++
  "  # Step 2: K64 blob_gas_used_from_versioned_hashes(...)\n" ++
  "  la t0, tcbg_struct\n" ++
  "  lwu t1, 168(t0)             # blob_versioned_hashes_offset (u32)\n" ++
  "  lwu t2, 172(t0)             # blob_versioned_hashes_length (u32)\n" ++
  "  add a0, s0, t1              # absolute blob_list ptr\n" ++
  "  mv a1, t2                   # blob_list length\n" ++
  "  mv a2, s1                   # gas_per_blob\n" ++
  "  mv a3, s2                   # out ptr\n" ++
  "  jal ra, blob_gas_used_from_versioned_hashes\n" ++
  "  beqz a0, .Ltcbg_ret\n" ++
  "  li a0, 2\n" ++
  "  j .Ltcbg_ret\n" ++
  ".Ltcbg_decode_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltcbg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_tx_eip4844_compute_blob_gas`: probe BuildUnit. Reads
    (inner_len, gas_per_blob, inner_bytes) from host input,
    writes (status, blob_gas_used) to OUTPUT (16 bytes). -/
def ziskTxEip4844ComputeBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # inner_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # inner_ptr\n" ++
  "  li a3, 0xa0010008           # out u64 ptr\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, tx_eip4844_compute_blob_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltcbg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  ".Ltcbg_pdone:"

def ziskTxEip4844ComputeBlobGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bgvh_count_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tcbg_struct:\n" ++
  "  .zero 248"

def ziskTxEip4844ComputeBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip4844ComputeBlobGasPrologue
  dataAsm     := ziskTxEip4844ComputeBlobGasDataSection
}

/-! ## tx_calculate_total_blob_gas -- PR-K92

    Python reference (`forks/amsterdam/vm/gas.py`):

      def calculate_total_blob_gas(tx) -> U64:
          if isinstance(tx, BlobTransaction):
              return GAS_PER_BLOB * U64(len(tx.blob_versioned_hashes))
          else:
              return U64(0)

    Accepts a transaction in its encoded form (legacy RLP list,
    or typed `[type_byte || rlp(inner)]`) and returns the per-tx
    blob_gas_used: 0 for any non-EIP-4844 type, otherwise the
    blob-count × gas-per-blob product computed by PR-K88.

    Composes:
      - PR-K40 `tx_type_dispatch`           — typed-tx detector
      - PR-K88 `tx_eip4844_compute_blob_gas` — count × gas_per_blob

    Useful per-tx primitive for `apply_body` and for receipt-side
    bookkeeping that needs the same number on every tx without
    branching on type in the caller.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet Cancun)
      a3 (input)  : u64 out ptr (receives total blob gas)
      ra (input)  : return
      a0 (output) : composite status code

    Status decade encoding (floor(status/100) identifies the
    failing step):

      0          : success
      1          : tx_type_dispatch failed (unknown tx type / empty)
      101..102   : tx_eip4844_compute_blob_gas forwarded
                   (101 = K45 decode, 102 = K64 sum)

    Uses two 8-byte `.data` scratch slots (`tctbg_type`,
    `tctbg_inner_off`) plus the buffers inherited from K88. -/
def txCalculateTotalBlobGasFunction : String :=
  "tx_calculate_total_blob_gas:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx_len\n" ++
  "  mv s3, a2                   # gas_per_blob (stash)\n" ++
  "  mv s2, a3                   # out ptr\n" ++
  "  # Default zero in case of early non-type-3 exit.\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: tx_type_dispatch(tx, len, &type, &inner_off)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, tctbg_type\n" ++
  "  la a3, tctbg_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lctbg_after_dispatch\n" ++
  "  li a0, 1\n" ++
  "  j .Lctbg_ret\n" ++
  ".Lctbg_after_dispatch:\n" ++
  "  la t0, tctbg_type\n" ++
  "  ld t1, 0(t0)\n" ++
  "  li t2, 3\n" ++
  "  bne t1, t2, .Lctbg_zero_ok\n" ++
  "  # type 3: compute blob gas via K88.\n" ++
  "  la t0, tctbg_inner_off\n" ++
  "  ld t3, 0(t0)\n" ++
  "  add a0, s0, t3              # inner_ptr\n" ++
  "  sub a1, s1, t3              # inner_len\n" ++
  "  mv a2, s3                   # gas_per_blob\n" ++
  "  mv a3, s2                   # out ptr\n" ++
  "  jal ra, tx_eip4844_compute_blob_gas\n" ++
  "  beqz a0, .Lctbg_ok\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0              # 1 → 101, 2 → 102\n" ++
  "  j .Lctbg_ret\n" ++
  ".Lctbg_zero_ok:\n" ++
  "  # *out already 0.\n" ++
  ".Lctbg_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lctbg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_calculate_total_blob_gas`: probe BuildUnit. Reads
    (tx_len, gas_per_blob, tx_bytes) from host input, writes
    (status, total_blob_gas) to OUTPUT (16 bytes). -/
def ziskTxCalculateTotalBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # tx_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # tx_ptr\n" ++
  "  li a3, 0xa0010008           # out u64 ptr\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, tx_calculate_total_blob_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lctbg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  txCalculateTotalBlobGasFunction ++ "\n" ++
  ".Lctbg_pdone:"

def ziskTxCalculateTotalBlobGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bgvh_count_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tcbg_struct:\n" ++
  "  .zero 248\n" ++
  ".balign 8\n" ++
  "tctbg_type:\n" ++
  "  .zero 8\n" ++
  "tctbg_inner_off:\n" ++
  "  .zero 8"

def ziskTxCalculateTotalBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxCalculateTotalBlobGasPrologue
  dataAsm     := ziskTxCalculateTotalBlobGasDataSection
}


end EvmAsm.Codegen
