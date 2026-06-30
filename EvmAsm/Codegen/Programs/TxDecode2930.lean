/-
  EvmAsm.Codegen.Programs.TxDecode2930

  EIP-2930 typed-transaction decoder split out of `TxDecode.lean`.

  Hosts:
    K42  tx_eip2930_decode   (11-field EIP-2930)

  Uses the cursor-advancing walker pair (`EvmAsm.Codegen.Programs.
  RlpWalk`) instead of the index-based `rlp_field_to_*` wrappers,
  so all 11 fields are decoded in a single left-to-right pass
  (11 item visits) rather than 0+1+...+10 = 55 re-walks.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

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

    access_list semantics: per `rlp_walk_next`'s contract for list
    items, the recorded (offset, length) span the *full* encoded
    sub-list including its RLP prefix, so the caller can recurse
    into it.  Byte-string items (data) are prefix-stripped.

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (216 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip2930DecodeFunction : String :=
  "tx_eip2930_decode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                  # inner_rlp ptr (list base)\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  jal ra, rlp_walk_init      # a0=cursor, a1=end, a2=status\n" ++
  "  bnez a2, .Lt29_fail\n" ++
  "  mv s1, a1                  # end\n" ++
  "  mv s3, a0                  # cursor\n" ++
  "  # Field 0: chain_id (u64 at offset 0)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next      # a0=advanced, a1=status, a2=content_len\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sub a0, a0, a2             # content_ptr = advanced - len\n" ++
  "  mv a1, a2                  # content_len\n" ++
  "  jal ra, rlp_content_to_u64 # a0=u64, a1=status\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sd a0, 0(s2)\n" ++
  "  # Field 1: nonce (u64 at offset 8)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sd a0, 8(s2)\n" ++
  "  # Field 2: gas_price (u256 at offset 16)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 16\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 3: gas_limit (u64 at offset 48)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sd a0, 48(s2)\n" ++
  "  # Field 4: to (0 or 20 bytes at 56; to_present u32 at 76)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  beqz a2, .Lt29_to_creation\n" ++
  "  li t0, 20\n" ++
  "  bne a2, t0, .Lt29_fail\n" ++
  "  sub t3, a0, a2             # content_ptr\n" ++
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
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 80\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 6: data (offset+length u64 at 112/120)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sub t3, a0, a2             # content_ptr\n" ++
  "  sub t1, t3, s0             # offset = content_ptr - base\n" ++
  "  sd t1, 112(s2)\n" ++
  "  sd a2, 120(s2)             # content_len\n" ++
  "  # Field 7: access_list (offset+length u64 at 128/136; full encoded item)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sub t3, a0, a2             # content_ptr\n" ++
  "  sub t1, t3, s0             # offset = content_ptr - base\n" ++
  "  sd t1, 128(s2)\n" ++
  "  sd a2, 136(s2)             # content_len (full span)\n" ++
  "  # Field 8: y_parity (u64 at offset 144)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sd a0, 144(s2)\n" ++
  "  # Field 9: r (u256 at offset 152)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 152\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  # Field 10: s (u256 at offset 184)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt29_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 184\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lt29_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lt29_ret\n" ++
  ".Lt29_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt29_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 64\n" ++
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
  rlpWalkHelpersClosure ++ "\n" ++
  txEip2930DecodeFunction ++ "\n" ++
  ".Lt29_pdone:"

/-- The decoder holds (cursor, end) in callee-saved registers and
    derives every content pointer arithmetically, so it needs no
    `.data` scratch. -/
def ziskTxEip2930DecodeDataSection : String := ""

def ziskTxEip2930DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip2930DecodePrologue
  dataAsm     := ziskTxEip2930DecodeDataSection
}

end EvmAsm.Codegen
