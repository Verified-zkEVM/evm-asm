/-
  EvmAsm.Codegen.Programs.TxDecode1559

  EIP-1559 typed-transaction decoder split out of `TxDecode.lean`.

  Hosts:
    K41  tx_eip1559_decode   (12-field EIP-1559)

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## tx_eip1559_decode -- PR-K41 full 12-field EIP-1559 decoder

    Decode the inner (post-type-byte) RLP body of an EIP-1559
    (type-2) transaction into a flat 248-byte output struct.
    Inner RLP shape (12 fields):

      rlp([
        chain_id, nonce,
        max_priority_fee_per_gas, max_fee_per_gas,
        gas_limit, to, value, data, access_list,
        y_parity, r, s
      ])

    Output struct (248 bytes):
       0..  8  chain_id              (u64 LE)
       8.. 16  nonce                 (u64 LE)
      16.. 48  max_priority_fee_per_gas (u256 BE)
      48.. 80  max_fee_per_gas       (u256 BE)
      80.. 88  gas_limit             (u64 LE)
      88..108  to (20-byte address; zero for creation)
     108..112  to_present (u32; 0 = creation, 1 = call)
     112..144  value                 (u256 BE)
     144..152  data_offset           (u64 within inner RLP)
     152..160  data_length           (u64)
     160..168  access_list_offset    (u64; whole encoded item incl. prefix)
     168..176  access_list_length    (u64; whole encoded item incl. prefix)
     176..184  y_parity              (u64; 0 or 1)
     184..216  r                     (u256 BE)
     216..248  s                     (u256 BE)

    Caller passes the inner RLP body -- after stripping the 0x02
    type byte that PR-K40 `tx_type_dispatch` reports via
    `inner_offset`.

    access_list semantics: per `rlp_list_nth_item`'s contract for
    list items, the returned (offset, length) span the *full*
    encoded sub-list including its RLP prefix, so the caller can
    recurse into it with another `rlp_list_nth_item` call.

    Calling convention:
      a0 (input)  : inner_rlp ptr
      a1 (input)  : inner_rlp byte length
      a2 (input)  : output struct ptr (248 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txEip1559DecodeFunction : String :=
  "tx_eip1559_decode:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # inner_rlp ptr\n" ++
  "  mv s1, a1                  # inner_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: chain_id (u64 at offset 0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 1: nonce (u64 at offset 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 2: max_priority_fee_per_gas (u256 at offset 16)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 16\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 3: max_fee_per_gas (u256 at offset 48)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 48\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 4: gas_limit (u64 at offset 80)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 5: to (0 or 20 bytes at offset 88; to_present u32 at 108)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, t1d_offset; la a4, t1d_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  la t0, t1d_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lt1d_to_creation\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lt1d_fail\n" ++
  "  la t0, t1d_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 88\n" ++
  "  ld t5,  0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t3); sd t5, 8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  li t5, 1\n" ++
  "  sw t5, 108(s2)             # to_present = 1\n" ++
  "  j .Lt1d_after_to\n" ++
  ".Lt1d_to_creation:\n" ++
  "  addi t4, s2, 88\n" ++
  "  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)\n" ++
  "  sw zero, 108(s2)           # to_present = 0\n" ++
  ".Lt1d_after_to:\n" ++
  "  # Field 6: value (u256 at offset 112)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6\n" ++
  "  addi a3, s2, 112\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 7: data (offset+length stored at 144/152)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, t1d_offset; la a4, t1d_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  la t0, t1d_offset; ld t1, 0(t0); sd t1, 144(s2)\n" ++
  "  la t0, t1d_length; ld t1, 0(t0); sd t1, 152(s2)\n" ++
  "  # Field 8: access_list (offset+length at 160/168; full encoded item)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  la a3, t1d_offset; la a4, t1d_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  la t0, t1d_offset; ld t1, 0(t0); sd t1, 160(s2)\n" ++
  "  la t0, t1d_length; ld t1, 0(t0); sd t1, 168(s2)\n" ++
  "  # Field 9: y_parity (u64 at offset 176)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  addi a3, s2, 176\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 10: r (u256 at offset 184)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  addi a3, s2, 184\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  # Field 11: s (u256 at offset 216)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 216\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lt1d_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lt1d_ret\n" ++
  ".Lt1d_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt1d_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_tx_eip1559_decode`: probe BuildUnit. Reads (inner_len,
    inner_bytes) from host input -- caller is expected to have
    stripped the 0x02 type byte. Writes (status, 248-byte struct)
    to OUTPUT (256 bytes total, matching ziskemu's output cap). -/
def ziskTxEip1559DecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # inner_len\n" ++
  "  addi a0, a3, 16             # inner ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 248 bytes (31 × 8 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 31\n" ++
  ".Lt1d_zinit:\n" ++
  "  beqz t1, .Lt1d_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lt1d_zinit\n" ++
  ".Lt1d_zdone:\n" ++
  "  jal ra, tx_eip1559_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lt1d_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip1559DecodeFunction ++ "\n" ++
  ".Lt1d_pdone:"

def ziskTxEip1559DecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t1d_offset:\n" ++
  "  .zero 8\n" ++
  "t1d_length:\n" ++
  "  .zero 8"

def ziskTxEip1559DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip1559DecodePrologue
  dataAsm     := ziskTxEip1559DecodeDataSection
}

end EvmAsm.Codegen
