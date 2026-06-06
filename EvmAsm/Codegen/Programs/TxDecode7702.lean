/-
  EvmAsm.Codegen.Programs.TxDecode7702

  EIP-7702 typed-transaction decoder split out of `TxDecode.lean`.

  Hosts:
    K44  tx_eip7702_decode   (13-field EIP-7702)

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

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

end EvmAsm.Codegen
