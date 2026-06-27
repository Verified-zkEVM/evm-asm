/-
  EvmAsm.Codegen.Programs.TxDecode4844

  EIP-4844 typed-transaction decoder split out of `TxDecode.lean`.

  Hosts:
    K45  tx_eip4844_decode   (14-field EIP-4844)

  Uses the cursor-advancing walker pair (`EvmAsm.Codegen.Programs.
  RlpWalk`) instead of the index-based `rlp_field_to_*` wrappers,
  so all 14 fields are decoded in a single left-to-right pass
  (14 item visits) rather than 0+1+...+13 = 91 re-walks.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

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
    ziskemu's 256-byte output cap, this decoder stores the field
    as `u64` (low 64 bits of the u256) and TOLERATES values that
    exceed u64 -- the full u256 (BE) is also persisted to the
    `.data` cell `tcbg_blob_fee_be` for callers (EIP-8037 gate /
    `BlockVerdict`) that need the complete value. In the high
    blob-fee regime (parent excess_blob_gas > ~328M) the blob gas
    price exceeds u64, so a valid tx's max_fee_per_blob_gas does
    too; the old index-based reject false-rejected those valid
    blob txs.

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
     160..168  max_fee_per_blob_gas      (u64 LE; low 64 bits of the u256)
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
      a0 (output) : 0 success / 1 parse fail -/
def txEip4844DecodeFunction : String :=
  "tx_eip4844_decode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                  # inner_rlp ptr (list base)\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  jal ra, rlp_walk_init      # a0=cursor, a1=end, a2=status\n" ++
  "  bnez a2, .Lt48_fail\n" ++
  "  mv s1, a1                  # end\n" ++
  "  mv s3, a0                  # cursor\n" ++
  "  # Field 0: chain_id (u64 at offset 0)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next      # a0=advanced, a1=status, a2=content_len\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub a0, a0, a2             # content_ptr = advanced - len\n" ++
  "  mv a1, a2                  # content_len\n" ++
  "  jal ra, rlp_content_to_u64 # a0=u64, a1=status\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sd a0, 0(s2)\n" ++
  "  # Field 1: nonce (u64 at offset 8)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sd a0, 8(s2)\n" ++
  "  # Field 2: max_priority_fee_per_gas (u256 at offset 16)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 16\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 3: max_fee_per_gas (u256 at offset 48)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 48\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 4: gas_limit (u64 at offset 80)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sd a0, 80(s2)\n" ++
  "  # Field 5: to (0 or 20 bytes at 88; to_present u32 at 108)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  beqz a2, .Lt48_to_creation\n" ++
  "  li t0, 20\n" ++
  "  bne a2, t0, .Lt48_fail\n" ++
  "  sub t3, a0, a2             # content_ptr\n" ++
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
  "  # Field 6: value (u256 at offset 112)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 112\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 7: data (offset+length u32 at 144/148)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub t3, a0, a2             # content_ptr\n" ++
  "  sub t1, t3, s0             # offset = content_ptr - base\n" ++
  "  sw t1, 144(s2)\n" ++
  "  sw a2, 148(s2)             # content_len\n" ++
  "  # Field 8: access_list (offset+length u32 at 152/156; full encoded item)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub t3, a0, a2             # content_ptr\n" ++
  "  sub t1, t3, s0             # offset = content_ptr - base\n" ++
  "  sw t1, 152(s2)\n" ++
  "  sw a2, 156(s2)             # content_len (full span)\n" ++
  "  # Field 9: max_fee_per_blob_gas (u256). Write the full BE u256 directly\n" ++
  "  # to tcbg_blob_fee_be (no sp+32 scratch needed), then BE-decode the low\n" ++
  "  # 64 bits (bytes 24..31) into the u64 view at struct offset 160.\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  la a2, tcbg_blob_fee_be\n" ++
  "  jal ra, rlp_content_to_u256_be  # persists full u256 BE -> tcbg; a0=status\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  la t0, tcbg_blob_fee_be\n" ++
  "  lbu t1, 24(t0); slli t1, t1, 56\n" ++
  "  lbu t2, 25(t0); slli t2, t2, 48; or t1, t1, t2\n" ++
  "  lbu t2, 26(t0); slli t2, t2, 40; or t1, t1, t2\n" ++
  "  lbu t2, 27(t0); slli t2, t2, 32; or t1, t1, t2\n" ++
  "  lbu t2, 28(t0); slli t2, t2, 24; or t1, t1, t2\n" ++
  "  lbu t2, 29(t0); slli t2, t2, 16; or t1, t1, t2\n" ++
  "  lbu t2, 30(t0); slli t2, t2,  8; or t1, t1, t2\n" ++
  "  lbu t2, 31(t0);                  or t1, t1, t2\n" ++
  "  sd t1, 160(s2)\n" ++
  "  # Field 10: blob_versioned_hashes (offset+length u32 at 168/172; full encoded item)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub t3, a0, a2             # content_ptr\n" ++
  "  sub t1, t3, s0             # offset = content_ptr - base\n" ++
  "  sw t1, 168(s2)\n" ++
  "  sw a2, 172(s2)             # content_len (full span)\n" ++
  "  # Field 11: y_parity (u64 at offset 176)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sd a0, 176(s2)\n" ++
  "  # Field 12: r (u256 at offset 184)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 184\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  # Field 13: s (u256 at offset 216)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Lt48_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 216\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Lt48_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lt48_ret\n" ++
  ".Lt48_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lt48_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 64\n" ++
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
  rlpWalkInitFunction ++ "\n" ++
  rlpWalkNextFunction ++ "\n" ++
  rlpContentToU64Function ++ "\n" ++
  rlpContentToU256BeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  ".Lt48_pdone:"

/-- The decoder holds (cursor, end) in callee-saved registers and
    derives every content pointer arithmetically, so the only
    `.data` cell it needs is `tcbg_blob_fee_be` -- the full BE
    u256 of `max_fee_per_blob_gas` that downstream consumers
    (`BlockVerdict` / EIP-8037 gate) read back. Declaring it here
    (previously it was only declared in unrelated probe data
    sections, leaving the standalone 4844 + dispatch probes unable
    to link) makes this probe self-contained. -/
def ziskTxEip4844DecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tcbg_blob_fee_be:\n" ++
  "  .zero 32"

def ziskTxEip4844DecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxEip4844DecodePrologue
  dataAsm     := ziskTxEip4844DecodeDataSection
}

end EvmAsm.Codegen
