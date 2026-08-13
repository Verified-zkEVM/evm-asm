/-
  EvmAsm.Codegen.Programs.BlockHashAtBlockNumber

  Number-keyed block_hash lookup. Inverse of #7370.
  Given a block_number and witness.headers, scan each
  header, extract its block.number via K233, and on first
  match keccak the header bytes to produce the block_hash.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderU64

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_hash_at_block_number

    Linear scan of witness.headers; for each entry extract
    its block.number, compare against target, and on first
    match return keccak of that entry.

    Inverse of #7370 (`block_number_at_block_hash`):
      * #7370 takes a hash, returns the number at that hash.
      * THIS takes a number, returns the hash at that number.

    The pairing forms a bridge between block hashes and
    block numbers: caller can translate freely depending on
    which key they have.

    Use cases:
      * EIP-2935 BLOCKHASH opcode emulation against a
        historical chain: caller wants the block_hash at
        height N.
      * Off-chain reconciliation: caller has block heights
        in a log and needs the hashes for downstream
        primitives (#7307 / #7312 / #7333).
      * Chain audit: given a target height, find the
        canonical hash that the witness vouches for.

    Linear scan cost: O(N) hash decodes vs O(N) hashes for
    #7370's K19 approach. Both primitives are O(N) in the
    witness size; the constant factor differs by whether
    we keccak each entry (#7370) or RLP-decode item 8 of
    each entry (this).

    Calling convention (4 args):
      a0 (input)  : block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte block_hash out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (block_hash written)
        1 = no header in witness.headers has that number
        2 = some header could not be RLP-decoded for its
            number field (the scan continues past parse
            failures but propagates status 2 if no match
            is found among the parseable entries)
-/
def blockHashAtBlockNumberFunction : String :=
  "block_hash_at_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target block_number\n" ++
  "  mv s1, a1                  # section ptr\n" ++
  "  mv s2, a2                  # section_len\n" ++
  "  mv s3, a3                  # block_hash out (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3)\n" ++
  "  sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li s7, 0                   # saw_parse_fail flag\n" ++
  "  beqz s2, .Lbhbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lbhbn_loop:\n" ++
  "  beq s5, s4, .Lbhbn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # el_i_start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lbhbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lbhbn_have_end\n" ++
  ".Lbhbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lbhbn_have_end:\n" ++
  "  sub s8, t4, s6             # el_i_len\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s8\n" ++
  "  la a2, bhbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lbhbn_parse_fail\n" ++
  "  la t0, bhbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lbhbn_hit\n" ++
  "  j .Lbhbn_step\n" ++
  ".Lbhbn_parse_fail:\n" ++
  "  li s7, 1\n" ++
  ".Lbhbn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lbhbn_loop\n" ++
  ".Lbhbn_hit:\n" ++
  "  # keccak(header bytes) -> block_hash out.\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s8\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lbhbn_ret\n" ++
  ".Lbhbn_finish:\n" ++
  "  bnez s7, .Lbhbn_parse_status\n" ++
  ".Lbhbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbhbn_ret\n" ++
  ".Lbhbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lbhbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_hash_at_block_number`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..40 : block_hash (32 B; zero on miss) -/
def ziskBlockHashAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  ld a0, 16(a6)               # target block_number\n" ++
  "  addi a1, a6, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # block_hash out\n" ++
  "  jal ra, block_hash_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbhbn_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  blockHashAtBlockNumberFunction ++ "\n" ++
  ".Lbhbn_pdone:"

def ziskBlockHashAtBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bhbn_number_scratch:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
