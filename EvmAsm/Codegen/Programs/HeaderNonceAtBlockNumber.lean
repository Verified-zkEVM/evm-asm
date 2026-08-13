/-
  EvmAsm.Codegen.Programs.HeaderNonceAtBlockNumber

  Number-keyed `header.nonce` extractor (RLP field 14,
  8 bytes -- the post-merge zero / pre-merge PoW nonce
  field; distinct from `account.nonce`). Composes K233 +
  the existing `header_extract_nonce` (from HeaderU64.lean).

  Third pre-vs-post-merge invariant primitive alongside
  ommers_hash (PR 7598) and difficulty (PR 7604): all three
  must be zero / EMPTY in post-merge witnesses per
  EIP-3675.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderU64

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## header_nonce_at_block_number

    Number-keyed extractor for `header.block.nonce` (RLP
    field 14, 8 bytes). EIP-3675 mandates 0 post-merge.

    DISTINCT FROM `nonce_at_block_number_address`, which
    walks the state trie for `account.nonce`. This one
    pulls the per-header PoW-nonce slot, which has nothing
    to do with accounts.

    Pipeline (composes K233 scan + existing
    header_extract_nonce; no new helpers):
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_nonce -> u64

    Use cases:
      * Post-merge invariant check: header.nonce != 0 in a
        post-merge witness is prima facie invalid.
      * Pre-merge historical surface: extract PoW-nonce for
        ethash-replay primitives.
      * Cross-fork audit: rounds out the merge-boundary
        check triple with ommers_hash (PR 7598) and
        difficulty (PR 7604).

    Calling convention (4 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 header.nonce out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (nonce written; 0 = post-merge)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header nonce extraction failed
            (RLP malformed / field 14 unexpected size)
-/
def headerNonceAtBlockNumberFunction : String :=
  "header_nonce_at_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # header.nonce u64 out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s8, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lhnbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lhnbn_loop:\n" ++
  "  beq s5, s4, .Lhnbn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # header start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lhnbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lhnbn_have_end\n" ++
  ".Lhnbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lhnbn_have_end:\n" ++
  "  sub s7, t4, s6\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, hnbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lhnbn_parse_fail\n" ++
  "  la t0, hnbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lhnbn_hit\n" ++
  "  j .Lhnbn_step\n" ++
  ".Lhnbn_parse_fail:\n" ++
  "  li s8, 1\n" ++
  ".Lhnbn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lhnbn_loop\n" ++
  ".Lhnbn_hit:\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_nonce\n" ++
  "  beqz a0, .Lhnbn_ret\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lhnbn_ret\n" ++
  ".Lhnbn_finish:\n" ++
  "  bnez s8, .Lhnbn_parse_status\n" ++
  ".Lhnbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhnbn_ret\n" ++
  ".Lhnbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lhnbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_header_nonce_at_block_number`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : header.nonce (u64; 0 on failure or post-merge) -/
def ziskHeaderNonceAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a0, 16(t4)               # target_block_number\n" ++
  "  addi a1, t4, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # u64 header.nonce out\n" ++
  "  jal ra, header_nonce_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhnbn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractNonceFunction ++ "\n" ++
  headerNonceAtBlockNumberFunction ++ "\n" ++
  ".Lhnbn_pdone:"

def ziskHeaderNonceAtBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "hen_offset:\n" ++
  "  .zero 8\n" ++
  "hen_length:\n" ++
  "  .zero 8\n" ++
  "hnbn_number_scratch:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
