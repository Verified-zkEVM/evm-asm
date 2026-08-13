/-
  EvmAsm.Codegen.Programs.ReceiptsRootAtBlockNumber

  Number-keyed `header.receipts_root` extractor (RLP field
  5, 32 bytes). Composes K233 + the existing
  `header_extract_receipts_root` (from HeaderFields.lean).

  Companion to `transactions_root_at_block_number` (#7560).
  Together they commit to both the tx-trie and receipt-trie
  for a historical block, enabling future tx-inclusion +
  receipt-inclusion proofs.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## receipts_root_at_block_number

    Number-keyed extractor for
    `header.block.receipts_root` (RLP field 5, 32 bytes).

    Pipeline (composes K233 scan + existing
    header_extract_receipts_root; no new helpers):
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_receipts_root -> 32 B

    Use cases:
      * Receipt-trie attestation: caller has an external
        merkle root for the block's receipts; verify it
        matches the on-chain root.
      * Empty-block detection: when receipts_root ==
        EMPTY_TRIE_ROOT, the block has no transactions.
      * Future receipt-inclusion proofs (e.g., for an L2
        light-client proving a deposit happened): pair
        with the existing MPT walk primitives.
      * Bloom-cross-check: combined with the
        block-logs-bloom validation primitives, verifies
        that bloom is consistent with the receipts trie.

    Calling convention (4 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte receipts_root out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (receipts_root written)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header receipts_root extraction failed
            (RLP malformed / field 5 size != 32)
-/
def receiptsRootAtBlockNumberFunction : String :=
  "receipts_root_at_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # receipts_root out (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li s8, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lrrbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lrrbn_loop:\n" ++
  "  beq s5, s4, .Lrrbn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # header start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lrrbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lrrbn_have_end\n" ++
  ".Lrrbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lrrbn_have_end:\n" ++
  "  sub s7, t4, s6\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, rrbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lrrbn_parse_fail\n" ++
  "  la t0, rrbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lrrbn_hit\n" ++
  "  j .Lrrbn_step\n" ++
  ".Lrrbn_parse_fail:\n" ++
  "  li s8, 1\n" ++
  ".Lrrbn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lrrbn_loop\n" ++
  ".Lrrbn_hit:\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_receipts_root\n" ++
  "  beqz a0, .Lrrbn_ret\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lrrbn_ret\n" ++
  ".Lrrbn_finish:\n" ++
  "  bnez s8, .Lrrbn_parse_status\n" ++
  ".Lrrbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lrrbn_ret\n" ++
  ".Lrrbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lrrbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_receipts_root_at_block_number`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..40 : receipts_root (32 B; 0 on failure) -/
def ziskReceiptsRootAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a0, 16(t4)               # target_block_number\n" ++
  "  addi a1, t4, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 32 B receipts_root out\n" ++
  "  jal ra, receipts_root_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lrrbn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractReceiptsRootFunction ++ "\n" ++
  receiptsRootAtBlockNumberFunction ++ "\n" ++
  ".Lrrbn_pdone:"

def ziskReceiptsRootAtBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "herr_offset:\n" ++
  "  .zero 8\n" ++
  "herr_length:\n" ++
  "  .zero 8\n" ++
  "rrbn_number_scratch:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
