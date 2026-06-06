/-
  EvmAsm.Codegen.Programs.BloomBlock

  Block-level logs-bloom composites split from Bloom.lean. The atomic
  bloom helpers stay in Bloom.lean; this module composes them over receipt
  lists and header validation.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## block_logs_bloom_from_receipts_list -- PR-K158

    Given an RLP-encoded list of receipts, compute the block-level
    `logs_bloom` by OR-accumulating each receipt's `logs_bloom`
    field. End-to-end composite tying together the four atomic
    bloom helpers shipped in PR-K151..K154:

      bzero(block_bloom)
      for receipt in receipts:
        receipt_extract_logs_bloom(receipt, scratch)   # K152
        bloom_or_into(block_bloom, scratch)            # K151

    Used by `block_validate_logs_bloom` (combined with K153 to
    extract the header's claimed bloom and K154 to compare).

    Empty receipts list (`0xc0`) is valid and leaves the output
    bloom untouched. Per-receipt parse failures propagate via the
    return code.

    Composes:
      - PR-K20 `rlp_list_nth_item`       -- walk each receipt
      - PR-K47 `rlp_list_count_items`    -- list cardinality
      - PR-K152 `receipt_extract_logs_bloom`
      - PR-K151 `bloom_or_into`

    Calling convention:
      a0 (input)  : receipts_rlp_list ptr (RLP list of receipts)
      a1 (input)  : receipts_rlp_list byte length
      a2 (input)  : 256-byte output bloom ptr
                    (mutable, caller zero-inits)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure (outer list malformed or a
            receipt isn't a proper RLP list)
        2 : a receipt's `logs_bloom` field length != 256 -/
def blockLogsBloomFromReceiptsListFunction : String :=
  "block_logs_bloom_from_receipts_list:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # receipts list ptr\n" ++
  "  mv s1, a1                   # receipts list len\n" ++
  "  mv s2, a2                   # output bloom ptr\n" ++
  "  # ---- Count receipts ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, blbr_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lblbr_parse_fail\n" ++
  "  la t0, blbr_count; ld s3, 0(t0)              # n_receipts\n" ++
  "  li s4, 0                                     # i\n" ++
  ".Lblbr_loop:\n" ++
  "  bge s4, s3, .Lblbr_done\n" ++
  "  # Extract receipt_i bounds (full encoded item).\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s4\n" ++
  "  la a3, blbr_offset; la a4, blbr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lblbr_parse_fail\n" ++
  "  la t0, blbr_offset; ld t1, 0(t0)\n" ++
  "  la t0, blbr_length; ld t2, 0(t0)\n" ++
  "  add a0, s0, t1                                # receipt_i ptr\n" ++
  "  mv a1, t2                                    # receipt_i len\n" ++
  "  la a2, blbr_scratch_bloom\n" ++
  "  jal ra, receipt_extract_logs_bloom\n" ++
  "  bnez a0, .Lblbr_child_err                    # 1 or 2 -> propagate\n" ++
  "  # OR scratch_bloom into output bloom.\n" ++
  "  mv a0, s2\n" ++
  "  la a1, blbr_scratch_bloom\n" ++
  "  jal ra, bloom_or_into\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lblbr_loop\n" ++
  ".Lblbr_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lblbr_ret\n" ++
  ".Lblbr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lblbr_ret\n" ++
  ".Lblbr_child_err:\n" ++
  "  # a0 carries the child's status (1 = parse fail, 2 = size fail).\n" ++
  ".Lblbr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_logs_bloom_from_receipts_list`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : receipts_list_rlp_len
      bytes  8..   : receipts_list_rlp
    Output layout (256 B, ziskemu cap):
      bytes  0..256 : accumulated logs_bloom (zero-initialised
                       by the probe before invoking the helper). -/
def ziskBlockLogsBloomFromReceiptsListPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # receipts_list_rlp_len\n" ++
  "  addi a0, a3, 16             # receipts_list_rlp ptr\n" ++
  "  li a2, 0xa0010000           # output bloom ptr (256 B)\n" ++
  "  # Zero output bloom (32 × sd zero).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 32\n" ++
  ".Lblbr_zero_loop:\n" ++
  "  beqz t1, .Lblbr_zero_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lblbr_zero_loop\n" ++
  ".Lblbr_zero_done:\n" ++
  "  jal ra, block_logs_bloom_from_receipts_list\n" ++
  "  j .Lblbr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  receiptExtractLogsBloomFunction ++ "\n" ++
  bloomOrIntoFunction ++ "\n" ++
  blockLogsBloomFromReceiptsListFunction ++ "\n" ++
  ".Lblbr_pdone:"

def ziskBlockLogsBloomFromReceiptsListDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "relb_offset:\n" ++
  "  .zero 8\n" ++
  "relb_length:\n" ++
  "  .zero 8\n" ++
  "blbr_count:\n" ++
  "  .zero 8\n" ++
  "blbr_offset:\n" ++
  "  .zero 8\n" ++
  "blbr_length:\n" ++
  "  .zero 8\n" ++
  "blbr_scratch_bloom:\n" ++
  "  .zero 256"

def ziskBlockLogsBloomFromReceiptsListProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockLogsBloomFromReceiptsListPrologue
  dataAsm     := ziskBlockLogsBloomFromReceiptsListDataSection
}

/-! ## block_validate_logs_bloom -- PR-K159

    End-to-end block-level `logs_bloom` validation: given the
    header RLP and the RLP list of receipts, recompute the
    block's bloom from receipts and check it byte-equals the
    header's claimed bloom.

      header_bloom = header_extract_logs_bloom(header_rlp)
      computed_bloom = block_logs_bloom_from_receipts_list(receipts)
      is_valid = bloom_eq(header_bloom, computed_bloom)

    Single-call entry point for callers that want the verdict
    without managing the scratch buffers themselves. The verdict
    is returned via an out pointer (1 if valid, 0 if not).

    Composes:
      - PR-K153 `header_extract_logs_bloom`        -- read header
      - PR-K158 `block_logs_bloom_from_receipts_list` -- recompute
      - PR-K154 `bloom_eq`                          -- compare

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : receipts_rlp_list ptr
      a3 (input)  : receipts_rlp_list byte length
      a4 (input)  : u64 out ptr (is_valid: 1 if matches, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : helpers succeeded -- predicate written
        1 : header parse failure / bloom field width != 256
        2 : receipts-list parse failure or receipt size failure
            (child status from PR-K158 propagated unchanged) -/
def blockValidateLogsBloomFunction : String :=
  "block_validate_logs_bloom:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # receipts list ptr\n" ++
  "  mv s3, a3                   # receipts list len\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  # ---- Extract header.logs_bloom into bvlb_header_bloom ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, bvlb_header_bloom\n" ++
  "  jal ra, header_extract_logs_bloom\n" ++
  "  bnez a0, .Lbvlb_header_fail\n" ++
  "  # ---- Zero bvlb_computed_bloom (256 B) ----\n" ++
  "  la t0, bvlb_computed_bloom\n" ++
  "  li t1, 32\n" ++
  ".Lbvlb_zero:\n" ++
  "  beqz t1, .Lbvlb_zero_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lbvlb_zero\n" ++
  ".Lbvlb_zero_done:\n" ++
  "  # ---- Compute block bloom from receipts list ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, bvlb_computed_bloom\n" ++
  "  jal ra, block_logs_bloom_from_receipts_list\n" ++
  "  bnez a0, .Lbvlb_receipts_fail\n" ++
  "  # ---- Compare the two blooms ----\n" ++
  "  la a0, bvlb_header_bloom\n" ++
  "  la a1, bvlb_computed_bloom\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, bloom_eq\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvlb_ret\n" ++
  ".Lbvlb_header_fail:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvlb_ret\n" ++
  ".Lbvlb_receipts_fail:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 2\n" ++
  ".Lbvlb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_validate_logs_bloom`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : receipts_list_rlp_len
      bytes 16..   : header_rlp || receipts_list_rlp
        (the script appends them with no padding between; the
         prologue computes the second pointer from the first
         length).
    Output layout:
      bytes  0.. 8 : status (0=ok, 1=header fail, 2=receipts fail)
      bytes  8..16 : is_valid (1 if bloom matches, 0 otherwise) -/
def ziskBlockValidateLogsBloomPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # header_rlp_len\n" ++
  "  ld a3, 16(a5)               # receipts_list_rlp_len\n" ++
  "  addi a0, a5, 24             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # receipts_list_rlp ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_logs_bloom\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvlb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  headerExtractLogsBloomFunction ++ "\n" ++
  receiptExtractLogsBloomFunction ++ "\n" ++
  bloomOrIntoFunction ++ "\n" ++
  bloomEqFunction ++ "\n" ++
  blockLogsBloomFromReceiptsListFunction ++ "\n" ++
  blockValidateLogsBloomFunction ++ "\n" ++
  ".Lbvlb_pdone:"

def ziskBlockValidateLogsBloomDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "helb_offset:\n" ++
  "  .zero 8\n" ++
  "helb_length:\n" ++
  "  .zero 8\n" ++
  "relb_offset:\n" ++
  "  .zero 8\n" ++
  "relb_length:\n" ++
  "  .zero 8\n" ++
  "blbr_count:\n" ++
  "  .zero 8\n" ++
  "blbr_offset:\n" ++
  "  .zero 8\n" ++
  "blbr_length:\n" ++
  "  .zero 8\n" ++
  "blbr_scratch_bloom:\n" ++
  "  .zero 256\n" ++
  "bvlb_header_bloom:\n" ++
  "  .zero 256\n" ++
  "bvlb_computed_bloom:\n" ++
  "  .zero 256"

def ziskBlockValidateLogsBloomProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateLogsBloomPrologue
  dataAsm     := ziskBlockValidateLogsBloomDataSection
}

end EvmAsm.Codegen
