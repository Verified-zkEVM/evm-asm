/-
  EvmAsm.Codegen.Programs.ReceiptsConsensus

  Compose receipt-root and logs-bloom validation from one receipt-list input.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.BloomBlock
import EvmAsm.Codegen.Programs.ReceiptsRootIndexed

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_validate_receipts_consensus_list

    Validate both receipt consensus commitments from a single RLP list of
    already-encoded legacy receipts:
      * header.receipts_root == MPT(indexed(receipts))
      * header.logs_bloom == OR(receipt.logs_bloom)

    The helper first converts the RLP list items into `{ptr, len}` descriptors
    for `block_validate_receipts_root_indexed`, then reuses the original RLP
    list for `block_validate_logs_bloom`.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : receipts_rlp_list ptr
      a3 (input)  : receipts_rlp_list byte length
      ra (input)  : return
      a0 (output) : status
        0 : both helpers succeeded and both predicates matched
        1 : receipts-root helper/list-descriptor failure
        2 : receipts-root mismatch
        3 : logs-bloom helper failure
        4 : logs-bloom mismatch
      a1 (output) : receipts_root predicate bit
      a2 (output) : logs_bloom predicate bit -/
def blockValidateReceiptsConsensusListFunction : String :=
  "block_validate_receipts_consensus_list:\n" ++
  "  addi sp, sp, -72\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # header ptr\n" ++
  "  mv s1, a1                   # header len\n" ++
  "  mv s2, a2                   # receipts list ptr\n" ++
  "  mv s3, a3                   # receipts list len\n" ++
  "  la t0, brcl_root_valid; sd zero, 0(t0)\n" ++
  "  la t0, brcl_bloom_valid; sd zero, 0(t0)\n" ++
  "  # Count list items and build receipt value descriptors.\n" ++
  "  mv a0, s2; mv a1, s3; la a2, brcl_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbrcl_root_fail\n" ++
  "  la t0, brcl_count; ld s4, 0(t0)\n" ++
  "  li t0, 129; bgeu s4, t0, .Lbrcl_root_fail\n" ++
  "  li s5, 0                    # i\n" ++
  "  la s6, brcl_value_descs\n" ++
  ".Lbrcl_desc_loop:\n" ++
  "  beq s5, s4, .Lbrcl_desc_done\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, s5\n" ++
  "  la a3, brcl_offset; la a4, brcl_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbrcl_root_fail\n" ++
  "  la t0, brcl_offset; ld t1, 0(t0); add t2, s2, t1\n" ++
  "  la t0, brcl_length; ld t3, 0(t0)\n" ++
  "  slli t4, s5, 4; add t5, s6, t4\n" ++
  "  sd t2, 0(t5); sd t3, 8(t5)\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lbrcl_desc_loop\n" ++
  ".Lbrcl_desc_done:\n" ++
  "  mv a0, s0; mv a1, s1; la a2, brcl_value_descs; mv a3, s4\n" ++
  "  jal ra, block_validate_receipts_root_indexed\n" ++
  "  bnez a0, .Lbrcl_root_fail\n" ++
  "  la t0, brcl_root_valid; sd a1, 0(t0)\n" ++
  "  beqz a1, .Lbrcl_root_mismatch\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; la a4, brcl_bloom_valid\n" ++
  "  jal ra, block_validate_logs_bloom\n" ++
  "  bnez a0, .Lbrcl_bloom_fail\n" ++
  "  la t0, brcl_bloom_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbrcl_bloom_mismatch\n" ++
  "  li a0, 0\n" ++
  "  j .Lbrcl_ret\n" ++
  ".Lbrcl_root_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbrcl_ret\n" ++
  ".Lbrcl_root_mismatch:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbrcl_ret\n" ++
  ".Lbrcl_bloom_fail:\n" ++
  "  li a0, 3\n" ++
  "  j .Lbrcl_ret\n" ++
  ".Lbrcl_bloom_mismatch:\n" ++
  "  li a0, 4\n" ++
  ".Lbrcl_ret:\n" ++
  "  la t0, brcl_root_valid; ld a1, 0(t0)\n" ++
  "  la t0, brcl_bloom_valid; ld a2, 0(t0)\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 72\n" ++
  "  ret"

/-- `zisk_block_validate_receipts_consensus_list`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : receipts_list_rlp_len
      bytes 16..   : header_rlp || receipts_list_rlp
    Output layout:
      bytes  0.. 8 : status (0..4)
      bytes  8..16 : receipts_root predicate bit
      bytes 16..24 : logs_bloom predicate bit -/
def ziskBlockValidateReceiptsConsensusListPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # header_rlp_len\n" ++
  "  ld a3, 16(a5)               # receipts_list_rlp_len\n" ++
  "  addi a0, a5, 24             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # receipts_list_rlp ptr\n" ++
  "  jal ra, block_validate_receipts_consensus_list\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0); sd a1, 8(t0); sd a2, 16(t0)\n" ++
  "  j .Lbrcl_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptDeleteAccFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  mptStateRootInsFunction ++ "\n" ++
  mptIndexedTrieRootSmallFunction ++ "\n" ++
  headerExtractReceiptsRootFunction ++ "\n" ++
  blockValidateReceiptsRootIndexedFunction ++ "\n" ++
  headerExtractLogsBloomFunction ++ "\n" ++
  receiptExtractLogsBloomFunction ++ "\n" ++
  bloomOrIntoFunction ++ "\n" ++
  bloomEqFunction ++ "\n" ++
  blockLogsBloomFromReceiptsListFunction ++ "\n" ++
  blockValidateLogsBloomFunction ++ "\n" ++
  blockValidateReceiptsConsensusListFunction ++ "\n" ++
  ".Lbrcl_pdone:"

def ziskBlockValidateReceiptsConsensusListDataSection : String :=
  ziskBlockValidateReceiptsRootIndexedDataSection ++ "\n" ++
  ziskBlockValidateLogsBloomDataSection ++ "\n" ++
  ".balign 8\n" ++
  "brcl_count:\n  .zero 8\n" ++
  "brcl_offset:\n  .zero 8\n" ++
  "brcl_length:\n  .zero 8\n" ++
  "brcl_root_valid:\n  .zero 8\n" ++
  "brcl_bloom_valid:\n  .zero 8\n" ++
  "brcl_value_descs:\n  .zero 2048"

def ziskBlockValidateReceiptsConsensusListProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateReceiptsConsensusListPrologue
  dataAsm     := ziskBlockValidateReceiptsConsensusListDataSection
}

end EvmAsm.Codegen
