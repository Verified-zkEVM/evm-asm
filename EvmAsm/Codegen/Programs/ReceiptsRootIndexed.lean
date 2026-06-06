/-
  EvmAsm.Codegen.Programs.ReceiptsRootIndexed

  Standalone block-level receipts_root validator backed by the generic indexed
  trie builder. This extends the old fixed one- and two-receipt probes to the
  descriptor-array shape used by real blocks.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.MptIndexedTrieRoot

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_validate_receipts_root_indexed

    Validate `header.receipts_root` against the MPT root of an indexed list of
    already-encoded receipts. Keys are `rlp(0)..rlp(N-1)` and root computation
    is delegated to `mpt_indexed_trie_root_small`, currently supporting
    `N <= 128`.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : receipt value descriptor array ptr, entries `{ptr:u64, len:u64}`
      a3 (input)  : number of receipts
      ra (input)  : return
      a0 (output) : status
        0 : success -- predicate returned in a1
        1 : header RLP parse failure / field 5 missing
        2 : header.receipts_root length != 32
        3 : indexed trie builder failure
      a1 (output) : 1 iff the extracted root equals the computed root -/
def blockValidateReceiptsRootIndexedFunction : String :=
  "block_validate_receipts_root_indexed:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # value descriptors\n" ++
  "  mv s3, a3                   # n receipts\n" ++
  "  # ---- Extract header.receipts_root (field 5) ----\n" ++
  "  mv a0, s0; mv a1, s1; la a2, bvrri_expected_root\n" ++
  "  jal ra, header_extract_receipts_root\n" ++
  "  bnez a0, .Lbvrri_header_fail\n" ++
  "  # ---- Compute indexed receipts trie root ----\n" ++
  "  mv a0, s2; mv a1, s3; la a2, bvrri_computed_root\n" ++
  "  jal ra, mpt_indexed_trie_root_small\n" ++
  "  bnez a0, .Lbvrri_trie_fail\n" ++
  "  la t0, bvrri_expected_root\n" ++
  "  la t1, bvrri_computed_root\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lbvrri_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lbvrri_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbvrri_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbvrri_neq\n" ++
  "  li a0, 0\n" ++
  "  li a1, 1\n" ++
  "  j .Lbvrri_ret\n" ++
  ".Lbvrri_neq:\n" ++
  "  li a0, 0\n" ++
  "  li a1, 0\n" ++
  "  j .Lbvrri_ret\n" ++
  ".Lbvrri_header_fail:\n" ++
  "  li a1, 0\n" ++
  "  j .Lbvrri_ret\n" ++
  ".Lbvrri_trie_fail:\n" ++
  "  li a0, 3\n" ++
  "  li a1, 0\n" ++
  ".Lbvrri_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_validate_receipts_root_indexed`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : number of receipts
      bytes 16..   : receipt_len table (u64 each)
                      header_rlp
                      receipt blobs, each 8-byte aligned
    Output layout:
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : is_valid -/
def ziskBlockValidateReceiptsRootIndexedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # header_rlp_len\n" ++
  "  ld s2, 16(s0)               # n receipts\n" ++
  "  addi s3, s0, 24             # length table\n" ++
  "  slli t0, s2, 3; add s4, s3, t0   # header_rlp ptr\n" ++
  "  add s5, s4, s1              # receipt blob cursor\n" ++
  "  addi s5, s5, 7; andi s5, s5, -8\n" ++
  "  la s6, bvrri_value_descs\n" ++
  "  li s7, 129\n" ++
  "  bgeu s2, s7, .Lbvrri_pdesc_done\n" ++
  "  li s8, 0                    # i\n" ++
  ".Lbvrri_pdesc_loop:\n" ++
  "  beq s8, s2, .Lbvrri_pdesc_done\n" ++
  "  slli t1, s8, 3; add t2, s3, t1; ld t3, 0(t2)\n" ++
  "  slli t4, s8, 4; add t5, s6, t4\n" ++
  "  sd s5, 0(t5); sd t3, 8(t5)\n" ++
  "  add s5, s5, t3\n" ++
  "  addi s5, s5, 7; andi s5, s5, -8\n" ++
  "  addi s8, s8, 1\n" ++
  "  j .Lbvrri_pdesc_loop\n" ++
  ".Lbvrri_pdesc_done:\n" ++
  "  mv a0, s4; mv a1, s1; la a2, bvrri_value_descs; mv a3, s2\n" ++
  "  jal ra, block_validate_receipts_root_indexed\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0); sd a1, 8(t0)\n" ++
  "  j .Lbvrri_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
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
  ".Lbvrri_pdone:"

def ziskBlockValidateReceiptsRootIndexedDataSection : String :=
  ziskMptIndexedTrieRootSmallDataSection ++ "\n" ++
  ".balign 8\n" ++
  "herr_offset:\n  .zero 8\n" ++
  "herr_length:\n  .zero 8\n" ++
  "bvrri_expected_root:\n  .zero 32\n" ++
  "bvrri_computed_root:\n  .zero 32\n" ++
  "bvrri_value_descs:\n  .zero 2048"

def ziskBlockValidateReceiptsRootIndexedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateReceiptsRootIndexedPrologue
  dataAsm     := ziskBlockValidateReceiptsRootIndexedDataSection
}

end EvmAsm.Codegen
