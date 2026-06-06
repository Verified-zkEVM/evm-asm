/-
  EvmAsm.Codegen.Programs.MptIndexedTrieRoot

  Build an MPT root from an indexed list of values by inserting keys
  rlp(0), rlp(1), ... from an initially empty trie. This first slice supports
  compact one-byte RLP indices 0..127 and delegates the trie mutation work to
  the existing insert-aware state-root driver.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptStateRootIns

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_indexed_trie_root_small -- indexed trie builder for indices < 128

    a0 = value descriptor array ptr, entries `{ptr:u64, len:u64}`
    a1 = number of values, must be <= 128
    a2 = out root ptr
    a0 (output) = 0 ok / 1 too many values / sub-status from mpt_state_root_ins.

    Each key is encoded as the nibble path of RLP(index):
      index 0    -> RLP 0x80 -> nibbles [8,0]
      index 1..127 -> single byte -> nibbles [hi,lo]
-/
def mptIndexedTrieRootSmallFunction : String :=
  "mpt_indexed_trie_root_small:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # value descriptors\n" ++
  "  mv s1, a1                   # n values\n" ++
  "  mv s2, a2                   # out root\n" ++
  "  li t0, 129\n" ++
  "  bgeu s1, t0, .Litr_fail\n" ++
  "  li s3, 0                    # i\n" ++
  ".Litr_build_loop:\n" ++
  "  beq s3, s1, .Litr_build_done\n" ++
  "  slli t0, s3, 4; add t0, s0, t0     # &value_desc[i]\n" ++
  "  ld t1, 0(t0)                       # value ptr\n" ++
  "  ld t2, 8(t0)                       # value len\n" ++
  "  slli t3, s3, 1; la t4, itr_paths; add t4, t4, t3\n" ++
  "  beqz s3, .Litr_key_zero\n" ++
  "  srli t5, s3, 4\n" ++
  "  andi t6, s3, 15\n" ++
  "  sb t5, 0(t4); sb t6, 1(t4)\n" ++
  "  j .Litr_key_done\n" ++
  ".Litr_key_zero:\n" ++
  "  li t5, 8; sb t5, 0(t4); sb zero, 1(t4)\n" ++
  ".Litr_key_done:\n" ++
  "  slli t5, s3, 5; slli t6, s3, 3; add t5, t5, t6\n" ++
  "  la s4, itr_changes; add s4, s4, t5\n" ++
  "  sd t4, 0(s4)                # path ptr\n" ++
  "  li t5, 2; sd t5, 8(s4)      # path len\n" ++
  "  sd t1, 16(s4)               # value ptr\n" ++
  "  sd t2, 24(s4)               # value len\n" ++
  "  li t5, 1; sd t5, 32(s4)     # mode = insert\n" ++
  "  addi s3, s3, 1\n" ++
  "  j .Litr_build_loop\n" ++
  ".Litr_build_done:\n" ++
  "  la a0, iw_empty_trie_root\n" ++
  "  la a1, itr_empty_witness\n" ++
  "  li a2, 0\n" ++
  "  la a3, itr_changes\n" ++
  "  mv a4, s1\n" ++
  "  mv a5, s2\n" ++
  "  jal ra, mpt_state_root_ins\n" ++
  "  j .Litr_ret\n" ++
  ".Litr_fail:\n" ++
  "  li a0, 1\n" ++
  ".Litr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskMptIndexedTrieRootSmallPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld s0, 8(t0)                # n values\n" ++
  "  addi s1, t0, 16             # length table\n" ++
  "  slli s2, s0, 3; add s2, s1, s2   # blob cursor\n" ++
  "  la s3, itr_value_descs\n" ++
  "  li s4, 0                    # i\n" ++
  ".Litrp_desc_loop:\n" ++
  "  beq s4, s0, .Litrp_desc_done\n" ++
  "  slli t1, s4, 3; add t2, s1, t1; ld t3, 0(t2)    # len[i]\n" ++
  "  slli t4, s4, 4; add t5, s3, t4\n" ++
  "  sd s2, 0(t5); sd t3, 8(t5)\n" ++
  "  add s2, s2, t3\n" ++
  "  addi s2, s2, 7; andi s2, s2, -8\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Litrp_desc_loop\n" ++
  ".Litrp_desc_done:\n" ++
  "  la a0, itr_value_descs\n" ++
  "  mv a1, s0\n" ++
  "  li a2, 0xa0010000\n" ++
  "  jal ra, mpt_indexed_trie_root_small\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)\n" ++
  "  j .Litrp_done\n" ++
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
  ".Litrp_done:"

def ziskMptIndexedTrieRootSmallDataSection : String :=
  ziskMptStateRootInsDataSection ++ "\n" ++
  ".balign 8\n" ++
  "itr_empty_witness:\n  .zero 8\n" ++
  "itr_value_descs:\n  .zero 2048\n" ++
  "itr_paths:\n  .zero 256\n" ++
  "itr_changes:\n  .zero 8192"

def ziskMptIndexedTrieRootSmallProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptIndexedTrieRootSmallPrologue
  dataAsm     := ziskMptIndexedTrieRootSmallDataSection
}

end EvmAsm.Codegen
