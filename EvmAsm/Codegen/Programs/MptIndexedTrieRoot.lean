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

/-! ## mpt_indexed_trie_root_one_leaf -- streaming one-leaf transaction trie root

    Specialized path for the common EIP-7934 boundary case where the transaction
    trie has exactly one value. The general MPT insertion path materializes the
    whole leaf node in a fixed 16 KiB scratch buffer; this helper only buffers
    the small RLP prefixes and absorbs the large transaction bytes directly into
    keccak.

    a0 = value ptr, a1 = value len, a2 = out root ptr; returns a0 = 0. -/
def mptIndexedTrieRootOneLeafFunction : String :=
  "mpt_indexed_trie_root_one_leaf:\n" ++
  "  addi sp, sp, -120\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s1, a0                   # value ptr\n" ++
  "  mv s2, a1                   # value len\n" ++
  "  mv s3, a2                   # out root\n" ++
  "  la s0, zk3_state\n" ++
  "  mv t0, s0; li t1, 25\n" ++
  ".Litol_zero:\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Litol_zero\n" ++
  "  li s4, 0                    # current keccak rate offset\n" ++
  "  # Build the RLP encoding prefixes for leaf([8,0], value).\n" ++
  "  li t0, 1\n" ++
  "  bne s2, t0, .Litol_value_has_prefix\n" ++
  "  lbu t1, 0(s1)\n" ++
  "  li t2, 128\n" ++
  "  bltu t1, t2, .Litol_value_single_byte\n" ++
  ".Litol_value_has_prefix:\n" ++
  "  li a0, 0x80\n" ++
  "  mv a1, s2\n" ++
  "  addi a2, sp, 88             # value prefix scratch\n" ++
  "  jal ra, rlp_prefix_to_buffer\n" ++
  "  mv s5, a0                   # value prefix len\n" ++
  "  add s6, s5, s2              # encoded value item len\n" ++
  "  j .Litol_value_len_done\n" ++
  ".Litol_value_single_byte:\n" ++
  "  li s5, 0                    # no RLP string prefix\n" ++
  "  mv s6, s2                   # encoded value item len = 1\n" ++
  ".Litol_value_len_done:\n" ++
  "  addi a1, s6, 3              # list payload: hp item (3) + value item\n" ++
  "  li a0, 0xc0\n" ++
  "  addi a2, sp, 104            # list prefix scratch\n" ++
  "  jal ra, rlp_prefix_to_buffer\n" ++
  "  mv s7, a0                   # list prefix len\n" ++
  "  addi t0, sp, 112            # hp item scratch\n" ++
  "  li t1, 0x82; sb t1, 0(t0)\n" ++
  "  li t1, 0x20; sb t1, 1(t0)\n" ++
  "  li t1, 0x80; sb t1, 2(t0)\n" ++
  "  addi a0, sp, 104; mv a1, s7; jal ra, .Litol_absorb\n" ++
  "  addi a0, sp, 112; li a1, 3; jal ra, .Litol_absorb\n" ++
  "  beqz s5, .Litol_absorb_value\n" ++
  "  addi a0, sp, 88; mv a1, s5; jal ra, .Litol_absorb\n" ++
  ".Litol_absorb_value:\n" ++
  "  mv a0, s1; mv a1, s2; jal ra, .Litol_absorb\n" ++
  "  # keccak padding at the current rate offset.\n" ++
  "  add t0, s0, s4\n" ++
  "  lbu t1, 0(t0); xori t1, t1, 0x01; sb t1, 0(t0)\n" ++
  "  addi t0, s0, 135\n" ++
  "  lbu t1, 0(t0); xori t1, t1, 0x80; sb t1, 0(t0)\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  ld t0,  0(s0); sd t0,  0(s3)\n" ++
  "  ld t0,  8(s0); sd t0,  8(s3)\n" ++
  "  ld t0, 16(s0); sd t0, 16(s3)\n" ++
  "  ld t0, 24(s0); sd t0, 24(s3)\n" ++
  "  li a0, 0\n" ++
  ".Litol_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 120\n" ++
  "  ret\n" ++
  "  # Absorb a0/a1 bytes into zk3_state using LBU so unaligned SSZ values are OK.\n" ++
  ".Litol_absorb:\n" ++
  "  mv s8, a0\n" ++
  "  mv s9, a1\n" ++
  ".Litol_absorb_loop:\n" ++
  "  beqz s9, .Litol_absorb_ret\n" ++
  "  lbu t0, 0(s8)\n" ++
  "  add t1, s0, s4\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  xor t2, t2, t0\n" ++
  "  sb t2, 0(t1)\n" ++
  "  addi s8, s8, 1\n" ++
  "  addi s9, s9, -1\n" ++
  "  addi s4, s4, 1\n" ++
  "  li t3, 136\n" ++
  "  bne s4, t3, .Litol_absorb_loop\n" ++
  "  mv a0, s0\n" ++
  "  .4byte 0x80052073\n" ++
  "  li s4, 0\n" ++
  "  j .Litol_absorb_loop\n" ++
  ".Litol_absorb_ret:\n" ++
  "  ret\n" ++
  "  # rlp_prefix_to_buffer(base, len, out): base is 0x80 or 0xc0.\n" ++
  "rlp_prefix_to_buffer:\n" ++
  "  li t0, 55\n" ++
  "  bgtu a1, t0, .Lrptb_long\n" ++
  "  add t1, a0, a1\n" ++
  "  sb t1, 0(a2)\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lrptb_long:\n" ++
  "  mv t0, a1\n" ++
  "  li t1, 0                    # len(len)\n" ++
  ".Lrptb_count:\n" ++
  "  addi t1, t1, 1\n" ++
  "  srli t0, t0, 8\n" ++
  "  bnez t0, .Lrptb_count\n" ++
  "  addi t2, a0, 55\n" ++
  "  add t2, t2, t1\n" ++
  "  sb t2, 0(a2)\n" ++
  "  li t2, 0                    # output byte index\n" ++
  ".Lrptb_store:\n" ++
  "  beq t2, t1, .Lrptb_done\n" ++
  "  sub t3, t1, t2\n" ++
  "  addi t3, t3, -1\n" ++
  "  slli t3, t3, 3\n" ++
  "  srl t4, a1, t3\n" ++
  "  andi t4, t4, 255\n" ++
  "  add t5, a2, t2\n" ++
  "  sb t4, 1(t5)\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lrptb_store\n" ++
  ".Lrptb_done:\n" ++
  "  addi a0, t1, 1\n" ++
  "  ret"

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
  "  li t0, 1\n" ++
  "  beq s1, t0, .Litr_one_leaf\n" ++
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
  ".Litr_one_leaf:\n" ++
  "  ld a0, 0(s0)                # value ptr\n" ++
  "  ld a1, 8(s0)                # value len\n" ++
  "  mv a2, s2                   # out root\n" ++
  "  jal ra, mpt_indexed_trie_root_one_leaf\n" ++
  "  j .Litr_ret\n" ++
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
  mptIndexedTrieRootOneLeafFunction ++ "\n" ++
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
