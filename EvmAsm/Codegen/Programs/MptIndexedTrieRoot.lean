/-
  EvmAsm.Codegen.Programs.MptIndexedTrieRoot

  Build an MPT root from an indexed list of values by inserting keys
  rlp(0), rlp(1), ... from an initially empty trie. The generic path supports
  indices 0..255 and delegates the trie mutation work to the existing
  insert-aware state-root driver.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.MptStateRootIns
import EvmAsm.Codegen.Programs.MptBoundedSort

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_indexed_trie_root_small -- indexed trie builder for indices <= 255

    a0 = value descriptor array ptr, entries `{ptr:u64, len:u64}`
    a1 = number of values, must be <= 256
    a2 = out root ptr
    a0 (output) = 0 ok / 1 too many values / sub-status from mpt_state_root_ins.

    Each key is encoded as the nibble path of RLP(index):
      index 0    -> RLP 0x80 -> nibbles [8,0]
      index 1..127 -> single byte -> nibbles [hi,lo]
      index 128..255 -> bytes 0x81 index -> nibbles [8,1,hi,lo]
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


/-! ## mpt_indexed_stream_leaf_hash -- arbitrary shallow indexed-key leaf

    Hash `rlp([hp(path, leaf=true), value])` without materialising `value`.
    Indexed keys up to the 200M-gas transaction bound have at most six
    nibbles.  The input value is absorbed directly into Keccak, so a valid
    near-`MAX_RLP_BLOCK_SIZE` transaction never reaches `mset_node` or the
    legacy leaf scratch.

    Callers use this only after proving the encoded leaf is at least 32 bytes;
    shorter leaves are represented inline by the bounded builder.

    a0=path nibbles, a1=path length (<=6), a2=value, a3=value length,
    a4=out hash. Returns 0 on success, 1 on an out-of-domain path. -/
def mptIndexedStreamLeafHashFunction : String :=
  "mpt_indexed_stream_leaf_hash:\n" ++
  "  addi sp, sp, -176\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s1, a0; mv s2, a1; mv s3, a2; mv s4, a3; mv s5, a4; li t0, 6; bgtu s2, t0, .Lmislh_fail; li t0, 27; bltu s4, t0, .Lmislh_fail\n" ++
  "  mv a0, s1; mv a1, s2; li a2, 1; addi a3, sp, 88; jal ra, hp_encode_nibbles; mv s7, a0\n" ++
  "  addi a0, sp, 88; mv a1, s7; addi a2, sp, 96; addi a3, sp, 144; jal ra, rlp_encode_bytes; ld s7, 144(sp)\n" ++
  "  li t0, 1; bne s4, t0, .Lmislh_value_prefix; lbu t1, 0(s3); li t2, 128; bgeu t1, t2, .Lmislh_value_prefix; li s8, 0; j .Lmislh_value_ready\n" ++
  ".Lmislh_value_prefix:\n" ++
  "  li a0, 0x80; mv a1, s4; addi a2, sp, 112; jal ra, rlp_prefix_to_buffer; mv s8, a0\n" ++
  ".Lmislh_value_ready:\n" ++
  "  add t0, s7, s8; add a1, t0, s4; li a0, 0xc0; addi a2, sp, 128; jal ra, rlp_prefix_to_buffer; mv s9, a0\n" ++
  "  la s0, zk3_state; mv t0, s0; li t1, 25\n" ++
  ".Lmislh_zero:\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lmislh_zero\n" ++
  "  li s6, 0; addi a0, sp, 128; mv a1, s9; jal ra, .Lmislh_absorb; addi a0, sp, 96; mv a1, s7; jal ra, .Lmislh_absorb; beqz s8, .Lmislh_value\n" ++
  "  addi a0, sp, 112; mv a1, s8; jal ra, .Lmislh_absorb\n" ++
  ".Lmislh_value:\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, .Lmislh_absorb; add t0, s0, s6; lbu t1, 0(t0); xori t1, t1, 0x01; sb t1, 0(t0); addi t0, s0, 135; lbu t1, 0(t0); xori t1, t1, 0x80; sb t1, 0(t0); mv a0, s0; .4byte 0x80052073\n" ++
  "  ld t0, 0(s0); sd t0, 0(s5); ld t0, 8(s0); sd t0, 8(s5); ld t0, 16(s0); sd t0, 16(s5); ld t0, 24(s0); sd t0, 24(s5); li a0, 0; j .Lmislh_ret\n" ++
  ".Lmislh_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lmislh_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); addi sp, sp, 176; ret\n" ++
  ".Lmislh_absorb:\n" ++
  "  beqz a1, .Lmislh_absorb_ret; lbu t0, 0(a0); add t1, s0, s6; lbu t2, 0(t1); xor t2, t2, t0; sb t2, 0(t1); addi a0, a0, 1; addi a1, a1, -1; addi s6, s6, 1; li t3, 136; bne s6, t3, .Lmislh_absorb; sd a0, 160(sp); sd a1, 168(sp); mv a0, s0; .4byte 0x80052073; ld a0, 160(sp); ld a1, 168(sp); li s6, 0; j .Lmislh_absorb\n" ++
  ".Lmislh_absorb_ret:\n" ++
  "  ret"

/-! ## `mpt_indexed_sort_changes` -- lexicographic MSD sort for RLP indices

    Indexed trie keys are RLP encodings, not numeric byte strings: in
    particular `rlp(0)=0x80` sorts after 127 and before 128.  The bounded
    indexed builder therefore sorts the generated nibble paths before its
    depth-first construction.  Descriptors have the same 40-byte layout as
    the state-root builder (`path, path_len, value, value_len, mode`), but
    paths are 2, 4, or 6 nibbles long.  A key that ends at a partition depth
    is necessarily a singleton for canonical RLP integer keys, so no
    terminator bucket is needed.

    Both the descriptor count and the pending range stack are bounded by the
    explicit gas-derived entry capacity / maximum key depth. -/
def mptIndexedSortChangesFunction : String :=
  "mpt_indexed_sort_changes:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  li t0, " ++ toString itrIndexedEntryCapacity ++ "; bgtu a1, t0, .Lmis_fail; mv s0, a0; mv s1, a1; li s4, 0\n" ++
  ".Lmis_validate_rec:\n" ++
  "  beq s4, s1, .Lmis_validated; slli t0, s4, 5; slli t1, s4, 3; add t0, t0, t1; add t0, s0, t0; ld t2, 0(t0); ld t3, 8(t0); li t4, 2; bltu t3, t4, .Lmis_fail; li t4, " ++ toString itrIndexedKeyMaxNibbles ++ "; bgtu t3, t4, .Lmis_fail; andi t4, t3, 1; bnez t4, .Lmis_fail; li s5, 0\n" ++
  ".Lmis_validate_nibble:\n" ++
  "  beq s5, t3, .Lmis_validate_next; add t4, t2, s5; lbu t5, 0(t4); li t4, 16; bgeu t5, t4, .Lmis_fail; addi s5, s5, 1; j .Lmis_validate_nibble\n" ++
  ".Lmis_validate_next:\n" ++
  "  addi s4, s4, 1; j .Lmis_validate_rec\n" ++
  ".Lmis_validated:\n" ++
  "  la s2, itr_sort_ranges; li s3, 0; beqz s1, .Lmis_ok; sd zero, 0(s2); sd s1, 8(s2); sd zero, 16(s2); sd zero, 24(s2); li s3, 1\n" ++
  ".Lmis_pop:\n" ++
  "  beqz s3, .Lmis_ok; addi s3, s3, -1; slli t0, s3, 5; add t0, s2, t0; ld s4, 0(t0); ld s5, 8(t0); ld s6, 16(t0); addi t1, s4, 1; bgeu t1, s5, .Lmis_pop; li t1, " ++ toString itrIndexedKeyMaxNibbles ++ "; bgeu s6, t1, .Lmis_pop; mv s7, s4; li t6, 0\n" ++
  ".Lmis_digit:\n" ++
  "  li t0, 16; beq t6, t0, .Lmis_pop; mv t1, s7\n" ++
  ".Lmis_scan:\n" ++
  "  beq t1, s5, .Lmis_group; slli t0, t1, 5; slli t2, t1, 3; add t0, t0, t2; add t0, s0, t0; ld t2, 0(t0); ld t3, 8(t0); bgeu s6, t3, .Lmis_fail; add t2, t2, s6; lbu t3, 0(t2); li t4, 16; bgeu t3, t4, .Lmis_fail; bne t3, t6, .Lmis_scan_next; beq t1, s7, .Lmis_scan_match; slli t2, s7, 5; slli t3, s7, 3; add t2, t2, t3; add t2, s0, t2; la t3, itr_sort_scratch; li t4, 5\n" ++
  ".Lmis_swap:\n" ++
  "  ld t5, 0(t0); sd t5, 0(t3); ld t5, 0(t2); sd t5, 0(t0); ld t5, 0(t3); sd t5, 0(t2); addi t0, t0, 8; addi t2, t2, 8; addi t3, t3, 8; addi t4, t4, -1; bnez t4, .Lmis_swap\n" ++
  ".Lmis_scan_match:\n" ++
  "  addi s7, s7, 1\n" ++
  ".Lmis_scan_next:\n" ++
  "  addi t1, t1, 1; j .Lmis_scan\n" ++
  ".Lmis_group:\n" ++
  "  addi t0, s4, 1; bgeu t0, s7, .Lmis_digit_next; li t0, " ++ toString itrIndexedSortRangeStackCapacity ++ "; bgeu s3, t0, .Lmis_fail; slli t0, s3, 5; add t0, s2, t0; sd s4, 0(t0); sd s7, 8(t0); addi t1, s6, 1; sd t1, 16(t0); sd zero, 24(t0); addi s3, s3, 1\n" ++
  ".Lmis_digit_next:\n" ++
  "  mv s4, s7; addi t6, t6, 1; j .Lmis_digit\n" ++
  ".Lmis_fail:\n  li a0, 1; j .Lmis_ret\n" ++
  ".Lmis_ok:\n  li a0, 0\n" ++
  ".Lmis_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 96; ret"

/-! Construct one canonical raw child reference for an indexed-trie leaf.
    Small values use the regular encoder into a fixed 1 KiB structural scratch;
    every value at least 27 bytes uses the streaming helper, so no transaction
    or receipt payload is copied into an MPT buffer. -/
def mptIndexedLeafRefFunction : String :=
  "mpt_indexed_leaf_ref:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; sd zero, 0(s5); li t0, " ++ toString itrIndexedKeyMaxNibbles ++ "; bgtu s1, t0, .Lmilr_fail; li t0, 27; bgeu s3, t0, .Lmilr_stream\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; la a4, itr_builder_node; la a5, itr_builder_node_len; jal ra, mpt_leaf_node_encode_from_nibbles; bnez a0, .Lmilr_fail; la t0, itr_builder_node_len; ld t1, 0(t0); li t2, 32; bgeu t1, t2, .Lmilr_small_hash; la t0, itr_builder_node; mv t2, s4\n" ++
  ".Lmilr_copy:\n" ++
  "  beqz t1, .Lmilr_inline_ok; lbu t3, 0(t0); sb t3, 0(t2); addi t0, t0, 1; addi t2, t2, 1; addi t1, t1, -1; j .Lmilr_copy\n" ++
  ".Lmilr_inline_ok:\n" ++
  "  la t0, itr_builder_node_len; ld t1, 0(t0); sd t1, 0(s5); li a0, 0; j .Lmilr_ret\n" ++
  ".Lmilr_small_hash:\n" ++
  "  la a0, itr_builder_node; mv a1, t1; mv a2, s4; jal ra, zkvm_keccak256; li t0, 32; sd t0, 0(s5); li a0, 0; j .Lmilr_ret\n" ++
  ".Lmilr_stream:\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s4; jal ra, mpt_indexed_stream_leaf_hash; bnez a0, .Lmilr_fail; li t0, 32; sd t0, 0(s5); li a0, 0; j .Lmilr_ret\n" ++
  ".Lmilr_fail:\n  li a0, 1\n" ++
  ".Lmilr_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 64; ret"

/-! Build a canonical indexed-trie subtree from an already lexicographically
    sorted descriptor interval.  There are at most seven live frames (root
    plus six RLP-index nibbles); each is 1 KiB so it can directly use the
    audited raw-reference branch/extension encoders.  No frame is indexed by
    an untrusted count and no result is inserted into NodeDb. -/
def mptIndexedBuildSubtreeFunction : String :=
  "mpt_indexed_build_subtree:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; bgeu s1, s2, .Lmibs_fail; li t0, " ++ toString itrIndexedKeyMaxNibbles ++ "; bgtu s3, t0, .Lmibs_fail; addi t0, s1, 1; bne t0, s2, .Lmibs_multi\n" ++
  "  slli t0, s1, 5; slli t1, s1, 3; add t0, t0, t1; add t0, s0, t0; ld a0, 0(t0); ld a1, 8(t0); bltu a1, s3, .Lmibs_fail; add a0, a0, s3; sub a1, a1, s3; ld a2, 16(t0); ld a3, 24(t0); mv a4, s4; mv a5, s5; jal ra, mpt_indexed_leaf_ref; bnez a0, .Lmibs_fail; li a0, 0; j .Lmibs_ret\n" ++
  ".Lmibs_multi:\n" ++
  "  li t0, " ++ toString itrIndexedKeyMaxNibbles ++ "; bgeu s3, t0, .Lmibs_fail; la s6, itr_builder_frames; slli t0, s3, 10; add s6, s6, t0; li t0, 16; mv t1, s6\n" ++
  ".Lmibs_clear:\n" ++
  "  beqz t0, .Lmibs_common; sd zero, 0(t1); addi t1, t1, 40; addi t0, t0, -1; j .Lmibs_clear\n" ++
  ".Lmibs_common:\n" ++
  "  slli t0, s1, 5; slli t1, s1, 3; add t0, t0, t1; add t0, s0, t0; ld s7, 0(t0); ld s8, 8(t0); addi t0, s2, -1; slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; add t1, s0, t1; ld s9, 0(t1); ld t6, 8(t1); li t2, 0\n" ++
  ".Lmibs_common_loop:\n" ++
  "  add t0, s3, t2; bgeu t0, s8, .Lmibs_common_done; bgeu t0, t6, .Lmibs_common_done; add t1, s7, t0; lbu t1, 0(t1); add t3, s9, t0; lbu t3, 0(t3); bne t1, t3, .Lmibs_common_done; addi t2, t2, 1; j .Lmibs_common_loop\n" ++
  ".Lmibs_common_done:\n" ++
  "  beqz t2, .Lmibs_branch; sd t2, 88(sp); mv a0, s0; mv a1, s1; mv a2, s2; add a3, s3, t2; addi a4, s6, 8; mv a5, s6; jal ra, mpt_indexed_build_subtree; bnez a0, .Lmibs_fail; ld t2, 88(sp); add t0, s7, s3; addi t1, s6, " ++ toString bsrMptFrameExtensionPathOffset ++ "; mv t3, t2\n" ++
  ".Lmibs_prefix_copy:\n" ++
  "  beqz t3, .Lmibs_prefix_done; lbu t4, 0(t0); sb t4, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t3, t3, -1; j .Lmibs_prefix_copy\n" ++
  ".Lmibs_prefix_done:\n" ++
  "  sd t2, " ++ toString bsrMptFrameExtensionPathLenOffset ++ "(s6); addi t0, s6, 8; sd t0, " ++ toString bsrMptFrameExtensionChildPtrOffset ++ "(s6); ld t0, 0(s6); sd t0, " ++ toString bsrMptFrameExtensionChildLenOffset ++ "(s6); mv a0, s6; la a1, itr_builder_node; mv a2, s4; mv a3, s5; jal ra, mpt_bounded_encode_extension; bnez a0, .Lmibs_fail; li a0, 0; j .Lmibs_ret\n" ++
  ".Lmibs_branch:\n" ++
  "  mv s7, s1; li s8, 0\n" ++
  ".Lmibs_digit:\n" ++
  "  li t0, 16; beq s8, t0, .Lmibs_encode_branch; mv s9, s7\n" ++
  ".Lmibs_scan:\n" ++
  "  beq s9, s2, .Lmibs_group; slli t0, s9, 5; slli t1, s9, 3; add t0, t0, t1; add t0, s0, t0; ld t1, 0(t0); ld t2, 8(t0); bgeu s3, t2, .Lmibs_fail; add t1, t1, s3; lbu t1, 0(t1); bne t1, s8, .Lmibs_group; addi s9, s9, 1; j .Lmibs_scan\n" ++
  ".Lmibs_group:\n" ++
  "  beq s7, s9, .Lmibs_next_digit; mv a0, s0; mv a1, s7; mv a2, s9; addi a3, s3, 1; slli t0, s8, 5; slli t1, s8, 3; add t0, t0, t1; add t0, s6, t0; addi a4, t0, 8; mv a5, t0; jal ra, mpt_indexed_build_subtree; bnez a0, .Lmibs_fail\n" ++
  ".Lmibs_next_digit:\n" ++
  "  mv s7, s9; addi s8, s8, 1; j .Lmibs_digit\n" ++
  ".Lmibs_encode_branch:\n" ++
  "  mv a0, s6; la a1, itr_builder_node; addi a2, sp, 96; jal ra, mpt_bounded_encode_branch; bnez a0, .Lmibs_fail; la a0, itr_builder_node; ld a1, 96(sp); mv a2, s4; mv a3, s5; jal ra, mpt_bounded_node_ref; bnez a0, .Lmibs_fail; li a0, 0; j .Lmibs_ret\n" ++
  ".Lmibs_fail:\n  li a0, 1\n" ++
  ".Lmibs_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); addi sp, sp, 112; ret"

/-! Bounded replacement for the indexed transaction/receipt trie root.
    `a0=descriptors`, `a1=count`, `a2=out_root[32]`; the input contains the
    already-decoded transaction or receipt RLP values.  It is intentionally
    empty-trie-only: indexed transaction and receipt tries are constructed
    from their ordered value arrays, never mutated through NodeDb. -/
def mptIndexedTrieRootBoundedFunction : String :=
  "mpt_indexed_trie_root_bounded:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; li t0, " ++ toString itrIndexedEntryCapacity ++ "; bgtu s1, t0, .Lmitrb_fail; beqz s1, .Lmitrb_empty; mv a0, s0; mv a1, s1; jal ra, mpt_indexed_sort_changes; bnez a0, .Lmitrb_fail; mv a0, s0; li a1, 0; mv a2, s1; li a3, 0; la a4, itr_root_ref; la a5, itr_root_ref_len; jal ra, mpt_indexed_build_subtree; bnez a0, .Lmitrb_fail; la t0, itr_root_ref_len; ld t1, 0(t0); li t2, 32; bne t1, t2, .Lmitrb_inline_root; la t0, itr_root_ref; li t1, 32\n" ++
  ".Lmitrb_copy:\n" ++
  "  beqz t1, .Lmitrb_ok; lbu t2, 0(t0); sb t2, 0(s2); addi t0, t0, 1; addi s2, s2, 1; addi t1, t1, -1; j .Lmitrb_copy\n" ++
  ".Lmitrb_inline_root:\n" ++
  "  la a0, itr_root_ref; mv a1, t1; mv a2, s2; jal ra, zkvm_keccak256; j .Lmitrb_ok\n" ++
  ".Lmitrb_empty:\n" ++
  "  la t0, iw_empty_trie_root; li t1, 32; j .Lmitrb_copy\n" ++
  ".Lmitrb_fail:\n  li a0, 1; j .Lmitrb_ret\n" ++
  ".Lmitrb_ok:\n  li a0, 0\n" ++
  ".Lmitrb_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); addi sp, sp, 48; ret"

/-! Production-facing adapter for the existing indexed-root ABI:
    `a0={ptr,len}[]`, `a1=count`, `a2=out_root`.  It constructs the canonical
    RLP-index nibble descriptors in the gas-sized fixed arenas, then delegates
    only to `mpt_indexed_trie_root_bounded`. -/
def mptIndexedTrieRootBoundedFromValuesFunction : String :=
  "  .globl mpt_indexed_trie_root_bounded_from_values\n" ++
  "mpt_indexed_trie_root_bounded_from_values:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; li t0, " ++ toString itrIndexedEntryCapacity ++ "; bgtu s1, t0, .Lmitrbv_fail; la s3, itr_paths; la s4, itr_changes; li t0, 0\n" ++
  ".Lmitrbv_loop:\n" ++
  "  beq t0, s1, .Lmitrbv_call; slli t1, t0, 4; add t1, s0, t1; ld t2, 0(t1); ld t3, 8(t1); slli t4, t0, 3; add t5, s3, t4; bnez t0, .Lmitrbv_nonzero; li t1, 8; sb t1, 0(t5); sb zero, 1(t5); li t1, 2; j .Lmitrbv_path_done\n" ++
  ".Lmitrbv_nonzero:\n" ++
  "  li t6, 128; bgeu t0, t6, .Lmitrbv_ge128; srli t1, t0, 4; andi t6, t0, 15; sb t1, 0(t5); sb t6, 1(t5); li t1, 2; j .Lmitrbv_path_done\n" ++
  ".Lmitrbv_ge128:\n" ++
  "  li t6, 256; bgeu t0, t6, .Lmitrbv_ge256; li t1, 8; sb t1, 0(t5); li t1, 1; sb t1, 1(t5); srli t1, t0, 4; andi t6, t0, 15; sb t1, 2(t5); sb t6, 3(t5); li t1, 4; j .Lmitrbv_path_done\n" ++
  ".Lmitrbv_ge256:\n" ++
  "  li t1, 8; sb t1, 0(t5); li t1, 2; sb t1, 1(t5); srli t1, t0, 12; andi t1, t1, 15; sb t1, 2(t5); srli t1, t0, 8; andi t1, t1, 15; sb t1, 3(t5); srli t1, t0, 4; andi t1, t1, 15; sb t1, 4(t5); andi t1, t0, 15; sb t1, 5(t5); li t1, 6\n" ++
  ".Lmitrbv_path_done:\n" ++
  "  slli t4, t0, 5; slli t6, t0, 3; add t4, t4, t6; add t4, s4, t4; sd t5, 0(t4); sd t1, 8(t4); sd t2, 16(t4); sd t3, 24(t4); sd zero, 32(t4); addi t0, t0, 1; j .Lmitrbv_loop\n" ++
  ".Lmitrbv_call:\n" ++
  "  mv a0, s4; mv a1, s1; mv a2, s2; jal ra, mpt_indexed_trie_root_bounded; j .Lmitrbv_ret\n" ++
  ".Lmitrbv_fail:\n  li a0, 1\n" ++
  ".Lmitrbv_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); addi sp, sp, 64; ret"

/-! ## mpt_indexed_large_leaf_hash -- streaming large-value leaf node hash

    Compute `keccak(rlp([hp_path, value]))` for large indexed-trie leaves
    without materializing the full leaf node. This helper is intended for
    branch slots that will use `0xa0 || hash`, so it deliberately accepts only
    values whose RLP item is already large.

    a0 = value ptr, a1 = value len, a2 = path kind (0 empty, 1 one nibble),
    a3 = low nibble when kind=1, a4 = out hash ptr.
    Returns a0 = 0 ok / 1 unsupported small value or bad path kind. -/
def mptIndexedLargeLeafHash_prog : Program :=
  [ .ADDI .x2 .x2 (-144 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x9 .x10,
    .MV .x18 .x11,
    .MV .x19 .x12,
    .MV .x20 .x13,
    .MV .x21 .x14,
    .LI .x5 (56 : Word),
    .BLTU .x18 .x5 (252 : BitVec 13),
    .LI .x5 (1 : Word),
    .BLTU .x5 .x19 (244 : BitVec 13),
    .LI .x5 (15 : Word),
    .BLTU .x5 .x20 (236 : BitVec 13),
    .AUIPC .x8 (laHi GuestAddrs.zk3_state (GuestAddrs.mpt_indexed_large_leaf_hash + 100)),
    .ADDI .x8 .x8 (laLo GuestAddrs.zk3_state (GuestAddrs.mpt_indexed_large_leaf_hash + 100)),
    .MV .x5 .x8,
    .LI .x6 (25 : Word),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-12 : BitVec 13),
    .LI .x22 (0 : Word),
    .LI .x10 (128 : Word),
    .MV .x11 .x18,
    .ADDI .x12 .x2 (104 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_prefix_to_buffer (GuestAddrs.mpt_indexed_large_leaf_hash + 148)),
    .MV .x23 .x10,
    .ADD .x24 .x23 .x18,
    .ADDI .x11 .x24 (1 : BitVec 12),
    .LI .x10 (192 : Word),
    .ADDI .x12 .x2 (120 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_prefix_to_buffer (GuestAddrs.mpt_indexed_large_leaf_hash + 172)),
    .MV .x25 .x10,
    .ADDI .x5 .x2 (136 : BitVec 12),
    .BEQ .x19 .x0 (12 : BitVec 13),
    .ORI .x6 .x20 (48 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x6 (32 : Word),
    .SB .x5 .x6 (0 : BitVec 12),
    .ADDI .x10 .x2 (120 : BitVec 12),
    .MV .x11 .x25,
    .JAL .x1 (184 : BitVec 21),
    .ADDI .x10 .x2 (136 : BitVec 12),
    .LI .x11 (1 : Word),
    .JAL .x1 (172 : BitVec 21),
    .ADDI .x10 .x2 (104 : BitVec 12),
    .MV .x11 .x23,
    .JAL .x1 (160 : BitVec 21),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .JAL .x1 (148 : BitVec 21),
    .ADD .x5 .x8 .x22,
    .LBU .x6 .x5 (0 : BitVec 12),
    .XORI .x6 .x6 (1 : BitVec 12),
    .SB .x5 .x6 (0 : BitVec 12),
    .ADDI .x5 .x8 (135 : BitVec 12),
    .LBU .x6 .x5 (0 : BitVec 12),
    .XORI .x6 .x6 (128 : BitVec 12),
    .SB .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x8,
    .CSRS (2048 : BitVec 12) .x10,
    .LD .x5 .x8 (0 : BitVec 12),
    .SD .x21 .x5 (0 : BitVec 12),
    .LD .x5 .x8 (8 : BitVec 12),
    .SD .x21 .x5 (8 : BitVec 12),
    .LD .x5 .x8 (16 : BitVec 12),
    .SD .x21 .x5 (16 : BitVec 12),
    .LD .x5 .x8 (24 : BitVec 12),
    .SD .x21 .x5 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (144 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .MV .x26 .x10,
    .MV .x27 .x11,
    .BEQ .x27 .x0 (60 : BitVec 13),
    .LBU .x5 .x26 (0 : BitVec 12),
    .ADD .x6 .x8 .x22,
    .LBU .x7 .x6 (0 : BitVec 12),
    .XOR .x7 .x7 .x5,
    .SB .x6 .x7 (0 : BitVec 12),
    .ADDI .x26 .x26 (1 : BitVec 12),
    .ADDI .x27 .x27 (-1 : BitVec 12),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .LI .x28 (136 : Word),
    .BNE .x22 .x28 (-40 : BitVec 13),
    .MV .x10 .x8,
    .CSRS (2048 : BitVec 12) .x10,
    .LI .x22 (0 : Word),
    .JAL .x0 (-56 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptIndexedLargeLeafHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptIndexedLargeLeafHash_relocs : RelocTable :=
  [ (25, .la .x8 "zk3_state"),
    (37, .jal .x1 "rlp_prefix_to_buffer"),
    (43, .jal .x1 "rlp_prefix_to_buffer") ]

def mptIndexedLargeLeafHashFunction : String :=
  "mpt_indexed_large_leaf_hash:\n" ++ emitProgramR mptIndexedLargeLeafHash_prog mptIndexedLargeLeafHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptIndexedLargeLeafHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptIndexedLargeLeafHashFunction_eq_prog :
    mptIndexedLargeLeafHashFunction = "mpt_indexed_large_leaf_hash:\n" ++ emitProgramR mptIndexedLargeLeafHash_prog mptIndexedLargeLeafHash_relocs := rfl

#guard mptIndexedLargeLeafHashFunction.startsWith "mpt_indexed_large_leaf_hash:\n"
#guard mptIndexedLargeLeafHash_prog.length = 117
/-! ## mpt_indexed_trie_root_large -- grouped large-value indexed trie root

    Fast path for contiguous indexed keys 0..n-1, n <= 128, when every value is
    large enough to be referenced by hash from a branch slot. It covers the
    two-nibble RLP-index key space used by the transaction and withdrawal tries
    before the 128 boundary.

    a0 = value descriptor array ptr, a1 = number of values, a2 = out root ptr.
    Returns a0 = 0 ok / 1 internal failure / 2 unsupported, use generic path. -/
def mptIndexedTrieRootLarge_prog : Program :=
  [ .ADDI .x2 .x2 (-2016 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .ADDI .x22 .x2 (160 : BitVec 12),
    .ADDI .x23 .x2 (760 : BitVec 12),
    .ADDI .x24 .x2 (1360 : BitVec 12),
    .LI .x5 (2 : Word),
    .BLTU .x9 .x5 (280 : BitVec 13),
    .LI .x5 (129 : Word),
    .BGEU .x9 .x5 (272 : BitVec 13),
    .LI .x26 (0 : Word),
    .BEQ .x26 .x9 (32 : BitVec 13),
    .SLLI .x5 .x26 (4 : BitVec 6),
    .ADD .x5 .x8 .x5,
    .LD .x6 .x5 (8 : BitVec 12),
    .LI .x7 (56 : Word),
    .BLTU .x6 .x7 (244 : BitVec 13),
    .ADDI .x26 .x26 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .MV .x25 .x22,
    .LI .x19 (0 : Word),
    .LI .x5 (16 : Word),
    .BEQ .x19 .x5 (184 : BitVec 13),
    .LI .x20 (0 : Word),
    .LI .x21 (0 : Word),
    .LI .x26 (0 : Word),
    .BEQ .x26 .x9 (44 : BitVec 13),
    .BEQ .x26 .x0 (12 : BitVec 13),
    .SRLI .x6 .x26 (4 : BitVec 6),
    .JAL .x0 (8 : BitVec 21),
    .LI .x6 (8 : Word),
    .BNE .x6 .x19 (16 : BitVec 13),
    .BNE .x20 .x0 (8 : BitVec 13),
    .MV .x21 .x26,
    .ADDI .x20 .x20 (1 : BitVec 12),
    .ADDI .x26 .x26 (1 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .BEQ .x20 .x0 (104 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x20 .x5 (28 : BitVec 13),
    .JAL .x1 (220 : BitVec 21),
    .ADDI .x11 .x2 (1968 : BitVec 12),
    .MV .x10 .x25,
    .JAL .x1 (376 : BitVec 21),
    .MV .x25 .x10,
    .JAL .x0 (84 : BitVec 21),
    .SLLI .x5 .x21 (4 : BitVec 6),
    .ADD .x5 .x8 .x5,
    .LD .x10 .x5 (0 : BitVec 12),
    .LD .x11 .x5 (8 : BitVec 12),
    .LI .x12 (1 : Word),
    .BEQ .x21 .x0 (12 : BitVec 13),
    .ANDI .x13 .x21 (15 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x13 (0 : Word),
    .ADDI .x14 .x2 (1968 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.mpt_indexed_large_leaf_hash (GuestAddrs.mpt_indexed_trie_root_large + 280)),
    .BNE .x10 .x0 (88 : BitVec 13),
    .MV .x10 .x25,
    .ADDI .x11 .x2 (1968 : BitVec 12),
    .JAL .x1 (308 : BitVec 21),
    .MV .x25 .x10,
    .JAL .x0 (16 : BitVec 21),
    .LI .x5 (128 : Word),
    .SB .x25 .x5 (0 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-184 : BitVec 21),
    .LI .x5 (128 : Word),
    .SB .x25 .x5 (0 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .SUB .x11 .x25 .x22,
    .MV .x10 .x22,
    .MV .x12 .x18,
    .JAL .x1 (300 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (2016 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x2 .x25 (128 : BitVec 12),
    .SD .x2 .x1 (152 : BitVec 12),
    .MV .x25 .x23,
    .LI .x20 (0 : Word),
    .LI .x5 (16 : Word),
    .BEQ .x20 .x5 (96 : BitVec 13),
    .SLLI .x26 .x19 (4 : BitVec 6),
    .ADD .x26 .x26 .x20,
    .BEQ .x26 .x0 (64 : BitVec 13),
    .BGEU .x26 .x9 (60 : BitVec 13),
    .SLLI .x5 .x26 (4 : BitVec 6),
    .ADD .x5 .x8 .x5,
    .LD .x10 .x5 (0 : BitVec 12),
    .LD .x11 .x5 (8 : BitVec 12),
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .ADDI .x14 .x2 (1968 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.mpt_indexed_large_leaf_hash (GuestAddrs.mpt_indexed_trie_root_large + 504)),
    .BNE .x10 .x0 (84 : BitVec 13),
    .MV .x10 .x25,
    .ADDI .x11 .x2 (1968 : BitVec 12),
    .JAL .x1 (84 : BitVec 21),
    .MV .x25 .x10,
    .JAL .x0 (16 : BitVec 21),
    .LI .x5 (128 : Word),
    .SB .x25 .x5 (0 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-96 : BitVec 21),
    .LI .x5 (128 : Word),
    .SB .x25 .x5 (0 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .SUB .x11 .x25 .x23,
    .MV .x10 .x23,
    .ADDI .x12 .x2 (1968 : BitVec 12),
    .JAL .x1 (76 : BitVec 21),
    .LD .x25 .x2 (128 : BitVec 12),
    .LD .x1 .x2 (152 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LD .x25 .x2 (128 : BitVec 12),
    .LD .x1 .x2 (152 : BitVec 12),
    .JAL .x0 (-228 : BitVec 21),
    .LI .x5 (160 : Word),
    .SB .x10 .x5 (0 : BitVec 12),
    .ADDI .x5 .x10 (1 : BitVec 12),
    .LI .x6 (32 : Word),
    .LBU .x7 .x11 (0 : BitVec 12),
    .SB .x5 .x7 (0 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-20 : BitVec 13),
    .ADDI .x10 .x10 (33 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (104 : BitVec 12),
    .SD .x2 .x11 (112 : BitVec 12),
    .SD .x2 .x12 (120 : BitVec 12),
    .SD .x2 .x1 (144 : BitVec 12),
    .LI .x10 (192 : Word),
    .LD .x11 .x2 (112 : BitVec 12),
    .MV .x12 .x24,
    .JAL .x1 (jalOff GuestAddrs.rlp_prefix_to_buffer (GuestAddrs.mpt_indexed_trie_root_large + 680)),
    .MV .x5 .x10,
    .ADD .x6 .x24 .x5,
    .LD .x7 .x2 (104 : BitVec 12),
    .LD .x28 .x2 (112 : BitVec 12),
    .BEQ .x28 .x0 (28 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .SB .x6 .x29 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LD .x28 .x2 (112 : BitVec 12),
    .ADD .x11 .x5 .x28,
    .MV .x10 .x24,
    .LD .x12 .x2 (120 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.mpt_indexed_trie_root_large + 744)),
    .LD .x1 .x2 (144 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptIndexedTrieRootLarge_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptIndexedTrieRootLarge_relocs : RelocTable :=
  [ (70, .jal .x1 "mpt_indexed_large_leaf_hash"),
    (126, .jal .x1 "mpt_indexed_large_leaf_hash"),
    (170, .jal .x1 "rlp_prefix_to_buffer"),
    (186, .jal .x1 "zkvm_keccak256") ]

def mptIndexedTrieRootLargeFunction : String :=
  "mpt_indexed_trie_root_large:\n" ++ emitProgramR mptIndexedTrieRootLarge_prog mptIndexedTrieRootLarge_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptIndexedTrieRootLarge_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptIndexedTrieRootLargeFunction_eq_prog :
    mptIndexedTrieRootLargeFunction = "mpt_indexed_trie_root_large:\n" ++ emitProgramR mptIndexedTrieRootLarge_prog mptIndexedTrieRootLarge_relocs := rfl

#guard mptIndexedTrieRootLargeFunction.startsWith "mpt_indexed_trie_root_large:\n"
#guard mptIndexedTrieRootLarge_prog.length = 189
def mptIndexedTrieRootSmall_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .LUI .x5 (1 : BitVec 20),
    .ADDIW .x5 .x5 (-2047 : BitVec 12),
    .BGEU .x9 .x5 (420 : BitVec 13),
    .BEQ .x9 .x0 (328 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x9 .x5 (300 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.mpt_indexed_trie_root_large (GuestAddrs.mpt_indexed_trie_root_small + 76)),
    .LI .x5 (2 : Word),
    .BNE .x10 .x5 (388 : BitVec 13),
    .LI .x19 (0 : Word),
    .BEQ .x19 .x9 (332 : BitVec 13),
    .SLLI .x5 .x19 (4 : BitVec 6),
    .ADD .x5 .x8 .x5,
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .SLLI .x28 .x19 (3 : BitVec 6),
    .AUIPC .x29 (laHi GuestAddrs.itr_paths (GuestAddrs.mpt_indexed_trie_root_small + 116)),
    .ADDI .x29 .x29 (laLo GuestAddrs.itr_paths (GuestAddrs.mpt_indexed_trie_root_small + 116)),
    .ADD .x29 .x29 .x28,
    .BEQ .x19 .x0 (152 : BitVec 13),
    .LI .x5 (256 : Word),
    .BGEU .x19 .x5 (76 : BitVec 13),
    .LI .x5 (128 : Word),
    .BGEU .x19 .x5 (28 : BitVec 13),
    .SRLI .x30 .x19 (4 : BitVec 6),
    .ANDI .x31 .x19 (15 : BitVec 12),
    .SB .x29 .x30 (0 : BitVec 12),
    .SB .x29 .x31 (1 : BitVec 12),
    .LI .x5 (2 : Word),
    .JAL .x0 (128 : BitVec 21),
    .LI .x30 (8 : Word),
    .SB .x29 .x30 (0 : BitVec 12),
    .LI .x30 (1 : Word),
    .SB .x29 .x30 (1 : BitVec 12),
    .SRLI .x30 .x19 (4 : BitVec 6),
    .ANDI .x31 .x19 (15 : BitVec 12),
    .SB .x29 .x30 (2 : BitVec 12),
    .SB .x29 .x31 (3 : BitVec 12),
    .LI .x5 (4 : Word),
    .JAL .x0 (88 : BitVec 21),
    .LI .x30 (8 : Word),
    .SB .x29 .x30 (0 : BitVec 12),
    .LI .x30 (2 : Word),
    .SB .x29 .x30 (1 : BitVec 12),
    .SRLI .x30 .x19 (12 : BitVec 6),
    .ANDI .x30 .x30 (15 : BitVec 12),
    .SB .x29 .x30 (2 : BitVec 12),
    .SRLI .x30 .x19 (8 : BitVec 6),
    .ANDI .x30 .x30 (15 : BitVec 12),
    .SB .x29 .x30 (3 : BitVec 12),
    .SRLI .x30 .x19 (4 : BitVec 6),
    .ANDI .x30 .x30 (15 : BitVec 12),
    .SB .x29 .x30 (4 : BitVec 12),
    .ANDI .x31 .x19 (15 : BitVec 12),
    .SB .x29 .x31 (5 : BitVec 12),
    .LI .x5 (6 : Word),
    .JAL .x0 (20 : BitVec 21),
    .LI .x30 (8 : Word),
    .SB .x29 .x30 (0 : BitVec 12),
    .SB .x29 .x0 (1 : BitVec 12),
    .LI .x5 (2 : Word),
    .SD .x2 .x5 (48 : BitVec 12),
    .SLLI .x30 .x19 (5 : BitVec 6),
    .SLLI .x31 .x19 (3 : BitVec 6),
    .ADD .x30 .x30 .x31,
    .AUIPC .x20 (laHi GuestAddrs.itr_changes (GuestAddrs.mpt_indexed_trie_root_small + 312)),
    .ADDI .x20 .x20 (laLo GuestAddrs.itr_changes (GuestAddrs.mpt_indexed_trie_root_small + 312)),
    .ADD .x20 .x20 .x30,
    .SD .x20 .x29 (0 : BitVec 12),
    .LD .x30 .x2 (48 : BitVec 12),
    .SD .x20 .x30 (8 : BitVec 12),
    .SD .x20 .x6 (16 : BitVec 12),
    .SD .x20 .x7 (24 : BitVec 12),
    .LI .x30 (1 : Word),
    .SD .x20 .x30 (32 : BitVec 12),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-264 : BitVec 21),
    .LD .x10 .x8 (0 : BitVec 12),
    .LD .x11 .x8 (8 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.mpt_indexed_trie_root_one_leaf (GuestAddrs.mpt_indexed_trie_root_small + 372)),
    .JAL .x0 (96 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.iw_empty_trie_root (GuestAddrs.mpt_indexed_trie_root_small + 380)),
    .ADDI .x5 .x5 (laLo GuestAddrs.iw_empty_trie_root (GuestAddrs.mpt_indexed_trie_root_small + 380)),
    .LI .x6 (32 : Word),
    .LBU .x7 .x5 (0 : BitVec 12),
    .SB .x18 .x7 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (52 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.iw_empty_trie_root (GuestAddrs.mpt_indexed_trie_root_small + 424)),
    .ADDI .x10 .x10 (laLo GuestAddrs.iw_empty_trie_root (GuestAddrs.mpt_indexed_trie_root_small + 424)),
    .AUIPC .x11 (laHi GuestAddrs.itr_empty_witness (GuestAddrs.mpt_indexed_trie_root_small + 432)),
    .ADDI .x11 .x11 (laLo GuestAddrs.itr_empty_witness (GuestAddrs.mpt_indexed_trie_root_small + 432)),
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.itr_changes (GuestAddrs.mpt_indexed_trie_root_small + 444)),
    .ADDI .x13 .x13 (laLo GuestAddrs.itr_changes (GuestAddrs.mpt_indexed_trie_root_small + 444)),
    .MV .x14 .x9,
    .MV .x15 .x18,
    .JAL .x1 (jalOff GuestAddrs.mpt_state_root_ins (GuestAddrs.mpt_indexed_trie_root_small + 460)),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptIndexedTrieRootSmall_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptIndexedTrieRootSmall_relocs : RelocTable :=
  [ (19, .jal .x1 "mpt_indexed_trie_root_large"),
    (29, .la .x29 "itr_paths"),
    (78, .la .x20 "itr_changes"),
    (93, .jal .x1 "mpt_indexed_trie_root_one_leaf"),
    (95, .la .x5 "iw_empty_trie_root"),
    (106, .la .x10 "iw_empty_trie_root"),
    (108, .la .x11 "itr_empty_witness"),
    (111, .la .x13 "itr_changes"),
    (115, .jal .x1 "mpt_state_root_ins") ]

def mptIndexedTrieRootSmallFunction : String :=
  "mpt_indexed_trie_root_small:\n" ++ emitProgramR mptIndexedTrieRootSmall_prog mptIndexedTrieRootSmall_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptIndexedTrieRootSmall_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptIndexedTrieRootSmallFunction_eq_prog :
    mptIndexedTrieRootSmallFunction = "mpt_indexed_trie_root_small:\n" ++ emitProgramR mptIndexedTrieRootSmall_prog mptIndexedTrieRootSmall_relocs := rfl

#guard mptIndexedTrieRootSmallFunction.startsWith "mpt_indexed_trie_root_small:\n"
#guard mptIndexedTrieRootSmall_prog.length = 126
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
  mptIndexedLargeLeafHashFunction ++ "\n" ++
  mptIndexedTrieRootLargeFunction ++ "\n" ++
  mptIndexedTrieRootSmallFunction ++ "\n" ++
  ".Litrp_done:"

def ziskMptIndexedTrieRootSmallDataSection : String :=
  ziskMptStateRootInsDataSection ++ "\n" ++
  ".balign 8\n" ++
  "itr_empty_witness:\n  .zero 8\n" ++
  "itr_value_descs:\n  .zero " ++ toString (itrIndexedEntryCapacity * 16) ++ "\n" ++
  "itr_paths:\n  .zero " ++ toString (itrIndexedEntryCapacity * 8) ++ "\n" ++
  "itr_changes:\n  .zero " ++ toString (itrIndexedEntryCapacity * 40) ++ "\n" ++
  "itr_sort_ranges:\n  .zero " ++ toString (itrIndexedSortRangeStackCapacity * 32) ++ "\n" ++
  "itr_sort_scratch:\n  .zero 40\n" ++
  "itr_builder_node_len:\n  .zero 8\n" ++
  "itr_builder_node:\n  .zero 1024"
  ++ "\nitr_builder_frames:\n  .zero " ++ toString (itrIndexedBuilderFrameCapacity * 1024) ++
  "\nitr_root_ref_len:\n  .zero 8\nitr_root_ref:\n  .zero 32"

def ziskMptIndexedTrieRootSmallProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptIndexedTrieRootSmallPrologue
  dataAsm     := ziskMptIndexedTrieRootSmallDataSection
}

/-! Same host value-array ABI as the legacy indexed-root probe, routed through
    the bounded adapter. -/
def ziskMptIndexedTrieRootBoundedValuesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000; ld s0, 8(t0); addi s1, t0, 16; slli s2, s0, 3; add s2, s1, s2; la s3, itr_value_descs; li s4, 0\n" ++
  ".Lmitrbvp_desc:\n" ++
  "  beq s4, s0, .Lmitrbvp_call; slli t1, s4, 3; add t2, s1, t1; ld t3, 0(t2); slli t4, s4, 4; add t5, s3, t4; sd s2, 0(t5); sd t3, 8(t5); add s2, s2, t3; addi s2, s2, 7; andi s2, s2, -8; addi s4, s4, 1; j .Lmitrbvp_desc\n" ++
  ".Lmitrbvp_call:\n" ++
  "  la a0, itr_value_descs; mv a1, s0; li a2, 0xa0010000; jal ra, mpt_indexed_trie_root_bounded_from_values; li t0, 0xa0010020; sd a0, 0(t0); j .Lmitrbvp_done\n" ++
  hpEncodeNibblesFunction ++ "\n" ++ rlpEncodeBytesFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++ rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++ mptExtensionNodeEncodeFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++ mptBoundedNodeRefFunction ++ "\n" ++
  mptBoundedEncodeBranchFunction ++ "\n" ++ mptBoundedEncodeExtensionFunction ++ "\n" ++
  mptIndexedTrieRootOneLeafFunction ++ "\n" ++ mptIndexedStreamLeafHashFunction ++ "\n" ++
  mptIndexedSortChangesFunction ++ "\n" ++ mptIndexedLeafRefFunction ++ "\n" ++
  mptIndexedBuildSubtreeFunction ++ "\n" ++ mptIndexedTrieRootBoundedFunction ++ "\n" ++
  mptIndexedTrieRootBoundedFromValuesFunction ++ "\n.Lmitrbvp_done:"

def ziskMptIndexedTrieRootBoundedValuesProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptIndexedTrieRootBoundedValuesPrologue
  dataAsm := ziskMptIndexedTrieRootSmallDataSection
}


/-! Probe for `mpt_indexed_large_leaf_hash`.

    Input layout (file maps to INPUT+8):
      +8  path kind (0 empty, 1 one nibble)
      +16 nibble
      +24 value_len
      +32 value bytes, padded by the host test script
    Output: +0 hash, +32 status. -/
def ziskMptIndexedLargeLeafHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # path kind\n" ++
  "  ld a3, 16(t0)               # nibble\n" ++
  "  ld a1, 24(t0)               # value len\n" ++
  "  addi a0, t0, 32             # value ptr\n" ++
  "  li a4, 0xa0010000           # out hash\n" ++
  "  jal ra, mpt_indexed_large_leaf_hash\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)\n" ++
  "  j .Lillhp_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  mptIndexedTrieRootOneLeafFunction ++ "\n" ++
  mptIndexedLargeLeafHashFunction ++ "\n" ++
  ".Lillhp_done:"

def ziskMptIndexedLargeLeafHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptIndexedLargeLeafHashPrologue
  dataAsm     := ziskMptStateRootInsDataSection
}

/-! Probe for the general streaming indexed-leaf hash.

    Input layout (file maps to INPUT+8): path_len at +8, value_len at +16,
    up to six path nibbles at +24, and value bytes at +32. -/
def ziskMptIndexedStreamLeafHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0); ld a3, 16(t0); addi a0, t0, 24; addi a2, t0, 32; li a4, 0xa0010000\n" ++
  "  jal ra, mpt_indexed_stream_leaf_hash\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0); j .Lmislhp_done\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  mptIndexedTrieRootOneLeafFunction ++ "\n" ++
  mptIndexedStreamLeafHashFunction ++ "\n" ++
  ".Lmislhp_done:"

def ziskMptIndexedStreamLeafHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptIndexedStreamLeafHashPrologue
  dataAsm     := ziskMptStateRootInsDataSection
}

/-! Probe for the indexed RLP-key sorter.  The input holds `{path_len,u64;
    path[8]}` records in deliberately numeric order; the output is the sorted
    original record index for each descriptor. -/
def ziskMptIndexedSortChangesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000; ld s1, 8(s0); addi s2, s0, 16; la s3, itr_changes; li s4, 0\n" ++
  ".Lmisprobe_load:\n" ++
  "  beq s4, s1, .Lmisprobe_sort; slli t0, s4, 4; add t0, s2, t0; ld t1, 0(t0); addi t2, t0, 8; slli t3, s4, 5; slli t4, s4, 3; add t3, t3, t4; add t3, s3, t3; sd t2, 0(t3); sd t1, 8(t3); sd zero, 16(t3); sd zero, 24(t3); sd s4, 32(t3); addi s4, s4, 1; j .Lmisprobe_load\n" ++
  ".Lmisprobe_sort:\n" ++
  "  mv a0, s3; mv a1, s1; jal ra, mpt_indexed_sort_changes; li t0, 0xa0010000; sd a0, 0(t0); bnez a0, .Lmisprobe_halt; li s4, 0\n" ++
  ".Lmisprobe_out:\n" ++
  "  beq s4, s1, .Lmisprobe_halt; slli t1, s4, 5; slli t2, s4, 3; add t1, t1, t2; add t1, s3, t1; ld t2, 32(t1); slli t3, s4, 3; addi t3, t3, 8; add t3, t0, t3; sd t2, 0(t3); addi s4, s4, 1; j .Lmisprobe_out\n" ++
  mptIndexedSortChangesFunction ++ "\n" ++
  ".Lmisprobe_halt:"

def ziskMptIndexedSortChangesProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptIndexedSortChangesPrologue
  dataAsm := ziskMptIndexedTrieRootSmallDataSection
}

/-! Bounded indexed-root probe.  Each input record is `{path_len:u64,
    path[8], value_len:u64, value[round8]}`; it is deliberately a descriptor-level
    probe so the root KAT can cover the exact 0/127/128/256 RLP paths. -/
def ziskMptIndexedTrieRootBoundedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000; ld s1, 8(s0); addi s2, s0, 16; la s3, itr_changes; li t0, " ++ toString itrIndexedEntryCapacity ++ "; bgtu s1, t0, .Lmitrbp_root; li s4, 0\n" ++
  ".Lmitrbp_load:\n" ++
  "  beq s4, s1, .Lmitrbp_root; mv t0, s2; ld t1, 0(t0); addi t2, t0, 8; ld t3, 16(t0); addi t4, t0, 24; slli t5, s4, 5; slli t6, s4, 3; add t5, t5, t6; add t5, s3, t5; sd t2, 0(t5); sd t1, 8(t5); sd t4, 16(t5); sd t3, 24(t5); sd zero, 32(t5); add s2, t4, t3; addi s2, s2, 7; andi s2, s2, -8; addi s4, s4, 1; j .Lmitrbp_load\n" ++
  ".Lmitrbp_root:\n" ++
  "  mv a0, s3; mv a1, s1; li a2, 0xa0010000; jal ra, mpt_indexed_trie_root_bounded; li t0, 0xa0010020; sd a0, 0(t0); j .Lmitrbp_done\n" ++
  hpEncodeNibblesFunction ++ "\n" ++ rlpEncodeBytesFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++ rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++ mptExtensionNodeEncodeFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++ mptBoundedNodeRefFunction ++ "\n" ++
  mptBoundedEncodeBranchFunction ++ "\n" ++ mptBoundedEncodeExtensionFunction ++ "\n" ++
  mptIndexedTrieRootOneLeafFunction ++ "\n" ++ mptIndexedStreamLeafHashFunction ++ "\n" ++
  mptIndexedSortChangesFunction ++ "\n" ++ mptIndexedLeafRefFunction ++ "\n" ++
  mptIndexedBuildSubtreeFunction ++ "\n" ++ mptIndexedTrieRootBoundedFunction ++ "\n" ++
  ".Lmitrbp_done:"

def ziskMptIndexedTrieRootBoundedProbeUnit : BuildUnit := {
  body := NOP
  prologueAsm := ziskMptIndexedTrieRootBoundedPrologue
  dataAsm := ziskMptIndexedTrieRootSmallDataSection
}

end EvmAsm.Codegen
