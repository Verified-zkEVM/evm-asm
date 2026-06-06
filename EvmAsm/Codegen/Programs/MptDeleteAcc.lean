/-
  EvmAsm.Codegen.Programs.MptDeleteAcc

  Executable delete accumulator for existing MPT keys. This slice handles
  deleting a single-leaf trie to EMPTY_TRIE_ROOT, branch-only bubbling, and
  the first branch-collapse cases through the shared node DB.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptDeleteWalkDb
import EvmAsm.Codegen.Programs.MptInsertWalk
import EvmAsm.Codegen.Programs.MptInternal

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_delete_acc -- DB-aware delete accumulator.

    a0=root_hash, a1=witness, a2=witness_len, a3=path, a4=path_len,
    a7=out_root -> a0 status:
      0 ok
      1 not found / incomplete witness
      2 parse or splice failure
      3 deletion would require an uncovered branch/extension collapse
-/
def mptDeleteAccFunction : String :=
  "mpt_delete_acc:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a1                   # witness\n" ++
  "  mv s1, a3                   # path\n" ++
  "  mv s2, a4                   # path_len\n" ++
  "  mv s5, a7                   # out_root\n" ++
  "  la t0, mdacc_witness_len; sd a2, 0(t0)\n" ++
  "  mv a1, s0\n" ++
  "  mv a3, s1\n" ++
  "  mv a4, s2\n" ++
  "  la a5, mset_stack\n" ++
  "  la a6, mset_meta\n" ++
  "  jal ra, mpt_delete_walk_db\n" ++
  "  bnez a0, .Lmdacc_ret\n" ++
  "  la t0, mset_meta; ld s6, 0(t0)   # depth\n" ++
  "  beqz s6, .Lmdacc_empty_root\n" ++
  "  # Bubble supports branch ancestors and extension ancestors whose child\n" ++
  "  # remains canonical. Extension/leaf merge is handled by a follow-up.\n" ++
  "  li t0, 0\n" ++
  ".Lmdacc_check_loop:\n" ++
  "  beq t0, s6, .Lmdacc_check_done\n" ++
  "  la t1, mset_stack; slli t2, t0, 5; add t1, t1, t2\n" ++
  "  ld t3, 16(t1); li t4, 1; bgtu t3, t4, .Lmdacc_need_collapse\n" ++
  "  addi t0, t0, 1; j .Lmdacc_check_loop\n" ++
  ".Lmdacc_check_done:\n" ++
  "  # If the deepest branch would become collapsible after deleting this\n" ++
  "  # child, stay conservative. No-collapse bubbling is canonical only when\n" ++
  "  # the terminal branch still has at least two child refs, or has a branch\n" ++
  "  # value plus at least one child.\n" ++
  "  addi t0, s6, -1\n" ++
  "  la t1, mset_stack; slli t2, t0, 5; add t1, t1, t2\n" ++
  "  ld s3, 0(t1)                # terminal branch ptr\n" ++
  "  ld s4, 8(t1)                # terminal branch len\n" ++
  "  ld t3, 16(t1); bnez t3, .Lmdacc_need_collapse\n" ++
  "  ld s7, 24(t1)               # deleted child nibble\n" ++
  "  li s1, 0                    # i\n" ++
  "  li s2, 0                    # non-empty child count after deletion\n" ++
  ".Lmdacc_count_children:\n" ++
  "  li t1, 16; beq s1, t1, .Lmdacc_count_done\n" ++
  "  beq s1, s7, .Lmdacc_count_next\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, s1\n" ++
  "  la a3, mw_child_offset; la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmdacc_fail\n" ++
  "  la t1, mw_child_length; ld t1, 0(t1)\n" ++
  "  beqz t1, .Lmdacc_count_next\n" ++
  "  la t2, mdacc_survivor_nibble; sd s1, 0(t2)\n" ++
  "  addi s2, s2, 1\n" ++
  ".Lmdacc_count_next:\n" ++
  "  addi s1, s1, 1\n" ++
  "  j .Lmdacc_count_children\n" ++
  ".Lmdacc_count_done:\n" ++
  "  mv a0, s3; mv a1, s4; li a2, 16\n" ++
  "  la a3, mw_child_offset; la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmdacc_fail\n" ++
  "  la t0, mw_child_length; ld t0, 0(t0)  # branch value length\n" ++
  "  beqz s2, .Lmdacc_zero_children\n" ++
  "  li t1, 1; bne s2, t1, .Lmdacc_no_collapse_needed\n" ++
  "  beqz t0, .Lmdacc_collapse_one_child\n" ++
  "  j .Lmdacc_no_collapse_needed\n" ++
  ".Lmdacc_zero_children:\n" ++
  "  bnez t0, .Lmdacc_collapse_branch_value\n" ++
  "  j .Lmdacc_need_collapse\n" ++
  ".Lmdacc_collapse_branch_value:\n" ++
  "  mv a0, s3; mv a1, s4; li a2, 16\n" ++
  "  la a3, mw_child_offset; la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmdacc_fail\n" ++
  "  la t0, mw_child_offset; ld t0, 0(t0); add a2, s3, t0\n" ++
  "  la t0, mw_child_length; ld a3, 0(t0)\n" ++
  "  la a0, mdacc_collapsed_path; mv a1, zero\n" ++
  "  la a4, mset_node; la a5, mset_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la t0, mset_node_len; ld s4, 0(t0)\n" ++
  "  la a0, mset_node; mv a1, s4\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  addi s7, s6, -1\n" ++
  "  j .Lmdacc_bubble\n" ++
  ".Lmdacc_collapse_one_child:\n" ++
  "  la t0, mdacc_survivor_nibble; ld a2, 0(t0)\n" ++
  "  mv a0, s3; mv a1, s4\n" ++
  "  la a3, mw_child_offset; la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmdacc_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  li t2, 32; bne t1, t2, .Lmdacc_need_collapse\n" ++
  "  la t0, mw_child_offset; ld t0, 0(t0); add a2, s3, t0\n" ++
  "  mv a0, s0; la t0, mdacc_witness_len; ld a1, 0(t0)\n" ++
  "  la a3, mdacc_child_ptr; la a4, mdacc_child_len\n" ++
  "  jal ra, mpt_node_resolve\n" ++
  "  bnez a0, .Lmdacc_need_collapse\n" ++
  "  la t0, mdacc_child_ptr; ld a0, 0(t0)\n" ++
  "  la t0, mdacc_child_len; ld a1, 0(t0)\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  li t0, 2; beq a0, t0, .Lmdacc_collapse_leaf_child\n" ++
  "  li t0, 1; beq a0, t0, .Lmdacc_collapse_extension_child\n" ++
  "  beqz a0, .Lmdacc_collapse_branch_child\n" ++
  "  j .Lmdacc_need_collapse\n" ++
  ".Lmdacc_collapse_leaf_child:\n" ++
  "  la t0, mdacc_child_ptr; ld a0, 0(t0)\n" ++
  "  la t0, mdacc_child_len; ld a1, 0(t0)\n" ++
  "  la a2, mdacc_leaf_path; la a3, mdacc_leaf_path_len; la a4, mdacc_leaf_value_ptr; la a5, mdacc_leaf_value_len\n" ++
  "  jal ra, mpt_leaf_extract\n" ++
  "  bnez a0, .Lmdacc_need_collapse\n" ++
  "  la t0, mdacc_survivor_nibble; ld t1, 0(t0); la t2, mdacc_collapsed_path; sb t1, 0(t2)\n" ++
  "  la t3, mdacc_leaf_path; addi t2, t2, 1; la t0, mdacc_leaf_path_len; ld t4, 0(t0)\n" ++
  ".Lmdacc_cpath_cp:\n" ++
  "  beqz t4, .Lmdacc_cpath_done\n" ++
  "  lbu t5, 0(t3); sb t5, 0(t2); addi t3, t3, 1; addi t2, t2, 1; addi t4, t4, -1; j .Lmdacc_cpath_cp\n" ++
  ".Lmdacc_cpath_done:\n" ++
  "  la t0, mdacc_leaf_path_len; ld a1, 0(t0); addi a1, a1, 1\n" ++
  "  la a0, mdacc_collapsed_path; la t0, mdacc_leaf_value_ptr; ld a2, 0(t0); la t0, mdacc_leaf_value_len; ld a3, 0(t0)\n" ++
  "  la a4, mset_node; la a5, mset_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la t0, mset_node_len; ld s4, 0(t0)\n" ++
  "  la a0, mset_node; mv a1, s4\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  addi s7, s6, -1\n" ++
  "  j .Lmdacc_bubble\n" ++
  ".Lmdacc_collapse_extension_child:\n" ++
  "  la t0, mdacc_child_ptr; ld a0, 0(t0)\n" ++
  "  la t0, mdacc_child_len; ld a1, 0(t0)\n" ++
  "  la a2, mdacc_leaf_path; la a3, mdacc_leaf_path_len; la a4, mdacc_leaf_value_ptr; la a5, mdacc_leaf_value_len\n" ++
  "  jal ra, mpt_extension_extract\n" ++
  "  bnez a0, .Lmdacc_need_collapse\n" ++
  "  la t0, mdacc_survivor_nibble; ld t1, 0(t0); la t2, mdacc_collapsed_path; sb t1, 0(t2)\n" ++
  "  la t3, mdacc_leaf_path; addi t2, t2, 1; la t0, mdacc_leaf_path_len; ld t4, 0(t0)\n" ++
  ".Lmdacc_epath_cp:\n" ++
  "  beqz t4, .Lmdacc_epath_done\n" ++
  "  lbu t5, 0(t3); sb t5, 0(t2); addi t3, t3, 1; addi t2, t2, 1; addi t4, t4, -1; j .Lmdacc_epath_cp\n" ++
  ".Lmdacc_epath_done:\n" ++
  "  la t0, mdacc_leaf_value_ptr; ld t0, 0(t0)\n" ++
  "  la t1, mdacc_leaf_value_len; ld t2, 0(t1)\n" ++
  "  li t3, 32; bne t2, t3, .Lmdacc_ext_child_inline\n" ++
  "  la t4, mset_ref; li t5, 0xa0; sb t5, 0(t4); addi t4, t4, 1; li t5, 32\n" ++
  ".Lmdacc_ext_child_hash_cp:\n" ++
  "  beqz t5, .Lmdacc_ext_child_hash_done\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_ext_child_hash_cp\n" ++
  ".Lmdacc_ext_child_hash_done:\n" ++
  "  li t5, 33; la t4, mset_ref_len; sd t5, 0(t4); j .Lmdacc_ext_child_ready\n" ++
  ".Lmdacc_ext_child_inline:\n" ++
  "  la t4, mset_ref; mv t5, t2\n" ++
  ".Lmdacc_ext_child_inline_cp:\n" ++
  "  beqz t5, .Lmdacc_ext_child_inline_done\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_ext_child_inline_cp\n" ++
  ".Lmdacc_ext_child_inline_done:\n" ++
  "  la t4, mset_ref_len; sd t2, 0(t4)\n" ++
  ".Lmdacc_ext_child_ready:\n" ++
  "  la t0, mdacc_leaf_path_len; ld a1, 0(t0); addi a1, a1, 1\n" ++
  "  la a0, mdacc_collapsed_path; la a2, mset_ref; la t0, mset_ref_len; ld a3, 0(t0)\n" ++
  "  la a4, mset_node; la a5, mset_node_len\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  la t0, mset_node_len; ld s4, 0(t0)\n" ++
  "  la a0, mset_node; mv a1, s4\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  addi s7, s6, -1\n" ++
  "  j .Lmdacc_bubble\n" ++
  ".Lmdacc_collapse_branch_child:\n" ++
  "  la t0, mdacc_survivor_nibble; ld t1, 0(t0); la t2, mdacc_collapsed_path; sb t1, 0(t2)\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, t1\n" ++
  "  la a3, mw_child_offset; la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmdacc_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  li t2, 32; bne t1, t2, .Lmdacc_need_collapse\n" ++
  "  la t0, mw_child_offset; ld t0, 0(t0); add t0, s3, t0\n" ++
  "  la t4, mset_ref; li t5, 0xa0; sb t5, 0(t4); addi t4, t4, 1; li t5, 32\n" ++
  ".Lmdacc_branch_child_hash_cp:\n" ++
  "  beqz t5, .Lmdacc_branch_child_hash_done\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_branch_child_hash_cp\n" ++
  ".Lmdacc_branch_child_hash_done:\n" ++
  "  la t4, mset_ref_len; li t5, 33; sd t5, 0(t4)\n" ++
  "  la a0, mdacc_collapsed_path; li a1, 1; la a2, mset_ref; li a3, 33\n" ++
  "  la a4, mset_node; la a5, mset_node_len\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  la t0, mset_node_len; ld s4, 0(t0)\n" ++
  "  la a0, mset_node; mv a1, s4\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  addi s7, s6, -1\n" ++
  "  j .Lmdacc_bubble\n" ++
  ".Lmdacc_no_collapse_needed:\n" ++
  "  # current_ref = RLP empty string/list item (0x80), the canonical empty\n" ++
  "  # branch child reference.\n" ++
  "  la t0, mset_ref; li t1, 0x80; sb t1, 0(t0)\n" ++
  "  la t0, mset_ref_len; li t1, 1; sd t1, 0(t0)\n" ++
  "  mv s7, s6                   # i = depth\n" ++
  ".Lmdacc_bubble:\n" ++
  "  beqz s7, .Lmdacc_root\n" ++
  "  addi s7, s7, -1\n" ++
  "  la t0, mset_stack; slli t1, s7, 5; add t0, t0, t1\n" ++
  "  ld t2, 0(t0)                # node_ptr ABS\n" ++
  "  ld t3, 8(t0)                # node_len\n" ++
  "  ld t4, 16(t0)               # kind\n" ++
  "  li t6, 1; beq t4, t6, .Lmdacc_bubble_extension\n" ++
  "  bnez t4, .Lmdacc_need_collapse\n" ++
  "  ld t5, 24(t0)               # branch nibble\n" ++
  "  mv a0, t2; mv a1, t3; mv a2, t5\n" ++
  "  la a3, mset_ref; la t0, mset_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, mset_node; la a6, mset_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lmdacc_fail\n" ++
  "  la t0, mset_node_len; ld s4, 0(t0)\n" ++
  "  la a0, mset_node; mv a1, s4\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  j .Lmdacc_bubble\n" ++
  ".Lmdacc_bubble_extension:\n" ++
  "  mv a0, t2; mv a1, t3\n" ++
  "  la a2, mdacc_leaf_path; la a3, mdacc_leaf_path_len; la a4, mdacc_leaf_value_ptr; la a5, mdacc_leaf_value_len\n" ++
  "  jal ra, mpt_extension_extract\n" ++
  "  bnez a0, .Lmdacc_need_collapse\n" ++
  "  la t0, mdacc_leaf_path_len; ld t4, 0(t0); la t1, mdacc_ext_path_len; sd t4, 0(t1)\n" ++
  "  la t2, mdacc_leaf_path; la t3, mdacc_collapsed_path\n" ++
  ".Lmdacc_bext_path_cp:\n" ++
  "  beqz t4, .Lmdacc_bext_path_done\n" ++
  "  lbu t5, 0(t2); sb t5, 0(t3); addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lmdacc_bext_path_cp\n" ++
  ".Lmdacc_bext_path_done:\n" ++
  "  la a0, mset_node; mv a1, s4\n" ++
  "  la a2, mdacc_leaf_path; la a3, mdacc_leaf_path_len; la a4, mdacc_leaf_value_ptr; la a5, mdacc_leaf_value_len\n" ++
  "  jal ra, mpt_leaf_extract\n" ++
  "  beqz a0, .Lmdacc_bubble_ext_leaf\n" ++
  "  la a0, mset_node; mv a1, s4\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  li t0, 1; beq a0, t0, .Lmdacc_bubble_ext_ext\n" ++
  "  li t0, 2; beq a0, t0, .Lmdacc_need_collapse\n" ++
  "  li t0, 3; beq a0, t0, .Lmdacc_need_collapse\n" ++
  ".Lmdacc_bubble_ext_rewrap:\n" ++
  "  la a0, mdacc_collapsed_path; la t0, mdacc_ext_path_len; ld a1, 0(t0)\n" ++
  "  la a2, mset_ref; la t0, mset_ref_len; ld a3, 0(t0)\n" ++
  "  la a4, mset_node; la a5, mset_node_len\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  la t0, mset_node_len; ld s4, 0(t0)\n" ++
  "  la a0, mset_node; mv a1, s4\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  j .Lmdacc_bubble\n" ++
  ".Lmdacc_bubble_ext_ext:\n" ++
  "  la a0, mset_node; mv a1, s4\n" ++
  "  la a2, mdacc_leaf_path; la a3, mdacc_leaf_path_len; la a4, mdacc_leaf_value_ptr; la a5, mdacc_leaf_value_len\n" ++
  "  jal ra, mpt_extension_extract\n" ++
  "  bnez a0, .Lmdacc_need_collapse\n" ++
  "  la t0, mdacc_ext_path_len; ld t1, 0(t0)\n" ++
  "  la t2, mdacc_collapsed_path; add t2, t2, t1\n" ++
  "  la t3, mdacc_leaf_path; la t0, mdacc_leaf_path_len; ld t4, 0(t0)\n" ++
  ".Lmdacc_bext_ext_path_cp:\n" ++
  "  beqz t4, .Lmdacc_bext_ext_path_done\n" ++
  "  lbu t5, 0(t3); sb t5, 0(t2); addi t3, t3, 1; addi t2, t2, 1; addi t4, t4, -1; j .Lmdacc_bext_ext_path_cp\n" ++
  ".Lmdacc_bext_ext_path_done:\n" ++
  "  la t0, mdacc_ext_path_len; ld t1, 0(t0); la t0, mdacc_leaf_path_len; ld t2, 0(t0); add t1, t1, t2; la t0, mdacc_ext_path_len; sd t1, 0(t0)\n" ++
  "  la t0, mdacc_leaf_value_ptr; ld t0, 0(t0)\n" ++
  "  la t1, mdacc_leaf_value_len; ld t2, 0(t1)\n" ++
  "  li t3, 32; bne t2, t3, .Lmdacc_bext_ext_inline\n" ++
  "  la t4, mset_ref; li t5, 0xa0; sb t5, 0(t4); addi t4, t4, 1; li t5, 32\n" ++
  ".Lmdacc_bext_ext_hash_cp:\n" ++
  "  beqz t5, .Lmdacc_bext_ext_hash_done\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_bext_ext_hash_cp\n" ++
  ".Lmdacc_bext_ext_hash_done:\n" ++
  "  la t4, mset_ref_len; li t5, 33; sd t5, 0(t4); j .Lmdacc_bubble_ext_rewrap\n" ++
  ".Lmdacc_bext_ext_inline:\n" ++
  "  la t4, mset_ref; mv t5, t2\n" ++
  ".Lmdacc_bext_ext_inline_cp:\n" ++
  "  beqz t5, .Lmdacc_bext_ext_inline_done\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_bext_ext_inline_cp\n" ++
  ".Lmdacc_bext_ext_inline_done:\n" ++
  "  la t4, mset_ref_len; sd t2, 0(t4); j .Lmdacc_bubble_ext_rewrap\n" ++
  ".Lmdacc_bubble_ext_leaf:\n" ++
  "  la t0, mdacc_ext_path_len; ld t1, 0(t0)\n" ++
  "  la t2, mdacc_collapsed_path; add t2, t2, t1\n" ++
  "  la t3, mdacc_leaf_path; la t0, mdacc_leaf_path_len; ld t4, 0(t0)\n" ++
  ".Lmdacc_bext_leaf_cp:\n" ++
  "  beqz t4, .Lmdacc_bext_leaf_done\n" ++
  "  lbu t5, 0(t3); sb t5, 0(t2); addi t3, t3, 1; addi t2, t2, 1; addi t4, t4, -1; j .Lmdacc_bext_leaf_cp\n" ++
  ".Lmdacc_bext_leaf_done:\n" ++
  "  la t0, mdacc_ext_path_len; ld a1, 0(t0); la t0, mdacc_leaf_path_len; ld t1, 0(t0); add a1, a1, t1\n" ++
  "  la a0, mdacc_collapsed_path; la t0, mdacc_leaf_value_ptr; ld a2, 0(t0); la t0, mdacc_leaf_value_len; ld a3, 0(t0)\n" ++
  "  la a4, mset_node; la a5, mset_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la t0, mset_node_len; ld s4, 0(t0)\n" ++
  "  la a0, mset_node; mv a1, s4\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  j .Lmdacc_bubble\n" ++
  ".Lmdacc_root:\n" ++
  "  la a0, mset_node; mv a1, s4; mv a2, s5\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lmdacc_ret\n" ++
  ".Lmdacc_empty_root:\n" ++
  "  la t0, iw_empty_trie_root\n" ++
  "  ld t1, 0(t0); sd t1, 0(s5)\n" ++
  "  ld t1, 8(t0); sd t1, 8(s5)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s5)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmdacc_ret\n" ++
  ".Lmdacc_need_collapse:\n" ++
  "  li a0, 3\n" ++
  "  j .Lmdacc_ret\n" ++
  ".Lmdacc_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmdacc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- Probe input (file maps to INPUT+8):
      +8 witness_len | +16 path_len | +24 root_hash | +56 path | witness.
    Output: root@0, status@32. -/
def ziskMptDeleteAccPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, mset_db_count; sd zero, 0(t0)\n" ++
  "  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)\n" ++
  "  jal ra, mpt_resolve_cache_reset\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness_len\n" ++
  "  ld a4, 16(t0)               # path_len\n" ++
  "  addi a0, t0, 24             # root_hash ptr\n" ++
  "  addi a3, t0, 56             # path ptr\n" ++
  "  add t1, a3, a4; addi t1, t1, 7; andi t1, t1, -8\n" ++
  "  mv a1, t1                   # witness ptr\n" ++
  "  li a7, 0xa0010000           # out root\n" ++
  "  jal ra, mpt_delete_acc\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)\n" ++
  "  j .Lmdacc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  mptDeleteAccFunction ++ "\n" ++
  ".Lmdacc_pdone:"

def ziskMptDeleteAccDataSection : String :=
  ziskMptSetAccDataSection ++ "\n" ++
  ".balign 8\n" ++
  "mle_path_off:\n  .zero 8\n" ++
  "mle_path_len:\n  .zero 8\n" ++
  "mdacc_witness_len:\n  .zero 8\n" ++
  "mdacc_survivor_nibble:\n  .zero 8\n" ++
  "mdacc_child_ptr:\n  .zero 8\n" ++
  "mdacc_child_len:\n  .zero 8\n" ++
  "mdacc_leaf_path_len:\n  .zero 8\n" ++
  "mdacc_ext_path_len:\n  .zero 8\n" ++
  "mdacc_leaf_value_ptr:\n  .zero 8\n" ++
  "mdacc_leaf_value_len:\n  .zero 8\n" ++
  "mee_path_off:\n  .zero 8\n" ++
  "mee_path_len:\n  .zero 8\n" ++
  "mxne_field_len:\n  .zero 8\n" ++
  "mxne_hp_len:\n  .zero 8\n" ++
  "mxne_cursor:\n  .zero 8\n" ++
  "mxne_total_payload:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "mdacc_leaf_path:\n  .zero 128\n" ++
  "mdacc_collapsed_path:\n  .zero 128\n" ++
  "mxne_hp_buf:\n  .zero 1024\n" ++
  "mxne_payload_buf:\n  .zero 16384\n" ++
  ".balign 32\n" ++
  iwEmptyTrieRootData

def ziskMptDeleteAccProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptDeleteAccPrologue
  dataAsm     := ziskMptDeleteAccDataSection
}

end EvmAsm.Codegen
