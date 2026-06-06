/-
  EvmAsm.Codegen.Programs.MptInsertAcc

  mpt_insert_acc (bead evm-asm-fhsxz.2.4.2.6.5): insert a NEW key into a
  witness+DB-backed MPT, APPENDING every new node to the appendable node DB so
  that subsequent changes in mpt_state_root see them. The insert analogue of
  mpt_set_acc.

  = mpt_insert (Programs/MptInsert) with three mechanical changes, mirroring
  how mpt_set_acc differs from mpt_set:
    * descend with mpt_insert_walk_db (witness+DB resolve, ABSOLUTE node ptrs);
    * the terminal / ancestor node pointers are ABSOLUTE (no witness-base add);
    * every freshly re-encoded node is node_db_append'd (the new root included,
      so the next change can resolve it).

  Supported cases (sound for 64-nibble account paths): EMPTY_TRIE,
  BRANCH_EMPTY_SLOT, LEAF_SPLIT, EXTENSION_SPLIT. The node DB (mset_db_*) is global
  and reset by the caller (mpt_state_root / the probe) before the first change.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptInsert
import EvmAsm.Codegen.Programs.MptInsertWalkDb

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_insert_acc -- DB-aware insert; appends new nodes to the DB.
    ABI matches mpt_insert (a0=root_hash, a1=witness, a2=witness_len, a3=path,
    a4=path_len, a5=value, a6=value_len, a7=out_root -> a0 = 0/1/2). -/
def mptInsertAccFunction : String :=
  "mpt_insert_acc:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a1                   # witness ptr\n" ++
  "  mv s1, a3                   # path ptr\n" ++
  "  mv s2, a4                   # path_len\n" ++
  "  mv s3, a5                   # value ptr\n" ++
  "  mv s4, a6                   # value_len\n" ++
  "  mv s5, a7                   # out_root\n" ++
  "  la t0, ins_wl; sd a2, 0(t0)\n" ++
  "  mv a1, s0\n" ++
  "  la t0, ins_wl; ld a2, 0(t0)\n" ++
  "  mv a3, s1\n" ++
  "  mv a4, s2\n" ++
  "  la a5, ins_stack\n" ++
  "  la a6, ins_meta\n" ++
  "  jal ra, mpt_insert_walk_db\n" ++
  "  bnez a0, .Lacc_ret\n" ++
  "  la t0, ins_meta\n" ++
  "  ld s6, 0(t0)                # depth\n" ++
  "  ld s8, 8(t0)                # consumed\n" ++
  "  ld t1, 16(t0)               # case\n" ++
  "  li t2, 3; beq t1, t2, .Lacc_empty\n" ++
  "  li t2, 0; beq t1, t2, .Lacc_branch_empty\n" ++
  "  li t2, 1; beq t1, t2, .Lacc_leaf_split\n" ++
  "  li t2, 2; beq t1, t2, .Lacc_ext_split\n" ++
  "  li a0, 1; j .Lacc_ret       # exists / branch-value: conservative\n" ++
  ".Lacc_empty:\n" ++
  "  mv a0, s1; mv a1, s2; mv a2, s3; mv a3, s4\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0); mv a2, s5\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0; j .Lacc_ret\n" ++
  ".Lacc_leaf_split:\n" ++
  "  la t0, ins_meta; ld a0, 24(t0)        # terminal leaf ptr ABSOLUTE\n" ++
  "  la t0, ins_meta; ld a1, 32(t0)\n" ++
  "  la a2, ins_k; la a3, ins_kcount; la a4, ins_lv_ptr; la a5, ins_lv_len\n" ++
  "  jal ra, mpt_leaf_extract\n" ++
  "  bnez a0, .Lacc_fail\n" ++
  "  la t0, ins_meta; ld t1, 40(t0); la t2, ins_m; sd t1, 0(t2)\n" ++
  "  la t2, ins_k; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_niba; sd t3, 0(t4)\n" ++
  "  add t2, s1, s8; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_nibb; sd t3, 0(t4)\n" ++
  "  la t0, ins_kcount; ld t1, 0(t0); la t2, ins_m; ld t3, 0(t2)\n" ++
  "  la a0, ins_k; add a0, a0, t3; addi a0, a0, 1\n" ++
  "  sub a1, t1, t3; addi a1, a1, -1\n" ++
  "  la t0, ins_lv_ptr; ld a2, 0(t0); la t0, ins_lv_len; ld a3, 0(t0)\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  la t2, ins_m; ld t3, 0(t2)\n" ++
  "  add a0, s1, s8; add a0, a0, t3; addi a0, a0, 1\n" ++
  "  sub a1, s2, s8; sub a1, a1, t3; addi a1, a1, -1\n" ++
  "  mv a2, s3; mv a3, s4\n" ++
  "  la a4, ins_node2; la a5, ins_node2_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref2; la a3, ins_ref2_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  la a0, ins_empty_branch; li a1, 18\n" ++
  "  la t0, ins_niba; ld a2, 0(t0)\n" ++
  "  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node; la a6, ins_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lacc_fail\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la t0, ins_nibb; ld a2, 0(t0)\n" ++
  "  la a3, ins_ref2; la t0, ins_ref2_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node2; la a6, ins_node2_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lacc_fail\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  la t0, ins_node2_len; ld t1, 0(t0); la t2, ins_node_len; sd t1, 0(t2)\n" ++
  "  la a0, ins_node; la a1, ins_node2; mv a2, t1\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  la t0, ins_m; ld t1, 0(t0); beqz t1, .Lacc_ls_bubble\n" ++
  "  la a0, ins_k; mv a1, t1\n" ++
  "  la a2, ins_ref; la t0, ins_ref_len; ld a3, 0(t0)\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  ".Lacc_ls_bubble:\n" ++
  "  mv s7, s6\n" ++
  "  j .Lacc_bubble\n" ++
  ".Lacc_ext_split:\n" ++
  "  # Split the terminal extension. Rebuild its remainder under a branch,\n" ++
  "  # add the new leaf on the divergent nibble, optionally wrap the shared\n" ++
  "  # prefix in a new extension, then bubble through ancestors.\n" ++
  "  la t0, ins_meta; ld s9, 24(t0)        # terminal extension ptr ABSOLUTE\n" ++
  "  la t0, ins_meta; ld a1, 32(t0)        # terminal extension len\n" ++
  "  mv a0, s9; li a2, 0; la a3, mle_path_off; la a4, mle_path_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lacc_fail\n" ++
  "  la t0, mle_path_off; ld t0, 0(t0); add a0, s9, t0\n" ++
  "  la t0, mle_path_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_k; la a3, ins_kcount; la a4, ins_niba\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Lacc_fail\n" ++
  "  la t0, ins_niba; ld t0, 0(t0); bnez t0, .Lacc_fail\n" ++
  "  # child_ref from extension item 1. For hash refs, rlp_list_nth_item strips\n" ++
  "  # the 0xa0 byte, so re-wrap 32-byte refs before feeding extension encode.\n" ++
  "  la t0, ins_meta; ld a1, 32(t0); mv a0, s9; li a2, 1; la a3, mle_path_off; la a4, ins_lv_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lacc_fail\n" ++
  "  la t0, mle_path_off; ld t0, 0(t0); add t0, s9, t0; la t1, ins_lv_ptr; sd t0, 0(t1)\n" ++
  "  la t1, ins_lv_len; ld t2, 0(t1); li t3, 32; bne t2, t3, .Lacc_ext_child_inline\n" ++
  "  la t4, ins_ref; li t5, 0xa0; sb t5, 0(t4); addi t4, t4, 1; li t5, 32\n" ++
  ".Lacc_ext_child_hash_cp:\n" ++
  "  beqz t5, .Lacc_ext_child_hash_done\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lacc_ext_child_hash_cp\n" ++
  ".Lacc_ext_child_hash_done:\n" ++
  "  li t5, 33; la t4, ins_ref_len; sd t5, 0(t4); j .Lacc_ext_child_ready\n" ++
  ".Lacc_ext_child_inline:\n" ++
  "  la t4, ins_ref; mv t5, t2\n" ++
  ".Lacc_ext_child_inline_cp:\n" ++
  "  beqz t5, .Lacc_ext_child_inline_done\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lacc_ext_child_inline_cp\n" ++
  ".Lacc_ext_child_inline_done:\n" ++
  "  la t4, ins_ref_len; sd t2, 0(t4)\n" ++
  ".Lacc_ext_child_ready:\n" ++
  "  la t0, ins_meta; ld t1, 40(t0); la t2, ins_m; sd t1, 0(t2)\n" ++
  "  la t2, ins_k; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_niba; sd t3, 0(t4)\n" ++
  "  add t2, s1, s8; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_nibb; sd t3, 0(t4)\n" ++
  "  # old side: if extension remainder after the divergent nibble is non-empty,\n" ++
  "  # wrap the existing child_ref in a shorter extension; otherwise use it as-is.\n" ++
  "  la t0, ins_kcount; ld t1, 0(t0); la t2, ins_m; ld t3, 0(t2)\n" ++
  "  sub t4, t1, t3; addi t4, t4, -1\n" ++
  "  beqz t4, .Lacc_ext_old_ready\n" ++
  "  la a0, ins_k; add a0, a0, t3; addi a0, a0, 1\n" ++
  "  mv a1, t4; la a2, ins_ref; la t0, ins_ref_len; ld a3, 0(t0)\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  ".Lacc_ext_old_ready:\n" ++
  "  # new side leaf = leaf(path[consumed+m+1..], value).\n" ++
  "  la t2, ins_m; ld t3, 0(t2)\n" ++
  "  add a0, s1, s8; add a0, a0, t3; addi a0, a0, 1\n" ++
  "  sub a1, s2, s8; sub a1, a1, t3; addi a1, a1, -1\n" ++
  "  mv a2, s3; mv a3, s4\n" ++
  "  la a4, ins_node2; la a5, ins_node2_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref2; la a3, ins_ref2_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  # branch with old and new children.\n" ++
  "  la a0, ins_empty_branch; li a1, 18\n" ++
  "  la t0, ins_niba; ld a2, 0(t0)\n" ++
  "  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node; la a6, ins_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lacc_fail\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la t0, ins_nibb; ld a2, 0(t0)\n" ++
  "  la a3, ins_ref2; la t0, ins_ref2_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node2; la a6, ins_node2_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lacc_fail\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  la t0, ins_node2_len; ld t1, 0(t0); la t2, ins_node_len; sd t1, 0(t2)\n" ++
  "  la a0, ins_node; la a1, ins_node2; mv a2, t1\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  la t0, ins_m; ld t1, 0(t0); beqz t1, .Lacc_ext_bubble\n" ++
  "  la a0, ins_k; mv a1, t1\n" ++
  "  la a2, ins_ref; la t0, ins_ref_len; ld a3, 0(t0)\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  ".Lacc_ext_bubble:\n" ++
  "  mv s7, s6\n" ++
  "  j .Lacc_bubble\n" ++
  ".Lacc_branch_empty:\n" ++
  "  add a0, s1, s8; addi a0, a0, 1\n" ++
  "  sub a1, s2, s8; addi a1, a1, -1\n" ++
  "  mv a2, s3; mv a3, s4\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  la t0, ins_meta; ld a0, 24(t0)        # terminal branch ptr ABSOLUTE\n" ++
  "  la t0, ins_meta; ld a1, 32(t0)\n" ++
  "  add t2, s1, s8; lbu a2, 0(t2)         # nibble = path[consumed]\n" ++
  "  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node; la a6, ins_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lacc_fail\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  mv s7, s6\n" ++
  ".Lacc_bubble:\n" ++
  "  beqz s7, .Lacc_root\n" ++
  "  addi s7, s7, -1\n" ++
  "  la t0, ins_stack\n" ++
  "  slli t1, s7, 5; add t0, t0, t1\n" ++
  "  ld t2, 0(t0)                # node_ptr ABSOLUTE\n" ++
  "  ld t3, 8(t0)\n" ++
  "  ld t4, 16(t0)\n" ++
  "  ld t5, 24(t0)\n" ++
  "  mv a0, t2; mv a1, t3        # ABSOLUTE src ptr\n" ++
  "  beqz t4, .Lacc_k_branch\n" ++
  "  li a2, 1; j .Lacc_k_done\n" ++
  ".Lacc_k_branch:\n" ++
  "  mv a2, t5\n" ++
  ".Lacc_k_done:\n" ++
  "  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node; la a6, ins_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lacc_fail\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  jal ra, node_db_append\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  j .Lacc_bubble\n" ++
  ".Lacc_root:\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0); mv a2, s5\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  ".Lacc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  ".Lacc_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lacc_ret"

/-- `zisk_mpt_insert_acc`: probe. Resets the node DB, then a SINGLE insert
    (same input layout as zisk_mpt_insert). With the DB empty every node is
    resolved from the witness, so the new root equals the witness-only
    mpt_insert root -- verified against the mi_* vectors. The DB-resolve path
    is exercised by the mpt_set_acc verification (same mpt_node_resolve) and,
    end-to-end, by the .3 integration. Output: OUTPUT+0 root, OUTPUT+32 status. -/
def ziskMptInsertAccPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, mset_db_count; sd zero, 0(t0)\n" ++
  "  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)\n" ++
  "  jal ra, mpt_resolve_cache_reset\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness_len\n" ++
  "  ld a4, 16(t0)               # path_len\n" ++
  "  ld a6, 24(t0)               # value_len\n" ++
  "  addi a0, t0, 32             # root_hash ptr\n" ++
  "  addi a3, t0, 64             # path ptr\n" ++
  "  add a5, a3, a4              # value ptr\n" ++
  "  add t1, a4, a6\n" ++
  "  addi t1, t1, 7\n" ++
  "  andi t1, t1, -8\n" ++
  "  add a1, a3, t1             # witness ptr\n" ++
  "  li a7, 0xa0010000          # out_root\n" ++
  "  jal ra, mpt_insert_acc\n" ++
  "  li t0, 0xa0010020\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lacc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
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
  mptExtensionNodeEncodeFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  ".Lacc_pdone:"

/-- Data: the mpt_insert probe scratch/buffers (mw_*, mlnen_*, mset_* [set],
    iw_empty_trie_root, ins_*, mxne_*) + the DB-resolve labels (mset_res_*,
    iwd_*) + the node DB (mset_db_*). -/
def ziskMptInsertAccDataSection : String :=
  ziskMptInsertDataSection ++ "\n" ++
  ".balign 8\n" ++
  "mset_res_off:\n  .zero 8\n" ++
  "mset_res_len:\n  .zero 8\n" ++
  "iwd_ptr:\n  .zero 8\n" ++
  "iwd_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "iwd_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "mset_db_count:\n  .zero 8\n" ++
  "mset_db_top:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "mset_db_hash:\n  .zero 32\n" ++
  mptResolveCacheDataSection ++ "\n" ++
  ".balign 8\n" ++
  "mset_db_data:\n  .zero 8388608"

def ziskMptInsertAccProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptInsertAccPrologue
  dataAsm     := ziskMptInsertAccDataSection
}

end EvmAsm.Codegen
