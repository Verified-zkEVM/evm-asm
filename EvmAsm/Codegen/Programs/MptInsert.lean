/-
  EvmAsm.Codegen.Programs.MptInsert

  mpt_insert (bead evm-asm-fhsxz.2.4.2.6.2): insert a NEW key into a witness-
  backed MPT and return the new root. Account creation for withdrawals to
  absent / precompile recipients (parent bead .2.4.2.6).

  Composes mpt_insert_walk (sibling .1, classifies WHERE the absent key
  diverges) + a per-case terminal restructure + the SAME bubble-up pass that
  mpt_set uses (re-encode each ancestor's touched slot, hash at >=32 B, keccak
  the root).

  Cases supported in THIS slice (sound for fixed-length 64-nibble account
  paths, which never end inside a node):
    case 3 EMPTY_TRIE        : root := keccak(leaf(full_path, value)).
    case 0 BRANCH_EMPTY_SLOT : fill the terminal branch's empty slot
                               path[consumed] with leaf(path[consumed+1..],
                               value); bubble up the ancestor stack.
    case 1 LEAF_SPLIT        : split terminal leaf into a new branch, optionally
                               wrapped by an extension.
    case 2 EXTENSION_SPLIT   : split terminal extension into a new branch,
                               optionally wrapped by the shared prefix.

  Conservative (returns status 1, caller -> conservative MISS, never a false
  positive) on case 4 EXISTS / 5 BRANCH_VALUE, which are not on the
  withdrawal-insert path.

  Reuses mpt_set's leaf encoder / node-slot encoder / splice helpers verbatim.
  All scratch is 8-aligned; the no-misaligned invariant holds (nibbles read
  byte-wise inside the reused helpers).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptSet
import EvmAsm.Codegen.Programs.MptInsertWalk
import EvmAsm.Codegen.Programs.MptInternal
import EvmAsm.Codegen.Programs.MptEncode

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_insert -- insert a NEW (path, value), recompute the root.

    Calling convention (mirrors mpt_set, with value where new_value was):
      a0 (input)  : root_hash ptr (32 bytes)
      a1 (input)  : witness section ptr
      a2 (input)  : witness section length
      a3 (input)  : path_nibbles ptr (one byte per nibble)
      a4 (input)  : path_nibbles length
      a5 (input)  : value ptr
      a6 (input)  : value length
      a7 (input)  : out_root ptr (32 bytes, written on success)
      a0 (output) : 0 (ok) / 1 (unsupported divergence / incomplete witness ->
                    conservative) / 2 (parse / splice fail) -/
def mptInsertFunction : String :=
  "mpt_insert:\n" ++
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
  "  la t0, ins_wl; sd a2, 0(t0) # stash witness_len\n" ++
  "  # ---- classify divergence (a0=root_hash unchanged) ----\n" ++
  "  mv a1, s0\n" ++
  "  la t0, ins_wl; ld a2, 0(t0)\n" ++
  "  mv a3, s1\n" ++
  "  mv a4, s2\n" ++
  "  la a5, ins_stack\n" ++
  "  la a6, ins_meta\n" ++
  "  jal ra, mpt_insert_walk\n" ++
  "  bnez a0, .Lins_ret          # incomplete witness / parse -> propagate\n" ++
  "  la t0, ins_meta\n" ++
  "  ld s6, 0(t0)                # depth (ancestors)\n" ++
  "  ld s8, 8(t0)                # consumed (ancestor nibbles)\n" ++
  "  ld t1, 16(t0)               # case\n" ++
  "  li t2, 3; beq t1, t2, .Lins_empty\n" ++
  "  li t2, 0; beq t1, t2, .Lins_branch_empty\n" ++
  "  li t2, 1; beq t1, t2, .Lins_leaf_split\n" ++
  "  li t2, 2; beq t1, t2, .Lins_ext_split\n" ++
  "  li a0, 1; j .Lins_ret       # exists / branch-value: conservative\n" ++
  ".Lins_empty:\n" ++
  "  # root := keccak(leaf(full path, value)).\n" ++
  "  mv a0, s1; mv a1, s2; mv a2, s3; mv a3, s4\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0); mv a2, s5\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0; j .Lins_ret\n" ++
  ".Lins_leaf_split:\n" ++
  "  # split the terminal leaf: shared prefix m = match_len. Build a branch with\n" ++
  "  # the old leaf' at K[m] and the new leaf at P[m]; wrap in extension if m>0.\n" ++
  "  la t0, ins_meta; ld t1, 24(t0); add a0, s0, t1     # terminal leaf ptr\n" ++
  "  la t0, ins_meta; ld a1, 32(t0)                      # terminal len\n" ++
  "  la a2, ins_k; la a3, ins_kcount; la a4, ins_lv_ptr; la a5, ins_lv_len\n" ++
  "  jal ra, mpt_leaf_extract\n" ++
  "  bnez a0, .Lins_fail\n" ++
  "  la t0, ins_meta; ld t1, 40(t0); la t2, ins_m; sd t1, 0(t2)   # m\n" ++
  "  # nibble_old = K[m]; nibble_new = path[consumed + m]\n" ++
  "  la t2, ins_k; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_niba; sd t3, 0(t4)\n" ++
  "  add t2, s1, s8; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_nibb; sd t3, 0(t4)\n" ++
  "  # old_leaf' = leaf(K[m+1..], LV) -> ins_node ; ref_old -> ins_ref\n" ++
  "  la t0, ins_kcount; ld t1, 0(t0); la t2, ins_m; ld t3, 0(t2)\n" ++
  "  la a0, ins_k; add a0, a0, t3; addi a0, a0, 1\n" ++
  "  sub a1, t1, t3; addi a1, a1, -1\n" ++
  "  la t0, ins_lv_ptr; ld a2, 0(t0); la t0, ins_lv_len; ld a3, 0(t0)\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  # new_leaf = leaf(P[m+1..], value) -> ins_node2 ; ref_new -> ins_ref2\n" ++
  "  la t2, ins_m; ld t3, 0(t2)\n" ++
  "  add a0, s1, s8; add a0, a0, t3; addi a0, a0, 1\n" ++
  "  sub a1, s2, s8; sub a1, a1, t3; addi a1, a1, -1\n" ++
  "  mv a2, s3; mv a3, s4\n" ++
  "  la a4, ins_node2; la a5, ins_node2_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref2; la a3, ins_ref2_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  # branch = splice(empty_branch, K[m], ref_old) then splice(.., P[m], ref_new)\n" ++
  "  la a0, ins_empty_branch; li a1, 18\n" ++
  "  la t0, ins_niba; ld a2, 0(t0)\n" ++
  "  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node; la a6, ins_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lins_fail\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la t0, ins_nibb; ld a2, 0(t0)\n" ++
  "  la a3, ins_ref2; la t0, ins_ref2_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node2; la a6, ins_node2_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lins_fail\n" ++
  "  # branch node is in ins_node2; ref -> ins_ref\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  # copy the branch into ins_node so .Lins_root (m=0, depth=0) hashes it\n" ++
  "  la t0, ins_node2_len; ld t1, 0(t0); la t2, ins_node_len; sd t1, 0(t2)\n" ++
  "  la a0, ins_node; la a1, ins_node2; mv a2, t1\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  # if m > 0: wrap extension(K[0..m] -> branch_ref) -> ins_node ; ref -> ins_ref\n" ++
  "  la t0, ins_m; ld t1, 0(t0); beqz t1, .Lins_ls_bubble\n" ++
  "  la a0, ins_k; mv a1, t1\n" ++
  "  la a2, ins_ref; la t0, ins_ref_len; ld a3, 0(t0)\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  ".Lins_ls_bubble:\n" ++
  "  mv s7, s6\n" ++
  "  j .Lins_bubble\n" ++
  ".Lins_ext_split:\n" ++
  "  # split the terminal extension: old child/ref on K[m], new leaf on P[m],\n" ++
  "  # with the shared prefix wrapped back into an extension when m > 0.\n" ++
  "  la t0, ins_meta; ld t1, 24(t0); add s9, s0, t1     # terminal extension ptr\n" ++
  "  la t0, ins_meta; ld a1, 32(t0)                      # terminal len\n" ++
  "  mv a0, s9; li a2, 0; la a3, mle_path_off; la a4, mle_path_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lins_fail\n" ++
  "  la t0, mle_path_off; ld t0, 0(t0); add a0, s9, t0\n" ++
  "  la t0, mle_path_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_k; la a3, ins_kcount; la a4, ins_niba\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Lins_fail\n" ++
  "  la t0, ins_niba; ld t0, 0(t0); bnez t0, .Lins_fail\n" ++
  "  # child_ref from extension item 1. rlp_list_nth_item strips the 0xa0 byte\n" ++
  "  # for hash refs, so re-wrap 32-byte refs before extension encoding.\n" ++
  "  la t0, ins_meta; ld a1, 32(t0); mv a0, s9; li a2, 1; la a3, mle_path_off; la a4, ins_lv_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lins_fail\n" ++
  "  la t0, mle_path_off; ld t0, 0(t0); add t0, s9, t0; la t1, ins_lv_ptr; sd t0, 0(t1)\n" ++
  "  la t1, ins_lv_len; ld t2, 0(t1); li t3, 32; bne t2, t3, .Lins_ext_child_inline\n" ++
  "  la t4, ins_ref; li t5, 0xa0; sb t5, 0(t4); addi t4, t4, 1; li t5, 32\n" ++
  ".Lins_ext_child_hash_cp:\n" ++
  "  beqz t5, .Lins_ext_child_hash_done\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lins_ext_child_hash_cp\n" ++
  ".Lins_ext_child_hash_done:\n" ++
  "  li t5, 33; la t4, ins_ref_len; sd t5, 0(t4); j .Lins_ext_child_ready\n" ++
  ".Lins_ext_child_inline:\n" ++
  "  la t4, ins_ref; mv t5, t2\n" ++
  ".Lins_ext_child_inline_cp:\n" ++
  "  beqz t5, .Lins_ext_child_inline_done\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lins_ext_child_inline_cp\n" ++
  ".Lins_ext_child_inline_done:\n" ++
  "  la t4, ins_ref_len; sd t2, 0(t4)\n" ++
  ".Lins_ext_child_ready:\n" ++
  "  la t0, ins_meta; ld t1, 40(t0); la t2, ins_m; sd t1, 0(t2)\n" ++
  "  la t2, ins_k; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_niba; sd t3, 0(t4)\n" ++
  "  add t2, s1, s8; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_nibb; sd t3, 0(t4)\n" ++
  "  # old side: wrap the extension remainder after the divergent nibble when\n" ++
  "  # it is non-empty, otherwise reuse the existing child ref directly.\n" ++
  "  la t0, ins_kcount; ld t1, 0(t0); la t2, ins_m; ld t3, 0(t2)\n" ++
  "  sub t4, t1, t3; addi t4, t4, -1\n" ++
  "  beqz t4, .Lins_ext_old_ready\n" ++
  "  la a0, ins_k; add a0, a0, t3; addi a0, a0, 1\n" ++
  "  mv a1, t4; la a2, ins_ref; la t0, ins_ref_len; ld a3, 0(t0)\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  ".Lins_ext_old_ready:\n" ++
  "  # new side leaf = leaf(path[consumed+m+1..], value).\n" ++
  "  la t2, ins_m; ld t3, 0(t2)\n" ++
  "  add a0, s1, s8; add a0, a0, t3; addi a0, a0, 1\n" ++
  "  sub a1, s2, s8; sub a1, a1, t3; addi a1, a1, -1\n" ++
  "  mv a2, s3; mv a3, s4\n" ++
  "  la a4, ins_node2; la a5, ins_node2_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref2; la a3, ins_ref2_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  # branch with old and new children.\n" ++
  "  la a0, ins_empty_branch; li a1, 18\n" ++
  "  la t0, ins_niba; ld a2, 0(t0)\n" ++
  "  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node; la a6, ins_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lins_fail\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la t0, ins_nibb; ld a2, 0(t0)\n" ++
  "  la a3, ins_ref2; la t0, ins_ref2_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node2; la a6, ins_node2_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lins_fail\n" ++
  "  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  la t0, ins_node2_len; ld t1, 0(t0); la t2, ins_node_len; sd t1, 0(t2)\n" ++
  "  la a0, ins_node; la a1, ins_node2; mv a2, t1\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  la t0, ins_m; ld t1, 0(t0); beqz t1, .Lins_ext_bubble\n" ++
  "  la a0, ins_k; mv a1, t1\n" ++
  "  la a2, ins_ref; la t0, ins_ref_len; ld a3, 0(t0)\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_extension_node_encode\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  ".Lins_ext_bubble:\n" ++
  "  mv s7, s6\n" ++
  "  j .Lins_bubble\n" ++
  ".Lins_branch_empty:\n" ++
  "  # leaf = leaf(path[consumed+1..], value).\n" ++
  "  add a0, s1, s8; addi a0, a0, 1\n" ++
  "  sub a1, s2, s8; addi a1, a1, -1\n" ++
  "  mv a2, s3; mv a3, s4\n" ++
  "  la a4, ins_node; la a5, ins_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  # leaf_ref = node_slot_encode(leaf).\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  # splice the terminal branch's slot[path[consumed]] := leaf_ref.\n" ++
  "  la t0, ins_meta; ld t1, 24(t0)        # terminal_offset\n" ++
  "  add a0, s0, t1\n" ++
  "  la t0, ins_meta; ld a1, 32(t0)        # terminal_len\n" ++
  "  add t2, s1, s8; lbu a2, 0(t2)         # nibble = path[consumed]\n" ++
  "  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node; la a6, ins_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lins_fail\n" ++
  "  # ins_ref := node_slot_encode(new branch), then bubble up.\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  mv s7, s6                   # i = depth\n" ++
  ".Lins_bubble:\n" ++
  "  beqz s7, .Lins_root\n" ++
  "  addi s7, s7, -1\n" ++
  "  la t0, ins_stack\n" ++
  "  slli t1, s7, 5; add t0, t0, t1        # &record[i]\n" ++
  "  ld t2, 0(t0)                # node_offset\n" ++
  "  ld t3, 8(t0)                # node_len\n" ++
  "  ld t4, 16(t0)               # kind (0 branch / 1 ext)\n" ++
  "  ld t5, 24(t0)               # nibble\n" ++
  "  add a0, s0, t2; mv a1, t3\n" ++
  "  beqz t4, .Lins_k_branch\n" ++
  "  li a2, 1; j .Lins_k_done\n" ++
  ".Lins_k_branch:\n" ++
  "  mv a2, t5\n" ++
  ".Lins_k_done:\n" ++
  "  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, ins_node; la a6, ins_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lins_fail\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)\n" ++
  "  la a2, ins_ref; la a3, ins_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  j .Lins_bubble\n" ++
  ".Lins_root:\n" ++
  "  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0); mv a2, s5\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  ".Lins_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  ".Lins_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lins_ret"

/-- `zisk_mpt_insert`: probe BuildUnit. Reuses `scripts/mpt_ref.py`
    `build_probe_input` layout (value where new_value was) and writes the new
    32-byte root to OUTPUT+0, status to OUTPUT+32 -- same as the mpt_set probe,
    so the check script compares OUTPUT[0:32] against the reference root.
    Output layout:
      OUTPUT+0  : 32-byte recomputed new root
      OUTPUT+32 : status (0 ok / 1 unsupported|miss / 2 fail) -/
def ziskMptInsertPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness_len\n" ++
  "  ld a4, 16(t0)               # path_len\n" ++
  "  ld a6, 24(t0)               # value_len\n" ++
  "  addi a0, t0, 32             # root_hash ptr (INPUT+32)\n" ++
  "  addi a3, t0, 64             # path ptr (INPUT+64)\n" ++
  "  add a5, a3, a4              # value ptr = path + path_len\n" ++
  "  add t1, a4, a6\n" ++
  "  addi t1, t1, 7\n" ++
  "  andi t1, t1, -8\n" ++
  "  add a1, a3, t1             # witness ptr\n" ++
  "  li a7, 0xa0010000          # out_root at OUTPUT+0 (32 B)\n" ++
  "  jal ra, mpt_insert\n" ++
  "  li t0, 0xa0010020\n" ++
  "  sd a0, 0(t0)               # status at OUTPUT+32\n" ++
  "  j .Lmins_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptInsertWalkFunction ++ "\n" ++
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
  mptInsertFunction ++ "\n" ++
  ".Lmins_pdone:"

/-- Data section: the mpt_set probe scratch (mw_*, mlnen_*, mset_*) + the
    walk's `iw_empty_trie_root` + mpt_insert's own buffers (`ins_*`). All
    labels are disjoint. -/
def ziskMptInsertDataSection : String :=
  ziskMptSetDataSection ++ "\n" ++
  ".balign 8\n" ++
  iwEmptyTrieRootData ++ "\n" ++
  ".balign 8\n" ++
  "ins_wl:\n  .zero 8\n" ++
  "ins_node_len:\n  .zero 8\n" ++
  "ins_ref_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "ins_meta:\n  .zero 48\n" ++
  ".balign 8\n" ++
  "ins_stack:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "ins_ref:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_node:\n  .zero 2048\n" ++
  -- leaf-split scratch + buffers (and mpt_leaf_extract's mle_* scratch)
  ".balign 8\n" ++
  "mle_path_off:\n  .zero 8\n" ++
  "mle_path_len:\n  .zero 8\n" ++
  "ins_kcount:\n  .zero 8\n" ++
  "ins_lv_ptr:\n  .zero 8\n" ++
  "ins_lv_len:\n  .zero 8\n" ++
  "ins_m:\n  .zero 8\n" ++
  "ins_niba:\n  .zero 8\n" ++
  "ins_nibb:\n  .zero 8\n" ++
  "ins_node2_len:\n  .zero 8\n" ++
  "ins_ref2_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "ins_k:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_ref2:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_node2:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "ins_empty_branch:\n" ++
  "  .byte 0xd1,0x80,0x80,0x80,0x80,0x80,0x80,0x80\n" ++
  "  .byte 0x80,0x80,0x80,0x80,0x80,0x80,0x80,0x80\n" ++
  "  .byte 0x80,0x80\n" ++
  -- mpt_extension_node_encode scratch (mxne_*)
  ".balign 8\n" ++
  "mxne_field_len:\n  .zero 8\n" ++
  "mxne_hp_len:\n  .zero 8\n" ++
  "mxne_cursor:\n  .zero 8\n" ++
  "mxne_total_payload:\n  .zero 8\n" ++
  "mxne_hp_buf:\n  .zero 1024\n" ++
  "mxne_payload_buf:\n  .zero 16384"

def ziskMptInsertProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptInsertPrologue
  dataAsm     := ziskMptInsertDataSection
}

end EvmAsm.Codegen
