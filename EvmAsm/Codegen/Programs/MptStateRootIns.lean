/-
  EvmAsm.Codegen.Programs.MptStateRootIns

  mpt_state_root_ins (bead evm-asm-fhsxz.2.4.2.6.3): the insert-aware multi-
  change post-state-root driver. Like mpt_state_root, but each change carries a
  mutation mode and dispatches to mpt_set_acc (0), mpt_insert_acc (1),
  mpt_delete_acc (2), or no-op (3). All mutators share the global appendable node DB,
  so changes thread
  sequentially: a modify (e.g. an EIP-2935/4788 system write) populates the DB,
  and a later insert (e.g. a withdrawal to a precompile/absent account) resolves
  the updated root from it.

  Change descriptor (40 bytes):
    +0 path_ptr | +8 path_len | +16 value_ptr | +24 value_len | +32 mode
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptSetAcc
import EvmAsm.Codegen.Programs.MptInsertAcc
import EvmAsm.Codegen.Programs.MptDeleteAcc

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_state_root_ins -- multi-change recompute with INSERT/MODIFY dispatch.
    a0 = root_hash ptr   a1 = witness   a2 = witness_len
    a3 = changes ptr (array of 40-byte descriptors)   a4 = n_changes
    a5 = out_root ptr   a0 (output) = 0 / nonzero (failing sub-status). -/
def mptStateRootInsFunction : String :=
  "mpt_state_root_ins:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a1                   # witness\n" ++
  "  mv s1, a2                   # witness_len\n" ++
  "  mv s2, a3                   # changes\n" ++
  "  mv s3, a4                   # n_changes\n" ++
  "  mv s4, a5                   # out_root\n" ++
  "  # current root := root_hash (a0) -> mset_dr_root\n" ++
  "  la t0, mset_dr_root\n" ++
  "  ld t1,  0(a0); sd t1,  0(t0)\n" ++
  "  ld t1,  8(a0); sd t1,  8(t0)\n" ++
  "  ld t1, 16(a0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(a0); sd t1, 24(t0)\n" ++
  "  # init the node DB (shared by mpt_set_acc + mpt_insert_acc)\n" ++
  "  la t0, mset_db_count; sd zero, 0(t0)\n" ++
  "  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)\n" ++
  "  jal ra, mpt_resolve_cache_reset\n" ++
  "  la t0, sri_fail_index; sd zero, 0(t0)\n" ++
  "  la t0, sri_fail_mode; sd zero, 0(t0)\n" ++
  "  la t0, sri_fail_status; sd zero, 0(t0)\n" ++
  "  li s5, 0                    # i\n" ++
  ".Lsri_loop:\n" ++
  "  beq s5, s3, .Lsri_done\n" ++
  "  slli t0, s5, 5; slli t1, s5, 3; add t0, t0, t1   # 40 * i\n" ++
  "  add t0, s2, t0              # &change[i]\n" ++
  "  ld a3, 0(t0)                # path_ptr\n" ++
  "  ld a4, 8(t0)                # path_len\n" ++
  "  ld a5, 16(t0)               # value_ptr\n" ++
  "  ld a6, 24(t0)               # value_len\n" ++
  "  ld t2, 32(t0)               # mode: 0=set, 1=insert, 2=delete, 3=noop\n" ++
  "  la t3, sri_cur_mode; sd t2, 0(t3)\n" ++
  "  la a0, mset_dr_root\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s1\n" ++
  "  la a7, mset_dr_root\n" ++
  "  li t3, 3; beq t2, t3, .Lsri_noop\n" ++
  "  li t3, 2; beq t2, t3, .Lsri_delete\n" ++
  "  beqz t2, .Lsri_modify\n" ++
  "  jal ra, mpt_insert_acc\n" ++
  "  j .Lsri_after\n" ++
  ".Lsri_delete:\n" ++
  "  jal ra, mpt_delete_acc\n" ++
  "  j .Lsri_after\n" ++
  ".Lsri_modify:\n" ++
  "  jal ra, mpt_set_acc\n" ++
  "  j .Lsri_after\n" ++
  ".Lsri_noop:\n" ++
  "  li a0, 0\n" ++
  ".Lsri_after:\n" ++
  "  bnez a0, .Lsri_fail\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lsri_loop\n" ++
  ".Lsri_done:\n" ++
  "  la t0, mset_dr_root\n" ++
  "  ld t1,  0(t0); sd t1,  0(s4)\n" ++
  "  ld t1,  8(t0); sd t1,  8(s4)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s4)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s4)\n" ++
  "  li a0, 0\n" ++
  ".Lsri_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n" ++
  ".Lsri_fail:\n" ++
  "  la t0, sri_fail_index; sd s5, 0(t0)\n" ++
  "  la t0, sri_cur_mode; ld t1, 0(t0); la t0, sri_fail_mode; sd t1, 0(t0)\n" ++
  "  la t0, sri_fail_status; sd a0, 0(t0)\n" ++
  "  j .Lsri_ret"

/-- `zisk_mpt_state_root_ins`: probe applying a LIST of changes, each tagged
    insert/modify, to exercise the dispatch + the shared node DB (a modify then
    an insert that resolves the modified root from the DB).
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  witness_len            +16 n_changes (N)
      +24 root_hash (32B)        +56 table: N x (path_len:u64, value_len:u64,
                                     is_insert:u64)  (24 B each)
      +56+24N : blobs path0,value0,...  (each 8-aligned)
      then : witness section (8-aligned)
    Output: OUTPUT+0 = final 32-byte root; OUTPUT+32 = status. -/
def ziskMptStateRootInsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness_len\n" ++
  "  ld a4, 16(t0)               # n_changes\n" ++
  "  addi a0, t0, 24             # root_hash ptr\n" ++
  "  slli t1, a4, 4; slli t2, a4, 3; add t1, t1, t2   # 24 * N (table size)\n" ++
  "  addi t2, t0, 56             # table base\n" ++
  "  add t3, t2, t1              # blob cursor = table base + 24N\n" ++
  "  la t4, sri_changes          # descriptor array dst\n" ++
  "  li t5, 0                    # i\n" ++
  ".Lsrip_build:\n" ++
  "  beq t5, a4, .Lsrip_build_done\n" ++
  "  slli t6, t5, 4; slli t0, t5, 3; add t6, t6, t0; add t6, t2, t6   # &table[i]\n" ++
  "  ld a5, 0(t6)                # path_len\n" ++
  "  ld a6, 8(t6)                # value_len\n" ++
  "  ld a7, 16(t6)               # is_insert\n" ++
  "  # descriptor[i] at sri_changes + 40*i\n" ++
  "  slli t0, t5, 5; slli t1, t5, 3; add t0, t0, t1; add t0, t4, t0\n" ++
  "  sd t3, 0(t0)                # path_ptr = blob cursor\n" ++
  "  sd a5, 8(t0)                # path_len\n" ++
  "  add t3, t3, a5              # advance over path\n" ++
  "  addi t3, t3, 7; andi t3, t3, -8\n" ++
  "  sd t3, 16(t0)               # value_ptr\n" ++
  "  sd a6, 24(t0)               # value_len\n" ++
  "  sd a7, 32(t0)               # is_insert\n" ++
  "  add t3, t3, a6              # advance over value\n" ++
  "  addi t3, t3, 7; andi t3, t3, -8\n" ++
  "  addi t5, t5, 1\n" ++
  "  j .Lsrip_build\n" ++
  ".Lsrip_build_done:\n" ++
  "  # witness ptr = blob cursor (already 8-aligned); a2=witness_len, a4=N kept\n" ++
  "  mv a1, t3\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a0, t0, 24             # root_hash ptr\n" ++
  "  la a3, sri_changes\n" ++
  "  li a5, 0xa0010000           # out_root\n" ++
  "  jal ra, mpt_state_root_ins\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)\n" ++
  "  j .Lsri_pdone\n" ++
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
  ".Lsri_pdone:"

/-- Data: the mpt_insert_acc probe scratch/DB (covers both insert + set acc
    needs: mw_*, mlnen_*, mset_[set]_*, ins_*, iwd_*, mxne_*, mset_res_*,
    mset_db_*) + mpt_set_record_walk_db's mset_rw_* + the driver's mset_dr_root
    + sri_changes descriptor array. -/
def ziskMptStateRootInsDataSection : String :=
  ziskMptInsertAccDataSection ++ "\n" ++
  ".balign 8\n" ++
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
  ".balign 8\n" ++
  "mdacc_leaf_path:\n  .zero 128\n" ++
  "mdacc_collapsed_path:\n  .zero 128\n" ++
  ".balign 8\n" ++
  "mset_rw_ptr:\n  .zero 8\n" ++
  "mset_rw_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "mset_dr_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "sri_cur_mode:\n  .zero 8\n" ++
  "sri_fail_index:\n  .zero 8\n" ++
  "sri_fail_mode:\n  .zero 8\n" ++
  "sri_fail_status:\n  .zero 8\n" ++
  "sri_changes:\n  .zero 4096"

def ziskMptStateRootInsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptStateRootInsPrologue
  dataAsm     := ziskMptStateRootInsDataSection
}

end EvmAsm.Codegen
