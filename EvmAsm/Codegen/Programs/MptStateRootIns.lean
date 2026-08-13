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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
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
def mptStateRootIns_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x12,
    .MV .x18 .x13,
    .MV .x19 .x14,
    .MV .x20 .x15,
    .AUIPC .x5 (laHi GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root_ins + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root_ins + 52)),
    .LD .x6 .x10 (0 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x6 .x10 (8 : BitVec 12),
    .SD .x5 .x6 (8 : BitVec 12),
    .LD .x6 .x10 (16 : BitVec 12),
    .SD .x5 .x6 (16 : BitVec 12),
    .LD .x6 .x10 (24 : BitVec 12),
    .SD .x5 .x6 (24 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_count (GuestAddrs.mpt_state_root_ins + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_count (GuestAddrs.mpt_state_root_ins + 92)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_data (GuestAddrs.mpt_state_root_ins + 104)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_data (GuestAddrs.mpt_state_root_ins + 104)),
    .AUIPC .x6 (laHi GuestAddrs.mset_db_top (GuestAddrs.mpt_state_root_ins + 112)),
    .ADDI .x6 .x6 (laLo GuestAddrs.mset_db_top (GuestAddrs.mpt_state_root_ins + 112)),
    .SD .x6 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.mpt_resolve_cache_reset (GuestAddrs.mpt_state_root_ins + 124)),
    .AUIPC .x5 (laHi GuestAddrs.sri_fail_index (GuestAddrs.mpt_state_root_ins + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sri_fail_index (GuestAddrs.mpt_state_root_ins + 128)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sri_fail_mode (GuestAddrs.mpt_state_root_ins + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sri_fail_mode (GuestAddrs.mpt_state_root_ins + 140)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sri_fail_status (GuestAddrs.mpt_state_root_ins + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sri_fail_status (GuestAddrs.mpt_state_root_ins + 152)),
    .SD .x5 .x0 (0 : BitVec 12),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x19 (136 : BitVec 13),
    .SLLI .x5 .x21 (5 : BitVec 6),
    .SLLI .x6 .x21 (3 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .ADD .x5 .x18 .x5,
    .LD .x13 .x5 (0 : BitVec 12),
    .LD .x14 .x5 (8 : BitVec 12),
    .LD .x15 .x5 (16 : BitVec 12),
    .LD .x16 .x5 (24 : BitVec 12),
    .LD .x7 .x5 (32 : BitVec 12),
    .AUIPC .x28 (laHi GuestAddrs.sri_cur_mode (GuestAddrs.mpt_state_root_ins + 208)),
    .ADDI .x28 .x28 (laLo GuestAddrs.sri_cur_mode (GuestAddrs.mpt_state_root_ins + 208)),
    .SD .x28 .x7 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root_ins + 220)),
    .ADDI .x10 .x10 (laLo GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root_ins + 220)),
    .MV .x11 .x8,
    .MV .x12 .x9,
    .AUIPC .x17 (laHi GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root_ins + 236)),
    .ADDI .x17 .x17 (laLo GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root_ins + 236)),
    .LI .x28 (3 : Word),
    .BEQ .x7 .x28 (40 : BitVec 13),
    .LI .x28 (2 : Word),
    .BEQ .x7 .x28 (16 : BitVec 13),
    .BEQ .x7 .x0 (20 : BitVec 13),
    .JAL .x1 (jalOff GuestAddrs.mpt_insert_acc (GuestAddrs.mpt_state_root_ins + 264)),
    .JAL .x0 (24 : BitVec 21),
    .JAL .x1 (jalOff GuestAddrs.mpt_delete_acc (GuestAddrs.mpt_state_root_ins + 272)),
    .JAL .x0 (16 : BitVec 21),
    .JAL .x1 (jalOff GuestAddrs.mpt_set_acc (GuestAddrs.mpt_state_root_ins + 280)),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .BNE .x10 .x0 (92 : BitVec 13),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-132 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root_ins + 304)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root_ins + 304)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x20 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x20 .x6 (8 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x20 .x6 (16 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x20 .x6 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sri_fail_index (GuestAddrs.mpt_state_root_ins + 384)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sri_fail_index (GuestAddrs.mpt_state_root_ins + 384)),
    .SD .x5 .x21 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sri_cur_mode (GuestAddrs.mpt_state_root_ins + 396)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sri_cur_mode (GuestAddrs.mpt_state_root_ins + 396)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sri_fail_mode (GuestAddrs.mpt_state_root_ins + 408)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sri_fail_mode (GuestAddrs.mpt_state_root_ins + 408)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.sri_fail_status (GuestAddrs.mpt_state_root_ins + 420)),
    .ADDI .x5 .x5 (laLo GuestAddrs.sri_fail_status (GuestAddrs.mpt_state_root_ins + 420)),
    .SD .x5 .x10 (0 : BitVec 12),
    .JAL .x0 (-84 : BitVec 21) ]

/-- Reloc side-table for `mptStateRootIns_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptStateRootIns_relocs : RelocTable :=
  [ (13, .la .x5 "mset_dr_root"),
    (23, .la .x5 "mset_db_count"),
    (26, .la .x5 "mset_db_data"),
    (28, .la .x6 "mset_db_top"),
    (31, .jal .x1 "mpt_resolve_cache_reset"),
    (32, .la .x5 "sri_fail_index"),
    (35, .la .x5 "sri_fail_mode"),
    (38, .la .x5 "sri_fail_status"),
    (52, .la .x28 "sri_cur_mode"),
    (55, .la .x10 "mset_dr_root"),
    (59, .la .x17 "mset_dr_root"),
    (66, .jal .x1 "mpt_insert_acc"),
    (68, .jal .x1 "mpt_delete_acc"),
    (70, .jal .x1 "mpt_set_acc"),
    (76, .la .x5 "mset_dr_root"),
    (96, .la .x5 "sri_fail_index"),
    (99, .la .x5 "sri_cur_mode"),
    (102, .la .x5 "sri_fail_mode"),
    (105, .la .x5 "sri_fail_status") ]

def mptStateRootInsFunction : String :=
  "mpt_state_root_ins:\n" ++ emitProgramR mptStateRootIns_prog mptStateRootIns_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptStateRootIns_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptStateRootInsFunction_eq_prog :
    mptStateRootInsFunction = "mpt_state_root_ins:\n" ++ emitProgramR mptStateRootIns_prog mptStateRootIns_relocs := rfl

#guard mptStateRootInsFunction.startsWith "mpt_state_root_ins:\n"
#guard mptStateRootIns_prog.length = 109
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
  rlpWalkHelpersClosure ++ "\n" ++
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
  -- One extracted state-node HP path is <= 2047 nibbles.  Collapsing an
  -- extension with a leaf can concatenate two such paths.
  "mdacc_leaf_path:\n  .zero 2048\n" ++
  "mdacc_collapsed_path:\n  .zero 4096\n" ++
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


end EvmAsm.Codegen
