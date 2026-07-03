/-
  EvmAsm.Codegen.Programs.MptSetAcc

  Accumulating MPT update (bead evm-asm-fhsxz.4.3.1): the sequential-update
  primitive that multi-change post-state-root recompute is built on.

  A single `mpt_set` (Programs/MptSet.lean) reads the static witness and
  returns one new root. But a block changes MANY keys, applied in sequence:
  after update 1 the ROOT node changes, so update 2's walk must start at the
  NEW root — which is NOT in the original witness. There is no shortcut
  (disjoint-prefix updates still rewrite the shared root).

  So `mpt_set_acc` threads an appendable NODE DB:
    * `node_db_append`  — keccak a freshly re-encoded node and store
                          (hash, len, bytes) so later updates can find it.
    * `node_db_lookup`  — linear scan of the DB by 32-byte keccak.
    * `mpt_node_resolve`— resolve a node hash to an ABSOLUTE pointer, trying
                          the appended DB first, then the witness (SSZ section).
    * `mpt_set_record_walk_db` — like `mpt_set_record_walk` but resolves via
                          witness+DB and records ABSOLUTE node ptrs (an
                          on-path ancestor can live in the DB, so a
                          witness-relative offset would be wrong).
    * `mpt_set_acc`     — record-walk-db → re-encode leaf → bubble up
                          (`mpt_splice_slot` + `mpt_node_slot_encode`),
                          APPENDING each new node to the DB → keccak the root.

  Reuses `mpt_splice_slot` / `mset_memcpy` and the merged single-update
  scratch from `Programs/MptSet.lean`; helper-function scratch from
  `ziskMptWalkDataSection`. All multi-byte DB stores are u64-aligned (records
  are 40 + roundup8(len) bytes, starting on an 8-aligned base); node payloads
  are read byte-wise (no-misaligned invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.MptSet

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## node_db_append -- store a freshly re-encoded node, keyed by keccak

    The node DB is a record region: a u64 `mset_db_count` and a u64
    `mset_db_top` (next-free ptr), with records
      keccak[32] | len:u64 | bytes[len] (padded to 8)
    laid out from `mset_db_data`. Append keccaks the node and writes the
    record. a0 = node ptr, a1 = node length. -/
def nodeDbAppend_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 36)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 36)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.node_db_append + 44)),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 48)),
    .LD .x18 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 60)),
    .ADDI .x6 .x6 (laLo GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 60)),
    .LD .x7 .x6 (0 : BitVec 12),
    .SD .x18 .x7 (0 : BitVec 12),
    .LD .x7 .x6 (8 : BitVec 12),
    .SD .x18 .x7 (8 : BitVec 12),
    .LD .x7 .x6 (16 : BitVec 12),
    .SD .x18 .x7 (16 : BitVec 12),
    .LD .x7 .x6 (24 : BitVec 12),
    .SD .x18 .x7 (24 : BitVec 12),
    .SD .x18 .x9 (32 : BitVec 12),
    .ADDI .x10 .x18 (40 : BitVec 12),
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.node_db_append + 116)),
    .ADDI .x5 .x9 (7 : BitVec 12),
    .ANDI .x5 .x5 (-8 : BitVec 12),
    .ADDI .x5 .x5 (40 : BitVec 12),
    .ADD .x18 .x18 .x5,
    .AUIPC .x6 (laHi GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 136)),
    .ADDI .x6 .x6 (laLo GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 136)),
    .SD .x6 .x18 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.mset_db_count (GuestAddrs.node_db_append + 148)),
    .ADDI .x6 .x6 (laLo GuestAddrs.mset_db_count (GuestAddrs.node_db_append + 148)),
    .LD .x7 .x6 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .SD .x6 .x7 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `nodeDbAppend_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def nodeDbAppend_relocs : RelocTable :=
  [ (9, .la .x12 "mset_db_hash"),
    (11, .jal .x1 "zkvm_keccak256"),
    (12, .la .x5 "mset_db_top"),
    (15, .la .x6 "mset_db_hash"),
    (29, .jal .x1 "mset_memcpy"),
    (34, .la .x6 "mset_db_top"),
    (37, .la .x6 "mset_db_count") ]

def nodeDbAppendFunction : String :=
  "node_db_append:\n" ++ emitProgramR nodeDbAppend_prog nodeDbAppend_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `nodeDbAppend_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem nodeDbAppendFunction_eq_prog :
    nodeDbAppendFunction = "node_db_append:\n" ++ emitProgramR nodeDbAppend_prog nodeDbAppend_relocs := rfl

#guard nodeDbAppendFunction.startsWith "node_db_append:\n"
#guard nodeDbAppend_prog.length = 48
/-! ## node_db_lookup -- find a DB node by 32-byte keccak (leaf, pure)

    a0 = target hash ptr, a1 = out_ptr ptr (absolute node bytes ptr),
    a2 = out_len ptr. a0 = 0 (found) / 1 (miss). Linear scan; reads only
    8-aligned record fields (the variable node bytes are skipped, not
    loaded). -/
def nodeDbLookup_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.mset_db_count (GuestAddrs.node_db_lookup + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_count (GuestAddrs.node_db_lookup + 0)),
    .LD .x31 .x5 (0 : BitVec 12),
    .AUIPC .x30 (laHi GuestAddrs.mset_db_data (GuestAddrs.node_db_lookup + 12)),
    .ADDI .x30 .x30 (laLo GuestAddrs.mset_db_data (GuestAddrs.node_db_lookup + 12)),
    .BEQ .x31 .x0 (104 : BitVec 13),
    .LD .x5 .x30 (0 : BitVec 12),
    .LD .x6 .x10 (0 : BitVec 12),
    .BNE .x5 .x6 (64 : BitVec 13),
    .LD .x5 .x30 (8 : BitVec 12),
    .LD .x6 .x10 (8 : BitVec 12),
    .BNE .x5 .x6 (52 : BitVec 13),
    .LD .x5 .x30 (16 : BitVec 12),
    .LD .x6 .x10 (16 : BitVec 12),
    .BNE .x5 .x6 (40 : BitVec 13),
    .LD .x5 .x30 (24 : BitVec 12),
    .LD .x6 .x10 (24 : BitVec 12),
    .BNE .x5 .x6 (28 : BitVec 13),
    .ADDI .x5 .x30 (40 : BitVec 12),
    .SD .x11 .x5 (0 : BitVec 12),
    .LD .x6 .x30 (32 : BitVec 12),
    .SD .x12 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LD .x6 .x30 (32 : BitVec 12),
    .ADDI .x6 .x6 (7 : BitVec 12),
    .ANDI .x6 .x6 (-8 : BitVec 12),
    .ADDI .x6 .x6 (40 : BitVec 12),
    .ADD .x30 .x30 .x6,
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-100 : BitVec 21),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `nodeDbLookup_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def nodeDbLookup_relocs : RelocTable :=
  [ (0, .la .x5 "mset_db_count"),
    (3, .la .x30 "mset_db_data") ]

def nodeDbLookupFunction : String :=
  "node_db_lookup:\n" ++ emitProgramR nodeDbLookup_prog nodeDbLookup_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `nodeDbLookup_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem nodeDbLookupFunction_eq_prog :
    nodeDbLookupFunction = "node_db_lookup:\n" ++ emitProgramR nodeDbLookup_prog nodeDbLookup_relocs := rfl

#guard nodeDbLookupFunction.startsWith "node_db_lookup:\n"
#guard nodeDbLookup_prog.length = 33
/-! ## mpt_resolve_cache_reset -- clear the witness-node resolver cache.

    The cache is direct-mapped and stores only successful witness-section
    resolutions. It is reset alongside the appended node DB so cached absolute
    input pointers never cross probe/block invocations. -/
def mptResolveCacheResetFunction : String :=
  "mpt_resolve_cache_reset:\n" ++
  "  la t0, mset_res_cache_valid\n" ++
  "  li t1, 4096\n" ++
  ".Lmrc_reset_loop:\n" ++
  "  beqz t1, .Lmrc_reset_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lmrc_reset_loop\n" ++
  ".Lmrc_reset_done:\n" ++
  "  ret"

/-- Backing storage for `mpt_node_resolve`'s direct-mapped witness cache. -/
def mptResolveCacheDataSection : String :=
  ".balign 8\n" ++
  "mset_res_cache_valid:\n  .zero 32768\n" ++
  ".balign 32\n" ++
  "mset_res_cache_data:\n  .zero 196608"

/-! ## mpt_node_resolve -- hash -> absolute node ptr (DB, then witness)

    a0 = witness ptr, a1 = witness_len, a2 = target hash ptr,
    a3 = out_ptr ptr (ABSOLUTE), a4 = out_len ptr. a0 = 0 / 1. Tries the
    appended DB first, then the witness SSZ section (witness_lookup_by_hash
    returns a section offset, converted to absolute here). -/
def mptNodeResolveFunction : String :=
  "mpt_node_resolve:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, s4\n" ++
  "  jal ra, node_db_lookup\n" ++
  "  beqz a0, .Lres_ret\n" ++
  "  # Direct-mapped cache for witness-section resolutions. DB lookup wins;\n" ++
  "  # the cache only avoids repeated scans of the immutable witness list.\n" ++
  "  lbu t0, 0(s2)\n" ++
  "  lbu t1, 1(s2); slli t1, t1, 8; or t0, t0, t1; li t2, 4095; and t0, t0, t2\n" ++
  "  la t1, mset_res_cache_valid\n" ++
  "  slli t2, t0, 3; add t1, t1, t2\n" ++
  "  ld t2, 0(t1); beqz t2, .Lres_cache_miss\n" ++
  "  slli t2, t0, 5; slli t3, t0, 4; add t2, t2, t3   # 48 * index\n" ++
  "  la t3, mset_res_cache_data; add t2, t3, t2\n" ++
  "  ld t3,  0(t2); ld t4,  0(s2); bne t3, t4, .Lres_cache_miss\n" ++
  "  ld t3,  8(t2); ld t4,  8(s2); bne t3, t4, .Lres_cache_miss\n" ++
  "  ld t3, 16(t2); ld t4, 16(s2); bne t3, t4, .Lres_cache_miss\n" ++
  "  ld t3, 24(t2); ld t4, 24(s2); bne t3, t4, .Lres_cache_miss\n" ++
  "  ld t3, 32(t2); sd t3, 0(s3)\n" ++
  "  ld t3, 40(t2); sd t3, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lres_ret\n" ++
  ".Lres_cache_miss:\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  la a3, mset_res_off; la a4, mset_res_len\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lres_ret\n" ++
  "  la t0, mset_res_off; ld t1, 0(t0); add t1, s0, t1   # abs = witness + off\n" ++
  "  sd t1, 0(s3)\n" ++
  "  la t0, mset_res_len; ld t1, 0(t0); sd t1, 0(s4)\n" ++
  "  lbu t0, 0(s2)\n" ++
  "  lbu t1, 1(s2); slli t1, t1, 8; or t0, t0, t1; li t2, 4095; and t0, t0, t2\n" ++
  "  slli t2, t0, 5; slli t3, t0, 4; add t2, t2, t3   # 48 * index\n" ++
  "  la t3, mset_res_cache_data; add t2, t3, t2\n" ++
  "  ld t3,  0(s2); sd t3,  0(t2)\n" ++
  "  ld t3,  8(s2); sd t3,  8(t2)\n" ++
  "  ld t3, 16(s2); sd t3, 16(t2)\n" ++
  "  ld t3, 24(s2); sd t3, 24(t2)\n" ++
  "  ld t3, 0(s3); sd t3, 32(t2)\n" ++
  "  ld t3, 0(s4); sd t3, 40(t2)\n" ++
  "  la t1, mset_res_cache_valid; slli t3, t0, 3; add t1, t1, t3; li t3, 1; sd t3, 0(t1)\n" ++
  "  li a0, 0\n" ++
  ".Lres_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## mpt_set_record_walk_db -- record-walk resolving via witness+DB

    Same descent as `mpt_set_record_walk`, but every node hash is resolved
    via `mpt_node_resolve` (DB then witness), and the recorded node pointer
    is ABSOLUTE (a multi-update ancestor may live in the DB). Reuses the
    mw_* / mnk_* helper scratch. ABI matches mpt_set_record_walk:
    a0=root_hash, a1=witness, a2=witness_len, a3=path, a4=path_len,
    a5=stack_out, a6=meta_out -> a0 status (0/1/2).
    stack record: (node_ptr_ABS, node_len, kind, nibble); meta:
    (depth, consumed, leaf_ptr_ABS, leaf_len). -/
def mptSetRecordWalkDbFunction : String :=
  "mpt_set_record_walk_db:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a1                   # witness\n" ++
  "  mv s1, a2                   # witness_len\n" ++
  "  mv s2, a3                   # path\n" ++
  "  mv s3, a4                   # path_len\n" ++
  "  mv s4, a5                   # stack_out cursor\n" ++
  "  mv s5, a6                   # meta_out\n" ++
  "  li s9, 0                    # depth\n" ++
  "  # root resolve (hash ptr = a0 = root_hash).\n" ++
  "  mv a2, a0\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a3, mset_rw_ptr; la a4, mset_rw_len\n" ++
  "  jal ra, mpt_node_resolve\n" ++
  "  bnez a0, .Lmrwdb_not_found\n" ++
  "  la t0, mset_rw_ptr; ld s7, 0(t0)   # absolute node ptr\n" ++
  "  la t0, mset_rw_len; ld s8, 0(t0)\n" ++
  "  li s6, 0\n" ++
  ".Lmrwdb_loop:\n" ++
  "  mv a0, s7; mv a1, s8\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  beqz a0, .Lmrwdb_branch\n" ++
  "  li t0, 1; beq a0, t0, .Lmrwdb_extension\n" ++
  "  li t0, 2; beq a0, t0, .Lmrwdb_leaf\n" ++
  "  j .Lmrwdb_parse_fail\n" ++
  ".Lmrwdb_branch:\n" ++
  "  beq s6, s3, .Lmrwdb_branch_end\n" ++
  "  add t0, s2, s6; lbu t1, 0(t0)       # nibble\n" ++
  "  sd s7,  0(s4); sd s8,  8(s4); sd zero, 16(s4); sd t1, 24(s4)\n" ++
  "  addi s4, s4, 32; addi s9, s9, 1\n" ++
  "  mv a0, s7; mv a1, s8; mv a2, t1\n" ++
  "  la a3, mw_child_offset; la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  addi s6, s6, 1\n" ++
  "  bnez a0, .Lmrwdb_parse_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmrwdb_not_found\n" ++
  "  li t2, 32; beq t1, t2, .Lmrwdb_branch_hash\n" ++
  "  la t0, mw_child_offset; ld t2, 0(t0); add s7, s7, t2; mv s8, t1\n" ++
  "  j .Lmrwdb_loop\n" ++
  ".Lmrwdb_branch_hash:\n" ++
  "  la t0, mw_child_offset; ld t1, 0(t0); add a2, s7, t1   # hash ptr\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a3, mset_rw_ptr; la a4, mset_rw_len\n" ++
  "  jal ra, mpt_node_resolve\n" ++
  "  bnez a0, .Lmrwdb_not_found\n" ++
  "  la t0, mset_rw_ptr; ld s7, 0(t0)\n" ++
  "  la t0, mset_rw_len; ld s8, 0(t0)\n" ++
  "  j .Lmrwdb_loop\n" ++
  ".Lmrwdb_branch_end:\n" ++
  "  sd s9, 0(s5); sd s6, 8(s5); sd s7, 16(s5); sd s8, 24(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmrwdb_ret\n" ++
  ".Lmrwdb_extension:\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 0\n" ++
  "  la a3, mw_path_offset; la a4, mw_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmrwdb_parse_fail\n" ++
  "  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, mw_path_length; ld a1, 0(t0)\n" ++
  "  la a2, mw_nibble_buf; la a3, mw_nibble_count; la a4, mw_is_leaf\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Lmrwdb_parse_fail\n" ++
  "  la t0, mw_is_leaf; ld t1, 0(t0); bnez t1, .Lmrwdb_parse_fail\n" ++
  "  la t0, mw_nibble_count; ld t1, 0(t0)\n" ++
  "  add t2, s6, t1; bgtu t2, s3, .Lmrwdb_not_found\n" ++
  "  la t2, mw_nibble_buf; add t3, s2, s6; mv t4, t1\n" ++
  ".Lmrwdb_ext_cmp:\n" ++
  "  beqz t4, .Lmrwdb_ext_cmp_done\n" ++
  "  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lmrwdb_not_found\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lmrwdb_ext_cmp\n" ++
  ".Lmrwdb_ext_cmp_done:\n" ++
  "  add s6, s6, t1\n" ++
  "  sd s7, 0(s4); sd s8, 8(s4); li t3, 1; sd t3, 16(s4); sd zero, 24(s4)\n" ++
  "  addi s4, s4, 32; addi s9, s9, 1\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 1\n" ++
  "  la a3, mw_child_offset; la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmrwdb_parse_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  la t0, mw_child_offset; ld t2, 0(t0); add t3, s7, t2\n" ++
  "  li t4, 32; beq t1, t4, .Lmrwdb_ext_hash\n" ++
  "  mv s7, t3; mv s8, t1; j .Lmrwdb_loop\n" ++
  ".Lmrwdb_ext_hash:\n" ++
  "  mv a2, t3                   # hash ptr (= s7 + child_offset)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a3, mset_rw_ptr; la a4, mset_rw_len\n" ++
  "  jal ra, mpt_node_resolve\n" ++
  "  bnez a0, .Lmrwdb_not_found\n" ++
  "  la t0, mset_rw_ptr; ld s7, 0(t0)\n" ++
  "  la t0, mset_rw_len; ld s8, 0(t0)\n" ++
  "  j .Lmrwdb_loop\n" ++
  ".Lmrwdb_leaf:\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 0\n" ++
  "  la a3, mw_path_offset; la a4, mw_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmrwdb_parse_fail\n" ++
  "  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, mw_path_length; ld a1, 0(t0)\n" ++
  "  la a2, mw_nibble_buf; la a3, mw_nibble_count; la a4, mw_is_leaf\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Lmrwdb_parse_fail\n" ++
  "  la t0, mw_is_leaf; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lmrwdb_parse_fail\n" ++
  "  la t0, mw_nibble_count; ld t1, 0(t0)\n" ++
  "  sub t2, s3, s6; bne t1, t2, .Lmrwdb_not_found\n" ++
  "  la t2, mw_nibble_buf; add t3, s2, s6; mv t4, t1\n" ++
  ".Lmrwdb_leaf_cmp:\n" ++
  "  beqz t4, .Lmrwdb_leaf_match\n" ++
  "  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lmrwdb_not_found\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lmrwdb_leaf_cmp\n" ++
  ".Lmrwdb_leaf_match:\n" ++
  "  sd s9, 0(s5); sd s6, 8(s5); sd s7, 16(s5); sd s8, 24(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lmrwdb_ret\n" ++
  ".Lmrwdb_not_found:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmrwdb_ret\n" ++
  ".Lmrwdb_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmrwdb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-! ## mpt_set_acc -- value-only update that APPENDS new nodes to the DB

    Like `mpt_set` but (a) the descent resolves via DB+witness, (b) every
    re-encoded node (leaf + each spliced ancestor) is appended to the DB so
    a subsequent `mpt_set_acc` (threaded on the returned root) can traverse
    the updated trie. Reuses the merged mset_node / mset_ref / mset_stack /
    mset_meta scratch (mpt_set itself is not run in the same program).

    a0=root_hash, a1=witness, a2=witness_len, a3=path, a4=path_len,
    a5=new_value, a6=new_value_len, a7=out_root -> a0 status (0/1/2). -/
def mptSetAccFunction : String :=
  "mpt_set_acc:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a1                   # witness\n" ++
  "  mv s1, a3                   # path\n" ++
  "  mv s2, a4                   # path_len\n" ++
  "  mv s3, a5                   # new_value\n" ++
  "  mv s4, a6                   # new_value_len\n" ++
  "  mv s5, a7                   # out_root\n" ++
  "  # record-walk-db (a0=root_hash, a2=witness_len unchanged)\n" ++
  "  mv a1, s0\n" ++
  "  mv a3, s1\n" ++
  "  mv a4, s2\n" ++
  "  la a5, mset_stack\n" ++
  "  la a6, mset_meta\n" ++
  "  jal ra, mpt_set_record_walk_db\n" ++
  "  bnez a0, .Lmacc_ret\n" ++
  "  la t0, mset_meta; ld s6, 0(t0); ld s8, 8(t0)   # depth, consumed\n" ++
  "  # re-encode leaf from path[consumed:] + new_value\n" ++
  "  add a0, s1, s8; sub a1, s2, s8\n" ++
  "  mv a2, s3; mv a3, s4\n" ++
  "  la a4, mset_node; la a5, mset_node_len\n" ++
  "  jal ra, mpt_leaf_node_encode_from_nibbles\n" ++
  "  bnez a0, .Lmacc_fail\n" ++
  "  la t0, mset_node_len; ld s9, 0(t0)\n" ++
  "  # append leaf to DB\n" ++
  "  la a0, mset_node; mv a1, s9\n" ++
  "  jal ra, node_db_append\n" ++
  "  # current_ref = node_slot_encode(leaf)\n" ++
  "  la a0, mset_node; mv a1, s9; la a2, mset_ref; la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  mv s7, s6                   # i = depth\n" ++
  ".Lmacc_bubble:\n" ++
  "  beqz s7, .Lmacc_root\n" ++
  "  addi s7, s7, -1\n" ++
  "  la t0, mset_stack; slli t1, s7, 5; add t0, t0, t1   # &record[i]\n" ++
  "  ld t2, 0(t0)                # node_ptr ABS\n" ++
  "  ld t3, 8(t0)                # node_len\n" ++
  "  ld t4, 16(t0)               # kind\n" ++
  "  ld t5, 24(t0)               # nibble\n" ++
  "  mv a0, t2                   # src = absolute node ptr\n" ++
  "  mv a1, t3\n" ++
  "  beqz t4, .Lmacc_k_branch\n" ++
  "  li a2, 1\n" ++
  "  j .Lmacc_k_done\n" ++
  ".Lmacc_k_branch:\n" ++
  "  mv a2, t5\n" ++
  ".Lmacc_k_done:\n" ++
  "  la a3, mset_ref; la t0, mset_ref_len; ld a4, 0(t0)\n" ++
  "  la a5, mset_node; la a6, mset_node_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lmacc_fail\n" ++
  "  la t0, mset_node_len; ld s9, 0(t0)\n" ++
  "  # append new node to DB\n" ++
  "  la a0, mset_node; mv a1, s9\n" ++
  "  jal ra, node_db_append\n" ++
  "  # current_ref = node_slot_encode(new node)\n" ++
  "  la a0, mset_node; mv a1, s9; la a2, mset_ref; la a3, mset_ref_len\n" ++
  "  jal ra, mpt_node_slot_encode\n" ++
  "  j .Lmacc_bubble\n" ++
  ".Lmacc_root:\n" ++
  "  la a0, mset_node; mv a1, s9; mv a2, s5\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  ".Lmacc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  ".Lmacc_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lmacc_ret"

/-- `zisk_mpt_set_acc`: probe applying TWO sequential value-only updates to
    exercise the appendable node DB (update 2 must resolve update 1's new
    root from the DB and a sibling leaf from the witness).
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8 witness_len, +16 path1_len, +24 value1_len, +32 path2_len,
      +40 value2_len, +48 root_hash(32B), +80 path1, then value1, path2,
      value2, witness section -- each segment 8-aligned.
    Output: OUTPUT+0 = 32-byte final root; OUTPUT+32 = status of update 2. -/
def ziskMptSetAccPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  # init node DB: count = 0, top = &mset_db_data.\n" ++
  "  la t0, mset_db_count; sd zero, 0(t0)\n" ++
  "  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)\n" ++
  "  jal ra, mpt_resolve_cache_reset\n" ++
  "  # ---- update 1 ----\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness_len\n" ++
  "  ld t1, 16(t0)               # path1_len\n" ++
  "  ld t2, 24(t0)               # value1_len\n" ++
  "  ld t3, 32(t0)               # path2_len\n" ++
  "  ld t4, 40(t0)               # value2_len\n" ++
  "  addi a0, t0, 48             # root_hash\n" ++
  "  addi t5, t0, 80             # path1 ptr\n" ++
  "  mv a3, t5                   # a3 = path1\n" ++
  "  addi t6, t1, 7; andi t6, t6, -8; add t5, t5, t6   # value1 ptr\n" ++
  "  mv a5, t5                   # a5 = value1\n" ++
  "  addi t6, t2, 7; andi t6, t6, -8; add t5, t5, t6   # path2 ptr\n" ++
  "  addi t6, t3, 7; andi t6, t6, -8; add t5, t5, t6   # value2 ptr\n" ++
  "  addi t6, t4, 7; andi t6, t6, -8; add a1, t5, t6   # witness ptr\n" ++
  "  mv a4, t1                   # path1_len\n" ++
  "  mv a6, t2                   # value1_len\n" ++
  "  la a7, mset_tmproot\n" ++
  "  jal ra, mpt_set_acc\n" ++
  "  # ---- update 2 (root = mset_tmproot) ----\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness_len\n" ++
  "  ld t1, 16(t0)               # path1_len\n" ++
  "  ld t2, 24(t0)               # value1_len\n" ++
  "  ld t3, 32(t0)               # path2_len\n" ++
  "  ld t4, 40(t0)               # value2_len\n" ++
  "  addi t5, t0, 80             # path1 ptr\n" ++
  "  addi t6, t1, 7; andi t6, t6, -8; add t5, t5, t6   # value1 ptr\n" ++
  "  addi t6, t2, 7; andi t6, t6, -8; add t5, t5, t6   # path2 ptr\n" ++
  "  mv a3, t5                   # a3 = path2\n" ++
  "  addi t6, t3, 7; andi t6, t6, -8; add t5, t5, t6   # value2 ptr\n" ++
  "  mv a5, t5                   # a5 = value2\n" ++
  "  addi t6, t4, 7; andi t6, t6, -8; add a1, t5, t6   # witness ptr\n" ++
  "  la a0, mset_tmproot\n" ++
  "  mv a4, t3                   # path2_len\n" ++
  "  mv a6, t4                   # value2_len\n" ++
  "  li a7, 0xa0010000           # out_root at OUTPUT+0\n" ++
  "  jal ra, mpt_set_acc\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)    # status at OUTPUT+32\n" ++
  "  j .Lmacc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  ".Lmacc_pdone:"

/-- Data section for `zisk_mpt_set_acc`: the full single-update scratch
    (`ziskMptSetDataSection` -- record-walk helpers + `mlnen_*` leaf encoder
    + `mset_*` splice scratch/buffers, reused) plus the node-DB / resolve /
    record-walk-db / tmp-root labels. All disjoint. -/
def ziskMptSetAccDataSection : String :=
  ziskMptSetDataSection ++ "\n" ++
  ".balign 8\n" ++
  "mset_db_count:\n  .zero 8\n" ++
  "mset_db_top:\n  .zero 8\n" ++
  "mset_res_off:\n  .zero 8\n" ++
  "mset_res_len:\n  .zero 8\n" ++
  "mset_rw_ptr:\n  .zero 8\n" ++
  "mset_rw_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "mset_db_hash:\n  .zero 32\n" ++
  mptResolveCacheDataSection ++ "\n" ++
  ".balign 32\n" ++
  "mset_tmproot:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "mset_db_data:\n  .zero 8388608"

def ziskMptSetAccProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptSetAccPrologue
  dataAsm     := ziskMptSetAccDataSection
}

/-! ## mpt_state_root -- multi-change post-state-root recompute (driver)

    Sequentially apply a list of value-only changes via `mpt_set_acc`,
    threading the root through the appendable node DB, and return the final
    root. This is the generic engine for `compute_state_root_and_trie_changes`
    (bead evm-asm-fhsxz.4.3.2): the withdrawal / account-RLP / verdict
    specifics live in Step 2 (evm-asm-fhsxz.2).

    a0 = root_hash ptr (32 bytes)
    a1 = witness ptr            a2 = witness length
    a3 = changes ptr            (array of 32-byte descriptors, each
                                 (path_ptr:u64, path_len:u64,
                                  value_ptr:u64, value_len:u64))
    a4 = n_changes              a5 = out_root ptr (32 bytes)
    a0 (output) = 0 (ok) / nonzero (the failing mpt_set_acc status)

    Initializes the node DB, then loops: each `mpt_set_acc` resolves the
    current root from the DB (or witness) and appends its new nodes, so the
    next change traverses the updated trie. The threaded root is kept in
    `mset_dr_root` (reading a0 then writing a7 to the same buffer is safe:
    mpt_set_acc consumes the input root before writing the output). -/
def mptStateRoot_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root + 52)),
    .LD .x6 .x10 (0 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x6 .x10 (8 : BitVec 12),
    .SD .x5 .x6 (8 : BitVec 12),
    .LD .x6 .x10 (16 : BitVec 12),
    .SD .x5 .x6 (16 : BitVec 12),
    .LD .x6 .x10 (24 : BitVec 12),
    .SD .x5 .x6 (24 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_count (GuestAddrs.mpt_state_root + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_count (GuestAddrs.mpt_state_root + 92)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_db_data (GuestAddrs.mpt_state_root + 104)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_db_data (GuestAddrs.mpt_state_root + 104)),
    .AUIPC .x6 (laHi GuestAddrs.mset_db_top (GuestAddrs.mpt_state_root + 112)),
    .ADDI .x6 .x6 (laLo GuestAddrs.mset_db_top (GuestAddrs.mpt_state_root + 112)),
    .SD .x6 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.mpt_resolve_cache_reset (GuestAddrs.mpt_state_root + 124)),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x19 (68 : BitVec 13),
    .SLLI .x5 .x21 (5 : BitVec 6),
    .ADD .x5 .x18 .x5,
    .LD .x13 .x5 (0 : BitVec 12),
    .LD .x14 .x5 (8 : BitVec 12),
    .LD .x15 .x5 (16 : BitVec 12),
    .LD .x16 .x5 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root + 160)),
    .ADDI .x10 .x10 (laLo GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root + 160)),
    .MV .x11 .x8,
    .MV .x12 .x9,
    .AUIPC .x17 (laHi GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root + 176)),
    .ADDI .x17 .x17 (laLo GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root + 176)),
    .JAL .x1 (jalOff GuestAddrs.mpt_set_acc (GuestAddrs.mpt_state_root + 184)),
    .BNE .x10 .x0 (92 : BitVec 13),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-64 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_dr_root (GuestAddrs.mpt_state_root + 200)),
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
    .JAL .x0 (-36 : BitVec 21) ]

/-- Reloc side-table for `mptStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptStateRoot_relocs : RelocTable :=
  [ (13, .la .x5 "mset_dr_root"),
    (23, .la .x5 "mset_db_count"),
    (26, .la .x5 "mset_db_data"),
    (28, .la .x6 "mset_db_top"),
    (31, .jal .x1 "mpt_resolve_cache_reset"),
    (40, .la .x10 "mset_dr_root"),
    (44, .la .x17 "mset_dr_root"),
    (46, .jal .x1 "mpt_set_acc"),
    (50, .la .x5 "mset_dr_root") ]

def mptStateRootFunction : String :=
  "mpt_state_root:\n" ++ emitProgramR mptStateRoot_prog mptStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptStateRootFunction_eq_prog :
    mptStateRootFunction = "mpt_state_root:\n" ++ emitProgramR mptStateRoot_prog mptStateRoot_relocs := rfl

#guard mptStateRootFunction.startsWith "mpt_state_root:\n"
#guard mptStateRoot_prog.length = 71
/-- `zisk_mpt_state_root`: probe applying a LIST of value-only changes.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  witness_len            +16 n_changes (N)
      +24 root_hash (32B)        +56 lengths table: N x (path_len:u64,
                                     value_len:u64)
      +56+16N : blobs path0,value0,...,path_{N-1},value_{N-1} (each 8-aligned)
      then : witness section (8-aligned)
    The prologue builds the 32-byte descriptor array (mset_dr_changes) by
    walking the lengths table + a running blob cursor, then calls
    `mpt_state_root`. Output: OUTPUT+0 = final 32-byte root; OUTPUT+32 = status. -/
def ziskMptStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness_len\n" ++
  "  ld a4, 16(t0)               # n_changes\n" ++
  "  addi a0, t0, 24             # root_hash ptr\n" ++
  "  slli t1, a4, 4              # 16 * N (lengths table size)\n" ++
  "  addi t2, t0, 56             # table base\n" ++
  "  add t3, t2, t1              # blob cursor = table base + 16N\n" ++
  "  la t4, mset_dr_changes      # descriptor array dst\n" ++
  "  li t5, 0                    # i\n" ++
  ".Lsrp_build:\n" ++
  "  beq t5, a4, .Lsrp_build_done\n" ++
  "  slli t6, t5, 4; add t6, t2, t6   # &table[i]\n" ++
  "  ld a5, 0(t6)                # path_len\n" ++
  "  ld a6, 8(t6)                # value_len\n" ++
  "  sd t3, 0(t4)                # desc.path_ptr\n" ++
  "  sd a5, 8(t4)                # desc.path_len\n" ++
  "  addi a3, a5, 7; andi a3, a3, -8; add t3, t3, a3   # cursor += roundup8(path_len)\n" ++
  "  sd t3, 16(t4)               # desc.value_ptr\n" ++
  "  sd a6, 24(t4)               # desc.value_len\n" ++
  "  addi a3, a6, 7; andi a3, a3, -8; add t3, t3, a3   # cursor += roundup8(value_len)\n" ++
  "  addi t4, t4, 32\n" ++
  "  addi t5, t5, 1\n" ++
  "  j .Lsrp_build\n" ++
  ".Lsrp_build_done:\n" ++
  "  mv a1, t3                   # witness ptr (after last value)\n" ++
  "  la a3, mset_dr_changes      # changes array\n" ++
  "  li a5, 0xa0010000           # out_root at OUTPUT+0\n" ++
  "  jal ra, mpt_state_root\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)   # status at OUTPUT+32\n" ++
  "  j .Lsrp_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptStateRootFunction ++ "\n" ++
  ".Lsrp_pdone:"

/-- Data section for `zisk_mpt_state_root`: the acc-probe scratch plus the
    driver's threaded-root buffer and descriptor array. -/
def ziskMptStateRootDataSection : String :=
  ziskMptSetAccDataSection ++ "\n" ++
  ".balign 32\n" ++
  "mset_dr_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "mset_dr_changes:\n  .zero 2048"

def ziskMptStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptStateRootPrologue
  dataAsm     := ziskMptStateRootDataSection
}

end EvmAsm.Codegen
