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
    record. a0 = node ptr, a1 = node length.

    **sd13v safety boundary.** This legacy sequential helper has no end-of-
    arena check. It is safe only for its small probe callers: it must not be
    used for the gas-bounded block-state replay, where up to 100,000 distinct
    final keys can re-hash multiple ancestors and exceed the 8 MiB arena. The
    bounded sorted state-root builder replaces this appendable NodeDb path
    rather than adding a sort in front of it. -/
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
def mptResolveCacheReset_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.mset_res_cache_valid (GuestAddrs.mpt_resolve_cache_reset + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_res_cache_valid (GuestAddrs.mpt_resolve_cache_reset + 0)),
    .LUI .x6 (1 : BitVec 20),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptResolveCacheReset_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptResolveCacheReset_relocs : RelocTable :=
  [ (0, .la .x5 "mset_res_cache_valid") ]

def mptResolveCacheResetFunction : String :=
  "mpt_resolve_cache_reset:\n" ++ emitProgramR mptResolveCacheReset_prog mptResolveCacheReset_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptResolveCacheReset_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptResolveCacheResetFunction_eq_prog :
    mptResolveCacheResetFunction = "mpt_resolve_cache_reset:\n" ++ emitProgramR mptResolveCacheReset_prog mptResolveCacheReset_relocs := rfl

#guard mptResolveCacheResetFunction.startsWith "mpt_resolve_cache_reset:\n"
#guard mptResolveCacheReset_prog.length = 9
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
def mptNodeResolve_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x18,
    .MV .x11 .x19,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.node_db_lookup (GuestAddrs.mpt_node_resolve + 60)),
    .BEQ .x10 .x0 (352 : BitVec 13),
    .LBU .x5 .x18 (0 : BitVec 12),
    .LBU .x6 .x18 (1 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (-1 : BitVec 12),
    .AND .x5 .x5 .x7,
    .AUIPC .x6 (laHi GuestAddrs.mset_res_cache_valid (GuestAddrs.mpt_node_resolve + 96)),
    .ADDI .x6 .x6 (laLo GuestAddrs.mset_res_cache_valid (GuestAddrs.mpt_node_resolve + 96)),
    .SLLI .x7 .x5 (3 : BitVec 6),
    .ADD .x6 .x6 .x7,
    .LD .x7 .x6 (0 : BitVec 12),
    .BEQ .x7 .x0 (100 : BitVec 13),
    .SLLI .x7 .x5 (5 : BitVec 6),
    .SLLI .x28 .x5 (4 : BitVec 6),
    .ADD .x7 .x7 .x28,
    .AUIPC .x28 (laHi GuestAddrs.mset_res_cache_data (GuestAddrs.mpt_node_resolve + 132)),
    .ADDI .x28 .x28 (laLo GuestAddrs.mset_res_cache_data (GuestAddrs.mpt_node_resolve + 132)),
    .ADD .x7 .x28 .x7,
    .LD .x28 .x7 (0 : BitVec 12),
    .LD .x29 .x18 (0 : BitVec 12),
    .BNE .x28 .x29 (64 : BitVec 13),
    .LD .x28 .x7 (8 : BitVec 12),
    .LD .x29 .x18 (8 : BitVec 12),
    .BNE .x28 .x29 (52 : BitVec 13),
    .LD .x28 .x7 (16 : BitVec 12),
    .LD .x29 .x18 (16 : BitVec 12),
    .BNE .x28 .x29 (40 : BitVec 13),
    .LD .x28 .x7 (24 : BitVec 12),
    .LD .x29 .x18 (24 : BitVec 12),
    .BNE .x28 .x29 (28 : BitVec 13),
    .LD .x28 .x7 (32 : BitVec 12),
    .SD .x19 .x28 (0 : BitVec 12),
    .LD .x28 .x7 (40 : BitVec 12),
    .SD .x20 .x28 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (204 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.mset_res_off (GuestAddrs.mpt_node_resolve + 228)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mset_res_off (GuestAddrs.mpt_node_resolve + 228)),
    .AUIPC .x14 (laHi GuestAddrs.mset_res_len (GuestAddrs.mpt_node_resolve + 236)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mset_res_len (GuestAddrs.mpt_node_resolve + 236)),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_node_resolve + 244)),
    .BNE .x10 .x0 (168 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mset_res_off (GuestAddrs.mpt_node_resolve + 252)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_res_off (GuestAddrs.mpt_node_resolve + 252)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x6 .x8 .x6,
    .SD .x19 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_res_len (GuestAddrs.mpt_node_resolve + 272)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_res_len (GuestAddrs.mpt_node_resolve + 272)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x20 .x6 (0 : BitVec 12),
    .LBU .x5 .x18 (0 : BitVec 12),
    .LBU .x6 .x18 (1 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (-1 : BitVec 12),
    .AND .x5 .x5 .x7,
    .SLLI .x7 .x5 (5 : BitVec 6),
    .SLLI .x28 .x5 (4 : BitVec 6),
    .ADD .x7 .x7 .x28,
    .AUIPC .x28 (laHi GuestAddrs.mset_res_cache_data (GuestAddrs.mpt_node_resolve + 328)),
    .ADDI .x28 .x28 (laLo GuestAddrs.mset_res_cache_data (GuestAddrs.mpt_node_resolve + 328)),
    .ADD .x7 .x28 .x7,
    .LD .x28 .x18 (0 : BitVec 12),
    .SD .x7 .x28 (0 : BitVec 12),
    .LD .x28 .x18 (8 : BitVec 12),
    .SD .x7 .x28 (8 : BitVec 12),
    .LD .x28 .x18 (16 : BitVec 12),
    .SD .x7 .x28 (16 : BitVec 12),
    .LD .x28 .x18 (24 : BitVec 12),
    .SD .x7 .x28 (24 : BitVec 12),
    .LD .x28 .x19 (0 : BitVec 12),
    .SD .x7 .x28 (32 : BitVec 12),
    .LD .x28 .x20 (0 : BitVec 12),
    .SD .x7 .x28 (40 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.mset_res_cache_valid (GuestAddrs.mpt_node_resolve + 388)),
    .ADDI .x6 .x6 (laLo GuestAddrs.mset_res_cache_valid (GuestAddrs.mpt_node_resolve + 388)),
    .SLLI .x28 .x5 (3 : BitVec 6),
    .ADD .x6 .x6 .x28,
    .LI .x28 (1 : Word),
    .SD .x6 .x28 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptNodeResolve_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptNodeResolve_relocs : RelocTable :=
  [ (15, .jal .x1 "node_db_lookup"),
    (24, .la .x6 "mset_res_cache_valid"),
    (33, .la .x28 "mset_res_cache_data"),
    (57, .la .x13 "mset_res_off"),
    (59, .la .x14 "mset_res_len"),
    (61, .jal .x1 "witness_lookup_by_hash"),
    (63, .la .x5 "mset_res_off"),
    (68, .la .x5 "mset_res_len"),
    (82, .la .x28 "mset_res_cache_data"),
    (97, .la .x6 "mset_res_cache_valid") ]

def mptNodeResolveFunction : String :=
  "mpt_node_resolve:\n" ++ emitProgramR mptNodeResolve_prog mptNodeResolve_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptNodeResolve_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptNodeResolveFunction_eq_prog :
    mptNodeResolveFunction = "mpt_node_resolve:\n" ++ emitProgramR mptNodeResolve_prog mptNodeResolve_relocs := rfl

#guard mptNodeResolveFunction.startsWith "mpt_node_resolve:\n"
#guard mptNodeResolve_prog.length = 112
/-! ## mpt_set_record_walk_db -- record-walk resolving via witness+DB

    Same descent as `mpt_set_record_walk`, but every node hash is resolved
    via `mpt_node_resolve` (DB then witness), and the recorded node pointer
    is ABSOLUTE (a multi-update ancestor may live in the DB). Reuses the
    mw_* / mnk_* helper scratch. ABI matches mpt_set_record_walk:
    a0=root_hash, a1=witness, a2=witness_len, a3=path, a4=path_len,
    a5=stack_out, a6=meta_out -> a0 status (0/1/2).
    stack record: (node_ptr_ABS, node_len, kind, nibble); meta:
    (depth, consumed, leaf_ptr_ABS, leaf_len). -/
def mptSetRecordWalkDb_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
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
    .MV .x8 .x11,
    .MV .x9 .x12,
    .MV .x18 .x13,
    .MV .x19 .x14,
    .MV .x20 .x15,
    .MV .x21 .x16,
    .LI .x25 (0 : Word),
    .MV .x12 .x10,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x13 (laHi GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 88)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 88)),
    .AUIPC .x14 (laHi GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 96)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 96)),
    .JAL .x1 (jalOff GuestAddrs.mpt_node_resolve (GuestAddrs.mpt_set_record_walk_db + 104)),
    .BNE .x10 .x0 (860 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 112)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 112)),
    .LD .x23 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 124)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 124)),
    .LD .x24 .x5 (0 : BitVec 12),
    .LI .x22 (0 : Word),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .JAL .x1 (jalOff GuestAddrs.mpt_node_kind (GuestAddrs.mpt_set_record_walk_db + 148)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (240 : BitVec 13),
    .LI .x5 (2 : Word),
    .BEQ .x10 .x5 (592 : BitVec 13),
    .JAL .x0 (804 : BitVec 21),
    .BEQ .x22 .x19 (200 : BitVec 13),
    .ADD .x5 .x18 .x22,
    .LBU .x6 .x5 (0 : BitVec 12),
    .SD .x20 .x23 (0 : BitVec 12),
    .SD .x20 .x24 (8 : BitVec 12),
    .SD .x20 .x0 (16 : BitVec 12),
    .SD .x20 .x6 (24 : BitVec 12),
    .ADDI .x20 .x20 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .MV .x12 .x6,
    .AUIPC .x13 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_set_record_walk_db + 224)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_set_record_walk_db + 224)),
    .AUIPC .x14 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_set_record_walk_db + 232)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_set_record_walk_db + 232)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_set_record_walk_db + 240)),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .BNE .x10 .x0 (728 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_set_record_walk_db + 252)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_set_record_walk_db + 252)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (704 : BitVec 13),
    .LI .x7 (32 : Word),
    .BEQ .x6 .x7 (28 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_set_record_walk_db + 276)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_set_record_walk_db + 276)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x23 .x23 .x7,
    .MV .x24 .x6,
    .JAL .x0 (-156 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_set_record_walk_db + 300)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_set_record_walk_db + 300)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x12 .x23 .x6,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x13 (laHi GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 324)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 324)),
    .AUIPC .x14 (laHi GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 332)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 332)),
    .JAL .x1 (jalOff GuestAddrs.mpt_node_resolve (GuestAddrs.mpt_set_record_walk_db + 340)),
    .BNE .x10 .x0 (624 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 348)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 348)),
    .LD .x23 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 360)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 360)),
    .LD .x24 .x5 (0 : BitVec 12),
    .JAL .x0 (-232 : BitVec 21),
    .SD .x21 .x25 (0 : BitVec 12),
    .SD .x21 .x22 (8 : BitVec 12),
    .SD .x21 .x23 (16 : BitVec 12),
    .SD .x21 .x24 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (584 : BitVec 21),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_set_record_walk_db + 412)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_set_record_walk_db + 412)),
    .AUIPC .x14 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_set_record_walk_db + 420)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_set_record_walk_db + 420)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_set_record_walk_db + 428)),
    .BNE .x10 .x0 (544 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_set_record_walk_db + 436)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_set_record_walk_db + 436)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x10 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_set_record_walk_db + 452)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_set_record_walk_db + 452)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_set_record_walk_db + 464)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_set_record_walk_db + 464)),
    .AUIPC .x13 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_set_record_walk_db + 472)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_set_record_walk_db + 472)),
    .AUIPC .x14 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_set_record_walk_db + 480)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_set_record_walk_db + 480)),
    .JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_set_record_walk_db + 488)),
    .BNE .x10 .x0 (484 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_set_record_walk_db + 496)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_set_record_walk_db + 496)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (468 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_set_record_walk_db + 512)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_set_record_walk_db + 512)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x22 .x6,
    .BLTU .x19 .x7 (440 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_set_record_walk_db + 532)),
    .ADDI .x7 .x7 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_set_record_walk_db + 532)),
    .ADD .x28 .x18 .x22,
    .MV .x29 .x6,
    .BEQ .x29 .x0 (32 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (408 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADD .x22 .x22 .x6,
    .SD .x20 .x23 (0 : BitVec 12),
    .SD .x20 .x24 (8 : BitVec 12),
    .LI .x28 (1 : Word),
    .SD .x20 .x28 (16 : BitVec 12),
    .SD .x20 .x0 (24 : BitVec 12),
    .ADDI .x20 .x20 (32 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_set_record_walk_db + 624)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_set_record_walk_db + 624)),
    .AUIPC .x14 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_set_record_walk_db + 632)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_set_record_walk_db + 632)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_set_record_walk_db + 640)),
    .BNE .x10 .x0 (332 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_set_record_walk_db + 648)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_set_record_walk_db + 648)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_set_record_walk_db + 660)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_set_record_walk_db + 660)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x28 .x23 .x7,
    .LI .x29 (32 : Word),
    .BEQ .x6 .x29 (16 : BitVec 13),
    .MV .x23 .x28,
    .MV .x24 .x6,
    .JAL .x0 (-552 : BitVec 21),
    .MV .x12 .x28,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x13 (laHi GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 708)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 708)),
    .AUIPC .x14 (laHi GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 716)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 716)),
    .JAL .x1 (jalOff GuestAddrs.mpt_node_resolve (GuestAddrs.mpt_set_record_walk_db + 724)),
    .BNE .x10 .x0 (240 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 732)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_rw_ptr (GuestAddrs.mpt_set_record_walk_db + 732)),
    .LD .x23 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 744)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_rw_len (GuestAddrs.mpt_set_record_walk_db + 744)),
    .LD .x24 .x5 (0 : BitVec 12),
    .JAL .x0 (-616 : BitVec 21),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .LI .x12 (0 : Word),
    .AUIPC .x13 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_set_record_walk_db + 772)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_set_record_walk_db + 772)),
    .AUIPC .x14 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_set_record_walk_db + 780)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_set_record_walk_db + 780)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_set_record_walk_db + 788)),
    .BNE .x10 .x0 (184 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_set_record_walk_db + 796)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_set_record_walk_db + 796)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x10 .x23 .x6,
    .AUIPC .x5 (laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_set_record_walk_db + 812)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_set_record_walk_db + 812)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_set_record_walk_db + 824)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_set_record_walk_db + 824)),
    .AUIPC .x13 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_set_record_walk_db + 832)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_set_record_walk_db + 832)),
    .AUIPC .x14 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_set_record_walk_db + 840)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_set_record_walk_db + 840)),
    .JAL .x1 (jalOff GuestAddrs.hp_decode_nibbles (GuestAddrs.mpt_set_record_walk_db + 848)),
    .BNE .x10 .x0 (124 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_set_record_walk_db + 856)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_set_record_walk_db + 856)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (104 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_set_record_walk_db + 876)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_set_record_walk_db + 876)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SUB .x7 .x19 .x22,
    .BNE .x6 .x7 (76 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_set_record_walk_db + 896)),
    .ADDI .x7 .x7 (laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_set_record_walk_db + 896)),
    .ADD .x28 .x18 .x22,
    .MV .x29 .x6,
    .BEQ .x29 .x0 (32 : BitVec 13),
    .LBU .x30 .x7 (0 : BitVec 12),
    .LBU .x31 .x28 (0 : BitVec 12),
    .BNE .x30 .x31 (44 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .SD .x21 .x25 (0 : BitVec 12),
    .SD .x21 .x22 (8 : BitVec 12),
    .SD .x21 .x23 (16 : BitVec 12),
    .SD .x21 .x24 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
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
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `mptSetRecordWalkDb_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptSetRecordWalkDb_relocs : RelocTable :=
  [ (22, .la .x13 "mset_rw_ptr"),
    (24, .la .x14 "mset_rw_len"),
    (26, .jal .x1 "mpt_node_resolve"),
    (28, .la .x5 "mset_rw_ptr"),
    (31, .la .x5 "mset_rw_len"),
    (37, .jal .x1 "mpt_node_kind"),
    (56, .la .x13 "mw_child_offset"),
    (58, .la .x14 "mw_child_length"),
    (60, .jal .x1 "rlp_list_nth_item"),
    (63, .la .x5 "mw_child_length"),
    (69, .la .x5 "mw_child_offset"),
    (75, .la .x5 "mw_child_offset"),
    (81, .la .x13 "mset_rw_ptr"),
    (83, .la .x14 "mset_rw_len"),
    (85, .jal .x1 "mpt_node_resolve"),
    (87, .la .x5 "mset_rw_ptr"),
    (90, .la .x5 "mset_rw_len"),
    (103, .la .x13 "mw_path_offset"),
    (105, .la .x14 "mw_path_length"),
    (107, .jal .x1 "rlp_list_nth_item"),
    (109, .la .x5 "mw_path_offset"),
    (113, .la .x5 "mw_path_length"),
    (116, .la .x12 "mw_nibble_buf"),
    (118, .la .x13 "mw_nibble_count"),
    (120, .la .x14 "mw_is_leaf"),
    (122, .jal .x1 "hp_decode_nibbles"),
    (124, .la .x5 "mw_is_leaf"),
    (128, .la .x5 "mw_nibble_count"),
    (133, .la .x7 "mw_nibble_buf"),
    (156, .la .x13 "mw_child_offset"),
    (158, .la .x14 "mw_child_length"),
    (160, .jal .x1 "rlp_list_nth_item"),
    (162, .la .x5 "mw_child_length"),
    (165, .la .x5 "mw_child_offset"),
    (177, .la .x13 "mset_rw_ptr"),
    (179, .la .x14 "mset_rw_len"),
    (181, .jal .x1 "mpt_node_resolve"),
    (183, .la .x5 "mset_rw_ptr"),
    (186, .la .x5 "mset_rw_len"),
    (193, .la .x13 "mw_path_offset"),
    (195, .la .x14 "mw_path_length"),
    (197, .jal .x1 "rlp_list_nth_item"),
    (199, .la .x5 "mw_path_offset"),
    (203, .la .x5 "mw_path_length"),
    (206, .la .x12 "mw_nibble_buf"),
    (208, .la .x13 "mw_nibble_count"),
    (210, .la .x14 "mw_is_leaf"),
    (212, .jal .x1 "hp_decode_nibbles"),
    (214, .la .x5 "mw_is_leaf"),
    (219, .la .x5 "mw_nibble_count"),
    (224, .la .x7 "mw_nibble_buf") ]

def mptSetRecordWalkDbFunction : String :=
  "mpt_set_record_walk_db:\n" ++ emitProgramR mptSetRecordWalkDb_prog mptSetRecordWalkDb_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptSetRecordWalkDb_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptSetRecordWalkDbFunction_eq_prog :
    mptSetRecordWalkDbFunction = "mpt_set_record_walk_db:\n" ++ emitProgramR mptSetRecordWalkDb_prog mptSetRecordWalkDb_relocs := rfl

#guard mptSetRecordWalkDbFunction.startsWith "mpt_set_record_walk_db:\n"
#guard mptSetRecordWalkDb_prog.length = 258
/-! ## mpt_set_acc -- value-only update that APPENDS new nodes to the DB

    Like `mpt_set` but (a) the descent resolves via DB+witness, (b) every
    re-encoded node (leaf + each spliced ancestor) is appended to the DB so
    a subsequent `mpt_set_acc` (threaded on the returned root) can traverse
    the updated trie. Reuses the merged mset_node / mset_ref / mset_stack /
    mset_meta scratch (mpt_set itself is not run in the same program).

    a0=root_hash, a1=witness, a2=witness_len, a3=path, a4=path_len,
    a5=new_value, a6=new_value_len, a7=out_root -> a0 status (0/1/2). -/
def mptSetAcc_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
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
    .MV .x8 .x11,
    .MV .x9 .x13,
    .MV .x18 .x14,
    .MV .x19 .x15,
    .MV .x20 .x16,
    .MV .x21 .x17,
    .MV .x11 .x8,
    .MV .x13 .x9,
    .MV .x14 .x18,
    .AUIPC .x15 (laHi GuestAddrs.mset_stack (GuestAddrs.mpt_set_acc + 84)),
    .ADDI .x15 .x15 (laLo GuestAddrs.mset_stack (GuestAddrs.mpt_set_acc + 84)),
    .AUIPC .x16 (laHi GuestAddrs.mset_meta (GuestAddrs.mpt_set_acc + 92)),
    .ADDI .x16 .x16 (laLo GuestAddrs.mset_meta (GuestAddrs.mpt_set_acc + 92)),
    .JAL .x1 (jalOff GuestAddrs.mpt_set_record_walk_db (GuestAddrs.mpt_set_acc + 100)),
    .BNE .x10 .x0 (320 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mset_meta (GuestAddrs.mpt_set_acc + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_meta (GuestAddrs.mpt_set_acc + 108)),
    .LD .x22 .x5 (0 : BitVec 12),
    .LD .x24 .x5 (8 : BitVec 12),
    .ADD .x10 .x9 .x24,
    .SUB .x11 .x18 .x24,
    .MV .x12 .x19,
    .MV .x13 .x20,
    .AUIPC .x14 (laHi GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 140)),
    .ADDI .x14 .x14 (laLo GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 140)),
    .AUIPC .x15 (laHi GuestAddrs.mset_node_len (GuestAddrs.mpt_set_acc + 148)),
    .ADDI .x15 .x15 (laLo GuestAddrs.mset_node_len (GuestAddrs.mpt_set_acc + 148)),
    .JAL .x1 (jalOff GuestAddrs.mpt_leaf_node_encode_from_nibbles (GuestAddrs.mpt_set_acc + 156)),
    .BNE .x10 .x0 (316 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mset_node_len (GuestAddrs.mpt_set_acc + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_node_len (GuestAddrs.mpt_set_acc + 164)),
    .LD .x25 .x5 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 176)),
    .ADDI .x10 .x10 (laLo GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 176)),
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.node_db_append (GuestAddrs.mpt_set_acc + 188)),
    .AUIPC .x10 (laHi GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 192)),
    .ADDI .x10 .x10 (laLo GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 192)),
    .MV .x11 .x25,
    .AUIPC .x12 (laHi GuestAddrs.mset_ref (GuestAddrs.mpt_set_acc + 204)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mset_ref (GuestAddrs.mpt_set_acc + 204)),
    .AUIPC .x13 (laHi GuestAddrs.mset_ref_len (GuestAddrs.mpt_set_acc + 212)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mset_ref_len (GuestAddrs.mpt_set_acc + 212)),
    .JAL .x1 (jalOff GuestAddrs.mpt_node_slot_encode (GuestAddrs.mpt_set_acc + 220)),
    .MV .x23 .x22,
    .BEQ .x23 .x0 (172 : BitVec 13),
    .ADDI .x23 .x23 (-1 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.mset_stack (GuestAddrs.mpt_set_acc + 236)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_stack (GuestAddrs.mpt_set_acc + 236)),
    .SLLI .x6 .x23 (5 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .LD .x7 .x5 (0 : BitVec 12),
    .LD .x28 .x5 (8 : BitVec 12),
    .LD .x29 .x5 (16 : BitVec 12),
    .LD .x30 .x5 (24 : BitVec 12),
    .MV .x10 .x7,
    .MV .x11 .x28,
    .BEQ .x29 .x0 (12 : BitVec 13),
    .LI .x12 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .MV .x12 .x30,
    .AUIPC .x13 (laHi GuestAddrs.mset_ref (GuestAddrs.mpt_set_acc + 292)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mset_ref (GuestAddrs.mpt_set_acc + 292)),
    .AUIPC .x5 (laHi GuestAddrs.mset_ref_len (GuestAddrs.mpt_set_acc + 300)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_ref_len (GuestAddrs.mpt_set_acc + 300)),
    .LD .x14 .x5 (0 : BitVec 12),
    .AUIPC .x15 (laHi GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 312)),
    .ADDI .x15 .x15 (laLo GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 312)),
    .AUIPC .x16 (laHi GuestAddrs.mset_node_len (GuestAddrs.mpt_set_acc + 320)),
    .ADDI .x16 .x16 (laLo GuestAddrs.mset_node_len (GuestAddrs.mpt_set_acc + 320)),
    .JAL .x1 (jalOff GuestAddrs.mpt_splice_slot (GuestAddrs.mpt_set_acc + 328)),
    .BNE .x10 .x0 (144 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.mset_node_len (GuestAddrs.mpt_set_acc + 336)),
    .ADDI .x5 .x5 (laLo GuestAddrs.mset_node_len (GuestAddrs.mpt_set_acc + 336)),
    .LD .x25 .x5 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 348)),
    .ADDI .x10 .x10 (laLo GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 348)),
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.node_db_append (GuestAddrs.mpt_set_acc + 360)),
    .AUIPC .x10 (laHi GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 364)),
    .ADDI .x10 .x10 (laLo GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 364)),
    .MV .x11 .x25,
    .AUIPC .x12 (laHi GuestAddrs.mset_ref (GuestAddrs.mpt_set_acc + 376)),
    .ADDI .x12 .x12 (laLo GuestAddrs.mset_ref (GuestAddrs.mpt_set_acc + 376)),
    .AUIPC .x13 (laHi GuestAddrs.mset_ref_len (GuestAddrs.mpt_set_acc + 384)),
    .ADDI .x13 .x13 (laLo GuestAddrs.mset_ref_len (GuestAddrs.mpt_set_acc + 384)),
    .JAL .x1 (jalOff GuestAddrs.mpt_node_slot_encode (GuestAddrs.mpt_set_acc + 392)),
    .JAL .x0 (-168 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 400)),
    .ADDI .x10 .x10 (laLo GuestAddrs.mset_node (GuestAddrs.mpt_set_acc + 400)),
    .MV .x11 .x25,
    .MV .x12 .x21,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.mpt_set_acc + 416)),
    .LI .x10 (0 : Word),
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
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JAL .x0 (-56 : BitVec 21) ]

/-- Reloc side-table for `mptSetAcc_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def mptSetAcc_relocs : RelocTable :=
  [ (21, .la .x15 "mset_stack"),
    (23, .la .x16 "mset_meta"),
    (25, .jal .x1 "mpt_set_record_walk_db"),
    (27, .la .x5 "mset_meta"),
    (35, .la .x14 "mset_node"),
    (37, .la .x15 "mset_node_len"),
    (39, .jal .x1 "mpt_leaf_node_encode_from_nibbles"),
    (41, .la .x5 "mset_node_len"),
    (44, .la .x10 "mset_node"),
    (47, .jal .x1 "node_db_append"),
    (48, .la .x10 "mset_node"),
    (51, .la .x12 "mset_ref"),
    (53, .la .x13 "mset_ref_len"),
    (55, .jal .x1 "mpt_node_slot_encode"),
    (59, .la .x5 "mset_stack"),
    (73, .la .x13 "mset_ref"),
    (75, .la .x5 "mset_ref_len"),
    (78, .la .x15 "mset_node"),
    (80, .la .x16 "mset_node_len"),
    (82, .jal .x1 "mpt_splice_slot"),
    (84, .la .x5 "mset_node_len"),
    (87, .la .x10 "mset_node"),
    (90, .jal .x1 "node_db_append"),
    (91, .la .x10 "mset_node"),
    (94, .la .x12 "mset_ref"),
    (96, .la .x13 "mset_ref_len"),
    (98, .jal .x1 "mpt_node_slot_encode"),
    (100, .la .x10 "mset_node"),
    (104, .jal .x1 "zkvm_keccak256") ]

def mptSetAccFunction : String :=
  "mpt_set_acc:\n" ++ emitProgramR mptSetAcc_prog mptSetAcc_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `mptSetAcc_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem mptSetAccFunction_eq_prog :
    mptSetAccFunction = "mpt_set_acc:\n" ++ emitProgramR mptSetAcc_prog mptSetAcc_relocs := rfl

#guard mptSetAccFunction.startsWith "mpt_set_acc:\n"
#guard mptSetAcc_prog.length = 121
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
