/-
  EvmAsm.Codegen.Programs.WitnessValidation

  Witness-section validation primitives that walk an entire SSZ
  list section (witness.state / witness.codes / witness.storage)
  and check structural properties of each element. Distinct
  from `StateCompose.lean` and `EvmOpcodes.lean` (per-address
  composites) -- these primitives operate over the whole
  witness section.

  Currently hosts `witness_state_validate_node_kinds`,
  `witness_codes_validate_lengths`, and
  `witness_storage_validate_node_kinds`; future PRs may add
  further section validators.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_state_validate_node_kinds

    Walk an SSZ `witness.state` list section and call K21
    `mpt_node_kind` on every entry. Verifies that every entry
    parses as a valid MPT node (Leaf / Extension / Branch).
    Reports the index of the first malformed entry, or the
    total node count if all parse successfully.

    Spec-side rationale: every entry in `witness.state` is
    supposed to be the canonical RLP encoding of an MPT node
    on the proof path from header.state_root to some account.
    A witness with a non-parseable entry can't be safely
    consumed by `mpt_walk` -- this primitive catches structural
    failures up-front rather than discovering them mid-trie-walk.

    Distinct from previous witness-iteration primitives:
      * `witness_lookup_by_hash` (K19) -- searches by keccak
        match; stops on first hit, doesn't validate structure.
      * `validate_witness_state_contains_root` (PR #7143) --
        checks one specific hash is reachable; doesn't validate
        all entries.
      * `witness_headers_chain_validate` (PR #7158) -- iterates
        but checks parent-hash linkage between consecutive
        headers, not per-element MPT-node structure.

    Calling convention:
      a0 (input)  : witness.state section ptr
      a1 (input)  : section_len (0 ⇒ vacuous-valid)
      a2 (input)  : u64 out ptr (n_processed; on success the
                    total node count N, on failure the index of
                    the first invalid node)
      a3 (input)  : u64 out ptr (first_bad_index;
                    0xFFFFFFFFFFFFFFFF on success, else the
                    failing element's index)
      ra (input)  : return
      a0 (output) :
        0 = all entries parse as valid MPT nodes
        1 = some entry failed to parse (`mpt_node_kind` = 3)
-/
/-! Probe-only local PC placeholder. -/
def witnessStateValidateNodeKindsPc : Nat := 0x80000000

def witnessStateValidateNodeKinds_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .SD .x18 .x0 (0 : BitVec 12),
    .LI .x5 (-1 : Word),
    .SD .x19 .x5 (0 : BitVec 12),
    .BEQ .x9 .x0 (brOff (witnessStateValidateNodeKindsPc + 172) (witnessStateValidateNodeKindsPc + 64)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x20 .x5 (2 : BitVec 6),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x20 (brOff (witnessStateValidateNodeKindsPc + 172) (witnessStateValidateNodeKindsPc + 80)),
    .SLLI .x5 .x21 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .ADD .x10 .x8 .x7,
    .ADDI .x28 .x21 (1 : BitVec 12),
    .BEQ .x28 .x20 (24 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .ADD .x29 .x8 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x29 .x8 .x9,
    .SUB .x11 .x29 .x10,
    .JAL .x1 (jalOff GuestAddrs.mpt_node_kind (witnessStateValidateNodeKindsPc + 136)),
    .LI .x5 (3 : Word),
    .BEQ .x10 .x5 (12 : BitVec 13),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (jalOff (witnessStateValidateNodeKindsPc + 80) (witnessStateValidateNodeKindsPc + 152)),
    .SD .x18 .x21 (0 : BitVec 12),
    .SD .x19 .x21 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (20 : BitVec 21),
    .SD .x18 .x20 (0 : BitVec 12),
    .LI .x5 (-1 : Word),
    .SD .x19 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `witnessStateValidateNodeKinds_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessStateValidateNodeKinds_relocs : RelocTable :=
  [ (34, .jal .x1 "mpt_node_kind") ]

def witnessStateValidateNodeKindsFunction : String :=
  "witness_state_validate_node_kinds:\n" ++ emitProgramR witnessStateValidateNodeKinds_prog witnessStateValidateNodeKinds_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessStateValidateNodeKinds_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessStateValidateNodeKindsFunction_eq_prog :
    witnessStateValidateNodeKindsFunction = "witness_state_validate_node_kinds:\n" ++ emitProgramR witnessStateValidateNodeKinds_prog witnessStateValidateNodeKinds_relocs := rfl

#guard witnessStateValidateNodeKindsFunction.startsWith "witness_state_validate_node_kinds:\n"
#guard witnessStateValidateNodeKinds_prog.length = 57
/-- `zisk_witness_state_validate_node_kinds`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : section_len (u64 LE)
      bytes 16..   : witness.state section bytes
    Output layout:
      bytes  0.. 8 : status (0 ok / 1 parse fail)
      bytes  8..16 : n_processed (= N on success; first bad index on fail)
      bytes 16..24 : first_bad_index (0xFF..FF on success) -/
def ziskWitnessStateValidateNodeKindsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  addi a0, a5, 16             # section ptr\n" ++
  "  li a2, 0xa0010008\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, witness_state_validate_node_kinds\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwsvn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  witnessStateValidateNodeKindsFunction ++ "\n" ++
  ".Lwsvn_pdone:"

def ziskWitnessStateValidateNodeKindsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8"

def ziskWitnessStateValidateNodeKindsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessStateValidateNodeKindsPrologue
  dataAsm     := ziskWitnessStateValidateNodeKindsDataSection
}

/-! ## witness_codes_validate_lengths

    Walk an SSZ `witness.codes` list section and verify every
    entry's byte length is within a caller-supplied cap. Catches
    oversized code blobs up-front, before any account-driven
    lookup attempts to consume them.

    Spec-side rationale: per Amsterdam EIP-7907, deployed contract
    code is capped at 65536 bytes (0x10000, raised from the
    pre-Amsterdam EIP-170 0x6000 = 24576); per EIP-3860/EIP-7954,
    initcode is capped at 131072 bytes (0x20000 = 2×MAX_CODE_SIZE).
    Every entry in `witness.codes` is supposed to be deployed code
    referenced by some account's `code_hash`, so the deployed-code
    cap applies. A stateless guest that doesn't catch oversized
    entries up-front could waste keccak cycles hashing absurdly
    large blobs, or surface inconsistent results.

    The cap is passed as an argument so the same primitive can
    cover the deployed-code cap (65536) for current state and the
    initcode cap (131072), or any future tighter bound. (Earlier
    prose said 32768 for EIP-7907 — half-migrated constant; the
    primitive itself never hardcodes the bound.)

    Distinct from previous witness-iteration primitives:
      * PR `witness_state_validate_node_kinds` -- iterates
        witness.state and checks each entry parses as a valid
        MPT node (not bounded by length).
      * `witness_lookup_by_hash` (K19) -- searches for one hash
        match; doesn't bound per-element length.

    Calling convention:
      a0 (input)  : witness.codes section ptr
      a1 (input)  : section_len (0 ⇒ vacuous-valid)
      a2 (input)  : u64 max_byte_length (per-entry cap;
                    typical: 65536 = Amsterdam EIP-7907 MAX_CODE_SIZE)
      a3 (input)  : u64 out ptr (n_processed; on success the
                    total count N, on failure the index of the
                    first oversized entry)
      a4 (input)  : u64 out ptr (first_bad_index;
                    0xFFFFFFFFFFFFFFFF on success)
      ra (input)  : return
      a0 (output) :
        0 = all entries within cap (or empty section)
        1 = some entry exceeds `max_byte_length`
-/
def witnessCodesValidateLengths_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .SD .x19 .x0 (0 : BitVec 12),
    .LI .x5 (-1 : Word),
    .SD .x20 .x5 (0 : BitVec 12),
    .BEQ .x9 .x0 (92 : BitVec 13),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x21 .x5 (2 : BitVec 6),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x21 (76 : BitVec 13),
    .SLLI .x5 .x22 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .ADDI .x28 .x22 (1 : BitVec 12),
    .BEQ .x28 .x21 (24 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .SUB .x30 .x29 .x7,
    .JAL .x0 (8 : BitVec 21),
    .SUB .x30 .x9 .x7,
    .BLTU .x18 .x30 (12 : BitVec 13),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-56 : BitVec 21),
    .SD .x19 .x22 (0 : BitVec 12),
    .SD .x20 .x22 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (20 : BitVec 21),
    .SD .x19 .x21 (0 : BitVec 12),
    .LI .x5 (-1 : Word),
    .SD .x20 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def witnessCodesValidateLengthsFunction : String :=
  "witness_codes_validate_lengths:\n" ++ emitProgram witnessCodesValidateLengths_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `witnessCodesValidateLengths_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem witnessCodesValidateLengthsFunction_eq_prog :
    witnessCodesValidateLengthsFunction = "witness_codes_validate_lengths:\n" ++ emitProgram witnessCodesValidateLengths_prog := rfl

#guard witnessCodesValidateLengthsFunction.startsWith "witness_codes_validate_lengths:\n"
#guard witnessCodesValidateLengths_prog.length = 54
/-- `zisk_witness_codes_validate_lengths`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : section_len (u64 LE)
      bytes 16..24 : max_byte_length (u64 LE)
      bytes 24..   : witness.codes section bytes
    Output layout:
      bytes  0.. 8 : status (0 ok / 1 some entry too long)
      bytes  8..16 : n_processed (= N on success; first bad index on fail)
      bytes 16..24 : first_bad_index (0xFF..FF on success) -/
def ziskWitnessCodesValidateLengthsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  ld a2, 16(a5)               # max_byte_length\n" ++
  "  addi a0, a5, 24             # section ptr\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, witness_codes_validate_lengths\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwcvl_pdone\n" ++
  witnessCodesValidateLengthsFunction ++ "\n" ++
  ".Lwcvl_pdone:"

def ziskWitnessCodesValidateLengthsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "wcvl_dummy:\n" ++
  "  .zero 8"

def ziskWitnessCodesValidateLengthsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessCodesValidateLengthsPrologue
  dataAsm     := ziskWitnessCodesValidateLengthsDataSection
}

/-! ## witness_storage_validate_node_kinds

    Walk an SSZ `witness.storage` list section and call K21
    `mpt_node_kind` on every entry. Verifies that every entry
    parses as a valid MPT node (Leaf / Extension / Branch).
    Reports the index of the first malformed entry, or the
    total node count if all parse successfully.

    Spec-side rationale: every entry in `witness.storage` is
    supposed to be the canonical RLP encoding of an MPT node
    on the proof path from some `account.storage_root` down
    to a slot leaf. A witness with a non-parseable storage
    node can't be safely consumed by `mpt_walk` -- this
    primitive catches structural failures up-front rather
    than discovering them mid-trie-walk during a SLOAD.

    Structurally identical to the state-side variant
    (`witness_state_validate_node_kinds`) -- same iteration
    pattern, same per-element check via K21 `mpt_node_kind`.
    Keeping them as separate functions makes call sites
    self-documenting (the section being validated is in the
    function name) and isolates the `.data` scratch labels
    so a single ELF that links both probes wouldn't collide
    on labels.

    Calling convention:
      a0 (input)  : witness.storage section ptr
      a1 (input)  : section_len (0 ⇒ vacuous-valid)
      a2 (input)  : u64 out ptr (n_processed; on success the
                    total node count N, on failure the index of
                    the first invalid node)
      a3 (input)  : u64 out ptr (first_bad_index;
                    0xFFFFFFFFFFFFFFFF on success, else the
                    failing element's index)
      ra (input)  : return
      a0 (output) :
        0 = all entries parse as valid MPT nodes
        1 = some entry failed to parse (`mpt_node_kind` = 3)
-/
/-! Probe-only local PC placeholder. -/
def witnessStorageValidateNodeKindsPc : Nat := 0x80000000

def witnessStorageValidateNodeKinds_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .SD .x18 .x0 (0 : BitVec 12),
    .LI .x5 (-1 : Word),
    .SD .x19 .x5 (0 : BitVec 12),
    .BEQ .x9 .x0 (brOff (witnessStorageValidateNodeKindsPc + 172) (witnessStorageValidateNodeKindsPc + 64)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x20 .x5 (2 : BitVec 6),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x20 (brOff (witnessStorageValidateNodeKindsPc + 172) (witnessStorageValidateNodeKindsPc + 80)),
    .SLLI .x5 .x21 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .ADD .x10 .x8 .x7,
    .ADDI .x28 .x21 (1 : BitVec 12),
    .BEQ .x28 .x20 (24 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .ADD .x29 .x8 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x29 .x8 .x9,
    .SUB .x11 .x29 .x10,
    .JAL .x1 (jalOff GuestAddrs.mpt_node_kind (witnessStorageValidateNodeKindsPc + 136)),
    .LI .x5 (3 : Word),
    .BEQ .x10 .x5 (12 : BitVec 13),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (jalOff (witnessStorageValidateNodeKindsPc + 80) (witnessStorageValidateNodeKindsPc + 152)),
    .SD .x18 .x21 (0 : BitVec 12),
    .SD .x19 .x21 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (20 : BitVec 21),
    .SD .x18 .x20 (0 : BitVec 12),
    .LI .x5 (-1 : Word),
    .SD .x19 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `witnessStorageValidateNodeKinds_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessStorageValidateNodeKinds_relocs : RelocTable :=
  [ (34, .jal .x1 "mpt_node_kind") ]

def witnessStorageValidateNodeKindsFunction : String :=
  "witness_storage_validate_node_kinds:\n" ++ emitProgramR witnessStorageValidateNodeKinds_prog witnessStorageValidateNodeKinds_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessStorageValidateNodeKinds_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessStorageValidateNodeKindsFunction_eq_prog :
    witnessStorageValidateNodeKindsFunction = "witness_storage_validate_node_kinds:\n" ++ emitProgramR witnessStorageValidateNodeKinds_prog witnessStorageValidateNodeKinds_relocs := rfl

#guard witnessStorageValidateNodeKindsFunction.startsWith "witness_storage_validate_node_kinds:\n"
#guard witnessStorageValidateNodeKinds_prog.length = 57
/-- `zisk_witness_storage_validate_node_kinds`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : section_len (u64 LE)
      bytes 16..   : witness.storage section bytes
    Output layout:
      bytes  0.. 8 : status (0 ok / 1 parse fail)
      bytes  8..16 : n_processed (= N on success; first bad index on fail)
      bytes 16..24 : first_bad_index (0xFF..FF on success) -/
def ziskWitnessStorageValidateNodeKindsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  addi a0, a5, 16             # section ptr\n" ++
  "  li a2, 0xa0010008\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, witness_storage_validate_node_kinds\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwsgvn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  witnessStorageValidateNodeKindsFunction ++ "\n" ++
  ".Lwsgvn_pdone:"

def ziskWitnessStorageValidateNodeKindsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8"

def ziskWitnessStorageValidateNodeKindsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessStorageValidateNodeKindsPrologue
  dataAsm     := ziskWitnessStorageValidateNodeKindsDataSection
}

end EvmAsm.Codegen
