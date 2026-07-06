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
def witnessStateValidateNodeKindsFunction : String :=
  "witness_state_validate_node_kinds:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # n_processed out\n" ++
  "  mv s3, a3                  # first_bad_index out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  beqz s1, .Lwsvn_ok           # empty section ⇒ vacuous-valid\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s4, t0, 2               # s4 = N\n" ++
  "  li s5, 0                     # s5 = i\n" ++
  ".Lwsvn_loop:\n" ++
  "  beq s5, s4, .Lwsvn_ok\n" ++
  "  # Element i bounds.\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)                # inner_off_i\n" ++
  "  add a0, s0, t2               # el_i_start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lwsvn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4               # el_i_end\n" ++
  "  j .Lwsvn_have_end\n" ++
  ".Lwsvn_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lwsvn_have_end:\n" ++
  "  sub a1, t4, a0               # el_i_len\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  li t0, 3\n" ++
  "  beq a0, t0, .Lwsvn_parse_fail\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwsvn_loop\n" ++
  ".Lwsvn_parse_fail:\n" ++
  "  sd s5, 0(s2)                 # n_processed = i\n" ++
  "  sd s5, 0(s3)                 # first_bad_index = i\n" ++
  "  li a0, 1\n" ++
  "  j .Lwsvn_ret\n" ++
  ".Lwsvn_ok:\n" ++
  "  sd s4, 0(s2)                 # n_processed = N (full)\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 0(s3)                 # first_bad_index = -1\n" ++
  "  li a0, 0\n" ++
  ".Lwsvn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

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
    code is capped at 32768 bytes (0x8000, raised from the
    pre-Amsterdam EIP-170 0x6000 = 24576); per EIP-3860/EIP-7954,
    initcode is capped at 65536 bytes (0x10000). Every entry in
    `witness.codes` is supposed to be deployed code referenced
    by some account's `code_hash`, so the deployed-code cap applies. A
    stateless guest that doesn't catch oversized entries
    up-front could waste keccak cycles hashing absurdly large
    blobs, or surface inconsistent results.

    The cap is passed as an argument so the same primitive can
    cover the deployed-code cap (32768) for current state and the
    initcode cap (65536), or any future tighter bound.

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
                    typical: 32768 = Amsterdam EIP-7907 MAX_CODE_SIZE)
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
def witnessStorageValidateNodeKindsFunction : String :=
  "witness_storage_validate_node_kinds:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # n_processed out\n" ++
  "  mv s3, a3                  # first_bad_index out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  beqz s1, .Lwsgvn_ok          # empty section ⇒ vacuous-valid\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s4, t0, 2               # s4 = N\n" ++
  "  li s5, 0                     # s5 = i\n" ++
  ".Lwsgvn_loop:\n" ++
  "  beq s5, s4, .Lwsgvn_ok\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)                # inner_off_i\n" ++
  "  add a0, s0, t2               # el_i_start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lwsgvn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4               # el_i_end\n" ++
  "  j .Lwsgvn_have_end\n" ++
  ".Lwsgvn_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lwsgvn_have_end:\n" ++
  "  sub a1, t4, a0               # el_i_len\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  li t0, 3\n" ++
  "  beq a0, t0, .Lwsgvn_parse_fail\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwsgvn_loop\n" ++
  ".Lwsgvn_parse_fail:\n" ++
  "  sd s5, 0(s2)\n" ++
  "  sd s5, 0(s3)\n" ++
  "  li a0, 1\n" ++
  "  j .Lwsgvn_ret\n" ++
  ".Lwsgvn_ok:\n" ++
  "  sd s4, 0(s2)\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  li a0, 0\n" ++
  ".Lwsgvn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

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
