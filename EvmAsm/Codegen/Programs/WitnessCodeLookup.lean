/-
  EvmAsm.Codegen.Programs.WitnessCodeLookup

  Independent indexed lookup for witness.codes preimages. This deliberately
  uses code-specific globals so building a code index does not overwrite the
  witness.state index used by MPT/account lookups.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.MptWitnessLookup
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- The standalone `witness_codes_lookup_by_hash` entry point.

    The full code-index bundle below also contains the code-index builder and
    indexed helper cluster.  Keep this entry separate so the leaf routine can
    be represented as a `Program` and later receive its own triple, while the
    existing aggregate emitters continue to include the complete cluster. -/
def witnessCodesLookupByHash_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.wclh_lookup_calls (GuestAddrs.witness_codes_lookup_by_hash + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_lookup_calls (GuestAddrs.witness_codes_lookup_by_hash + 56)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_enabled (GuestAddrs.witness_codes_lookup_by_hash + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_enabled (GuestAddrs.witness_codes_lookup_by_hash + 76)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 220) (GuestAddrs.witness_codes_lookup_by_hash + 88)),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_section_ptr (GuestAddrs.witness_codes_lookup_by_hash + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_section_ptr (GuestAddrs.witness_codes_lookup_by_hash + 92)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BNE .x8 .x5 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 220) (GuestAddrs.witness_codes_lookup_by_hash + 104)),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_section_len (GuestAddrs.witness_codes_lookup_by_hash + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_section_len (GuestAddrs.witness_codes_lookup_by_hash + 108)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BNE .x9 .x5 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 220) (GuestAddrs.witness_codes_lookup_by_hash + 120)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x5 (laHi GuestAddrs.wclh_indexed_calls (GuestAddrs.witness_codes_lookup_by_hash + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_indexed_calls (GuestAddrs.witness_codes_lookup_by_hash + 144)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.witness_codes_lookup_by_hash_indexed (GuestAddrs.witness_codes_lookup_by_hash + 164)),
    .BNE .x10 .x0 (28 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.wclh_indexed_hits (GuestAddrs.witness_codes_lookup_by_hash + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_indexed_hits (GuestAddrs.witness_codes_lookup_by_hash + 172)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.witness_codes_lookup_by_hash + 580) (GuestAddrs.witness_codes_lookup_by_hash + 192)),
    .AUIPC .x5 (laHi GuestAddrs.wclh_indexed_misses (GuestAddrs.witness_codes_lookup_by_hash + 196)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_indexed_misses (GuestAddrs.witness_codes_lookup_by_hash + 196)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.witness_codes_lookup_by_hash + 580) (GuestAddrs.witness_codes_lookup_by_hash + 216)),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_calls (GuestAddrs.witness_codes_lookup_by_hash + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_calls (GuestAddrs.witness_codes_lookup_by_hash + 220)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_last_section_len (GuestAddrs.witness_codes_lookup_by_hash + 240)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_last_section_len (GuestAddrs.witness_codes_lookup_by_hash + 240)),
    .SD .x5 .x9 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_max_section_len (GuestAddrs.witness_codes_lookup_by_hash + 252)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_max_section_len (GuestAddrs.witness_codes_lookup_by_hash + 252)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BGEU .x6 .x9 (8 : BitVec 13),
    .SD .x5 .x9 (0 : BitVec 12),
    .BEQ .x9 .x0 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 556) (GuestAddrs.witness_codes_lookup_by_hash + 272)),
    .LI .x5 (4 : Word),
    .BLTU .x9 .x5 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 556) (GuestAddrs.witness_codes_lookup_by_hash + 280)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .ANDI .x6 .x5 (3 : BitVec 12),
    .BNE .x6 .x0 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 556) (GuestAddrs.witness_codes_lookup_by_hash + 292)),
    .BLTU .x9 .x5 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 556) (GuestAddrs.witness_codes_lookup_by_hash + 296)),
    .SRLI .x21 .x5 (2 : BitVec 6),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x21 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 556) (GuestAddrs.witness_codes_lookup_by_hash + 308)),
    .SLLI .x5 .x22 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .BLTU .x9 .x7 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 556) (GuestAddrs.witness_codes_lookup_by_hash + 324)),
    .ADD .x10 .x8 .x7,
    .ADDI .x28 .x22 (1 : BitVec 12),
    .BEQ .x28 .x21 (28 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .BLTU .x9 .x29 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 556) (GuestAddrs.witness_codes_lookup_by_hash + 352)),
    .ADD .x29 .x8 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x29 .x8 .x9,
    .BLTU .x29 .x10 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 556) (GuestAddrs.witness_codes_lookup_by_hash + 368)),
    .SUB .x11 .x29 .x10,
    .AUIPC .x12 (laHi GuestAddrs.wclh_scratch_hash (GuestAddrs.witness_codes_lookup_by_hash + 376)),
    .ADDI .x12 .x12 (laLo GuestAddrs.wclh_scratch_hash (GuestAddrs.witness_codes_lookup_by_hash + 376)),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_iterations (GuestAddrs.witness_codes_lookup_by_hash + 384)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_iterations (GuestAddrs.witness_codes_lookup_by_hash + 384)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.witness_codes_lookup_by_hash + 404)),
    .AUIPC .x5 (laHi GuestAddrs.wclh_scratch_hash (GuestAddrs.witness_codes_lookup_by_hash + 408)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_scratch_hash (GuestAddrs.witness_codes_lookup_by_hash + 408)),
    .MV .x6 .x18,
    .LD .x7 .x5 (0 : BitVec 12),
    .LD .x28 .x6 (0 : BitVec 12),
    .BNE .x7 .x28 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 548) (GuestAddrs.witness_codes_lookup_by_hash + 428)),
    .LD .x7 .x5 (8 : BitVec 12),
    .LD .x28 .x6 (8 : BitVec 12),
    .BNE .x7 .x28 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 548) (GuestAddrs.witness_codes_lookup_by_hash + 440)),
    .LD .x7 .x5 (16 : BitVec 12),
    .LD .x28 .x6 (16 : BitVec 12),
    .BNE .x7 .x28 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 548) (GuestAddrs.witness_codes_lookup_by_hash + 452)),
    .LD .x7 .x5 (24 : BitVec 12),
    .LD .x28 .x6 (24 : BitVec 12),
    .BNE .x7 .x28 (brOff (GuestAddrs.witness_codes_lookup_by_hash + 548) (GuestAddrs.witness_codes_lookup_by_hash + 464)),
    .SLLI .x5 .x22 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .SD .x19 .x7 (0 : BitVec 12),
    .ADDI .x28 .x22 (1 : BitVec 12),
    .BEQ .x28 .x21 (24 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .SUB .x29 .x29 .x7,
    .JAL .x0 (8 : BitVec 21),
    .SUB .x29 .x9 .x7,
    .SD .x20 .x29 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_hits (GuestAddrs.witness_codes_lookup_by_hash + 520)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_hits (GuestAddrs.witness_codes_lookup_by_hash + 520)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (36 : BitVec 21),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.witness_codes_lookup_by_hash + 308) (GuestAddrs.witness_codes_lookup_by_hash + 552)),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_misses (GuestAddrs.witness_codes_lookup_by_hash + 556)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_misses (GuestAddrs.witness_codes_lookup_by_hash + 556)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (1 : Word),
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

/-- Reloc side-table for `witnessCodesLookupByHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessCodesLookupByHash_relocs : RelocTable :=
  [ (14, .la .x5 "wclh_lookup_calls"),
    (19, .la .x5 "wcidx_enabled"),
    (23, .la .x5 "wcidx_section_ptr"),
    (27, .la .x5 "wcidx_section_len"),
    (36, .la .x5 "wclh_indexed_calls"),
    (41, .jal .x1 "witness_codes_lookup_by_hash_indexed"),
    (43, .la .x5 "wclh_indexed_hits"),
    (49, .la .x5 "wclh_indexed_misses"),
    (55, .la .x5 "wclh_linear_calls"),
    (60, .la .x5 "wclh_linear_last_section_len"),
    (63, .la .x5 "wclh_linear_max_section_len"),
    (94, .la .x12 "wclh_scratch_hash"),
    (96, .la .x5 "wclh_linear_iterations"),
    (101, .jal .x1 "zkvm_keccak256"),
    (102, .la .x5 "wclh_scratch_hash"),
    (130, .la .x5 "wclh_linear_hits"),
    (139, .la .x5 "wclh_linear_misses") ]

def witnessCodesLookupByHashEntryFunction : String :=
  "witness_codes_lookup_by_hash:\n" ++ emitProgramR witnessCodesLookupByHash_prog witnessCodesLookupByHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessCodesLookupByHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessCodesLookupByHashEntryFunction_eq_prog :
    witnessCodesLookupByHashEntryFunction = "witness_codes_lookup_by_hash:\n" ++ emitProgramR witnessCodesLookupByHash_prog witnessCodesLookupByHash_relocs := rfl

#guard witnessCodesLookupByHashEntryFunction.startsWith "witness_codes_lookup_by_hash:\n"
#guard witnessCodesLookupByHash_prog.length = 155
/-- Code-specific variant of `witness_lookup_by_hash`.

    The generated assembler is the existing K19 indexed/linear implementation
    with every state-index global and local label renamed from `widx`/`wlh` to
    `wcidx`/`wclh`, and with public entry points renamed to
    `witness_codes_index_build`, `witness_codes_lookup_by_hash_indexed`, and
    `witness_codes_lookup_by_hash`.

    This keeps state and code indexes live at the same time: a caller can build
    the regular `witness_index_build` for `witness.state`, build
    `witness_codes_index_build` for `witness.codes`, and then route code-hash
    preimage probes through this helper without invalidating state lookups.

    The rename is a pure textual recoding of the state-index cluster, applied
    per routine so each code-side routine has its own name (and can therefore
    be represented as a `Program` and carry its own triple) while the emitted
    bundle stays exactly the concatenation the single `.replace` produced. -/
def witnessCodesRecode (s : String) : String :=
  (((s.replace
      "witness_lookup_by_hash_indexed"
      "witness_codes_lookup_by_hash_indexed").replace
      "witness_lookup_by_hash"
      "witness_codes_lookup_by_hash").replace
      "witness_index_build"
      "witness_codes_index_build").replace
      "widx" "wcidx" |>.replace
      "wlh" "wclh"

/-- `wcidx_record_ptr(i)`: address of the `i`-th 48-byte code-index record. -/
def wcidxRecordPtr_prog : Program :=
  [ .SLLI .x5 .x10 (5 : BitVec 6),
    .SLLI .x6 .x10 (4 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .AUIPC .x10 (laHi GuestAddrs.wcidx_records (GuestAddrs.wcidx_record_ptr + 12)),
    .ADDI .x10 .x10 (laLo GuestAddrs.wcidx_records (GuestAddrs.wcidx_record_ptr + 12)),
    .ADD .x10 .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `wcidxRecordPtr_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def wcidxRecordPtr_relocs : RelocTable :=
  [ (3, .la .x10 "wcidx_records") ]

def wcidxRecordPtrFunction : String :=
  "wcidx_record_ptr:\n" ++ emitProgramR wcidxRecordPtr_prog wcidxRecordPtr_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `wcidxRecordPtr_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem wcidxRecordPtrFunction_eq_prog :
    wcidxRecordPtrFunction = "wcidx_record_ptr:\n" ++ emitProgramR wcidxRecordPtr_prog wcidxRecordPtr_relocs := rfl

#guard wcidxRecordPtrFunction.startsWith "wcidx_record_ptr:\n"
#guard wcidxRecordPtr_prog.length = 7
/-- `wcidx_cmp32(a, b)`: 32-byte unsigned compare over code-index hashes. -/
def wcidxCmp32_prog : Program :=
  [ .LI .x5 (32 : Word),
    .BEQ .x5 .x0 (44 : BitVec 13),
    .LBU .x6 .x10 (0 : BitVec 12),
    .LBU .x7 .x11 (0 : BitVec 12),
    .BLTU .x6 .x7 (24 : BitVec 13),
    .BLTU .x7 .x6 (36 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def wcidxCmp32Function : String :=
  "wcidx_cmp32:\n" ++ emitProgram wcidxCmp32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `wcidxCmp32_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem wcidxCmp32Function_eq_prog :
    wcidxCmp32Function = "wcidx_cmp32:\n" ++ emitProgram wcidxCmp32_prog := rfl

#guard wcidxCmp32Function.startsWith "wcidx_cmp32:\n"
#guard wcidxCmp32_prog.length = 16
/-- `wcidx_swap_records(p, q)`: swap two 48-byte code-index records. -/
def wcidxSwapRecords_prog : Program :=
  [ .BEQ .x10 .x11 (44 : BitVec 13),
    .LI .x31 (6 : Word),
    .BEQ .x31 .x0 (36 : BitVec 13),
    .LD .x5 .x10 (0 : BitVec 12),
    .LD .x6 .x11 (0 : BitVec 12),
    .SD .x10 .x6 (0 : BitVec 12),
    .SD .x11 .x5 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x31 .x31 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def wcidxSwapRecordsFunction : String :=
  "wcidx_swap_records:\n" ++ emitProgram wcidxSwapRecords_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `wcidxSwapRecords_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem wcidxSwapRecordsFunction_eq_prog :
    wcidxSwapRecordsFunction = "wcidx_swap_records:\n" ++ emitProgram wcidxSwapRecords_prog := rfl

#guard wcidxSwapRecordsFunction.startsWith "wcidx_swap_records:\n"
#guard wcidxSwapRecords_prog.length = 12
/-- `wcidx_sift_down(root, count)`: max-heap sift-down over the code-index array. -/
def wcidxSiftDown_prog : Program :=
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
    .SLLI .x18 .x8 (1 : BitVec 6),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .BGEU .x18 .x9 (brOff (GuestAddrs.wcidx_sift_down + 212) (GuestAddrs.wcidx_sift_down + 52)),
    .MV .x19 .x8,
    .MV .x10 .x19,
    .JAL .x1 (jalOff GuestAddrs.wcidx_record_ptr (GuestAddrs.wcidx_sift_down + 64)),
    .MV .x20 .x10,
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.wcidx_record_ptr (GuestAddrs.wcidx_sift_down + 76)),
    .MV .x21 .x10,
    .MV .x10 .x20,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.wcidx_cmp32 (GuestAddrs.wcidx_sift_down + 92)),
    .LI .x5 (0 : Word),
    .BNE .x10 .x5 (8 : BitVec 13),
    .MV .x19 .x18,
    .ADDI .x22 .x18 (1 : BitVec 12),
    .BGEU .x22 .x9 (52 : BitVec 13),
    .MV .x10 .x19,
    .JAL .x1 (jalOff GuestAddrs.wcidx_record_ptr (GuestAddrs.wcidx_sift_down + 120)),
    .MV .x20 .x10,
    .MV .x10 .x22,
    .JAL .x1 (jalOff GuestAddrs.wcidx_record_ptr (GuestAddrs.wcidx_sift_down + 132)),
    .MV .x21 .x10,
    .MV .x10 .x20,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.wcidx_cmp32 (GuestAddrs.wcidx_sift_down + 148)),
    .LI .x5 (0 : Word),
    .BNE .x10 .x5 (8 : BitVec 13),
    .MV .x19 .x22,
    .BEQ .x19 .x8 (48 : BitVec 13),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.wcidx_record_ptr (GuestAddrs.wcidx_sift_down + 172)),
    .MV .x20 .x10,
    .MV .x10 .x19,
    .JAL .x1 (jalOff GuestAddrs.wcidx_record_ptr (GuestAddrs.wcidx_sift_down + 184)),
    .MV .x21 .x10,
    .MV .x10 .x20,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.wcidx_swap_records (GuestAddrs.wcidx_sift_down + 200)),
    .MV .x8 .x19,
    .JAL .x0 (jalOff (GuestAddrs.wcidx_sift_down + 44) (GuestAddrs.wcidx_sift_down + 208)),
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

/-- Reloc side-table for `wcidxSiftDown_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def wcidxSiftDown_relocs : RelocTable :=
  [ (16, .jal .x1 "wcidx_record_ptr"),
    (19, .jal .x1 "wcidx_record_ptr"),
    (23, .jal .x1 "wcidx_cmp32"),
    (30, .jal .x1 "wcidx_record_ptr"),
    (33, .jal .x1 "wcidx_record_ptr"),
    (37, .jal .x1 "wcidx_cmp32"),
    (43, .jal .x1 "wcidx_record_ptr"),
    (46, .jal .x1 "wcidx_record_ptr"),
    (50, .jal .x1 "wcidx_swap_records") ]

def wcidxSiftDownFunction : String :=
  "wcidx_sift_down:\n" ++ emitProgramR wcidxSiftDown_prog wcidxSiftDown_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `wcidxSiftDown_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem wcidxSiftDownFunction_eq_prog :
    wcidxSiftDownFunction = "wcidx_sift_down:\n" ++ emitProgramR wcidxSiftDown_prog wcidxSiftDown_relocs := rfl

#guard wcidxSiftDownFunction.startsWith "wcidx_sift_down:\n"
#guard wcidxSiftDown_prog.length = 63
/-- `witness_codes_index_build(section_ptr, section_len)`: build the sorted
    `witness.codes` index, independent of the `witness.state` index. -/
def witnessCodesIndexBuild_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.wcidx_enabled (GuestAddrs.witness_codes_index_build + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_enabled (GuestAddrs.witness_codes_index_build + 48)),
    .SD .x5 .x0 (0 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .AUIPC .x5 (laHi GuestAddrs.wcidx_build_status (GuestAddrs.witness_codes_index_build + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_build_status (GuestAddrs.witness_codes_index_build + 68)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_build_section_len (GuestAddrs.witness_codes_index_build + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_build_section_len (GuestAddrs.witness_codes_index_build + 80)),
    .SD .x5 .x9 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_build_count (GuestAddrs.witness_codes_index_build + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_build_count (GuestAddrs.witness_codes_index_build + 92)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_lookup_calls (GuestAddrs.witness_codes_index_build + 104)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_lookup_calls (GuestAddrs.witness_codes_index_build + 104)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_indexed_calls (GuestAddrs.witness_codes_index_build + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_indexed_calls (GuestAddrs.witness_codes_index_build + 116)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_indexed_hits (GuestAddrs.witness_codes_index_build + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_indexed_hits (GuestAddrs.witness_codes_index_build + 128)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_indexed_misses (GuestAddrs.witness_codes_index_build + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_indexed_misses (GuestAddrs.witness_codes_index_build + 140)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_calls (GuestAddrs.witness_codes_index_build + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_calls (GuestAddrs.witness_codes_index_build + 152)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_hits (GuestAddrs.witness_codes_index_build + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_hits (GuestAddrs.witness_codes_index_build + 164)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_misses (GuestAddrs.witness_codes_index_build + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_misses (GuestAddrs.witness_codes_index_build + 176)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_iterations (GuestAddrs.witness_codes_index_build + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_iterations (GuestAddrs.witness_codes_index_build + 188)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_last_section_len (GuestAddrs.witness_codes_index_build + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_last_section_len (GuestAddrs.witness_codes_index_build + 200)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wclh_linear_max_section_len (GuestAddrs.witness_codes_index_build + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wclh_linear_max_section_len (GuestAddrs.witness_codes_index_build + 212)),
    .SD .x5 .x0 (0 : BitVec 12),
    .BEQ .x9 .x0 (brOff (GuestAddrs.witness_codes_index_build + 392) (GuestAddrs.witness_codes_index_build + 224)),
    .LI .x5 (4 : Word),
    .BLTU .x9 .x5 (brOff (GuestAddrs.witness_codes_index_build + 560) (GuestAddrs.witness_codes_index_build + 232)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .ANDI .x6 .x5 (3 : BitVec 12),
    .BNE .x6 .x0 (brOff (GuestAddrs.witness_codes_index_build + 560) (GuestAddrs.witness_codes_index_build + 244)),
    .BLTU .x9 .x5 (brOff (GuestAddrs.witness_codes_index_build + 560) (GuestAddrs.witness_codes_index_build + 248)),
    .SRLI .x18 .x5 (2 : BitVec 6),
    .AUIPC .x6 (laHi GuestAddrs.wcidx_build_count (GuestAddrs.witness_codes_index_build + 256)),
    .ADDI .x6 .x6 (laLo GuestAddrs.wcidx_build_count (GuestAddrs.witness_codes_index_build + 256)),
    .SD .x6 .x18 (0 : BitVec 12),
    .LUI .x6 (32 : BitVec 20),
    .BLTU .x6 .x18 (brOff (GuestAddrs.witness_codes_index_build + 560) (GuestAddrs.witness_codes_index_build + 272)),
    .MV .x19 .x5,
    .LI .x20 (0 : Word),
    .BEQ .x20 .x18 (brOff (GuestAddrs.witness_codes_index_build + 396) (GuestAddrs.witness_codes_index_build + 284)),
    .SLLI .x5 .x20 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x21 .x6 (0 : BitVec 12),
    .BLTU .x21 .x19 (brOff (GuestAddrs.witness_codes_index_build + 560) (GuestAddrs.witness_codes_index_build + 300)),
    .BLTU .x9 .x21 (brOff (GuestAddrs.witness_codes_index_build + 560) (GuestAddrs.witness_codes_index_build + 304)),
    .ADDI .x7 .x20 (1 : BitVec 12),
    .BEQ .x7 .x18 (24 : BitVec 13),
    .SLLI .x28 .x7 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x22 .x28 (0 : BitVec 12),
    .BLTU .x9 .x22 (brOff (GuestAddrs.witness_codes_index_build + 560) (GuestAddrs.witness_codes_index_build + 328)),
    .JAL .x0 (8 : BitVec 21),
    .MV .x22 .x9,
    .BLTU .x22 .x21 (brOff (GuestAddrs.witness_codes_index_build + 560) (GuestAddrs.witness_codes_index_build + 340)),
    .SUB .x23 .x22 .x21,
    .MV .x10 .x20,
    .JAL .x1 (jalOff GuestAddrs.wcidx_record_ptr (GuestAddrs.witness_codes_index_build + 352)),
    .MV .x24 .x10,
    .ADD .x10 .x8 .x21,
    .MV .x11 .x23,
    .MV .x12 .x24,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.witness_codes_index_build + 372)),
    .SD .x24 .x21 (32 : BitVec 12),
    .SD .x24 .x23 (40 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.witness_codes_index_build + 284) (GuestAddrs.witness_codes_index_build + 388)),
    .LI .x18 (0 : Word),
    .LI .x5 (2 : Word),
    .BLTU .x18 .x5 (brOff (GuestAddrs.witness_codes_index_build + 500) (GuestAddrs.witness_codes_index_build + 400)),
    .SRLI .x20 .x18 (1 : BitVec 6),
    .BEQ .x20 .x0 (24 : BitVec 13),
    .ADDI .x20 .x20 (-1 : BitVec 12),
    .MV .x10 .x20,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.wcidx_sift_down (GuestAddrs.witness_codes_index_build + 424)),
    .JAL .x0 (-20 : BitVec 21),
    .MV .x20 .x18,
    .LI .x5 (1 : Word),
    .BGEU .x5 .x20 (60 : BitVec 13),
    .ADDI .x20 .x20 (-1 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x1 (jalOff GuestAddrs.wcidx_record_ptr (GuestAddrs.witness_codes_index_build + 452)),
    .MV .x24 .x10,
    .MV .x10 .x20,
    .JAL .x1 (jalOff GuestAddrs.wcidx_record_ptr (GuestAddrs.witness_codes_index_build + 464)),
    .MV .x25 .x10,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.wcidx_swap_records (GuestAddrs.witness_codes_index_build + 480)),
    .LI .x10 (0 : Word),
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.wcidx_sift_down (GuestAddrs.witness_codes_index_build + 492)),
    .JAL .x0 (-60 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_section_ptr (GuestAddrs.witness_codes_index_build + 500)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_section_ptr (GuestAddrs.witness_codes_index_build + 500)),
    .SD .x5 .x8 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_section_len (GuestAddrs.witness_codes_index_build + 512)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_section_len (GuestAddrs.witness_codes_index_build + 512)),
    .SD .x5 .x9 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_count (GuestAddrs.witness_codes_index_build + 524)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_count (GuestAddrs.witness_codes_index_build + 524)),
    .SD .x5 .x18 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_enabled (GuestAddrs.witness_codes_index_build + 540)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_enabled (GuestAddrs.witness_codes_index_build + 540)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x6 (1 : Word),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_build_status (GuestAddrs.witness_codes_index_build + 564)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_build_status (GuestAddrs.witness_codes_index_build + 564)),
    .SD .x5 .x6 (0 : BitVec 12),
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
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `witnessCodesIndexBuild_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessCodesIndexBuild_relocs : RelocTable :=
  [ (12, .la .x5 "wcidx_enabled"),
    (17, .la .x5 "wcidx_build_status"),
    (20, .la .x5 "wcidx_build_section_len"),
    (23, .la .x5 "wcidx_build_count"),
    (26, .la .x5 "wclh_lookup_calls"),
    (29, .la .x5 "wclh_indexed_calls"),
    (32, .la .x5 "wclh_indexed_hits"),
    (35, .la .x5 "wclh_indexed_misses"),
    (38, .la .x5 "wclh_linear_calls"),
    (41, .la .x5 "wclh_linear_hits"),
    (44, .la .x5 "wclh_linear_misses"),
    (47, .la .x5 "wclh_linear_iterations"),
    (50, .la .x5 "wclh_linear_last_section_len"),
    (53, .la .x5 "wclh_linear_max_section_len"),
    (64, .la .x6 "wcidx_build_count"),
    (88, .jal .x1 "wcidx_record_ptr"),
    (93, .jal .x1 "zkvm_keccak256"),
    (106, .jal .x1 "wcidx_sift_down"),
    (113, .jal .x1 "wcidx_record_ptr"),
    (116, .jal .x1 "wcidx_record_ptr"),
    (120, .jal .x1 "wcidx_swap_records"),
    (123, .jal .x1 "wcidx_sift_down"),
    (125, .la .x5 "wcidx_section_ptr"),
    (128, .la .x5 "wcidx_section_len"),
    (131, .la .x5 "wcidx_count"),
    (135, .la .x5 "wcidx_enabled"),
    (141, .la .x5 "wcidx_build_status") ]

def witnessCodesIndexBuildFunction : String :=
  "witness_codes_index_build:\n" ++ emitProgramR witnessCodesIndexBuild_prog witnessCodesIndexBuild_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessCodesIndexBuild_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessCodesIndexBuildFunction_eq_prog :
    witnessCodesIndexBuildFunction = "witness_codes_index_build:\n" ++ emitProgramR witnessCodesIndexBuild_prog witnessCodesIndexBuild_relocs := rfl

#guard witnessCodesIndexBuildFunction.startsWith "witness_codes_index_build:\n"
#guard witnessCodesIndexBuild_prog.length = 158
/-- `witness_codes_lookup_by_hash_indexed(...)`: binary search of the code index. -/
def witnessCodesLookupByHashIndexed_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .MV .x18 .x14,
    .LI .x19 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.wcidx_count (GuestAddrs.witness_codes_lookup_by_hash_indexed + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wcidx_count (GuestAddrs.witness_codes_lookup_by_hash_indexed + 52)),
    .LD .x20 .x5 (0 : BitVec 12),
    .BGEU .x19 .x20 (brOff (GuestAddrs.witness_codes_lookup_by_hash_indexed + 156) (GuestAddrs.witness_codes_lookup_by_hash_indexed + 64)),
    .ADD .x21 .x19 .x20,
    .SRLI .x21 .x21 (1 : BitVec 6),
    .MV .x10 .x21,
    .JAL .x1 (jalOff GuestAddrs.wcidx_record_ptr (GuestAddrs.witness_codes_lookup_by_hash_indexed + 80)),
    .MV .x22 .x10,
    .MV .x10 .x22,
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.wcidx_cmp32 (GuestAddrs.witness_codes_lookup_by_hash_indexed + 96)),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (28 : BitVec 13),
    .LI .x5 (0 : Word),
    .BEQ .x10 .x5 (12 : BitVec 13),
    .MV .x20 .x21,
    .JAL .x0 (-56 : BitVec 21),
    .ADDI .x19 .x21 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.witness_codes_lookup_by_hash_indexed + 64) (GuestAddrs.witness_codes_lookup_by_hash_indexed + 128)),
    .LD .x5 .x22 (32 : BitVec 12),
    .SD .x9 .x5 (0 : BitVec 12),
    .LD .x5 .x22 (40 : BitVec 12),
    .SD .x18 .x5 (0 : BitVec 12),
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
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `witnessCodesLookupByHashIndexed_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessCodesLookupByHashIndexed_relocs : RelocTable :=
  [ (13, .la .x5 "wcidx_count"),
    (20, .jal .x1 "wcidx_record_ptr"),
    (24, .jal .x1 "wcidx_cmp32") ]

def witnessCodesLookupByHashIndexedFunction : String :=
  "witness_codes_lookup_by_hash_indexed:\n" ++ emitProgramR witnessCodesLookupByHashIndexed_prog witnessCodesLookupByHashIndexed_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessCodesLookupByHashIndexed_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessCodesLookupByHashIndexedFunction_eq_prog :
    witnessCodesLookupByHashIndexedFunction = "witness_codes_lookup_by_hash_indexed:\n" ++ emitProgramR witnessCodesLookupByHashIndexed_prog witnessCodesLookupByHashIndexed_relocs := rfl

#guard witnessCodesLookupByHashIndexedFunction.startsWith "witness_codes_lookup_by_hash_indexed:\n"
#guard witnessCodesLookupByHashIndexed_prog.length = 50
/-- The `wcidx_*` private data/bss labels. -/
def witnessCodesIndexDataSection : String := witnessCodesRecode witnessIndexDataSection

/-- ⚠️ Separator discipline mirrors `witnessIndexFunctions`: the recoding is
    textual, so the joiners here must reproduce the ones there exactly. The
    `#guard`s below pin every seam. -/
def witnessCodesLookupByHashHelpers : String :=
  "\n" ++ wcidxRecordPtrFunction ++ "\n" ++
  "\n" ++ wcidxCmp32Function ++ "\n" ++
  "\n" ++ wcidxSwapRecordsFunction ++ "\n" ++
  "\n" ++ wcidxSiftDownFunction ++ "\n" ++
  "\n" ++ witnessCodesIndexBuildFunction ++ "\n" ++
  "\n" ++ witnessCodesLookupByHashIndexedFunction ++ "\n" ++
  witnessCodesIndexDataSection

-- The recoding is exactly the whole-cluster rename this def used to perform in
-- one step; splitting it per routine must not perturb a single byte.
#guard witnessCodesLookupByHashHelpers = witnessCodesRecode witnessIndexFunctions

-- Seam pins, one per member boundary (`= 2` encodes "occurs exactly once").
#guard witnessCodesLookupByHashHelpers.startsWith "\nwcidx_record_ptr:\n"
#guard (witnessCodesLookupByHashHelpers.splitOn
  "  jalr x0, 0(x1)\n\nwcidx_cmp32:\n").length = 2
#guard (witnessCodesLookupByHashHelpers.splitOn
  "  li x10, 2\n  jalr x0, 0(x1)\n\nwcidx_swap_records:\n").length = 2
#guard (witnessCodesLookupByHashHelpers.splitOn
  "  addi x11, x11, 8\n  addi x31, x31, -1\n  jal x0, .-32\n  jalr x0, 0(x1)\n\nwcidx_sift_down:\n").length = 2
#guard (witnessCodesLookupByHashHelpers.splitOn
  "  ld x22, 56(x2)\n  addi x2, x2, 64\n  jalr x0, 0(x1)\n\nwitness_codes_index_build:\n").length = 2
#guard (witnessCodesLookupByHashHelpers.splitOn
  "  ld x25, 80(x2)\n  addi x2, x2, 96\n  jalr x0, 0(x1)\n\nwitness_codes_lookup_by_hash_indexed:\n").length = 2
#guard (witnessCodesLookupByHashHelpers.splitOn
  "  ld x22, 56(x2)\n  addi x2, x2, 64\n  jalr x0, 0(x1)\n.pushsection .data\n").length = 2

def witnessCodesLookupByHashBundle : String :=
  witnessCodesLookupByHashEntryFunction ++ "\n" ++
  witnessCodesLookupByHashHelpers

/-- `zisk_witness_codes_lookup_by_hash_indexed`: focused probe for the
    independent witness.codes index.

    Input layout matches `zisk_witness_lookup_by_hash_indexed`:
      bytes  0.. 8 : ziskemu metadata
      bytes  8..16 : section_len (u64)
      bytes 16..48 : target_hash (32 bytes)
      bytes 48..56 : lookup mode (0 = matching section, 1 = pointer mismatch)
      bytes 56..   : SSZ `witness.codes` list section

    Output:
      +0  lookup status (0 hit, 1 miss)
      +8  matched element offset within the section
      +16 matched element length
      +24 code-index build status
      +32 state-index enabled flag after code-index build (must remain 1)
      +40 code-index enabled flag
      +48 code-indexed lookup call count
      +56 code-linear lookup call count -/
def ziskWitnessCodesLookupByHashIndexedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld s0, 8(a5)                # section_len\n" ++
  "  addi s1, a5, 16             # target_hash ptr\n" ++
  "  ld s3, 48(a5)               # lookup mode\n" ++
  "  addi s2, a5, 56             # section ptr\n" ++
  "  # Build a tiny ordinary witness.state index first. The code-index build\n" ++
  "  # must not clear or overwrite this state-index enabled flag.\n" ++
  "  la a0, z_wclh_state_section\n" ++
  "  li a1, 5\n" ++
  "  jal ra, witness_index_build\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, witness_codes_index_build\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 24(t0)               # code-index build status\n" ++
  "  la t1, widx_enabled; ld t2, 0(t1); sd t2, 32(t0)\n" ++
  "  la t1, wcidx_enabled; ld t2, 0(t1); sd t2, 40(t0)\n" ++
  "  bnez a0, .Lwclh_probe_done\n" ++
  "  mv a0, s2\n" ++
  "  beqz s3, .Lwclh_probe_lookup_ptr_ready\n" ++
  "  addi a0, s2, 1              # deliberate section mismatch -> linear path\n" ++
  ".Lwclh_probe_lookup_ptr_ready:\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s1\n" ++
  "  li a3, 0xa0010008           # out_offset (OUTPUT + 8)\n" ++
  "  li a4, 0xa0010010           # out_length (OUTPUT + 16)\n" ++
  "  sd zero, 0(a3)\n" ++
  "  sd zero, 0(a4)\n" ++
  "  jal ra, witness_codes_lookup_by_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # lookup status\n" ++
  "  la t1, wclh_indexed_calls; ld t2, 0(t1); sd t2, 48(t0)\n" ++
  "  la t1, wclh_linear_calls; ld t2, 0(t1); sd t2, 56(t0)\n" ++
  ".Lwclh_probe_done:\n" ++
  "  j .Lwclh_probe_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  witnessCodesLookupByHashBundle ++ "\n" ++
  ".Lwclh_probe_pdone:"

def ziskWitnessCodesLookupByHashIndexedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  -- One SSZ list entry with a one-byte payload, enough to enable the regular
  -- state index before the code index is built.
  "z_wclh_state_section:\n" ++
  "  .byte 4,0,0,0,0xaa\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  "wclh_scratch_hash:\n" ++
  "  .zero 32"

def ziskWitnessCodesLookupByHashIndexedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessCodesLookupByHashIndexedPrologue
  dataAsm     := ziskWitnessCodesLookupByHashIndexedDataSection
}

end EvmAsm.Codegen
