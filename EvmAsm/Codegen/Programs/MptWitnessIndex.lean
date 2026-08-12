/-
  EvmAsm.Codegen.Programs.MptWitnessIndex

  Raw-asm helper cluster for the stateless witness NodeDb index used by
  `witness_lookup_by_hash`. Kept separate from Mpt.lean to stay under the
  codegen file-size guard.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Bytes stored per sorted witness-index record: 32-byte hash plus offset/len. -/
def mptWitnessIndexRecordBytes : Nat := 48

/-- Maximum `witness.state` records indexed by the stateless guest.

    The accepted `block_state_root` witness byte guard is 512 KiB. An SSZ
    `List[Bytes]` offset table uses four bytes per element, so the largest
    record count representable under that byte guard is 524288 / 4 = 131072.
    The backing arena is therefore about 6 MiB, well within the assumed ZisK RAM
    layout where input and RAM are separate regions. -/
def mptWitnessIndexCapacity : Nat := 524288 / 4

/-- Backing bytes reserved for `widx_records`. -/
def mptWitnessIndexArenaBytes : Nat :=
  mptWitnessIndexCapacity * mptWitnessIndexRecordBytes

/-- `widx_record_ptr(i)`: address of the `i`-th 48-byte index record. -/
def widxRecordPtr_prog : Program :=
  [ .SLLI .x5 .x10 (5 : BitVec 6),
    .SLLI .x6 .x10 (4 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .AUIPC .x10 (laHi GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12)),
    .ADDI .x10 .x10 (laLo GuestAddrs.widx_records (GuestAddrs.widx_record_ptr + 12)),
    .ADD .x10 .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `widxRecordPtr_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def widxRecordPtr_relocs : RelocTable :=
  [ (3, .la .x10 "widx_records") ]

def widxRecordPtrFunction : String :=
  "widx_record_ptr:\n" ++ emitProgramR widxRecordPtr_prog widxRecordPtr_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `widxRecordPtr_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem widxRecordPtrFunction_eq_prog :
    widxRecordPtrFunction = "widx_record_ptr:\n" ++ emitProgramR widxRecordPtr_prog widxRecordPtr_relocs := rfl

#guard widxRecordPtrFunction.startsWith "widx_record_ptr:\n"
#guard widxRecordPtr_prog.length = 7
/-- `widx_cmp32(a, b)`: 32-byte unsigned compare, returning 0/1/2 for lt/eq/gt. -/
def widxCmp32_prog : Program :=
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

def widxCmp32Function : String :=
  "widx_cmp32:\n" ++ emitProgram widxCmp32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `widxCmp32_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem widxCmp32Function_eq_prog :
    widxCmp32Function = "widx_cmp32:\n" ++ emitProgram widxCmp32_prog := rfl

#guard widxCmp32Function.startsWith "widx_cmp32:\n"
#guard widxCmp32_prog.length = 16
/-- `widx_swap_records(p, q)`: swap two 48-byte index records in place. -/
def widxSwapRecords_prog : Program :=
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

def widxSwapRecordsFunction : String :=
  "widx_swap_records:\n" ++ emitProgram widxSwapRecords_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `widxSwapRecords_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem widxSwapRecordsFunction_eq_prog :
    widxSwapRecordsFunction = "widx_swap_records:\n" ++ emitProgram widxSwapRecords_prog := rfl

#guard widxSwapRecordsFunction.startsWith "widx_swap_records:\n"
#guard widxSwapRecords_prog.length = 12
/-- `widx_sift_down(root, count)`: max-heap sift-down over the record array. -/
def widxSiftDown_prog : Program :=
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
    .BGEU .x18 .x9 (brOff (GuestAddrs.widx_sift_down + 212) (GuestAddrs.widx_sift_down + 52)),
    .MV .x19 .x8,
    .MV .x10 .x19,
    .JAL .x1 (jalOff GuestAddrs.widx_record_ptr (GuestAddrs.widx_sift_down + 64)),
    .MV .x20 .x10,
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.widx_record_ptr (GuestAddrs.widx_sift_down + 76)),
    .MV .x21 .x10,
    .MV .x10 .x20,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.widx_cmp32 (GuestAddrs.widx_sift_down + 92)),
    .LI .x5 (0 : Word),
    .BNE .x10 .x5 (8 : BitVec 13),
    .MV .x19 .x18,
    .ADDI .x22 .x18 (1 : BitVec 12),
    .BGEU .x22 .x9 (52 : BitVec 13),
    .MV .x10 .x19,
    .JAL .x1 (jalOff GuestAddrs.widx_record_ptr (GuestAddrs.widx_sift_down + 120)),
    .MV .x20 .x10,
    .MV .x10 .x22,
    .JAL .x1 (jalOff GuestAddrs.widx_record_ptr (GuestAddrs.widx_sift_down + 132)),
    .MV .x21 .x10,
    .MV .x10 .x20,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.widx_cmp32 (GuestAddrs.widx_sift_down + 148)),
    .LI .x5 (0 : Word),
    .BNE .x10 .x5 (8 : BitVec 13),
    .MV .x19 .x22,
    .BEQ .x19 .x8 (48 : BitVec 13),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.widx_record_ptr (GuestAddrs.widx_sift_down + 172)),
    .MV .x20 .x10,
    .MV .x10 .x19,
    .JAL .x1 (jalOff GuestAddrs.widx_record_ptr (GuestAddrs.widx_sift_down + 184)),
    .MV .x21 .x10,
    .MV .x10 .x20,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.widx_swap_records (GuestAddrs.widx_sift_down + 200)),
    .MV .x8 .x19,
    .JAL .x0 (jalOff (GuestAddrs.widx_sift_down + 44) (GuestAddrs.widx_sift_down + 208)),
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

/-- Reloc side-table for `widxSiftDown_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def widxSiftDown_relocs : RelocTable :=
  [ (16, .jal .x1 "widx_record_ptr"),
    (19, .jal .x1 "widx_record_ptr"),
    (23, .jal .x1 "widx_cmp32"),
    (30, .jal .x1 "widx_record_ptr"),
    (33, .jal .x1 "widx_record_ptr"),
    (37, .jal .x1 "widx_cmp32"),
    (43, .jal .x1 "widx_record_ptr"),
    (46, .jal .x1 "widx_record_ptr"),
    (50, .jal .x1 "widx_swap_records") ]

def widxSiftDownFunction : String :=
  "widx_sift_down:\n" ++ emitProgramR widxSiftDown_prog widxSiftDown_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `widxSiftDown_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem widxSiftDownFunction_eq_prog :
    widxSiftDownFunction = "widx_sift_down:\n" ++ emitProgramR widxSiftDown_prog widxSiftDown_relocs := rfl

#guard widxSiftDownFunction.startsWith "widx_sift_down:\n"
#guard widxSiftDown_prog.length = 63
/-- `witness_index_build(section_ptr, section_len)`: compute one keccak per SSZ
    list entry, store `(hash, offset, len)` records, and heapsort them by the
    full 32-byte hash. Capacity is `mptWitnessIndexCapacity`; larger sections
    fail conservatively at build. -/
def witnessIndexBuild_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.widx_enabled (GuestAddrs.witness_index_build + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_enabled (GuestAddrs.witness_index_build + 48)),
    .SD .x5 .x0 (0 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .AUIPC .x5 (laHi GuestAddrs.widx_build_status (GuestAddrs.witness_index_build + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_build_status (GuestAddrs.witness_index_build + 68)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.widx_build_section_len (GuestAddrs.witness_index_build + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_build_section_len (GuestAddrs.witness_index_build + 80)),
    .SD .x5 .x9 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.widx_build_count (GuestAddrs.witness_index_build + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_build_count (GuestAddrs.witness_index_build + 92)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_lookup_calls (GuestAddrs.witness_index_build + 104)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_lookup_calls (GuestAddrs.witness_index_build + 104)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_indexed_calls (GuestAddrs.witness_index_build + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_indexed_calls (GuestAddrs.witness_index_build + 116)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_indexed_hits (GuestAddrs.witness_index_build + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_indexed_hits (GuestAddrs.witness_index_build + 128)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_indexed_misses (GuestAddrs.witness_index_build + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_indexed_misses (GuestAddrs.witness_index_build + 140)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_calls (GuestAddrs.witness_index_build + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_calls (GuestAddrs.witness_index_build + 152)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_hits (GuestAddrs.witness_index_build + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_hits (GuestAddrs.witness_index_build + 164)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_misses (GuestAddrs.witness_index_build + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_misses (GuestAddrs.witness_index_build + 176)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_iterations (GuestAddrs.witness_index_build + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_iterations (GuestAddrs.witness_index_build + 188)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_last_section_len (GuestAddrs.witness_index_build + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_last_section_len (GuestAddrs.witness_index_build + 200)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_max_section_len (GuestAddrs.witness_index_build + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_max_section_len (GuestAddrs.witness_index_build + 212)),
    .SD .x5 .x0 (0 : BitVec 12),
    .BEQ .x9 .x0 (brOff (GuestAddrs.witness_index_build + 392) (GuestAddrs.witness_index_build + 224)),
    .LI .x5 (4 : Word),
    .BLTU .x9 .x5 (brOff (GuestAddrs.witness_index_build + 560) (GuestAddrs.witness_index_build + 232)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .ANDI .x6 .x5 (3 : BitVec 12),
    .BNE .x6 .x0 (brOff (GuestAddrs.witness_index_build + 560) (GuestAddrs.witness_index_build + 244)),
    .BLTU .x9 .x5 (brOff (GuestAddrs.witness_index_build + 560) (GuestAddrs.witness_index_build + 248)),
    .SRLI .x18 .x5 (2 : BitVec 6),
    .AUIPC .x6 (laHi GuestAddrs.widx_build_count (GuestAddrs.witness_index_build + 256)),
    .ADDI .x6 .x6 (laLo GuestAddrs.widx_build_count (GuestAddrs.witness_index_build + 256)),
    .SD .x6 .x18 (0 : BitVec 12),
    .LUI .x6 (32 : BitVec 20),
    .BLTU .x6 .x18 (brOff (GuestAddrs.witness_index_build + 560) (GuestAddrs.witness_index_build + 272)),
    .MV .x19 .x5,
    .LI .x20 (0 : Word),
    .BEQ .x20 .x18 (brOff (GuestAddrs.witness_index_build + 396) (GuestAddrs.witness_index_build + 284)),
    .SLLI .x5 .x20 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x21 .x6 (0 : BitVec 12),
    .BLTU .x21 .x19 (brOff (GuestAddrs.witness_index_build + 560) (GuestAddrs.witness_index_build + 300)),
    .BLTU .x9 .x21 (brOff (GuestAddrs.witness_index_build + 560) (GuestAddrs.witness_index_build + 304)),
    .ADDI .x7 .x20 (1 : BitVec 12),
    .BEQ .x7 .x18 (24 : BitVec 13),
    .SLLI .x28 .x7 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x22 .x28 (0 : BitVec 12),
    .BLTU .x9 .x22 (brOff (GuestAddrs.witness_index_build + 560) (GuestAddrs.witness_index_build + 328)),
    .JAL .x0 (8 : BitVec 21),
    .MV .x22 .x9,
    .BLTU .x22 .x21 (brOff (GuestAddrs.witness_index_build + 560) (GuestAddrs.witness_index_build + 340)),
    .SUB .x23 .x22 .x21,
    .MV .x10 .x20,
    .JAL .x1 (jalOff GuestAddrs.widx_record_ptr (GuestAddrs.witness_index_build + 352)),
    .MV .x24 .x10,
    .ADD .x10 .x8 .x21,
    .MV .x11 .x23,
    .MV .x12 .x24,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.witness_index_build + 372)),
    .SD .x24 .x21 (32 : BitVec 12),
    .SD .x24 .x23 (40 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.witness_index_build + 284) (GuestAddrs.witness_index_build + 388)),
    .LI .x18 (0 : Word),
    .LI .x5 (2 : Word),
    .BLTU .x18 .x5 (brOff (GuestAddrs.witness_index_build + 500) (GuestAddrs.witness_index_build + 400)),
    .SRLI .x20 .x18 (1 : BitVec 6),
    .BEQ .x20 .x0 (24 : BitVec 13),
    .ADDI .x20 .x20 (-1 : BitVec 12),
    .MV .x10 .x20,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.widx_sift_down (GuestAddrs.witness_index_build + 424)),
    .JAL .x0 (-20 : BitVec 21),
    .MV .x20 .x18,
    .LI .x5 (1 : Word),
    .BGEU .x5 .x20 (60 : BitVec 13),
    .ADDI .x20 .x20 (-1 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x1 (jalOff GuestAddrs.widx_record_ptr (GuestAddrs.witness_index_build + 452)),
    .MV .x24 .x10,
    .MV .x10 .x20,
    .JAL .x1 (jalOff GuestAddrs.widx_record_ptr (GuestAddrs.witness_index_build + 464)),
    .MV .x25 .x10,
    .MV .x10 .x24,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.widx_swap_records (GuestAddrs.witness_index_build + 480)),
    .LI .x10 (0 : Word),
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.widx_sift_down (GuestAddrs.witness_index_build + 492)),
    .JAL .x0 (-60 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.widx_section_ptr (GuestAddrs.witness_index_build + 500)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_section_ptr (GuestAddrs.witness_index_build + 500)),
    .SD .x5 .x8 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.widx_section_len (GuestAddrs.witness_index_build + 512)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_section_len (GuestAddrs.witness_index_build + 512)),
    .SD .x5 .x9 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.widx_count (GuestAddrs.witness_index_build + 524)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_count (GuestAddrs.witness_index_build + 524)),
    .SD .x5 .x18 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .AUIPC .x5 (laHi GuestAddrs.widx_enabled (GuestAddrs.witness_index_build + 540)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_enabled (GuestAddrs.witness_index_build + 540)),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x6 (1 : Word),
    .AUIPC .x5 (laHi GuestAddrs.widx_build_status (GuestAddrs.witness_index_build + 564)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_build_status (GuestAddrs.witness_index_build + 564)),
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

/-- Reloc side-table for `witnessIndexBuild_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessIndexBuild_relocs : RelocTable :=
  [ (12, .la .x5 "widx_enabled"),
    (17, .la .x5 "widx_build_status"),
    (20, .la .x5 "widx_build_section_len"),
    (23, .la .x5 "widx_build_count"),
    (26, .la .x5 "wlh_lookup_calls"),
    (29, .la .x5 "wlh_indexed_calls"),
    (32, .la .x5 "wlh_indexed_hits"),
    (35, .la .x5 "wlh_indexed_misses"),
    (38, .la .x5 "wlh_linear_calls"),
    (41, .la .x5 "wlh_linear_hits"),
    (44, .la .x5 "wlh_linear_misses"),
    (47, .la .x5 "wlh_linear_iterations"),
    (50, .la .x5 "wlh_linear_last_section_len"),
    (53, .la .x5 "wlh_linear_max_section_len"),
    (64, .la .x6 "widx_build_count"),
    (88, .jal .x1 "widx_record_ptr"),
    (93, .jal .x1 "zkvm_keccak256"),
    (106, .jal .x1 "widx_sift_down"),
    (113, .jal .x1 "widx_record_ptr"),
    (116, .jal .x1 "widx_record_ptr"),
    (120, .jal .x1 "widx_swap_records"),
    (123, .jal .x1 "widx_sift_down"),
    (125, .la .x5 "widx_section_ptr"),
    (128, .la .x5 "widx_section_len"),
    (131, .la .x5 "widx_count"),
    (135, .la .x5 "widx_enabled"),
    (141, .la .x5 "widx_build_status") ]

def witnessIndexBuildFunction : String :=
  "witness_index_build:\n" ++ emitProgramR witnessIndexBuild_prog witnessIndexBuild_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessIndexBuild_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessIndexBuildFunction_eq_prog :
    witnessIndexBuildFunction = "witness_index_build:\n" ++ emitProgramR witnessIndexBuild_prog witnessIndexBuild_relocs := rfl

#guard witnessIndexBuildFunction.startsWith "witness_index_build:\n"
#guard witnessIndexBuild_prog.length = 158
/-- `witness_lookup_by_hash_indexed(...)`: binary search of the sorted index
    built by `witness_index_build`. -/
def witnessLookupByHashIndexed_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.widx_count (GuestAddrs.witness_lookup_by_hash_indexed + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_count (GuestAddrs.witness_lookup_by_hash_indexed + 52)),
    .LD .x20 .x5 (0 : BitVec 12),
    .BGEU .x19 .x20 (brOff (GuestAddrs.witness_lookup_by_hash_indexed + 156) (GuestAddrs.witness_lookup_by_hash_indexed + 64)),
    .ADD .x21 .x19 .x20,
    .SRLI .x21 .x21 (1 : BitVec 6),
    .MV .x10 .x21,
    .JAL .x1 (jalOff GuestAddrs.widx_record_ptr (GuestAddrs.witness_lookup_by_hash_indexed + 80)),
    .MV .x22 .x10,
    .MV .x10 .x22,
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.widx_cmp32 (GuestAddrs.witness_lookup_by_hash_indexed + 96)),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (28 : BitVec 13),
    .LI .x5 (0 : Word),
    .BEQ .x10 .x5 (12 : BitVec 13),
    .MV .x20 .x21,
    .JAL .x0 (-56 : BitVec 21),
    .ADDI .x19 .x21 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.witness_lookup_by_hash_indexed + 64) (GuestAddrs.witness_lookup_by_hash_indexed + 128)),
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

/-- Reloc side-table for `witnessLookupByHashIndexed_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessLookupByHashIndexed_relocs : RelocTable :=
  [ (13, .la .x5 "widx_count"),
    (20, .jal .x1 "widx_record_ptr"),
    (24, .jal .x1 "widx_cmp32") ]

def witnessLookupByHashIndexedFunction : String :=
  "witness_lookup_by_hash_indexed:\n" ++ emitProgramR witnessLookupByHashIndexed_prog witnessLookupByHashIndexed_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessLookupByHashIndexed_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessLookupByHashIndexedFunction_eq_prog :
    witnessLookupByHashIndexedFunction = "witness_lookup_by_hash_indexed:\n" ++ emitProgramR witnessLookupByHashIndexed_prog witnessLookupByHashIndexed_relocs := rfl

#guard witnessLookupByHashIndexedFunction.startsWith "witness_lookup_by_hash_indexed:\n"
#guard witnessLookupByHashIndexed_prog.length = 50
/-- Private data/bss labels backing the witness index: the metadata words in
    `.data` and the six-MiB record arena in `.bss`. -/
def witnessIndexDataSection : String :=
  ".pushsection .data\n" ++
  ".balign 8\n" ++
  "widx_enabled:\n  .zero 8\n" ++
  "widx_section_ptr:\n  .zero 8\n" ++
  "widx_section_len:\n  .zero 8\n" ++
  "widx_count:\n  .zero 8\n" ++
  "widx_build_status:\n  .zero 8\n" ++
  "widx_build_section_len:\n  .zero 8\n" ++
  "widx_build_count:\n  .zero 8\n" ++
  "wlh_lookup_calls:\n  .zero 8\n" ++
  "wlh_indexed_calls:\n  .zero 8\n" ++
  "wlh_indexed_hits:\n  .zero 8\n" ++
  "wlh_indexed_misses:\n  .zero 8\n" ++
  "wlh_linear_calls:\n  .zero 8\n" ++
  "wlh_linear_hits:\n  .zero 8\n" ++
  "wlh_linear_misses:\n  .zero 8\n" ++
  "wlh_linear_iterations:\n  .zero 8\n" ++
  "wlh_linear_last_section_len:\n  .zero 8\n" ++
  "wlh_linear_max_section_len:\n  .zero 8\n" ++
  ".popsection\n" ++
  -- The index arena is runtime-built scratch, not initialized data.  Keep the
  -- metadata above in `.data`, but place the six-MiB record arena in NOBITS so
  -- it does not occupy the linked image's PROGBITS payload.
  ".section .bss, \"aw\", @nobits\n" ++
  ".balign 8\n" ++
  "widx_records:\n  .zero " ++ toString mptWitnessIndexArenaBytes ++ "\n" ++
  ".section .text"

/-- Sorted full-hash witness index helpers plus their private data labels.
    `witness_index_build(section_ptr, section_len)` computes one keccak per SSZ
    list entry, stores `(hash, offset, len)` records, and heapsorts them by the
    full 32-byte hash. `witness_lookup_by_hash_indexed` then does binary search.
    Capacity is `mptWitnessIndexCapacity`; larger sections fail conservatively
    at build.

    ⚠️ Separator discipline. Each routine def above ends with its own
    `"  ret\n"`, so the members are joined by a bare `"\n"` (the blank line
    between routines) and the leading `"\n"` opens the cluster the same way the
    single pre-split literal did. The data section follows the final `ret`
    with NO blank line. When a member is converted to `emitProgramR` it stops
    ending in a newline, and its trailing `"\n"` must move into the joiner here;
    the `#guard`s below pin every seam so that move cannot be silent. -/
def witnessIndexFunctions : String :=
  "\n" ++ widxRecordPtrFunction ++ "\n" ++
  "\n" ++ widxCmp32Function ++ "\n" ++
  "\n" ++ widxSwapRecordsFunction ++ "\n" ++
  "\n" ++ widxSiftDownFunction ++ "\n" ++
  "\n" ++ witnessIndexBuildFunction ++ "\n" ++
  "\n" ++ witnessLookupByHashIndexedFunction ++ "\n" ++
  witnessIndexDataSection

-- Seam pins, one per member boundary. `= 2` is `splitOn`'s encoding of "occurs
-- exactly once". Each pattern spans the join, so dropping or doubling a
-- separator on either side fails the guard.
#guard witnessIndexFunctions.startsWith "\nwidx_record_ptr:\n"
#guard (witnessIndexFunctions.splitOn "  jalr x0, 0(x1)\n\nwidx_cmp32:\n").length = 2
#guard (witnessIndexFunctions.splitOn "  li x10, 2\n  jalr x0, 0(x1)\n\nwidx_swap_records:\n").length = 2
#guard (witnessIndexFunctions.splitOn "  addi x11, x11, 8\n  addi x31, x31, -1\n  jal x0, .-32\n  jalr x0, 0(x1)\n\nwidx_sift_down:\n").length = 2
#guard (witnessIndexFunctions.splitOn "  ld x22, 56(x2)\n  addi x2, x2, 64\n  jalr x0, 0(x1)\n\nwitness_index_build:\n").length = 2
#guard (witnessIndexFunctions.splitOn "  ld x25, 80(x2)\n  addi x2, x2, 96\n  jalr x0, 0(x1)\n\nwitness_lookup_by_hash_indexed:\n").length = 2
-- The data section abuts the final `ret` with no blank line.
#guard (witnessIndexFunctions.splitOn "  ld x22, 56(x2)\n  addi x2, x2, 64\n  jalr x0, 0(x1)\n.pushsection .data\n").length = 2

end EvmAsm.Codegen
