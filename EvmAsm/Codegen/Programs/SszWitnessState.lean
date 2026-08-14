/-
  EvmAsm.Codegen.Programs.SszWitnessState

  extract_witness_state_section (bead evm-asm-fhsxz.2.4.2.2): locate the
  `ExecutionWitness.state` section within an `SszStatelessInput`. This is the
  `List[ByteList]` of RLP MPT nodes that `witness_lookup_by_hash` /
  `withdrawals_state_root` scan — the witness argument the Step-2 verdict
  recompute needs, extracted from the real guest input.

  Navigation (mirrors the existing decode_validation_bit, Decode/Program.lean):
    witness   = SSZ_BASE + outer.offsets[1]          (u32 @ SSZ_BASE+4)
    state_off = witness.inner.offsets[0]             (u32 @ witness+0)
    codes_off = witness.inner.offsets[1]             (u32 @ witness+4)
    state_ptr = witness + state_off
    state_len = codes_off - state_off
  The SSZ blob base is byte-unaligned in the real guest input, so every u32
  offset is read byte-wise (LBU + shift) — the existing decode uses LWU at an
  unaligned address, which would trap under the verified no-misaligned RV64
  semantics; this avoids that.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## sws_u32le -- read a little-endian u32 byte-wise (alignment-safe).
    a0 = ptr; returns the u32 value in a0. Leaf (uses t0/t1). -/
def swsU32le_prog : Program :=
  [ .LBU .x5 .x10 (0 : BitVec 12),
    .LBU .x6 .x10 (1 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (2 : BitVec 12),
    .SLLI .x6 .x6 (16 : BitVec 6),
    .OR .x5 .x5 .x6,
    .LBU .x6 .x10 (3 : BitVec 12),
    .SLLI .x6 .x6 (24 : BitVec 6),
    .OR .x5 .x5 .x6,
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def swsU32leFunction : String :=
  "sws_u32le:\n" ++ emitProgram swsU32le_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `swsU32le_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem swsU32leFunction_eq_prog :
    swsU32leFunction = "sws_u32le:\n" ++ emitProgram swsU32le_prog := rfl

#guard swsU32leFunction.startsWith "sws_u32le:\n"
#guard swsU32le_prog.length = 12
/-- `extract_witness_state_section`.
    a0 = SSZ_BASE ptr (start of the SszStatelessInput SSZ blob)
    a1 = out: state section absolute ptr (u64)
    a2 = out: state section length (u64)
    a0 (output) = 0. -/
def extractWitnessStateSection_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .ADDI .x10 .x8 (4 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.sws_u32le (GuestAddrs.extract_witness_state_section + 36)),
    .ADD .x8 .x8 .x10,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.sws_u32le (GuestAddrs.extract_witness_state_section + 48)),
    .MV .x29 .x10,
    .ADDI .x10 .x8 (4 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.sws_u32le (GuestAddrs.extract_witness_state_section + 60)),
    .SUB .x30 .x10 .x29,
    .ADD .x31 .x8 .x29,
    .SD .x9 .x31 (0 : BitVec 12),
    .SD .x18 .x30 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `extractWitnessStateSection_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def extractWitnessStateSection_relocs : RelocTable :=
  [ (9, .jal .x1 "sws_u32le"),
    (12, .jal .x1 "sws_u32le"),
    (15, .jal .x1 "sws_u32le") ]

def extractWitnessStateSectionFunction : String :=
  "extract_witness_state_section:\n" ++ emitProgramR extractWitnessStateSection_prog extractWitnessStateSection_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `extractWitnessStateSection_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem extractWitnessStateSectionFunction_eq_prog :
    extractWitnessStateSectionFunction = "extract_witness_state_section:\n" ++ emitProgramR extractWitnessStateSection_prog extractWitnessStateSection_relocs := rfl

#guard extractWitnessStateSectionFunction.startsWith "extract_witness_state_section:\n"
#guard extractWitnessStateSection_prog.length = 27
/-- `zisk_extract_witness_state_section`: probe. The input file (mapped to
    INPUT+8) is the SszStatelessInput SSZ blob directly (SSZ_BASE = INPUT+8 for
    the probe; in the real guest SSZ_BASE = INPUT+18 — same navigation, different
    base). Output: OUTPUT+0 = state_off (state_ptr - witness, informational via
    state_ptr - SSZ... actually state_ptr absolute), OUTPUT+0 = state_ptr,
    OUTPUT+8 = state_len, OUTPUT+16 = keccak256(state section). -/
def ziskExtractWitnessStateSectionPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000008           # SSZ_BASE = input start (probe)\n" ++
  "  la a1, sws_state_ptr\n" ++
  "  la a2, sws_state_len\n" ++
  "  jal ra, extract_witness_state_section\n" ++
  "  # OUTPUT+0 = state offset from SSZ_BASE; OUTPUT+8 = state_len;\n" ++
  "  # OUTPUT+16 = keccak256(state section).\n" ++
  "  la t0, sws_state_ptr; ld t1, 0(t0)   # state_ptr (absolute)\n" ++
  "  li t2, 0x40000008; sub t3, t1, t2    # state offset from SSZ_BASE\n" ++
  "  li t4, 0xa0010000; sd t3, 0(t4)\n" ++
  "  la t0, sws_state_len; ld t5, 0(t0)\n" ++
  "  li t4, 0xa0010008; sd t5, 0(t4)\n" ++
  "  # keccak(state_ptr, state_len) -> OUTPUT+16\n" ++
  "  la t0, sws_state_ptr; ld a0, 0(t0)\n" ++
  "  la t0, sws_state_len; ld a1, 0(t0)\n" ++
  "  li a2, 0xa0010010\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  j .Lsws_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  swsU32leFunction ++ "\n" ++
  extractWitnessStateSectionFunction ++ "\n" ++
  ".Lsws_pdone:"

def ziskExtractWitnessStateSectionDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "sws_state_ptr:\n  .zero 8\n" ++
  "sws_state_len:\n  .zero 8"


end EvmAsm.Codegen
