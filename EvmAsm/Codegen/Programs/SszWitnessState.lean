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
def extractWitnessStateSectionFunction : String :=
  "extract_witness_state_section:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # SSZ_BASE\n" ++
  "  mv s1, a1                   # out state_ptr\n" ++
  "  mv s2, a2                   # out state_len\n" ++
  "  # witness = SSZ_BASE + outer.offsets[1] (u32 @ SSZ_BASE+4)\n" ++
  "  addi a0, s0, 4\n" ++
  "  jal ra, sws_u32le\n" ++
  "  add s0, s0, a0              # s0 = witness addr (SSZ_BASE no longer needed)\n" ++
  "  # state_off = u32 @ witness+0\n" ++
  "  mv a0, s0\n" ++
  "  jal ra, sws_u32le\n" ++
  "  mv t4, a0                   # state_off (sws_u32le clobbers only t0/t1, so t4 survives)\n" ++
  "  # codes_off = u32 @ witness+4\n" ++
  "  addi a0, s0, 4\n" ++
  "  jal ra, sws_u32le           # a0 = codes_off; t4 = state_off\n" ++
  "  sub t5, a0, t4              # state_len = codes_off - state_off\n" ++
  "  add t6, s0, t4              # state_ptr = witness + state_off\n" ++
  "  sd t6, 0(s1)\n" ++
  "  sd t5, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

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

def ziskExtractWitnessStateSectionProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskExtractWitnessStateSectionPrologue
  dataAsm     := ziskExtractWitnessStateSectionDataSection
}

end EvmAsm.Codegen
