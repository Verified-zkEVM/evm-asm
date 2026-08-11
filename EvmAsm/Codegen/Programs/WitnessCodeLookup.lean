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
    preimage probes through this helper without invalidating state lookups. -/
def witnessCodesLookupByHashFunction : String :=
  (((witnessLookupByHashFunction.replace
      "witness_lookup_by_hash_indexed"
      "witness_codes_lookup_by_hash_indexed").replace
      "witness_lookup_by_hash"
      "witness_codes_lookup_by_hash").replace
      "witness_index_build"
      "witness_codes_index_build").replace
      "widx" "wcidx" |>.replace
      "wlh" "wclh"

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
  witnessCodesLookupByHashFunction ++ "\n" ++
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
