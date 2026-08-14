/-
  EvmAsm.Codegen.Programs.WitnessStorageKeccakAtIndex

  Storage-side mirror of #7215
  (`witness_state_keccak_at_index`). Index-based keccak256
  reader over the `witness.storage` SSZ list section.

  The function body is structurally identical to the state-
  side primitive -- both operate over arbitrary `List[Bytes]`
  SSZ sections. The distinct primitive exists to give callers
  a name that matches the section they're auditing, and to
  document use cases specific to storage.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_storage_keccak_at_index

    Read the i-th entry of a witness.storage SSZ list
    section and return its keccak256 hash in a 32-byte
    output buffer.

    Storage-side mirror of #7215. The function body is the
    same as the state-side primitive; this primitive exists
    as a distinct labelled entry point so callers naming
    their flows by section don't have to context-switch
    between "this primitive works on state OR storage".

    Use cases:
      * Storage-witness audit fixtures: "what's the keccak
        of the 3rd storage node?"
      * Manual storage-trie walk: caller traversing branch
        children by index materialises each node's hash.
      * Producer-claim verification on the storage side:
        verify a producer-provided list of N expected
        storage node hashes against the witness.

    Calling convention (4 args):
      a0 (input)  : witness.storage ptr
      a1 (input)  : witness.storage len
      a2 (input)  : index (u64)
      a3 (input)  : 32-byte out buffer ptr
      ra (input)  : return

      a0 (output) : 0 = ok / 1 = index OOB
-/
/-! Probe-only local PC placeholder. -/
def witnessStorageKeccakAtIndexPc : Nat := 0x80000000

def witnessStorageKeccakAtIndex_prog : Program :=
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
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (8 : BitVec 12),
    .SD .x19 .x0 (16 : BitVec 12),
    .SD .x19 .x0 (24 : BitVec 12),
    .BEQ .x9 .x0 (brOff (witnessStorageKeccakAtIndexPc + 144) (witnessStorageKeccakAtIndexPc + 60)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x20 .x5 (2 : BitVec 6),
    .BGEU .x18 .x20 (brOff (witnessStorageKeccakAtIndexPc + 144) (witnessStorageKeccakAtIndexPc + 72)),
    .SLLI .x5 .x18 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .ADD .x10 .x8 .x7,
    .ADDI .x28 .x18 (1 : BitVec 12),
    .BEQ .x28 .x20 (24 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .ADD .x29 .x8 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x29 .x8 .x9,
    .SUB .x11 .x29 .x10,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (witnessStorageKeccakAtIndexPc + 132)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `witnessStorageKeccakAtIndex_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessStorageKeccakAtIndex_relocs : RelocTable :=
  [ (33, .jal .x1 "zkvm_keccak256") ]

def witnessStorageKeccakAtIndexFunction : String :=
  "witness_storage_keccak_at_index:\n" ++ emitProgramR witnessStorageKeccakAtIndex_prog witnessStorageKeccakAtIndex_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessStorageKeccakAtIndex_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessStorageKeccakAtIndexFunction_eq_prog :
    witnessStorageKeccakAtIndexFunction = "witness_storage_keccak_at_index:\n" ++ emitProgramR witnessStorageKeccakAtIndex_prog witnessStorageKeccakAtIndex_relocs := rfl

#guard witnessStorageKeccakAtIndexFunction.startsWith "witness_storage_keccak_at_index:\n"
#guard witnessStorageKeccakAtIndex_prog.length = 45
/-- `zisk_witness_storage_keccak_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_storage_len (u64 LE)
      bytes 16..24 : index (u64 LE)
      bytes 24..   : witness.storage section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0=ok, 1=OOB)
      bytes  8..40 : keccak256 hash (zero on OOB) -/
def ziskWitnessStorageKeccakAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_storage_len\n" ++
  "  ld a2, 16(a6)               # index\n" ++
  "  addi a0, a6, 24             # witness.storage ptr\n" ++
  "  li a3, 0xa0010008           # out buf (32 B)\n" ++
  "  jal ra, witness_storage_keccak_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwzki_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessStorageKeccakAtIndexFunction ++ "\n" ++
  ".Lwzki_pdone:"

def ziskWitnessStorageKeccakAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200"


end EvmAsm.Codegen
