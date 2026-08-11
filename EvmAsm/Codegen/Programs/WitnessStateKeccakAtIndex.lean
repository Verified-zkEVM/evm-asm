/-
  EvmAsm.Codegen.Programs.WitnessStateKeccakAtIndex

  Index-based keccak256 reader over a witness.state SSZ
  list section. Given the section and an index, return the
  32-byte keccak256 hash of the entry at that index.

  Counterpart to K19 `witness_lookup_by_hash` which goes the
  other direction (hash -> offset). This primitive goes
  index -> hash, useful when a caller is iterating the
  witness in order rather than dispatching by hash.

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

/-! ## witness_state_keccak_at_index

    Read the i-th entry of a witness.state SSZ list section
    (or any SSZ List[Bytes]) and return its keccak256 hash
    in a 32-byte output buffer.

    Why this exists alongside K19:
      * K19 (`witness_lookup_by_hash`) is hash -> entry: you
        already have the target hash and want to find which
        entry it is.
      * THIS primitive is index -> hash: you want to walk
        the witness in order (e.g. for auditing or for
        verifying a producer's claimed entry-hash list).

    Use cases:
      * Test/fixture introspection: "what's keccak of the
        3rd entry in this witness?"
      * Manual MPT-walk: caller maintains the (cursor_hash,
        path_remaining) walk state and uses this primitive
        to materialise the next node hash from the index
        they already have.
      * Producer-claim verification: the caller has a list
        of N expected entry hashes (from off-chain
        bookkeeping) and wants to verify them in order.

    Calling convention (4 args):
      a0 (input)  : witness.state ptr
      a1 (input)  : witness.state len
      a2 (input)  : index (u64)
      a3 (input)  : 32-byte out buffer ptr
      ra (input)  : return

      a0 (output) :
        0 = success (32 bytes of keccak hash written)
        1 = index out of bounds (or empty section)
        (no other failure modes; SSZ structural problems
        in the inner-offset table will silently produce
        wrong hashes but not propagate as errors --
        callers wanting validation should chain
        witness_state_node_kind_distribution first)
-/
/-! Probe-only local PC placeholder. -/
def witnessStateKeccakAtIndexPc : Nat := 0x80000000

def witnessStateKeccakAtIndex_prog : Program :=
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
    .BEQ .x9 .x0 (brOff (witnessStateKeccakAtIndexPc + 144) (witnessStateKeccakAtIndexPc + 60)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x20 .x5 (2 : BitVec 6),
    .BGEU .x18 .x20 (brOff (witnessStateKeccakAtIndexPc + 144) (witnessStateKeccakAtIndexPc + 72)),
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
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (witnessStateKeccakAtIndexPc + 132)),
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

/-- Reloc side-table for `witnessStateKeccakAtIndex_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessStateKeccakAtIndex_relocs : RelocTable :=
  [ (33, .jal .x1 "zkvm_keccak256") ]

def witnessStateKeccakAtIndexFunction : String :=
  "witness_state_keccak_at_index:\n" ++ emitProgramR witnessStateKeccakAtIndex_prog witnessStateKeccakAtIndex_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessStateKeccakAtIndex_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessStateKeccakAtIndexFunction_eq_prog :
    witnessStateKeccakAtIndexFunction = "witness_state_keccak_at_index:\n" ++ emitProgramR witnessStateKeccakAtIndex_prog witnessStateKeccakAtIndex_relocs := rfl

#guard witnessStateKeccakAtIndexFunction.startsWith "witness_state_keccak_at_index:\n"
#guard witnessStateKeccakAtIndex_prog.length = 45
/-- `zisk_witness_state_keccak_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..24 : index (u64 LE)
      bytes 24..   : witness.state section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0 = ok, 1 = OOB)
      bytes  8..40 : 32-byte keccak hash (zero on OOB) -/
def ziskWitnessStateKeccakAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_state_len\n" ++
  "  ld a2, 16(a6)               # index\n" ++
  "  addi a0, a6, 24             # witness.state ptr\n" ++
  "  li a3, 0xa0010008           # out buf ptr (32 B)\n" ++
  "  jal ra, witness_state_keccak_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lwski_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessStateKeccakAtIndexFunction ++ "\n" ++
  ".Lwski_pdone:"

def ziskWitnessStateKeccakAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskWitnessStateKeccakAtIndexProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessStateKeccakAtIndexPrologue
  dataAsm     := ziskWitnessStateKeccakAtIndexDataSection
}

end EvmAsm.Codegen
