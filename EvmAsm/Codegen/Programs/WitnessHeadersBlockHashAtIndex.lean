/-
  EvmAsm.Codegen.Programs.WitnessHeadersBlockHashAtIndex

  Index-based block-hash extractor over witness.headers.
  Given the section and an index i, computes
  keccak256(witness.headers[i]) and returns it.

  The function body is structurally identical to #7215 /
  #7260 (state/storage versions). What's distinct is the
  SEMANTIC: each entry in witness.headers is a full RLP-
  encoded block header, and its keccak IS the canonical
  block hash. This primitive exists as a named entry point
  for callers asking "what's the block hash of the i-th
  historical header in the witness chain?"

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

/-! ## witness_headers_block_hash_at_index

    Locate the i-th header RLP in a witness.headers SSZ
    list section and return its keccak256 (= canonical
    block hash).

    Use cases:
      * Verify caller-supplied block hash against the i-th
        witness header: extract here, then compare.
      * Manual chain walk: caller maintains the
        (current_block_hash, walk_index) pair and uses
        this primitive to materialise each historical
        block hash by index.
      * Light-client header-chain audit: extract block
        hashes for a UI display, dispute resolution, or
        signature checks against an off-chain log.

    Distinct from #7215 (state) / #7260 (storage) in
    SEMANTIC -- those audit MPT node hashes, this one
    yields the EVM-spec block hash.

    Distinct from #7222: that takes two separate header
    RLPs and checks the chain link; this primitive just
    returns the hash of a single header.

    Calling convention (4 args):
      a0 (input)  : witness.headers ptr
      a1 (input)  : witness.headers len
      a2 (input)  : index (u64)
      a3 (input)  : 32-byte block_hash out buffer ptr
      ra (input)  : return

      a0 (output) : 0 = ok / 1 = index OOB (buffer zeroed)
-/
/-! Probe-only local PC placeholder. -/
def witnessHeadersBlockHashAtIndexPc : Nat := 0x80000000

def witnessHeadersBlockHashAtIndex_prog : Program :=
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
    .BEQ .x9 .x0 (brOff (witnessHeadersBlockHashAtIndexPc + 144) (witnessHeadersBlockHashAtIndexPc + 60)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x20 .x5 (2 : BitVec 6),
    .BGEU .x18 .x20 (brOff (witnessHeadersBlockHashAtIndexPc + 144) (witnessHeadersBlockHashAtIndexPc + 72)),
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
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (witnessHeadersBlockHashAtIndexPc + 132)),
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

/-- Reloc side-table for `witnessHeadersBlockHashAtIndex_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessHeadersBlockHashAtIndex_relocs : RelocTable :=
  [ (33, .jal .x1 "zkvm_keccak256") ]

def witnessHeadersBlockHashAtIndexFunction : String :=
  "witness_headers_block_hash_at_index:\n" ++ emitProgramR witnessHeadersBlockHashAtIndex_prog witnessHeadersBlockHashAtIndex_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessHeadersBlockHashAtIndex_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessHeadersBlockHashAtIndexFunction_eq_prog :
    witnessHeadersBlockHashAtIndexFunction = "witness_headers_block_hash_at_index:\n" ++ emitProgramR witnessHeadersBlockHashAtIndex_prog witnessHeadersBlockHashAtIndex_relocs := rfl

#guard witnessHeadersBlockHashAtIndexFunction.startsWith "witness_headers_block_hash_at_index:\n"
#guard witnessHeadersBlockHashAtIndex_prog.length = 45
/-- `zisk_witness_headers_block_hash_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : index (u64 LE)
      bytes 24..   : witness.headers section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0 = ok, 1 = OOB)
      bytes  8..40 : block_hash (32 B; zero on OOB) -/
def ziskWitnessHeadersBlockHashAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_headers_len\n" ++
  "  ld a2, 16(a6)               # index\n" ++
  "  addi a0, a6, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # out buf (32 B)\n" ++
  "  jal ra, witness_headers_block_hash_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessHeadersBlockHashAtIndexFunction ++ "\n" ++
  ".Lwhbh_pdone:"

def ziskWitnessHeadersBlockHashAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200"


end EvmAsm.Codegen
