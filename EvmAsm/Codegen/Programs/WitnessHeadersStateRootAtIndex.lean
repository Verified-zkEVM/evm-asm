/-
  EvmAsm.Codegen.Programs.WitnessHeadersStateRootAtIndex

  Index-based state_root extractor over witness.headers.
  Given (witness.headers, index), find the i-th header RLP
  and extract its state_root field (RLP item 3) into a
  32-byte output buffer.

  Useful for multi-block trust chains: caller has the
  witness.headers section (which holds parent header RLPs
  for BLOCKHASH support) and wants to extract the state_root
  of a specific past block to use for state-trie
  verification.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_headers_state_root_at_index

    Locate the i-th header RLP in a witness.headers SSZ
    list section and write its state_root field (RLP item 3,
    32 bytes) to the caller's output buffer.

    Composes SSZ inner-offset traversal + K201
    `header_extract_state_root`.

    Use cases:
      * Multi-block trust chain extension: caller has
        verified the chain link `keccak(witness.headers[i])
        == witness.headers[i+1].parent_hash` via #7222, and
        now wants the state_root of header i for state-trie
        verification against witness.state[i].
      * Light-client historical state queries: pull
        state_root_n from witness.headers[k] to verify an
        account / slot proof against block n's state.
      * Per-block state-root audit: chain N calls to extract
        all state_roots across a witness.headers run.

    Calling convention (4 args):
      a0 (input)  : witness.headers ptr
      a1 (input)  : witness.headers len
      a2 (input)  : index (u64)
      a3 (input)  : 32-byte state_root out buffer ptr
      ra (input)  : return

      a0 (output) :
        0 = success (state_root written)
        1 = index out of bounds (buffer zeroed)
        2 = header at index could not be RLP-decoded
        3 = state_root field has unexpected size
-/
/-! Probe-only local PC placeholder. -/
def witnessHeadersStateRootAtIndexPc : Nat := 0x80000000

def witnessHeadersStateRootAtIndex_prog : Program :=
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
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (8 : BitVec 12),
    .SD .x19 .x0 (16 : BitVec 12),
    .SD .x19 .x0 (24 : BitVec 12),
    .BEQ .x9 .x0 (brOff (witnessHeadersStateRootAtIndexPc + 164) (witnessHeadersStateRootAtIndexPc + 68)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x20 .x5 (2 : BitVec 6),
    .BGEU .x18 .x20 (brOff (witnessHeadersStateRootAtIndexPc + 164) (witnessHeadersStateRootAtIndexPc + 80)),
    .SLLI .x5 .x18 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .ADD .x21 .x8 .x7,
    .ADDI .x28 .x18 (1 : BitVec 12),
    .BEQ .x28 .x20 (24 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .ADD .x29 .x8 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x29 .x8 .x9,
    .SUB .x22 .x29 .x21,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (witnessHeadersStateRootAtIndexPc + 148)),
    .BEQ .x10 .x0 (16 : BitVec 13),
    .ADDI .x10 .x10 (1 : BitVec 12),
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

/-- Reloc side-table for `witnessHeadersStateRootAtIndex_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessHeadersStateRootAtIndex_relocs : RelocTable :=
  [ (37, .jal .x1 "header_extract_state_root") ]

def witnessHeadersStateRootAtIndexFunction : String :=
  "witness_headers_state_root_at_index:\n" ++ emitProgramR witnessHeadersStateRootAtIndex_prog witnessHeadersStateRootAtIndex_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessHeadersStateRootAtIndex_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessHeadersStateRootAtIndexFunction_eq_prog :
    witnessHeadersStateRootAtIndexFunction = "witness_headers_state_root_at_index:\n" ++ emitProgramR witnessHeadersStateRootAtIndex_prog witnessHeadersStateRootAtIndex_relocs := rfl

#guard witnessHeadersStateRootAtIndexFunction.startsWith "witness_headers_state_root_at_index:\n"
/-- `zisk_witness_headers_state_root_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : index (u64 LE)
      bytes 24..   : witness.headers section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status
      bytes  8..40 : state_root (32 B; zero on early-out) -/
def ziskWitnessHeadersStateRootAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_headers_len\n" ++
  "  ld a2, 16(a6)               # index\n" ++
  "  addi a0, a6, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # state_root out (32 B)\n" ++
  "  jal ra, witness_headers_state_root_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhsr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  witnessHeadersStateRootAtIndexFunction ++ "\n" ++
  ".Lwhsr_pdone:"

def ziskWitnessHeadersStateRootAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
