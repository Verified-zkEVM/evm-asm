/-
  EvmAsm.Codegen.Programs.WitnessHeadersFindIndexByBlockHash

  Pure search primitive: given a block_hash and
  witness.headers, return the index i such that
  keccak256(witness.headers[i]) == block_hash, or signal
  not-found.

  Hash -> index inverse of #7304 (which is index -> hash).
  Useful building block for hash-keyed flows that need to
  know the position (e.g. for downstream chain-link checks
  against neighbouring indices).

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.MptWitnessLookup
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_headers_find_index_by_block_hash

    Resolve the header through `witness_lookup_by_hash`, then translate the
    returned SSZ element offset back to its list index. If the caller has built
    a `witness.headers` index with `witness_index_build`, the hash resolution is
    binary-search based and this helper only walks the offset table.

    On miss, sets index to 0 and returns status 1; caller
    distinguishes via status, not via the written index
    (so the output buffer's contents on miss aren't
    semantically meaningful).

    Inverse of #7304: that returns hash for a given index;
    this returns index for a given hash.

    Use cases:
      * Translate a hash-keyed query into an index-keyed
        downstream call (e.g. caller has block_hash, wants
        to chain into #7283 / #7296 which take indices).
      * Detect whether a claimed block_hash is in the
        witness chain without doing the full account walk
        of #7307.
      * Audit: find which position in the chain the trusted
        anchor block sits at.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 index out ptr
      ra (input)  : return

      a0 (output) :
        0 = found (index written)
        1 = block_hash not in witness.headers
-/
/-! Probe-only local PC placeholder. -/
def witnessHeadersFindIndexByBlockHashPc : Nat := 0x80000000

def witnessHeadersFindIndexByBlockHash_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
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
    .SD .x2 .x0 (64 : BitVec 12),
    .SD .x2 .x0 (72 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .MV .x12 .x8,
    .ADDI .x13 .x2 (64 : BitVec 12),
    .ADDI .x14 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash (witnessHeadersFindIndexByBlockHashPc + 84)),
    .BNE .x10 .x0 (brOff (witnessHeadersFindIndexByBlockHashPc + 172) (witnessHeadersFindIndexByBlockHashPc + 88)),
    .LD .x20 .x2 (64 : BitVec 12),
    .LI .x5 (4 : Word),
    .BLTU .x18 .x5 (brOff (witnessHeadersFindIndexByBlockHashPc + 172) (witnessHeadersFindIndexByBlockHashPc + 100)),
    .LWU .x5 .x9 (0 : BitVec 12),
    .ANDI .x6 .x5 (3 : BitVec 12),
    .BNE .x6 .x0 (60 : BitVec 13),
    .BLTU .x18 .x5 (56 : BitVec 13),
    .SRLI .x21 .x5 (2 : BitVec 6),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x21 (44 : BitVec 13),
    .SLLI .x5 .x22 (2 : BitVec 6),
    .ADD .x6 .x9 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .BLTU .x18 .x7 (28 : BitVec 13),
    .BEQ .x7 .x20 (12 : BitVec 13),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .SD .x19 .x22 (0 : BitVec 12),
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
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `witnessHeadersFindIndexByBlockHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessHeadersFindIndexByBlockHash_relocs : RelocTable :=
  [ (21, .jal .x1 "witness_lookup_by_hash") ]

def witnessHeadersFindIndexByBlockHashFunction : String :=
  "witness_headers_find_index_by_block_hash:\n" ++ emitProgramR witnessHeadersFindIndexByBlockHash_prog witnessHeadersFindIndexByBlockHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessHeadersFindIndexByBlockHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessHeadersFindIndexByBlockHashFunction_eq_prog :
    witnessHeadersFindIndexByBlockHashFunction = "witness_headers_find_index_by_block_hash:\n" ++ emitProgramR witnessHeadersFindIndexByBlockHash_prog witnessHeadersFindIndexByBlockHash_relocs := rfl

#guard witnessHeadersFindIndexByBlockHashFunction.startsWith "witness_headers_find_index_by_block_hash:\n"
#guard witnessHeadersFindIndexByBlockHash_prog.length = 54
/-- `zisk_witness_headers_find_index_by_block_hash`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : block_hash (32 bytes)
      bytes 48..   : witness.headers section bytes
    The probe pre-builds the `witness.headers` index before calling the helper.
    Output layout (64 bytes):
      bytes  0.. 8 : status (0 = found, 1 = miss)
      bytes  8..16 : index (u64; 0 on miss)
      bytes 16..24 : index build status
      bytes 24..32 : witness_lookup_by_hash call count
      bytes 32..40 : indexed lookup call count
      bytes 40..48 : linear lookup call count
      bytes 48..56 : linear lookup iteration count
      bytes 56..64 : index build entry count -/
def ziskWitnessHeadersFindIndexByBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  addi a0, a6, 16             # block_hash ptr\n" ++
  "  addi a1, a6, 48             # witness.headers ptr\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, witness_index_build\n" ++
  "  li t0, 0xa0010010\n" ++
  "  sd a0, 0(t0)                # index build status\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  li a3, 0xa0010008           # index out\n" ++
  "  jal ra, witness_headers_find_index_by_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, wlh_lookup_calls; ld t2, 0(t1); sd t2, 24(t0)\n" ++
  "  la t1, wlh_indexed_calls; ld t2, 0(t1); sd t2, 32(t0)\n" ++
  "  la t1, wlh_linear_calls; ld t2, 0(t1); sd t2, 40(t0)\n" ++
  "  la t1, wlh_linear_iterations; ld t2, 0(t1); sd t2, 48(t0)\n" ++
  "  la t1, widx_build_count; ld t2, 0(t1); sd t2, 56(t0)\n" ++
  "  j .Lwhfi_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessHeadersFindIndexByBlockHashFunction ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  ".Lwhfi_pdone:"

def ziskWitnessHeadersFindIndexByBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32"

def ziskWitnessHeadersFindIndexByBlockHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessHeadersFindIndexByBlockHashPrologue
  dataAsm     := ziskWitnessHeadersFindIndexByBlockHashDataSection
}

end EvmAsm.Codegen
