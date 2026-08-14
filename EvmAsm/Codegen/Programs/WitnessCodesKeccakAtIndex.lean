/-
  EvmAsm.Codegen.Programs.WitnessCodesKeccakAtIndex

  Fourth index -> keccak primitive, completing the
  symmetric set:
    #7215  witness_state_keccak_at_index
    #7260  witness_storage_keccak_at_index
    #7304  witness_headers_block_hash_at_index
    this   witness_codes_keccak_at_index

  Body identical to siblings; distinct named primitive for
  call-site clarity and separate ELF.

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

/-! ## witness_codes_keccak_at_index

    Read the i-th entry of a witness.codes SSZ list section
    and return its keccak256 -- the canonical
    EIP-spec code_hash of that bytecode.

    Distinct semantic from siblings:
      * #7215 / #7260: MPT node hashes
      * #7304: canonical block hash
      * THIS: canonical code_hash (== keccak of deployed
        bytecode, the same value stored in an account
        struct's code_hash field)

    Use cases:
      * Witness audit: "what's the code_hash of the i-th
        contract in witness.codes?"
      * Producer-claim verification: caller has an off-chain
        list of expected code_hashes; this primitive
        materialises the actual hashes from witness in
        order.
      * Reverse-direction lookup: caller has just retrieved
        (offset, length) via #7333 and wants to confirm the
        keccak self-consistency by index.

    Calling convention (4 args):
      a0 (input)  : witness.codes ptr
      a1 (input)  : witness.codes len
      a2 (input)  : index (u64)
      a3 (input)  : 32-byte out buffer ptr
      ra (input)  : return

      a0 (output) : 0 = ok / 1 = index OOB
-/
/-! Probe-only local PC placeholder. -/
def witnessCodesKeccakAtIndexPc : Nat := 0x80000000

def witnessCodesKeccakAtIndex_prog : Program :=
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
    .BEQ .x9 .x0 (brOff (witnessCodesKeccakAtIndexPc + 144) (witnessCodesKeccakAtIndexPc + 60)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x20 .x5 (2 : BitVec 6),
    .BGEU .x18 .x20 (brOff (witnessCodesKeccakAtIndexPc + 144) (witnessCodesKeccakAtIndexPc + 72)),
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
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (witnessCodesKeccakAtIndexPc + 132)),
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

/-- Reloc side-table for `witnessCodesKeccakAtIndex_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessCodesKeccakAtIndex_relocs : RelocTable :=
  [ (33, .jal .x1 "zkvm_keccak256") ]

def witnessCodesKeccakAtIndexFunction : String :=
  "witness_codes_keccak_at_index:\n" ++ emitProgramR witnessCodesKeccakAtIndex_prog witnessCodesKeccakAtIndex_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessCodesKeccakAtIndex_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessCodesKeccakAtIndexFunction_eq_prog :
    witnessCodesKeccakAtIndexFunction = "witness_codes_keccak_at_index:\n" ++ emitProgramR witnessCodesKeccakAtIndex_prog witnessCodesKeccakAtIndex_relocs := rfl

#guard witnessCodesKeccakAtIndexFunction.startsWith "witness_codes_keccak_at_index:\n"
#guard witnessCodesKeccakAtIndex_prog.length = 45
/-- `zisk_witness_codes_keccak_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_codes_len (u64 LE)
      bytes 16..24 : index (u64 LE)
      bytes 24..   : witness.codes section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0=ok, 1=OOB)
      bytes  8..40 : keccak256 / code_hash (32 B; zero on OOB) -/
def ziskWitnessCodesKeccakAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_codes_len\n" ++
  "  ld a2, 16(a6)               # index\n" ++
  "  addi a0, a6, 24             # witness.codes ptr\n" ++
  "  li a3, 0xa0010008           # out buf (32 B)\n" ++
  "  jal ra, witness_codes_keccak_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwcki_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessCodesKeccakAtIndexFunction ++ "\n" ++
  ".Lwcki_pdone:"

def ziskWitnessCodesKeccakAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200"


end EvmAsm.Codegen
