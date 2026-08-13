/-
  EvmAsm.Codegen.Programs.WitnessStorageNodeKindDistribution

  Storage-side mirror of #7207
  (`witness_state_node_kind_distribution`). Iterates the
  witness.storage SSZ list section, classifies each entry
  via K22 mpt_node_kind, and returns per-kind counts in a
  32-byte buffer.

  Function body is structurally identical to the state-side
  primitive (both operate over SSZ List[Bytes] sections of
  MPT nodes). Distinct primitive exists for the same
  reasons as #7260: separate ELF, separate fixtures, and
  intent-revealing name at call sites.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_storage_node_kind_distribution

    Iterate every element of a witness.storage SSZ list
    section, call K22 mpt_node_kind on each, and accumulate
    counts of {branch, extension, leaf, parse_fail} into a
    32-byte output buffer (4 × u64 LE).

    Storage-side mirror of #7207. Useful storage-specific
    sanity checks:
      * A "single populated slot" storage trie has exactly
        ONE leaf and zero branches/extensions. Counts that
        deviate are bugged.
      * A populated multi-slot trie of N slots has
        leaf_count ≥ N (each leaf node carries the slot
        value) -- though some leaves may be embedded in
        branches' value slot, in which case the witness
        wouldn't list them separately.
      * A section dominated by parse_fail entries is
        broken.

    Output layout (32 bytes):
      bytes  0.. 8 : count_branch    (K22 = 0)
      bytes  8..16 : count_extension (K22 = 1)
      bytes 16..24 : count_leaf      (K22 = 2)
      bytes 24..32 : count_parse_fail (K22 = 3)

    Calling convention (3 args):
      a0 (input)  : witness.storage ptr
      a1 (input)  : witness.storage len
      a2 (input)  : output buffer ptr (32 bytes)
      ra (input)  : return

      a0 (output) : 0 (always; K22 parse failures counted
                    into slot 3, not propagated)
-/
/-! Probe-only local PC placeholder. -/
def witnessStorageNodeKindDistributionPc : Nat := 0x80000000

def witnessStorageNodeKindDistribution_prog : Program :=
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
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .BEQ .x9 .x0 (brOff (witnessStorageNodeKindDistributionPc + 176) (witnessStorageNodeKindDistributionPc + 64)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x19 .x5 (2 : BitVec 6),
    .LI .x20 (0 : Word),
    .BEQ .x20 .x19 (brOff (witnessStorageNodeKindDistributionPc + 176) (witnessStorageNodeKindDistributionPc + 80)),
    .SLLI .x5 .x20 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .ADD .x21 .x8 .x7,
    .ADDI .x28 .x20 (1 : BitVec 12),
    .BEQ .x28 .x19 (24 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .ADD .x29 .x8 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x29 .x8 .x9,
    .SUB .x22 .x29 .x21,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.mpt_node_kind (witnessStorageNodeKindDistributionPc + 144)),
    .SLLI .x5 .x10 (3 : BitVec 6),
    .ADD .x6 .x18 .x5,
    .LD .x7 .x6 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .SD .x6 .x7 (0 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (witnessStorageNodeKindDistributionPc + 80) (witnessStorageNodeKindDistributionPc + 172)),
    .LI .x10 (0 : Word),
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

/-- Reloc side-table for `witnessStorageNodeKindDistribution_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessStorageNodeKindDistribution_relocs : RelocTable :=
  [ (36, .jal .x1 "mpt_node_kind") ]

def witnessStorageNodeKindDistributionFunction : String :=
  "witness_storage_node_kind_distribution:\n" ++ emitProgramR witnessStorageNodeKindDistribution_prog witnessStorageNodeKindDistribution_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessStorageNodeKindDistribution_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessStorageNodeKindDistributionFunction_eq_prog :
    witnessStorageNodeKindDistributionFunction = "witness_storage_node_kind_distribution:\n" ++ emitProgramR witnessStorageNodeKindDistribution_prog witnessStorageNodeKindDistribution_relocs := rfl

#guard witnessStorageNodeKindDistributionFunction.startsWith "witness_storage_node_kind_distribution:\n"
#guard witnessStorageNodeKindDistribution_prog.length = 55
/-- `zisk_witness_storage_node_kind_distribution`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_storage_len (u64 LE)
      bytes 16..   : witness.storage section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : count_branch
      bytes 16..24 : count_extension
      bytes 24..32 : count_leaf
      bytes 32..40 : count_parse_fail -/
def ziskWitnessStorageNodeKindDistributionPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_storage_len\n" ++
  "  addi a0, a6, 16             # witness.storage ptr\n" ++
  "  li a2, 0xa0010008           # out buffer ptr (32 B)\n" ++
  "  jal ra, witness_storage_node_kind_distribution\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lwznd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  witnessStorageNodeKindDistributionFunction ++ "\n" ++
  ".Lwznd_pdone:"

def ziskWitnessStorageNodeKindDistributionDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
