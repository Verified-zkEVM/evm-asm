/-
  EvmAsm.Codegen.Programs.WitnessNodeKindDistribution

  Witness auditing primitive: classify every entry in a
  witness.state SSZ list section using K22 `mpt_node_kind`,
  and return the per-kind counts. Distinct from the
  inclusion-proof family -- this doesn't hash anything,
  doesn't walk, doesn't compare. Just structural shape audit.

  Useful as a fail-fast malformed-witness detector before
  spending cycles on a full state walk.

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

/-! ## witness_state_node_kind_distribution

    Iterate every element of a witness.state SSZ list section,
    call K22 `mpt_node_kind` on each, and accumulate counts
    of {branch, extension, leaf, parse_fail} into a 32-byte
    output buffer (4 × u64 LE).

    Useful for:
      * Detecting malformed witnesses where the section is
        nonempty but contains zero parsable MPT nodes (often
        a sign of incorrect serialisation or wrong-section
        confusion -- e.g. a code section pasted in as state).
      * Pre-flight sanity checks: a multi-account state trie
        of depth d must contain at least one branch node
        (unless N=1 in which case a single leaf suffices).
      * Auditing witness bloat: a section dominated by
        parse_fail entries is broken; one dominated by leaves
        relative to branches may indicate a high fan-out
        without proper branch packing.

    Does NOT walk any links between nodes. Does NOT compute
    keccak hashes. Pure entry-wise classification.

    Calling convention (3 args):
      a0 (input)  : witness.state ptr
      a1 (input)  : witness.state len
      a2 (input)  : output buffer ptr (32 bytes)
      ra (input)  : return

      a0 (output) : 0 = success (always; K22 parse failures
                    are counted into slot 3, not propagated)

    Output buffer layout (32 bytes):
      bytes  0.. 8 : count_branch    (K22 return = 0)
      bytes  8..16 : count_extension (K22 return = 1)
      bytes 16..24 : count_leaf      (K22 return = 2)
      bytes 24..32 : count_parse_fail (K22 return = 3)

    Note: K22 distinguishes nodes via item-2 probe + HP-nibble
    inspection, NOT by absolute structural correctness. A
    section entry that has the right RLP shape but invalid
    semantic content (e.g. branch with wrong child-hash sizes)
    will still be classified as branch -- the validity
    surfaces during the actual walk.
-/
/-! Probe-only local PC placeholder. -/
def witnessStateNodeKindDistributionPc : Nat := 0x80000000

def witnessStateNodeKindDistribution_prog : Program :=
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
    .BEQ .x9 .x0 (brOff (witnessStateNodeKindDistributionPc + 176) (witnessStateNodeKindDistributionPc + 64)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x19 .x5 (2 : BitVec 6),
    .LI .x20 (0 : Word),
    .BEQ .x20 .x19 (brOff (witnessStateNodeKindDistributionPc + 176) (witnessStateNodeKindDistributionPc + 80)),
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
    .JAL .x1 (jalOff GuestAddrs.mpt_node_kind (witnessStateNodeKindDistributionPc + 144)),
    .SLLI .x5 .x10 (3 : BitVec 6),
    .ADD .x6 .x18 .x5,
    .LD .x7 .x6 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .SD .x6 .x7 (0 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (witnessStateNodeKindDistributionPc + 80) (witnessStateNodeKindDistributionPc + 172)),
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

/-- Reloc side-table for `witnessStateNodeKindDistribution_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessStateNodeKindDistribution_relocs : RelocTable :=
  [ (36, .jal .x1 "mpt_node_kind") ]

def witnessStateNodeKindDistributionFunction : String :=
  "witness_state_node_kind_distribution:\n" ++ emitProgramR witnessStateNodeKindDistribution_prog witnessStateNodeKindDistribution_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessStateNodeKindDistribution_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessStateNodeKindDistributionFunction_eq_prog :
    witnessStateNodeKindDistributionFunction = "witness_state_node_kind_distribution:\n" ++ emitProgramR witnessStateNodeKindDistribution_prog witnessStateNodeKindDistribution_relocs := rfl

#guard witnessStateNodeKindDistributionFunction.startsWith "witness_state_node_kind_distribution:\n"
/-- `zisk_witness_state_node_kind_distribution`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..   : witness.state section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : count_branch
      bytes 16..24 : count_extension
      bytes 24..32 : count_leaf
      bytes 32..40 : count_parse_fail -/
def ziskWitnessStateNodeKindDistributionPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # witness.state ptr\n" ++
  "  li a2, 0xa0010008           # out buffer ptr (32 B)\n" ++
  "  jal ra, witness_state_node_kind_distribution\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lwsnd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  witnessStateNodeKindDistributionFunction ++ "\n" ++
  ".Lwsnd_pdone:"

def ziskWitnessStateNodeKindDistributionDataSection : String :=
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
