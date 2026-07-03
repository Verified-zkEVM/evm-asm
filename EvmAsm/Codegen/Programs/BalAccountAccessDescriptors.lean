/-
  EvmAsm.Codegen.Programs.BalAccountAccessDescriptors

  Convert runtime account-access outcome records into read-only account-trie
  descriptors for BAL/post-state replay. The descriptor shape matches
  `mpt_state_root_ins`: path_ptr, path_len, value_ptr, value_len, mode.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.Mpt

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_access_outcome_descriptors

    a0 = account outcome table ptr       a1 = outcome count
    a2 = state-changing account table    a3 = state-changing account count
    a4 = descriptors out ptr             a5 = path arena out ptr
    a6 = out_count ptr                   a0 output = 0 ok / 1 malformed

    Outcome rows use the runtime access record layout:
      +0  address[20] BE, padded to 32
      +32 status: 0 warm, 1 cold, 2 active precompile
      +40 gas delta, ignored here
      +48/+56 reserved

    State-changing rows are 32-byte stride, first 20 bytes canonical address.
    Duplicate outcome addresses and state-changing addresses are skipped. Rows
    that remain are emitted as mode=3 no-op account descriptors with the
    canonical empty-account RLP as value. -/
def balAccountAccessOutcomeDescriptors_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .SD .x22 .x0 (0 : BitVec 12),
    .LI .x23 (0 : Word),
    .LI .x24 (0 : Word),
    .BEQ .x23 .x9 (276 : BitVec 13),
    .SLLI .x5 .x23 (6 : BitVec 6),
    .ADD .x25 .x8 .x5,
    .LD .x6 .x25 (32 : BitVec 12),
    .LI .x7 (2 : Word),
    .BLTU .x7 .x6 (264 : BitVec 13),
    .LI .x26 (0 : Word),
    .BEQ .x26 .x19 (64 : BitVec 13),
    .SLLI .x5 .x26 (5 : BitVec 6),
    .ADD .x5 .x18 .x5,
    .MV .x6 .x25,
    .LI .x7 (0 : Word),
    .LI .x28 (20 : Word),
    .BEQ .x7 .x28 (216 : BitVec 13),
    .ADD .x29 .x5 .x7,
    .ADD .x30 .x6 .x7,
    .LBU .x29 .x29 (0 : BitVec 12),
    .LBU .x30 .x30 (0 : BitVec 12),
    .BNE .x29 .x30 (12 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .ADDI .x26 .x26 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .LI .x26 (0 : Word),
    .BEQ .x26 .x23 (64 : BitVec 13),
    .SLLI .x5 .x26 (6 : BitVec 6),
    .ADD .x5 .x8 .x5,
    .MV .x6 .x25,
    .LI .x7 (0 : Word),
    .LI .x28 (20 : Word),
    .BEQ .x7 .x28 (148 : BitVec 13),
    .ADD .x29 .x5 .x7,
    .ADD .x30 .x6 .x7,
    .LBU .x29 .x29 (0 : BitVec 12),
    .LBU .x30 .x30 (0 : BitVec 12),
    .BNE .x29 .x30 (12 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .ADDI .x26 .x26 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .MV .x10 .x25,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.baaod_hash (GuestAddrs.bal_account_access_outcome_descriptors + 260)),
    .ADDI .x12 .x12 (laLo GuestAddrs.baaod_hash (GuestAddrs.bal_account_access_outcome_descriptors + 260)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.bal_account_access_outcome_descriptors + 268)),
    .AUIPC .x10 (laHi GuestAddrs.baaod_hash (GuestAddrs.bal_account_access_outcome_descriptors + 272)),
    .ADDI .x10 .x10 (laLo GuestAddrs.baaod_hash (GuestAddrs.bal_account_access_outcome_descriptors + 272)),
    .LI .x11 (32 : Word),
    .MV .x12 .x21,
    .JAL .x1 (jalOff GuestAddrs.bytes_to_nibbles (GuestAddrs.bal_account_access_outcome_descriptors + 288)),
    .SLLI .x5 .x24 (5 : BitVec 6),
    .SLLI .x6 .x24 (3 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .ADD .x5 .x20 .x5,
    .SD .x5 .x21 (0 : BitVec 12),
    .LI .x6 (64 : Word),
    .SD .x5 .x6 (8 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.baaod_empty_account (GuestAddrs.bal_account_access_outcome_descriptors + 320)),
    .ADDI .x6 .x6 (laLo GuestAddrs.baaod_empty_account (GuestAddrs.bal_account_access_outcome_descriptors + 320)),
    .SD .x5 .x6 (16 : BitVec 12),
    .LI .x6 (70 : Word),
    .SD .x5 .x6 (24 : BitVec 12),
    .LI .x6 (3 : Word),
    .SD .x5 .x6 (32 : BitVec 12),
    .ADDI .x21 .x21 (64 : BitVec 12),
    .ADDI .x24 .x24 (1 : BitVec 12),
    .SD .x22 .x24 (0 : BitVec 12),
    .ADDI .x23 .x23 (1 : BitVec 12),
    .JAL .x0 (-272 : BitVec 21),
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
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountAccessOutcomeDescriptors_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountAccessOutcomeDescriptors_relocs : RelocTable :=
  [ (65, .la .x12 "baaod_hash"),
    (67, .jal .x1 "zkvm_keccak256"),
    (68, .la .x10 "baaod_hash"),
    (72, .jal .x1 "bytes_to_nibbles"),
    (80, .la .x6 "baaod_empty_account") ]

def balAccountAccessOutcomeDescriptorsFunction : String :=
  "bal_account_access_outcome_descriptors:\n" ++ emitProgramR balAccountAccessOutcomeDescriptors_prog balAccountAccessOutcomeDescriptors_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountAccessOutcomeDescriptors_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountAccessOutcomeDescriptorsFunction_eq_prog :
    balAccountAccessOutcomeDescriptorsFunction = "bal_account_access_outcome_descriptors:\n" ++ emitProgramR balAccountAccessOutcomeDescriptors_prog balAccountAccessOutcomeDescriptors_relocs := rfl

#guard balAccountAccessOutcomeDescriptorsFunction.startsWith "bal_account_access_outcome_descriptors:\n"
#guard balAccountAccessOutcomeDescriptors_prog.length = 109
/-- `zisk_bal_account_access_outcome_descriptors`: synthetic probe.
    Output:
      +0 status
      +8 descriptor count
      +16 descriptors
      +96 path arena for the two emitted rows. -/
def ziskBalAccountAccessOutcomeDescriptorsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, baaod_probe_outcomes\n" ++
  "  li a1, 4\n" ++
  "  la a2, baaod_probe_changed\n" ++
  "  li a3, 1\n" ++
  "  li a4, 0xa0010010\n" ++
  "  li a5, 0xa0010060\n" ++
  "  li a6, 0xa0010008\n" ++
  "  jal ra, bal_account_access_outcome_descriptors\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbaaod_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  balAccountAccessOutcomeDescriptorsFunction ++ "\n" ++
  ".Lbaaod_pdone:"

def ziskBalAccountAccessOutcomeDescriptorsDataSection : String :=
  ziskMptWalkDataSection ++ "\n" ++
  ".balign 32\n" ++
  "baaod_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baaod_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 32\n" ++
  "baaod_probe_changed:\n" ++
  "  .byte 0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb\n" ++
  "  .byte 0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb\n" ++
  "  .zero 12\n" ++
  ".balign 64\n" ++
  "baaod_probe_outcomes:\n" ++
  "  # cold account A\n" ++
  "  .byte 0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa\n" ++
  "  .byte 0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa\n" ++
  "  .zero 12\n" ++
  "  .quad 1,2500,0,0\n" ++
  "  # duplicate warm account A, skipped\n" ++
  "  .byte 0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa\n" ++
  "  .byte 0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa,0xaa\n" ++
  "  .zero 12\n" ++
  "  .quad 0,0,0,0\n" ++
  "  # account B already has a state-changing descriptor, skipped\n" ++
  "  .byte 0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb\n" ++
  "  .byte 0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb,0xbb\n" ++
  "  .zero 12\n" ++
  "  .quad 1,2500,0,0\n" ++
  "  # active precompile 0x04, emitted explicitly as read-only\n" ++
  "  .zero 19\n" ++
  "  .byte 0x04\n" ++
  "  .zero 12\n" ++
  "  .quad 2,0,0,0\n"

def ziskBalAccountAccessOutcomeDescriptorsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountAccessOutcomeDescriptorsPrologue
  dataAsm     := ziskBalAccountAccessOutcomeDescriptorsDataSection
}

end EvmAsm.Codegen
