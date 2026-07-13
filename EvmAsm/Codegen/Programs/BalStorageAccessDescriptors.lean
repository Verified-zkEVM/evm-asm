/-
  EvmAsm.Codegen.Programs.BalStorageAccessDescriptors

  Convert committed runtime storage-access outcome records for one account into
  read-only storage-trie descriptors. The descriptor shape matches
  `mpt_state_root_ins`: path_ptr, path_len, value_ptr, value_len, mode.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Mpt

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_storage_access_outcome_descriptors

    a0 = storage outcome table ptr      a1 = outcome count
    a2 = committed window table ptr     a3 = committed window count
    a4 = account token ptr (32 bytes)   a5 = descriptors out ptr
    a6 = path arena out ptr             a7 = out_count ptr
    a0 output = 0 ok / 1 malformed

    Storage outcome rows use the runtime access record layout:
      +0  account token[32]
      +32 storage slot[32]
      +64 status: 0 warm, 1 cold, 2 out-of-gas, 3 warmth-table full
      +72 gas delta, ignored here
      +80/+88 reserved

    Window rows follow `storage_effect_records` shape:
      +0 execution status (1 = success, 0 = reverted/failed)
      +8 committed outcome start index
      +16 committed outcome count
      +24 reserved

    Only successful windows and status 0/1 storage reads are materialized.
    Repeated reads of the same account/slot are compacted to the first
    descriptor. Paths are storage-trie paths: nibbles(keccak256(slot)). -/
def balStorageAccessOutcomeDescriptors_prog : Program :=
  [ .ADDI .x2 .x2 (-128 : BitVec 12),
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
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x23 .x17,
    .SD .x23 .x0 (0 : BitVec 12),
    .LI .x24 (0 : Word),
    .LI .x25 (0 : Word),
    .BEQ .x24 .x19 (328 : BitVec 13),
    .SLLI .x5 .x24 (5 : BitVec 6),
    .ADD .x26 .x18 .x5,
    .LD .x6 .x26 (0 : BitVec 12),
    .BEQ .x6 .x0 (304 : BitVec 13),
    .LI .x7 (1 : Word),
    .BNE .x6 .x7 (312 : BitVec 13),
    .LD .x28 .x26 (8 : BitVec 12),
    .LD .x29 .x26 (16 : BitVec 12),
    .ADD .x30 .x28 .x29,
    .BLTU .x30 .x28 (296 : BitVec 13),
    .BLTU .x9 .x30 (292 : BitVec 13),
    .SD .x2 .x30 (104 : BitVec 12),
    .MV .x27 .x28,
    .LD .x30 .x2 (104 : BitVec 12),
    .BEQ .x27 .x30 (260 : BitVec 13),
    .SLLI .x5 .x27 (6 : BitVec 6),
    .SLLI .x6 .x27 (5 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .ADD .x26 .x8 .x5,
    .LD .x6 .x26 (64 : BitVec 12),
    .LI .x7 (1 : Word),
    .BLTU .x7 .x6 (224 : BitVec 13),
    .MV .x5 .x26,
    .MV .x6 .x20,
    .LI .x7 (0 : Word),
    .LI .x28 (32 : Word),
    .BEQ .x7 .x28 (32 : BitVec 13),
    .ADD .x29 .x5 .x7,
    .ADD .x31 .x6 .x7,
    .LBU .x29 .x29 (0 : BitVec 12),
    .LBU .x31 .x31 (0 : BitVec 12),
    .BNE .x29 .x31 (184 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .ADDI .x10 .x26 (32 : BitVec 12),
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.bsaod_hash (GuestAddrs.bal_storage_access_outcome_descriptors + 248)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bsaod_hash (GuestAddrs.bal_storage_access_outcome_descriptors + 248)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.bal_storage_access_outcome_descriptors + 256)),
    .AUIPC .x10 (laHi GuestAddrs.bsaod_hash (GuestAddrs.bal_storage_access_outcome_descriptors + 260)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bsaod_hash (GuestAddrs.bal_storage_access_outcome_descriptors + 260)),
    .LI .x11 (32 : Word),
    .MV .x12 .x22,
    .JAL .x1 (jalOff GuestAddrs.bytes_to_nibbles (GuestAddrs.bal_storage_access_outcome_descriptors + 276)),
    .LI .x5 (0 : Word),
    .BEQ .x5 .x25 (64 : BitVec 13),
    .SUB .x6 .x25 .x5,
    .SLLI .x6 .x6 (6 : BitVec 6),
    .SUB .x7 .x22 .x6,
    .LI .x28 (0 : Word),
    .LI .x29 (64 : Word),
    .BEQ .x28 .x29 (104 : BitVec 13),
    .ADD .x30 .x7 .x28,
    .ADD .x31 .x22 .x28,
    .LBU .x30 .x30 (0 : BitVec 12),
    .LBU .x31 .x31 (0 : BitVec 12),
    .BNE .x30 .x31 (12 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .SLLI .x5 .x25 (5 : BitVec 6),
    .SLLI .x6 .x25 (3 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .ADD .x5 .x21 .x5,
    .SD .x5 .x22 (0 : BitVec 12),
    .LI .x6 (64 : Word),
    .SD .x5 .x6 (8 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bsaod_empty_value (GuestAddrs.bal_storage_access_outcome_descriptors + 376)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bsaod_empty_value (GuestAddrs.bal_storage_access_outcome_descriptors + 376)),
    .SD .x5 .x6 (16 : BitVec 12),
    .SD .x5 .x0 (24 : BitVec 12),
    .LI .x6 (3 : Word),
    .SD .x5 .x6 (32 : BitVec 12),
    .ADDI .x22 .x22 (64 : BitVec 12),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .SD .x23 .x25 (0 : BitVec 12),
    .ADDI .x27 .x27 (1 : BitVec 12),
    .JAL .x0 (-260 : BitVec 21),
    .ADDI .x24 .x24 (1 : BitVec 12),
    .JAL .x0 (-324 : BitVec 21),
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
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (128 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balStorageAccessOutcomeDescriptors_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balStorageAccessOutcomeDescriptors_relocs : RelocTable :=
  [ (62, .la .x12 "bsaod_hash"),
    (64, .jal .x1 "zkvm_keccak256"),
    (65, .la .x10 "bsaod_hash"),
    (69, .jal .x1 "bytes_to_nibbles"),
    (94, .la .x6 "bsaod_empty_value") ]

def balStorageAccessOutcomeDescriptorsFunction : String :=
  "bal_storage_access_outcome_descriptors:\n" ++ emitProgramR balStorageAccessOutcomeDescriptors_prog balStorageAccessOutcomeDescriptors_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balStorageAccessOutcomeDescriptors_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balStorageAccessOutcomeDescriptorsFunction_eq_prog :
    balStorageAccessOutcomeDescriptorsFunction = "bal_storage_access_outcome_descriptors:\n" ++ emitProgramR balStorageAccessOutcomeDescriptors_prog balStorageAccessOutcomeDescriptors_relocs := rfl

#guard balStorageAccessOutcomeDescriptorsFunction.startsWith "bal_storage_access_outcome_descriptors:\n"
#guard balStorageAccessOutcomeDescriptors_prog.length = 125
/-- `zisk_bal_storage_access_outcome_descriptors`: synthetic probe.
    Output:
      +0  status
      +8  descriptor count
      +16 descriptors
      +96 path arena for the two emitted rows. -/
def ziskBalStorageAccessOutcomeDescriptorsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, bsaod_probe_outcomes\n" ++
  "  li a1, 5\n" ++
  "  la a2, bsaod_probe_windows\n" ++
  "  li a3, 2\n" ++
  "  la a4, bsaod_probe_account\n" ++
  "  li a5, 0xa0010010\n" ++
  "  li a6, 0xa0010060\n" ++
  "  li a7, 0xa0010008\n" ++
  "  jal ra, bal_storage_access_outcome_descriptors\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbsaod_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  balStorageAccessOutcomeDescriptorsFunction ++ "\n" ++
  ".Lbsaod_pdone:"

def ziskBalStorageAccessOutcomeDescriptorsDataSection : String :=
  ziskMptWalkDataSection ++ "\n" ++
  ".balign 32\n" ++
  "bsaod_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bsaod_empty_value:\n  .zero 1\n" ++
  ".balign 32\n" ++
  "bsaod_probe_account:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "bsaod_probe_windows:\n" ++
  "  .quad 1,0,4,0              # committed rows 0..3\n" ++
  "  .quad 0,4,1,0              # reverted row 4, skipped\n" ++
  ".balign 64\n" ++
  "bsaod_probe_outcomes:\n" ++
  "  # cold slot A for the selected account\n" ++
  "  .zero 32\n" ++
  "  .rept 32\n  .byte 0x11\n  .endr\n" ++
  "  .quad 1,2000,0,0\n" ++
  "  # duplicate warm slot A, skipped\n" ++
  "  .zero 32\n" ++
  "  .rept 32\n  .byte 0x11\n  .endr\n" ++
  "  .quad 0,0,0,0\n" ++
  "  # other account slot, skipped by account token\n" ++
  "  .rept 32\n  .byte 0xcc\n  .endr\n" ++
  "  .rept 32\n  .byte 0x33\n  .endr\n" ++
  "  .quad 1,2000,0,0\n" ++
  "  # cold slot B for the selected account\n" ++
  "  .zero 32\n" ++
  "  .rept 32\n  .byte 0x22\n  .endr\n" ++
  "  .quad 1,2000,0,0\n" ++
  "  # reverted slot C for selected account, skipped by failed window\n" ++
  "  .zero 32\n" ++
  "  .rept 32\n  .byte 0x44\n  .endr\n" ++
  "  .quad 1,2000,0,0\n"

def ziskBalStorageAccessOutcomeDescriptorsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalStorageAccessOutcomeDescriptorsPrologue
  dataAsm     := ziskBalStorageAccessOutcomeDescriptorsDataSection
}

end EvmAsm.Codegen
