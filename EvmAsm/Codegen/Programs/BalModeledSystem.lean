/-
  EvmAsm.Codegen.Programs.BalModeledSystem

  Classifier for BAL AccountChanges rows whose effects are already modeled by
  the verdict's explicit system-write replay.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_is_modeled_system

    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a0 (output) = 1 EIP-2935 row / 2 EIP-4788 row / 0 other row / 3 parse failure.

    The verdict already replays EIP-2935 and EIP-4788 system writes before BAL
    post-state replay, so those BAL rows can be skipped in that verdict path. -/
def balAccountIsModeledSystem_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_is_modeled_system + 16)),
    .BNE .x12 .x0 (160 : BitVec 13),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_is_modeled_system + 24)),
    .BNE .x11 .x0 (152 : BitVec 13),
    .LI .x6 (20 : Word),
    .BNE .x12 .x6 (136 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .AUIPC .x30 (laHi GuestAddrs.bams_addr_ptr (GuestAddrs.bal_account_is_modeled_system + 44)),
    .ADDI .x30 .x30 (laLo GuestAddrs.bams_addr_ptr (GuestAddrs.bal_account_is_modeled_system + 44)),
    .SD .x30 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bams_addr_2935 (GuestAddrs.bal_account_is_modeled_system + 56)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bams_addr_2935 (GuestAddrs.bal_account_is_modeled_system + 56)),
    .LI .x7 (20 : Word),
    .BEQ .x7 .x0 (88 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .BNE .x28 .x29 (20 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .AUIPC .x30 (laHi GuestAddrs.bams_addr_ptr (GuestAddrs.bal_account_is_modeled_system + 100)),
    .ADDI .x30 .x30 (laLo GuestAddrs.bams_addr_ptr (GuestAddrs.bal_account_is_modeled_system + 100)),
    .LD .x5 .x30 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bams_addr_4788 (GuestAddrs.bal_account_is_modeled_system + 112)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bams_addr_4788 (GuestAddrs.bal_account_is_modeled_system + 112)),
    .LI .x7 (20 : Word),
    .BEQ .x7 .x0 (40 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .BNE .x28 .x29 (36 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (3 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountIsModeledSystem_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountIsModeledSystem_relocs : RelocTable :=
  [ (4, .jal .x1 "rlp_walk_init"),
    (6, .jal .x1 "rlp_walk_next"),
    (11, .la .x30 "bams_addr_ptr"),
    (14, .la .x6 "bams_addr_2935"),
    (25, .la .x30 "bams_addr_ptr"),
    (28, .la .x6 "bams_addr_4788") ]

def balAccountIsModeledSystemFunction : String :=
  "bal_account_is_modeled_system:\n" ++ emitProgramR balAccountIsModeledSystem_prog balAccountIsModeledSystem_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountIsModeledSystem_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountIsModeledSystemFunction_eq_prog :
    balAccountIsModeledSystemFunction = "bal_account_is_modeled_system:\n" ++ emitProgramR balAccountIsModeledSystem_prog balAccountIsModeledSystem_relocs := rfl

#guard balAccountIsModeledSystemFunction.startsWith "bal_account_is_modeled_system:\n"
#guard balAccountIsModeledSystem_prog.length = 50
def ziskBalAccountIsModeledSystemDataSection : String :=
  ".balign 8\n" ++
  "bams_addr_ptr:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bams_addr_2935:\n" ++
  "  .byte 0x00, 0x00, 0xF9, 0x08, 0x27, 0xF1, 0xC5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7A, 0x02, 0x33, 0x5B, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35\n" ++
  ".balign 32\n" ++
  "bams_addr_4788:\n" ++
  "  .byte 0x00, 0x0F, 0x3d, 0xf6, 0xD7, 0x32, 0x80, 0x7E\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xB7, 0xB8, 0xbB, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xBe, 0xac, 0x02\n"

end EvmAsm.Codegen
