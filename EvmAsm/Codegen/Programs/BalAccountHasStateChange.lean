/-
  EvmAsm.Codegen.Programs.BalAccountHasStateChange

  Cheap BAL AccountChanges classifier for post-state-root replay.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_has_state_change -- detect state-affecting BAL rows

    a0 = AccountChanges RLP ptr   a1 = AccountChanges length
    a0 (output) = 0 no post-state change / 1 has post-state change / 2 parse fail.

    AccountChanges fields:
      [address, storage_changes, storage_reads, balance_changes, nonce_changes, code_changes]
    `storage_reads` are read-only, so only fields 1, 3, 4, and 5 can affect the
    post-state root. -/
def balAccountHasStateChange_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_has_state_change + 36)),
    .BNE .x12 .x0 (128 : BitVec 13),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_has_state_change + 52)),
    .BNE .x11 .x0 (112 : BitVec 13),
    .MV .x8 .x10,
    .JAL .x1 (44 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_has_state_change + 76)),
    .BNE .x11 .x0 (88 : BitVec 13),
    .MV .x8 .x10,
    .JAL .x1 (20 : BitVec 21),
    .JAL .x1 (16 : BitVec 21),
    .JAL .x1 (12 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (68 : BitVec 21),
    .MV .x18 .x1,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_has_state_change + 120)),
    .BNE .x11 .x0 (44 : BitVec 13),
    .MV .x8 .x10,
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_has_state_change + 140)),
    .BNE .x12 .x0 (24 : BitVec 13),
    .BNE .x10 .x11 (12 : BitVec 13),
    .MV .x1 .x18,
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountHasStateChange_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountHasStateChange_relocs : RelocTable :=
  [ (9, .jal .x1 "rlp_walk_init"),
    (13, .jal .x1 "rlp_walk_next"),
    (19, .jal .x1 "rlp_walk_next"),
    (30, .jal .x1 "rlp_walk_next"),
    (35, .jal .x1 "rlp_walk_init") ]

def balAccountHasStateChangeFunction : String :=
  "bal_account_has_state_change:\n" ++ emitProgramR balAccountHasStateChange_prog balAccountHasStateChange_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountHasStateChange_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountHasStateChangeFunction_eq_prog :
    balAccountHasStateChangeFunction = "bal_account_has_state_change:\n" ++ emitProgramR balAccountHasStateChange_prog balAccountHasStateChange_relocs := rfl

#guard balAccountHasStateChangeFunction.startsWith "bal_account_has_state_change:\n"
#guard balAccountHasStateChange_prog.length = 49
def ziskBalAccountHasStateChangeDataSection : String :=
  ".balign 8\n"

end EvmAsm.Codegen
