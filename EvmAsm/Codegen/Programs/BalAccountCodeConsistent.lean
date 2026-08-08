/-
  EvmAsm.Codegen.Programs.BalAccountCodeConsistent

  `bal_account_code_consistent` (bead i3djw / bmvmx.1.6.4.4 — the CODE field) — the
  per-account CODE exec-vs-BAL comparator, completing the non-storage field family
  alongside the retired balance/nonce comparator (#8586). It uses the
  code field LOCATED by bal_account_nonstorage_finals (#8584, step .1) and compares
  the BAL's declared deployed code bytes against an execution-derived code effect,
  forward + reverse.

  An account's code only changes via CREATE/CREATE2 (deploy) or SELFDESTRUCT (clear),
  so this is the i3djw piece gated on CREATE/SELFDESTRUCT execution: the comparator is
  built + probe-tested now, wired once that exec produces code effects.

  Execution-derived code effect record:
    +0  has_code_change (u64; 1 if exec created/destroyed this account's code)
    +8  code_len        (u64; deployed code byte length)
    +16 code bytes      (the deployed bytecode)

  EIP-7928 code_changes carries the full new_code BYTES (not a hash), and exec has the
  deployed bytes at deploy time, so this compares bytes directly (no keccak): if the
  bytes match, the state code_hash = keccak(code) matches too.

  Direction: forward (BAL declares a code change => exec changed it AND bytes match) +
  reverse (exec changed code => BAL declares it, matching bytes). Conservative: parse
  failure returns 2, any mismatch/omission returns 1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- #11118: unlinked from guest; probe-only PC placeholders. -/
def balAccountCodeConsistentPc : Nat := 0x80002000
def baccFinalsPc : Nat := 0x80003000


/-! ## bal_account_code_consistent
    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = exec code effect record ptr (layout above)
    a0 (output) = 0 consistent / 1 inconsistent / 2 BAL parse failure. -/
def balAccountCodeConsistent_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x12,
    .AUIPC .x18 (laHi baccFinalsPc (balAccountCodeConsistentPc + 28)),
    .ADDI .x18 .x18 (laLo baccFinalsPc (balAccountCodeConsistentPc + 28)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_account_nonstorage_finals (balAccountCodeConsistentPc + 40)),
    .BNE .x10 .x0 (100 : BitVec 13),
    .LD .x5 .x18 (56 : BitVec 12),
    .LD .x6 .x9 (0 : BitVec 12),
    .BNE .x6 .x0 (12 : BitVec 13),
    .BEQ .x5 .x0 (68 : BitVec 13),
    .JAL .x0 (72 : BitVec 21),
    .BEQ .x5 .x0 (68 : BitVec 13),
    .LD .x7 .x18 (72 : BitVec 12),
    .LD .x28 .x9 (8 : BitVec 12),
    .BNE .x7 .x28 (56 : BitVec 13),
    .LD .x29 .x18 (64 : BitVec 12),
    .ADD .x29 .x8 .x29,
    .ADDI .x30 .x9 (16 : BitVec 12),
    .BEQ .x7 .x0 (32 : BitVec 13),
    .LBU .x31 .x29 (0 : BitVec 12),
    .LBU .x10 .x30 (0 : BitVec 12),
    .BNE .x31 .x10 (28 : BitVec 13),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountCodeConsistent_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountCodeConsistent_relocs : RelocTable :=
  [ (7, .la .x18 "bacc_finals"),
    (10, .jal .x1 "bal_account_nonstorage_finals") ]

def balAccountCodeConsistentFunction : String :=
  "bal_account_code_consistent:\n" ++ emitProgramR balAccountCodeConsistent_prog balAccountCodeConsistent_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountCodeConsistent_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountCodeConsistentFunction_eq_prog :
    balAccountCodeConsistentFunction = "bal_account_code_consistent:\n" ++ emitProgramR balAccountCodeConsistent_prog balAccountCodeConsistent_relocs := rfl

#guard balAccountCodeConsistentFunction.startsWith "bal_account_code_consistent:\n"
#guard balAccountCodeConsistent_prog.length = 43
/-- `zisk_bal_account_code_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : AccountChanges byte length
      bytes 16..24 : exec code effect padded byte length
      bytes 24..    : exec code effect (has_code_change u64 | code_len u64 | code bytes),
                      padded to 8; then the AccountChanges RLP
    Output: bytes 0..8 = status (0 consistent / 1 inconsistent / 2 parse fail). -/
def ziskBalAccountCodeConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # AccountChanges len\n" ++
  "  ld t1, 16(a5)               # exec effect padded length\n" ++
  "  addi a2, a5, 24             # exec code effect ptr (0x40000018, 8-aligned)\n" ++
  "  add a0, a2, t1              # AccountChanges ptr = effect ptr + padded effect length\n" ++
  "  jal ra, bal_account_code_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbacc_pdone\n" ++
  balAccountCodeConsistentFunction ++ "\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lbacc_pdone:"

def ziskBalAccountCodeConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bacc_finals:\n  .zero 88\n" ++
  ziskBalAccountNonstorageFinalsDataSection  -- finals helper scratch

def ziskBalAccountCodeConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountCodeConsistentPrologue
  dataAsm     := ziskBalAccountCodeConsistentDataSection
}

end EvmAsm.Codegen
