/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageConsistent

  `bal_account_nonstorage_consistent` (bead i3djw / bmvmx.1.6.4.4 step .2) — the
  per-account NON-storage exec-vs-BAL FINAL comparator, the non-storage analog of
  the storage comparators bal_storage_matches_exec_log (#8564) +
  bal_storage_covers_exec_log (#8569). It parses a BAL AccountChanges' final
  balance/nonce (via bal_account_nonstorage_finals #8584, step .1) and checks them
  against an execution-derived non-storage effect record for the same account.

  SCOPE — this verifies the per-account *block-final* values, in both directions:
    forward : if the BAL declares a final balance/nonce, it must equal the exec
              block-post value (catches a BAL declaring a WRONG final);
    reverse : if exec net-changed the field (block-post != block-pre), the BAL must
              declare it with the right final (catches a BAL OMITTING a real change).
  It deliberately does NOT reject an account whose final equals its pre-value with a
  spurious declaration (a net-zero V->...->V account is final-consistent); the per-tx
  TUPLE-SEQUENCE completeness is a separate layer (bmvmx.1.6.6, gated on the exec log
  carrying a tx index). Code changes are likewise out of scope here — they only occur
  via CREATE/SELFDESTRUCT, verified once that exec lands (i3djw create/delete steps).

  Execution-derived non-storage effect record (112 B, 8-byte aligned; the all-accounts
  wrapper .3 keys BAL accounts to these via addrHash):
    +0   addrHash      (32 B keccak(address))  -- keying for .3; unused here
    +32  pre_balance   (32 B big-endian)
    +64  post_balance  (32 B big-endian)
    +96  pre_nonce     (u64)
    +104 post_nonce    (u64)
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

/-! ## bal_account_nonstorage_consistent
    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = exec non-storage effect record ptr (112 B, layout above)
    a0 (output) = 0 consistent / 1 inconsistent / 2 BAL parse failure.

    Internally calls bal_account_nonstorage_finals into a scratch buffer, then for
    balance and nonce applies the forward+reverse FINAL checks described above. -/
def balAccountNonstorageConsistent_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x12,
    .AUIPC .x9 (laHi GuestAddrs.c2nsc_finals (GuestAddrs.bal_account_nonstorage_consistent + 20)),
    .ADDI .x9 .x9 (laLo GuestAddrs.c2nsc_finals (GuestAddrs.bal_account_nonstorage_consistent + 20)),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.bal_account_nonstorage_finals (GuestAddrs.bal_account_nonstorage_consistent + 32)),
    .BNE .x10 .x0 (192 : BitVec 13),
    .LD .x5 .x9 (0 : BitVec 12),
    .ADDI .x7 .x8 (32 : BitVec 12),
    .ADDI .x28 .x8 (64 : BitVec 12),
    .LI .x6 (0 : Word),
    .LD .x29 .x7 (0 : BitVec 12),
    .LD .x30 .x28 (0 : BitVec 12),
    .BNE .x29 .x30 (44 : BitVec 13),
    .LD .x29 .x7 (8 : BitVec 12),
    .LD .x30 .x28 (8 : BitVec 12),
    .BNE .x29 .x30 (32 : BitVec 13),
    .LD .x29 .x7 (16 : BitVec 12),
    .LD .x30 .x28 (16 : BitVec 12),
    .BNE .x29 .x30 (20 : BitVec 13),
    .LD .x29 .x7 (24 : BitVec 12),
    .LD .x30 .x28 (24 : BitVec 12),
    .BNE .x29 .x30 (8 : BitVec 13),
    .JAL .x0 (8 : BitVec 21),
    .LI .x6 (1 : Word),
    .BEQ .x6 .x0 (8 : BitVec 13),
    .BEQ .x5 .x0 (104 : BitVec 13),
    .BEQ .x5 .x0 (60 : BitVec 13),
    .ADDI .x7 .x9 (8 : BitVec 12),
    .ADDI .x28 .x8 (64 : BitVec 12),
    .LD .x29 .x7 (0 : BitVec 12),
    .LD .x30 .x28 (0 : BitVec 12),
    .BNE .x29 .x30 (80 : BitVec 13),
    .LD .x29 .x7 (8 : BitVec 12),
    .LD .x30 .x28 (8 : BitVec 12),
    .BNE .x29 .x30 (68 : BitVec 13),
    .LD .x29 .x7 (16 : BitVec 12),
    .LD .x30 .x28 (16 : BitVec 12),
    .BNE .x29 .x30 (56 : BitVec 13),
    .LD .x29 .x7 (24 : BitVec 12),
    .LD .x30 .x28 (24 : BitVec 12),
    .BNE .x29 .x30 (44 : BitVec 13),
    .LD .x5 .x9 (40 : BitVec 12),
    .LD .x7 .x8 (96 : BitVec 12),
    .LD .x28 .x8 (104 : BitVec 12),
    .BEQ .x7 .x28 (8 : BitVec 13),
    .BEQ .x5 .x0 (24 : BitVec 13),
    .BEQ .x5 .x0 (12 : BitVec 13),
    .LD .x29 .x9 (48 : BitVec 12),
    .BNE .x29 .x28 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountNonstorageConsistent_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountNonstorageConsistent_relocs : RelocTable :=
  [ (5, .la .x9 "c2nsc_finals"),
    (8, .jal .x1 "bal_account_nonstorage_finals") ]

def balAccountNonstorageConsistentFunction : String :=
  "bal_account_nonstorage_consistent:\n" ++ emitProgramR balAccountNonstorageConsistent_prog balAccountNonstorageConsistent_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountNonstorageConsistent_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountNonstorageConsistentFunction_eq_prog :
    balAccountNonstorageConsistentFunction = "bal_account_nonstorage_consistent:\n" ++ emitProgramR balAccountNonstorageConsistent_prog balAccountNonstorageConsistent_relocs := rfl

#guard balAccountNonstorageConsistentFunction.startsWith "bal_account_nonstorage_consistent:\n"
#guard balAccountNonstorageConsistent_prog.length = 63
/-- `zisk_bal_account_nonstorage_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes 8..16   : AccountChanges byte length
      bytes 16..128 : the 112-byte exec non-storage effect record (8-byte aligned)
      bytes 128..   : the AccountChanges RLP
    Output: bytes 0..8 = status (0 consistent / 1 inconsistent / 2 parse fail). -/
def ziskBalAccountNonstorageConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # AccountChanges len\n" ++
  "  addi a2, a5, 16             # exec effect record ptr (0x40000010, 8-aligned)\n" ++
  "  addi a0, a5, 128            # AccountChanges ptr (0x40000080, 8-aligned)\n" ++
  "  jal ra, bal_account_nonstorage_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lc2nsc_pdone\n" ++
  balAccountNonstorageConsistentFunction ++ "\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lc2nsc_pdone:"

def ziskBalAccountNonstorageConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "c2nsc_finals:\n  .zero 88\n" ++
  ziskBalAccountNonstorageFinalsDataSection  -- c2nsf_* + rfu_* scratch for the inlined finals helper

def ziskBalAccountNonstorageConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountNonstorageConsistentPrologue
  dataAsm     := ziskBalAccountNonstorageConsistentDataSection
}

end EvmAsm.Codegen
