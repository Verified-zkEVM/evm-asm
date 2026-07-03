/-
  EvmAsm.Codegen.Programs.BalAllAccountsNonstorageCovers

  `bal_all_accounts_nonstorage_covers` (bead i3djw / bmvmx.1.6.4.4 step .3b) — the
  REVERSE-completeness half of the all-accounts non-storage exec-vs-BAL check, the
  companion of bal_all_accounts_nonstorage_consistent (#8588, step .3a, forward) and
  the non-storage analog of bal_storage_covers_exec_log (#8569).

  Where .3a iterates BAL accounts and checks each declared final is reproduced by exec,
  .3b iterates the execution-derived non-storage effect array and checks that every
  account exec NET-CHANGED (post != pre, for balance or nonce) is PRESENT in the
  block_access_list — catching the soundness-critical case of an account exec changed
  but ENTIRELY ABSENT from the BAL (a producer hiding a balance/nonce movement).

  Effect record (112 B, 8-byte aligned), keyed by 20-byte big-endian address:
    +0 address (20B→32) | +32 pre_balance (32B BE) | +64 post_balance (32B BE)
    | +96 pre_nonce (u64) | +104 post_nonce (u64)

  The top-level recipient is SKIPPED (its balance/nonce are checked on the gas/balance
  path — claude-c1's sender/recipient balance compare), as in .3a / #8576. An effect
  with no net change (pre == post) imposes no obligation. A net-changed non-recipient
  effect that matches no BAL account returns 1 (conservative reject). This verifies only
  PRESENCE; the matched account's finals are verified by .3a. Code is out of scope until
  CREATE/SELFDESTRUCT exec.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.NonstorageEffectLog

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_all_accounts_nonstorage_covers
    a0 = BAL section RLP ptr (list of AccountChanges)   a1 = BAL section RLP length
    a2 = exec non-storage effect array base             a3 = effect record count
    a4 = skip-list ptr (array of 32-byte-padded 20-byte addresses to SKIP — the
         gas/value-coupled accounts {sender, recipient, coinbase}, checked on the gas path)
    a5 = skip-list count
    a0 (output) = 0 every net-changed effect is present in the BAL / 1 reject. -/
def balAllAccountsNonstorageCovers_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
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
    .MV .x26 .x15,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_all_accounts_nonstorage_covers + 84)),
    .BNE .x12 .x0 (428 : BitVec 13),
    .MV .x21 .x10,
    .MV .x24 .x11,
    .AUIPC .x5 (laHi GuestAddrs.c3cov_covered (GuestAddrs.bal_all_accounts_nonstorage_covers + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.c3cov_covered (GuestAddrs.bal_all_accounts_nonstorage_covers + 100)),
    .LI .x6 (0 : Word),
    .BEQ .x6 .x19 (20 : BitVec 13),
    .ADD .x7 .x5 .x6,
    .SB .x7 .x0 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .BEQ .x21 .x24 (188 : BitVec 13),
    .MV .x10 .x21,
    .MV .x11 .x24,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_all_accounts_nonstorage_covers + 144)),
    .BNE .x11 .x0 (368 : BitVec 13),
    .MV .x21 .x10,
    .SUB .x25 .x10 .x12,
    .MV .x22 .x12,
    .MV .x10 .x25,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_all_accounts_nonstorage_covers + 172)),
    .BNE .x12 .x0 (340 : BitVec 13),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_all_accounts_nonstorage_covers + 180)),
    .BNE .x11 .x0 (332 : BitVec 13),
    .LI .x7 (20 : Word),
    .BNE .x12 .x7 (124 : BitVec 13),
    .SUB .x23 .x10 .x12,
    .LI .x29 (0 : Word),
    .MV .x13 .x19,
    .BGEU .x29 .x13 (108 : BitVec 13),
    .ADD .x14 .x29 .x13,
    .SRLI .x14 .x14 (1 : BitVec 6),
    .SLLI .x30 .x14 (7 : BitVec 6),
    .SLLI .x31 .x14 (4 : BitVec 6),
    .SUB .x30 .x30 .x31,
    .ADD .x30 .x18 .x30,
    .LI .x16 (0 : Word),
    .LI .x17 (20 : Word),
    .BEQ .x16 .x17 (52 : BitVec 13),
    .ADD .x10 .x30 .x16,
    .LBU .x11 .x10 (0 : BitVec 12),
    .ADD .x10 .x23 .x16,
    .LBU .x12 .x10 (0 : BitVec 12),
    .BLTU .x11 .x12 (16 : BitVec 13),
    .BLTU .x12 .x11 (20 : BitVec 13),
    .ADDI .x16 .x16 (1 : BitVec 12),
    .JAL .x0 (-36 : BitVec 21),
    .ADDI .x29 .x14 (1 : BitVec 12),
    .JAL .x0 (-76 : BitVec 21),
    .MV .x13 .x14,
    .JAL .x0 (-84 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.c3cov_covered (GuestAddrs.bal_all_accounts_nonstorage_covers + 296)),
    .ADDI .x5 .x5 (laLo GuestAddrs.c3cov_covered (GuestAddrs.bal_all_accounts_nonstorage_covers + 296)),
    .ADD .x5 .x5 .x14,
    .LI .x6 (1 : Word),
    .SB .x5 .x6 (0 : BitVec 12),
    .JAL .x0 (-184 : BitVec 21),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x19 (184 : BitVec 13),
    .SLLI .x5 .x22 (7 : BitVec 6),
    .SLLI .x6 .x22 (4 : BitVec 6),
    .SUB .x5 .x5 .x6,
    .ADD .x23 .x18 .x5,
    .ADDI .x7 .x23 (32 : BitVec 12),
    .ADDI .x28 .x23 (64 : BitVec 12),
    .LD .x29 .x7 (0 : BitVec 12),
    .LD .x30 .x28 (0 : BitVec 12),
    .BNE .x29 .x30 (56 : BitVec 13),
    .LD .x29 .x7 (8 : BitVec 12),
    .LD .x30 .x28 (8 : BitVec 12),
    .BNE .x29 .x30 (44 : BitVec 13),
    .LD .x29 .x7 (16 : BitVec 12),
    .LD .x30 .x28 (16 : BitVec 12),
    .BNE .x29 .x30 (32 : BitVec 13),
    .LD .x29 .x7 (24 : BitVec 12),
    .LD .x30 .x28 (24 : BitVec 12),
    .BNE .x29 .x30 (20 : BitVec 13),
    .LD .x29 .x23 (96 : BitVec 12),
    .LD .x30 .x23 (104 : BitVec 12),
    .BNE .x29 .x30 (8 : BitVec 13),
    .JAL .x0 (88 : BitVec 21),
    .LI .x29 (0 : Word),
    .BEQ .x29 .x26 (60 : BitVec 13),
    .SLLI .x30 .x29 (5 : BitVec 6),
    .ADD .x30 .x20 .x30,
    .LI .x31 (0 : Word),
    .LI .x10 (20 : Word),
    .BEQ .x31 .x10 (60 : BitVec 13),
    .ADD .x10 .x23 .x31,
    .LBU .x11 .x10 (0 : BitVec 12),
    .ADD .x10 .x30 .x31,
    .LBU .x12 .x10 (0 : BitVec 12),
    .BNE .x11 .x12 (12 : BitVec 13),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (-56 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.c3cov_covered (GuestAddrs.bal_all_accounts_nonstorage_covers + 480)),
    .ADDI .x5 .x5 (laLo GuestAddrs.c3cov_covered (GuestAddrs.bal_all_accounts_nonstorage_covers + 480)),
    .ADD .x5 .x5 .x22,
    .LBU .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-180 : BitVec 21),
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
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAllAccountsNonstorageCovers_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAllAccountsNonstorageCovers_relocs : RelocTable :=
  [ (21, .jal .x1 "rlp_walk_init"),
    (25, .la .x5 "c3cov_covered"),
    (36, .jal .x1 "rlp_walk_next"),
    (43, .jal .x1 "rlp_walk_init"),
    (45, .jal .x1 "rlp_walk_next"),
    (74, .la .x5 "c3cov_covered"),
    (120, .la .x5 "c3cov_covered") ]

def balAllAccountsNonstorageCoversFunction : String :=
  "bal_all_accounts_nonstorage_covers:\n" ++ emitProgramR balAllAccountsNonstorageCovers_prog balAllAccountsNonstorageCovers_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAllAccountsNonstorageCovers_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAllAccountsNonstorageCoversFunction_eq_prog :
    balAllAccountsNonstorageCoversFunction = "bal_all_accounts_nonstorage_covers:\n" ++ emitProgramR balAllAccountsNonstorageCovers_prog balAllAccountsNonstorageCovers_relocs := rfl

#guard balAllAccountsNonstorageCoversFunction.startsWith "bal_all_accounts_nonstorage_covers:\n"
#guard balAllAccountsNonstorageCovers_prog.length = 144
/-- `zisk_bal_all_accounts_nonstorage_covers`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL section length
      bytes 16..24 : exec effect record count
      bytes 24..32 : skip-list count
      bytes 32..    : skip-list (count * 32B), then effect array (count * 112B), then the BAL section
    Output: bytes 0..8 = status (0 covered / 1 reject). -/
def ziskBalAllAccountsNonstorageCoversPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # BAL section len\n" ++
  "  ld a3, 16(t6)               # effect record count\n" ++
  "  ld a5, 24(t6)               # skip-list count\n" ++
  "  addi a4, t6, 32             # skip-list base (0x40000020, 8-aligned)\n" ++
  "  slli t0, a5, 5; add a2, a4, t0           # effect base = skip_base + skip_count*32\n" ++
  "  slli t0, a3, 7; slli t1, a3, 4; sub t0, t0, t1   # effect_count * 112\n" ++
  "  add a0, a2, t0              # BAL section ptr = effect_base + 112*count\n" ++
  "  jal ra, bal_all_accounts_nonstorage_covers\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lc3cov_pdone\n" ++
  balAllAccountsNonstorageCoversFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lc3cov_pdone:"

def ziskBalAllAccountsNonstorageCoversDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  -- bmvmx.5.5.7.3 step c: per-agg-entry "covered by some BAL account" bitmap (1 byte/entry),
  -- indexed by agg index, so it MUST be at least nonstorageEffectLogCap bytes.
  "c3cov_covered:\n  .zero " ++ toString nonstorageEffectLogCap ++ "\n"

def ziskBalAllAccountsNonstorageCoversProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsNonstorageCoversPrologue
  dataAsm     := ziskBalAllAccountsNonstorageCoversDataSection
}

end EvmAsm.Codegen
