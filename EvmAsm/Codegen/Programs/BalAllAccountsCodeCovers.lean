/-
  EvmAsm.Codegen.Programs.BalAllAccountsCodeCovers

  `bal_all_accounts_code_covers` (bead i3djw / bmvmx.1.6.4.4 — the all-accounts CODE
  reverse wrapper) — the reverse-completeness companion of the forward code wrapper
  bal_all_accounts_code_consistent (#8600), analogous to .3b vs .3a for balance/nonce.

  Where the forward wrapper iterates BAL accounts and checks each declared code change
  is reproduced by exec, this iterates the execution-derived code-effect array and checks
  that every account exec changed code for (CREATE/CREATE2 deploy or SELFDESTRUCT clear,
  `has_code_change=1`) is PRESENT in the block_access_list — catching a producer that
  hides a created/destroyed contract by omitting its account from the BAL.

  It verifies PRESENCE only: a present account's code declaration is verified by the
  forward wrapper (bal_account_code_consistent's per-account direction rejects a present
  account whose exec changed code the BAL didn't declare). So the obligation here is just
  "the account is in the BAL"; an absent account with `has_code_change=1` is a reject.

  The code-effect array is VARIABLE-STRIDE (per c2#11): one record
    +0 address (20B→32) | +32 has_code_change (u64) | +40 code_len (u64) | +48 code bytes
  with size 48 + roundup8(code_len). Records with `has_code_change=0` impose no obligation.
  No skip-list: code never changes for the gas/value accounts {sender,recipient,coinbase}.

  Conservative: any parse failure, or a `has_code_change=1` record whose address matches no
  BAL account, returns 1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- #11118: unlinked from guest; probe-only PC placeholder. -/
def balAllAccountsCodeCoversPc : Nat := 0x80000000


/-! ## bal_all_accounts_code_covers
    a0 = BAL section RLP ptr (list of AccountChanges)   a1 = BAL section RLP length
    a2 = exec code-effect array base (variable-stride)   a3 = record count
    a0 (output) = 0 every changed code-effect's account is present in the BAL / 1 reject. -/
def balAllAccountsCodeCovers_prog : Program :=
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
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x21 .x18,
    .LI .x22 (0 : Word),
    .BEQ .x22 .x19 (172 : BitVec 13),
    .LD .x5 .x21 (32 : BitVec 12),
    .BEQ .x5 .x0 (136 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balAllAccountsCodeCoversPc + 88)),
    .BNE .x12 .x0 (156 : BitVec 13),
    .MV .x23 .x10,
    .MV .x24 .x11,
    .BEQ .x23 .x24 (144 : BitVec 13),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balAllAccountsCodeCoversPc + 116)),
    .BNE .x11 .x0 (128 : BitVec 13),
    .MV .x23 .x10,
    .SUB .x7 .x10 .x12,
    .MV .x10 .x7,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balAllAccountsCodeCoversPc + 140)),
    .BNE .x12 .x0 (104 : BitVec 13),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balAllAccountsCodeCoversPc + 148)),
    .BNE .x11 .x0 (96 : BitVec 13),
    .LI .x7 (20 : Word),
    .BNE .x12 .x7 (48 : BitVec 13),
    .SUB .x7 .x10 .x12,
    .LI .x28 (0 : Word),
    .LI .x29 (20 : Word),
    .BEQ .x28 .x29 (36 : BitVec 13),
    .ADD .x29 .x21 .x28,
    .LBU .x30 .x29 (0 : BitVec 12),
    .ADD .x29 .x7 .x28,
    .LBU .x31 .x29 (0 : BitVec 12),
    .BNE .x30 .x31 (12 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .JAL .x0 (-104 : BitVec 21),
    .LD .x5 .x21 (40 : BitVec 12),
    .ADDI .x5 .x5 (7 : BitVec 12),
    .ANDI .x5 .x5 (-8 : BitVec 12),
    .ADDI .x5 .x5 (48 : BitVec 12),
    .ADD .x21 .x21 .x5,
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-168 : BitVec 21),
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
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAllAccountsCodeCovers_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAllAccountsCodeCovers_relocs : RelocTable :=
  [ (22, .jal .x1 "rlp_walk_init"),
    (29, .jal .x1 "rlp_walk_next"),
    (35, .jal .x1 "rlp_walk_init"),
    (37, .jal .x1 "rlp_walk_next") ]

def balAllAccountsCodeCoversFunction : String :=
  "bal_all_accounts_code_covers:\n" ++ emitProgramR balAllAccountsCodeCovers_prog balAllAccountsCodeCovers_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAllAccountsCodeCovers_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAllAccountsCodeCoversFunction_eq_prog :
    balAllAccountsCodeCoversFunction = "bal_all_accounts_code_covers:\n" ++ emitProgramR balAllAccountsCodeCovers_prog balAllAccountsCodeCovers_relocs := rfl

#guard balAllAccountsCodeCoversFunction.startsWith "bal_all_accounts_code_covers:\n"
/-- `zisk_bal_all_accounts_code_covers`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL section length
      bytes 16..24 : code-effect record count
      bytes 24..32 : code-effect array total byte length
      bytes 32..    : code-effect array (variable-stride), then the BAL section
    Output: bytes 0..8 = status (0 covered / 1 reject). -/
def ziskBalAllAccountsCodeCoversPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # BAL section len\n" ++
  "  ld a3, 16(t6)               # code-effect record count\n" ++
  "  ld t0, 24(t6)               # code-effect array total byte length\n" ++
  "  addi a2, t6, 32             # code-effect array base (0x40000020, 8-aligned)\n" ++
  "  add a0, a2, t0              # BAL section ptr = effect base + effect total length\n" ++
  "  jal ra, bal_all_accounts_code_covers\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbacov_pdone\n" ++
  balAllAccountsCodeCoversFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lbacov_pdone:"

/-- Scratch cells for `bal_all_accounts_code_covers` (currently empty; kept as a
    reusable hook for the probe and verdict data sections). -/
def balAllAccountsCodeCoversData : String :=
  ""

def ziskBalAllAccountsCodeCoversDataSection : String :=
  ".section .data\n" ++
  balAllAccountsCodeCoversData


end EvmAsm.Codegen
