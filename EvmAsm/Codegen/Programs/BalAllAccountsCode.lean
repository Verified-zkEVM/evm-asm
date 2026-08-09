/-
  EvmAsm.Codegen.Programs.BalAllAccountsCode

  `bal_all_accounts_code_consistent` (bead i3djw / bmvmx.1.6.4.4 — the all-accounts CODE
  forward wrapper) — runs the per-account code comparator bal_account_code_consistent
  (#8591) over every block_access_list account, completing the all-accounts non-storage
  surface (balance/nonce via #8588/#8589, code here).

  An account's code only changes via CREATE/CREATE2/SELFDESTRUCT, so each created/destroyed
  account has an execution-derived code-effect record keyed by its 20-byte big-endian
  address (per c2#5/c2#11 coordination). Because the deployed code is variable-length, the
  effect array is VARIABLE-STRIDE — one record:
    +0   address (20B BE in the low bytes, padded to 32)   <- key
    +32  has_code_change (u64)
    +40  code_len (u64)
    +48  code bytes (code_len, padded to 8 so the next record's address stays 8-aligned)
  i.e. record size = 48 + roundup8(code_len). The wrapper passes a2 = record+32 to
  bal_account_code_consistent (whose effect layout is `[has_code_change | code_len | code]`).

  DIRECTION — FORWARD: when an execution code-effect record exists for a BAL account, the
  BAL account's final code bytes must match it exactly (and `bal_account_code_consistent`'s
  own per-account reverse rejects a matched account whose exec changed code but the BAL omitted
  it). A BAL account with no execution code-effect imposes no forward obligation: EEST BALs can
  carry idempotent final-code preimages for already-existing accounts, so treating every
  `code_changes` tuple as a CREATE/SELFDESTRUCT effect false-rejects ordinary calls. The
  all-account reverse (`bal_all_accounts_code_covers`) still requires every execution-created
  code-effect account to be present in the BAL.

  EIP-7702 EXCEPTION (i3djw.4, per #8626): a set-code (EIP-7702) authorization installs the
  delegation indicator `0xef 0x01 0x00 || 20-byte address` (23 bytes) as the authority
  account's code DIRECTLY from the transaction's authorization list — not through a CREATE
  deposit — so execution emits no code-effect record for it. The forward direction would
  otherwise false-reject such a BAL code_change (declared, but no matching exec effect). So
  the no-effect reject branch first checks whether the BAL's declared new code is exactly a
  23-byte `0xef0100`-prefixed delegation indicator and, if so, SKIPS it. Any other
  code-declaring account with no exec effect is a genuine omission and still rejects.

  IMPORTANT (per c1#9/c2#11): this must only be wired once execution emits the code-effect
  records (.8b) — before that, removing CREATE from the self-contained gate (.8c) would leave
  a self-contained CREATE with no effect record, and the forward direction would false-reject.

  Conservative for actual execution code effects: parse failure or byte mismatch returns 1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.BalAccountCodeConsistent

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- #11118: unlinked from guest; probe-only PC placeholder.
    `balAccountCodeConsistentPc` lives in BalAccountCodeConsistent.lean. -/
def balAllAccountsCodeConsistentPc : Nat := 0x80000000


/-! ## bal_all_accounts_code_consistent
    a0 = BAL section RLP ptr (list of AccountChanges)   a1 = BAL section RLP length
    a2 = exec code-effect array base (variable-stride; layout above)   a3 = record count
    a0 (output) = 0 consistent / 1 reject. -/
def balAllAccountsCodeConsistent_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
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
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balAllAccountsCodeConsistentPc + 68)),
    .BNE .x12 .x0 (200 : BitVec 13),
    .MV .x20 .x10,
    .MV .x21 .x11,
    .BEQ .x20 .x21 (180 : BitVec 13),
    .MV .x10 .x20,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balAllAccountsCodeConsistentPc + 96)),
    .BNE .x11 .x0 (172 : BitVec 13),
    .MV .x20 .x10,
    .SUB .x22 .x10 .x12,
    .MV .x23 .x12,
    .MV .x10 .x22,
    .MV .x11 .x23,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balAllAccountsCodeConsistentPc + 124)),
    .BNE .x12 .x0 (144 : BitVec 13),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balAllAccountsCodeConsistentPc + 132)),
    .BNE .x11 .x0 (136 : BitVec 13),
    .LI .x7 (20 : Word),
    .BNE .x12 .x7 (116 : BitVec 13),
    .SUB .x24 .x10 .x12,
    .MV .x5 .x18,
    .LI .x6 (0 : Word),
    .BEQ .x6 .x19 (96 : BitVec 13),
    .LI .x7 (0 : Word),
    .LI .x28 (20 : Word),
    .BEQ .x7 .x28 (60 : BitVec 13),
    .ADD .x28 .x24 .x7,
    .LBU .x29 .x28 (0 : BitVec 12),
    .ADD .x28 .x5 .x7,
    .LBU .x30 .x28 (0 : BitVec 12),
    .BNE .x29 .x30 (12 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LD .x7 .x5 (40 : BitVec 12),
    .ADDI .x7 .x7 (7 : BitVec 12),
    .ANDI .x7 .x7 (-8 : BitVec 12),
    .ADDI .x7 .x7 (48 : BitVec 12),
    .ADD .x5 .x5 .x7,
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-68 : BitVec 21),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .ADDI .x12 .x5 (32 : BitVec 12),
    .JAL .x1 (jalOff balAccountCodeConsistentPc (balAllAccountsCodeConsistentPc + 244)),
    .BNE .x10 .x0 (24 : BitVec 13),
    .JAL .x0 (8 : BitVec 21),
    .JAL .x0 (4 : BitVec 21),
    .JAL .x0 (-176 : BitVec 21),
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
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAllAccountsCodeConsistent_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAllAccountsCodeConsistent_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_walk_init"),
    (24, .jal .x1 "rlp_walk_next"),
    (31, .jal .x1 "rlp_walk_init"),
    (33, .jal .x1 "rlp_walk_next"),
    (61, .jal .x1 "bal_account_code_consistent") ]

def balAllAccountsCodeConsistentFunction : String :=
  "bal_all_accounts_code_consistent:\n" ++ emitProgramR balAllAccountsCodeConsistent_prog balAllAccountsCodeConsistent_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAllAccountsCodeConsistent_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAllAccountsCodeConsistentFunction_eq_prog :
    balAllAccountsCodeConsistentFunction = "bal_all_accounts_code_consistent:\n" ++ emitProgramR balAllAccountsCodeConsistent_prog balAllAccountsCodeConsistent_relocs := rfl

#guard balAllAccountsCodeConsistentFunction.startsWith "bal_all_accounts_code_consistent:\n"
#guard balAllAccountsCodeConsistent_prog.length = 81
/-- `zisk_bal_all_accounts_code_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL section length
      bytes 16..24 : code-effect record count
      bytes 24..32 : code-effect array total byte length
      bytes 32..    : code-effect array (variable-stride), then the BAL section
    Output: bytes 0..8 = status (0 consistent / 1 reject). -/
def ziskBalAllAccountsCodeConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # BAL section len\n" ++
  "  ld a3, 16(t6)               # code-effect record count\n" ++
  "  ld t0, 24(t6)               # code-effect array total byte length\n" ++
  "  addi a2, t6, 32             # code-effect array base (0x40000020, 8-aligned)\n" ++
  "  add a0, a2, t0              # BAL section ptr = effect base + effect total length\n" ++
  "  jal ra, bal_all_accounts_code_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbaac_pdone\n" ++
  balAllAccountsCodeConsistentFunction ++ "\n" ++
  balAccountCodeConsistentFunction ++ "\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lbaac_pdone:"

def ziskBalAllAccountsCodeConsistentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  ziskBalAccountCodeConsistentDataSection  -- bacc_finals + finals helper scratch

def ziskBalAllAccountsCodeConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAllAccountsCodeConsistentPrologue
  dataAsm     := ziskBalAllAccountsCodeConsistentDataSection
}

end EvmAsm.Codegen
