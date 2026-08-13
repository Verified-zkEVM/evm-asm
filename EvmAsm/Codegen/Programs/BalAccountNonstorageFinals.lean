/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinals

  `bal_account_nonstorage_finals` (bead i3djw / bmvmx.1.6.4.4 step .1) — parse a BAL
  AccountChanges' NON-storage fields into their per-account FINAL values, the
  value-bearing companion of bal_storage_change_values (#8564, which does storage).
  This is the BAL-side foundation for the all-accounts non-storage exec-vs-BAL
  consistency check (the analog of bal_all_accounts_storage_consistent #8576).

  AccountChanges = RLP `[address, storage_changes, storage_reads, balance_changes,
  nonce_changes, code_changes]` (EIP-7928). Each of balance_changes (item 3) /
  nonce_changes (item 4) / code_changes (item 5) is a list of `[block_access_index,
  value]` tuples; the account's FINAL value for that field is the `value` of the
  LAST (highest block_access_index) tuple. (The per-tx tuple SEQUENCE is verified
  separately once the exec log carries a tx index — bmvmx.1.6.6.)

  GH #10753 bridge module: the program itself lives in the leaf
  `BalAccountNonstorageFinalsProg.lean` parameterised over the abstract `GuestLayout`;
  this module applies the concrete `guestLayout` and re-exposes
  `balAccountNonstorageFinals_prog` with its original name and type.
  Long B-type arms use named `brOff` (#11512) — BYTE-IDENTICAL regime (#11515).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsProg
import EvmAsm.Codegen.GuestLayoutInstance
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_nonstorage_finals

    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length   a2 = out ptr (88 B)
    a0 (output) = 0 ok / 1 parse failure (conservative). -/
def balAccountNonstorageFinals_prog : Program := balAccountNonstorageFinals_prog_of guestLayout

def balAccountCodeAtOrBefore_prog : Program :=
  [ .ADDI .x2 .x2 (-160 : BitVec 12),
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
    .SD .x18 .x0 (56 : BitVec 12),
    .SD .x18 .x0 (64 : BitVec 12),
    .SD .x18 .x0 (72 : BitVec 12),
    .SD .x2 .x0 (152 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (5 : Word),
    .ADDI .x13 .x2 (80 : BitVec 12),
    .ADDI .x14 .x2 (88 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item 2147483744),
    .BNE .x10 .x0 (brOff 2147483960 2147483748),
    .LD .x5 .x2 (80 : BitVec 12),
    .ADD .x20 .x8 .x5,
    .LD .x21 .x2 (88 : BitVec 12),
    .MV .x10 .x20,
    .MV .x11 .x21,
    .ADDI .x12 .x2 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items 2147483776),
    .BNE .x10 .x0 (brOff 2147483960 2147483780),
    .LI .x22 (0 : Word),
    .LI .x23 (0 : Word),
    .LD .x5 .x2 (96 : BitVec 12),
    .BEQ .x22 .x5 (brOff 2147483952 2147483796),
    .MV .x10 .x20,
    .MV .x11 .x21,
    .MV .x12 .x22,
    .ADDI .x13 .x2 (104 : BitVec 12),
    .ADDI .x14 .x2 (112 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item 2147483820),
    .BNE .x10 .x0 (brOff 2147483960 2147483824),
    .LD .x5 .x2 (104 : BitVec 12),
    .ADD .x24 .x20 .x5,
    .LD .x6 .x2 (112 : BitVec 12),
    .MV .x10 .x24,
    .MV .x11 .x6,
    .LI .x12 (0 : Word),
    .ADDI .x13 .x2 (120 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483856),
    .BNE .x10 .x0 (brOff 2147483960 2147483860),
    .LD .x5 .x2 (120 : BitVec 12),
    .BLTU .x19 .x5 (brOff 2147483944 2147483868),
    .BLTU .x5 .x23 (brOff 2147483944 2147483872),
    .SD .x2 .x5 (152 : BitVec 12),
    .MV .x10 .x24,
    .LD .x11 .x2 (112 : BitVec 12),
    .LI .x12 (1 : Word),
    .ADDI .x13 .x2 (128 : BitVec 12),
    .ADDI .x14 .x2 (136 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item 2147483900),
    .BNE .x10 .x0 (56 : BitVec 13),
    .LD .x6 .x2 (128 : BitVec 12),
    .ADD .x6 .x24 .x6,
    .SUB .x6 .x6 .x8,
    .SD .x18 .x6 (64 : BitVec 12),
    .LD .x6 .x2 (136 : BitVec 12),
    .SD .x18 .x6 (72 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x18 .x6 (56 : BitVec 12),
    .LD .x23 .x2 (152 : BitVec 12),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (jalOff 2147483792 2147483948),
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
    .ADDI .x2 .x2 (160 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountCodeAtOrBefore_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountCodeAtOrBefore_relocs : RelocTable :=
  [ (24, .jal .x1 "rlp_list_nth_item"),
    (32, .jal .x1 "rlp_list_count_items"),
    (43, .jal .x1 "rlp_list_nth_item"),
    (52, .jal .x1 "rlp_field_to_u64_strict"),
    (63, .jal .x1 "rlp_list_nth_item") ]

def balAccountCodeAtOrBeforeFunction : String :=
  "bal_account_code_at_or_before:\n" ++ emitProgramR balAccountCodeAtOrBefore_prog balAccountCodeAtOrBefore_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountCodeAtOrBefore_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountCodeAtOrBeforeFunction_eq_prog :
    balAccountCodeAtOrBeforeFunction = "bal_account_code_at_or_before:\n" ++ emitProgramR balAccountCodeAtOrBefore_prog balAccountCodeAtOrBefore_relocs := rfl

#guard balAccountCodeAtOrBeforeFunction.startsWith "bal_account_code_at_or_before:\n"
#guard balAccountCodeAtOrBefore_prog.length = 91
/-- `zisk_bal_account_nonstorage_finals`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes 8..16 : AccountChanges byte length
      bytes 16..  : the AccountChanges RLP
    Output: bytes 0..8 status, then the 88-byte finals block (see ABI above). -/
def ziskBalAccountNonstorageFinalsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # AccountChanges len\n" ++
  "  addi a0, a5, 16             # AccountChanges ptr\n" ++
  "  li a2, 0xa0010008           # finals out (OUTPUT + 8)\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lc2nsf_pdone\n" ++
  balAccountNonstorageFinalsFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lc2nsf_pdone:"

def ziskBalAccountNonstorageFinalsDataSection : String :=
  ""


end EvmAsm.Codegen
