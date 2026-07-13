/-
  EvmAsm.Codegen.Programs.AccountBalance

  account_add_balance (bead evm-asm-fhsxz.2.1): credit a wei delta to the
  balance field of an Ethereum account RLP. This is the per-withdrawal state
  mutation that Step 2 (header/withdrawal-only valid blocks) applies before
  recomputing the post-state root via mpt_state_root.

  An account value is rlp([nonce, balance, storageRoot, codeHash]); a
  withdrawal credits `amount_gwei * 1e9` wei to an EXISTING account's balance
  (a value-only update — no structural change). The balance is the RLP item
  at index 1, encoded as a minimal big-endian integer. We:
    1. read item 1 (the current balance bytes) via rlp_list_nth_item,
    2. right-align it into a 32-byte big-endian buffer,
    3. add the 32-byte delta with a byte-wise carry,
    4. strip leading zeros to minimal form and rlp_encode_bytes it,
    5. mpt_splice_slot the account list, replacing item 1 with the new
       balance encoding (which recomputes the outer list prefix).

  Reuses mpt_splice_slot / mset_memcpy (Programs/MptSet.lean) and the RLP
  read/encode helpers (Programs/RlpRead.lean). All multi-byte work is on
  8-aligned scratch; account/balance bytes are copied byte-wise (no-misaligned
  invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.MptSet
import EvmAsm.Codegen.Programs.AccountFieldExtract
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## account_add_balance -- balance += delta on an account RLP

    a0 = account RLP ptr        a1 = account RLP length
    a2 = delta ptr (32-byte big-endian)
    a3 = output buffer ptr      a4 = u64 out length ptr
    a0 (output) = 0 (ok) / 1 (parse fail / balance > 32 bytes)

    new account = rlp([nonce, balance+delta, storageRoot, codeHash]). -/
def accountAddBalance_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.aab_bal_off (GuestAddrs.account_add_balance + 60)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aab_bal_off (GuestAddrs.account_add_balance + 60)),
    .AUIPC .x14 (laHi GuestAddrs.aab_bal_len (GuestAddrs.account_add_balance + 68)),
    .ADDI .x14 .x14 (laLo GuestAddrs.aab_bal_len (GuestAddrs.account_add_balance + 68)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.account_add_balance + 76)),
    .BNE .x10 .x0 (316 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.aab_bal32 (GuestAddrs.account_add_balance + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aab_bal32 (GuestAddrs.account_add_balance + 84)),
    .SD .x5 .x0 (0 : BitVec 12),
    .SD .x5 .x0 (8 : BitVec 12),
    .SD .x5 .x0 (16 : BitVec 12),
    .SD .x5 .x0 (24 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.aab_bal_len (GuestAddrs.account_add_balance + 108)),
    .ADDI .x6 .x6 (laLo GuestAddrs.aab_bal_len (GuestAddrs.account_add_balance + 108)),
    .LD .x6 .x6 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BLTU .x7 .x6 (272 : BitVec 13),
    .AUIPC .x7 (laHi GuestAddrs.aab_bal_off (GuestAddrs.account_add_balance + 128)),
    .ADDI .x7 .x7 (laLo GuestAddrs.aab_bal_off (GuestAddrs.account_add_balance + 128)),
    .LD .x7 .x7 (0 : BitVec 12),
    .ADD .x7 .x8 .x7,
    .AUIPC .x28 (laHi GuestAddrs.aab_bal32 (GuestAddrs.account_add_balance + 144)),
    .ADDI .x28 .x28 (laLo GuestAddrs.aab_bal32 (GuestAddrs.account_add_balance + 144)),
    .LI .x29 (32 : Word),
    .SUB .x29 .x29 .x6,
    .ADD .x28 .x28 .x29,
    .MV .x30 .x6,
    .BEQ .x30 .x0 (28 : BitVec 13),
    .LBU .x31 .x7 (0 : BitVec 12),
    .SB .x28 .x31 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.aab_bal32 (GuestAddrs.account_add_balance + 196)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aab_bal32 (GuestAddrs.account_add_balance + 196)),
    .LI .x7 (31 : Word),
    .LI .x28 (0 : Word),
    .ADD .x29 .x5 .x7,
    .LBU .x30 .x29 (0 : BitVec 12),
    .ADD .x31 .x18 .x7,
    .LBU .x31 .x31 (0 : BitVec 12),
    .ADD .x30 .x30 .x31,
    .ADD .x30 .x30 .x28,
    .ANDI .x31 .x30 (255 : BitVec 12),
    .SB .x29 .x31 (0 : BitVec 12),
    .SRLI .x28 .x30 (8 : BitVec 6),
    .BEQ .x7 .x0 (12 : BitVec 13),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-44 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.aab_bal32 (GuestAddrs.account_add_balance + 260)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aab_bal32 (GuestAddrs.account_add_balance + 260)),
    .LI .x6 (0 : Word),
    .LI .x7 (32 : Word),
    .BEQ .x6 .x7 (24 : BitVec 13),
    .ADD .x28 .x5 .x6,
    .LBU .x28 .x28 (0 : BitVec 12),
    .BNE .x28 .x0 (12 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x7 (32 : Word),
    .SUB .x7 .x7 .x6,
    .AUIPC .x28 (laHi GuestAddrs.aab_bal32 (GuestAddrs.account_add_balance + 308)),
    .ADDI .x28 .x28 (laLo GuestAddrs.aab_bal32 (GuestAddrs.account_add_balance + 308)),
    .ADD .x28 .x28 .x6,
    .MV .x10 .x28,
    .MV .x11 .x7,
    .AUIPC .x12 (laHi GuestAddrs.aab_enc (GuestAddrs.account_add_balance + 328)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aab_enc (GuestAddrs.account_add_balance + 328)),
    .AUIPC .x13 (laHi GuestAddrs.aab_enc_len (GuestAddrs.account_add_balance + 336)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aab_enc_len (GuestAddrs.account_add_balance + 336)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.account_add_balance + 344)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.aab_enc (GuestAddrs.account_add_balance + 360)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aab_enc (GuestAddrs.account_add_balance + 360)),
    .AUIPC .x5 (laHi GuestAddrs.aab_enc_len (GuestAddrs.account_add_balance + 368)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aab_enc_len (GuestAddrs.account_add_balance + 368)),
    .LD .x14 .x5 (0 : BitVec 12),
    .MV .x15 .x19,
    .MV .x16 .x20,
    .JAL .x1 (jalOff GuestAddrs.mpt_splice_slot (GuestAddrs.account_add_balance + 388)),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountAddBalance_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountAddBalance_relocs : RelocTable :=
  [ (15, .la .x13 "aab_bal_off"),
    (17, .la .x14 "aab_bal_len"),
    (19, .jal .x1 "rlp_list_nth_item"),
    (21, .la .x5 "aab_bal32"),
    (27, .la .x6 "aab_bal_len"),
    (32, .la .x7 "aab_bal_off"),
    (36, .la .x28 "aab_bal32"),
    (49, .la .x5 "aab_bal32"),
    (65, .la .x5 "aab_bal32"),
    (77, .la .x28 "aab_bal32"),
    (82, .la .x12 "aab_enc"),
    (84, .la .x13 "aab_enc_len"),
    (86, .jal .x1 "rlp_encode_bytes"),
    (90, .la .x13 "aab_enc"),
    (92, .la .x5 "aab_enc_len"),
    (97, .jal .x1 "mpt_splice_slot") ]

def accountAddBalanceFunction : String :=
  "account_add_balance:\n" ++ emitProgramR accountAddBalance_prog accountAddBalance_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountAddBalance_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountAddBalanceFunction_eq_prog :
    accountAddBalanceFunction = "account_add_balance:\n" ++ emitProgramR accountAddBalance_prog accountAddBalance_relocs := rfl

#guard accountAddBalanceFunction.startsWith "account_add_balance:\n"
#guard accountAddBalance_prog.length = 108
/-! ## account_set_uint_field -- replace an account RLP uint field exactly

    a0 = account RLP ptr        a1 = account RLP length
    a2 = field index (0 nonce / 1 balance)
    a3 = value ptr (big-endian bytes)  a4 = value length (<= 32)
    a5 = output buffer ptr      a6 = u64 out length ptr
    a0 (output) = 0 (ok) / 1 (parse fail / value too long)

    The value is encoded as a canonical RLP integer, then spliced into the
    account list at the requested field. This is the BAL post-value analogue of
    account_add_balance: withdrawal replay adds a delta, BAL replay sets the
    exact post nonce/balance reported by the block access list. -/
def accountSetUintField_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .LI .x5 (32 : Word),
    .BLTU .x5 .x20 (84 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .AUIPC .x12 (laHi GuestAddrs.aab_enc (GuestAddrs.account_set_uint_field + 80)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aab_enc (GuestAddrs.account_set_uint_field + 80)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.account_set_uint_field + 88)),
    .AUIPC .x5 (laHi GuestAddrs.aab_enc_len (GuestAddrs.account_set_uint_field + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aab_enc_len (GuestAddrs.account_set_uint_field + 92)),
    .SD .x5 .x10 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .AUIPC .x13 (laHi GuestAddrs.aab_enc (GuestAddrs.account_set_uint_field + 116)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aab_enc (GuestAddrs.account_set_uint_field + 116)),
    .AUIPC .x5 (laHi GuestAddrs.aab_enc_len (GuestAddrs.account_set_uint_field + 124)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aab_enc_len (GuestAddrs.account_set_uint_field + 124)),
    .LD .x14 .x5 (0 : BitVec 12),
    .MV .x15 .x21,
    .MV .x16 .x22,
    .JAL .x1 (jalOff GuestAddrs.mpt_splice_slot (GuestAddrs.account_set_uint_field + 144)),
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
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountSetUintField_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountSetUintField_relocs : RelocTable :=
  [ (20, .la .x12 "aab_enc"),
    (22, .jal .x1 "rlp_encode_uint_be"),
    (23, .la .x5 "aab_enc_len"),
    (29, .la .x13 "aab_enc"),
    (31, .la .x5 "aab_enc_len"),
    (36, .jal .x1 "mpt_splice_slot") ]

def accountSetUintFieldFunction : String :=
  "account_set_uint_field:\n" ++ emitProgramR accountSetUintField_prog accountSetUintField_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountSetUintField_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountSetUintFieldFunction_eq_prog :
    accountSetUintFieldFunction = "account_set_uint_field:\n" ++ emitProgramR accountSetUintField_prog accountSetUintField_relocs := rfl

#guard accountSetUintFieldFunction.startsWith "account_set_uint_field:\n"
#guard accountSetUintField_prog.length = 49
/-- `zisk_account_add_balance`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  account_len (u64)
      +16 delta (32-byte big-endian)
      +48 account RLP bytes
    Output layout:
      OUTPUT+0 : new account RLP length (u64)
      OUTPUT+8 : new account RLP bytes -/
def ziskAccountAddBalancePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  addi a2, t0, 16             # delta32 ptr\n" ++
  "  addi a0, t0, 48             # account ptr\n" ++
  "  li a3, 0xa0010008           # out at OUTPUT+8\n" ++
  "  li a4, 0xa0010000           # out_len at OUTPUT+0\n" ++
  "  jal ra, account_add_balance\n" ++
  "  li t0, 0xa0010200; sd a0, 0(t0)   # status (debug) at OUTPUT+512\n" ++
  "  j .Laab_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  ".Laab_pdone:"

def ziskAccountAddBalanceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mset_span_start:\n  .zero 8\n" ++
  "mset_span_size:\n  .zero 8\n" ++
  "mset_payload_start:\n  .zero 8\n" ++
  "mset_head_len:\n  .zero 8\n" ++
  "mset_tail_start:\n  .zero 8\n" ++
  "mset_tail_len:\n  .zero 8\n" ++
  "mset_new_payload_len:\n  .zero 8\n" ++
  "mset_prefix_len:\n  .zero 8\n" ++
  "mset_cursor:\n  .zero 8\n" ++
  "aab_bal_off:\n  .zero 8\n" ++
  "aab_bal_len:\n  .zero 8\n" ++
  "aab_enc_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aab_bal32:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "aab_enc:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "aab_out_pad:\n  .zero 8"

def ziskAccountAddBalanceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountAddBalancePrologue
  dataAsm     := ziskAccountAddBalanceDataSection
}


/-- `zisk_account_set_uint_field`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  account_len (u64)
      +16 field_index (u64, 0 nonce / 1 balance)
      +24 value_len (u64)
      +32 value bytes (big-endian, up to 32 bytes)
      +64 account RLP bytes
    Output layout:
      OUTPUT+0 : new account RLP length (u64)
      OUTPUT+8 : new account RLP bytes
      OUTPUT+512 : status -/
def ziskAccountSetUintFieldPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  ld a2, 16(t0)               # field_index\n" ++
  "  ld a4, 24(t0)               # value_len\n" ++
  "  addi a3, t0, 32             # value ptr\n" ++
  "  addi a0, t0, 64             # account ptr\n" ++
  "  li a5, 0xa0010008           # out at OUTPUT+8\n" ++
  "  li a6, 0xa0010000           # out_len at OUTPUT+0\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  li t0, 0xa0010200; sd a0, 0(t0)   # status at OUTPUT+512\n" ++
  "  j .Lasuf_pdone\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  ".Lasuf_pdone:"

def ziskAccountSetUintFieldProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountSetUintFieldPrologue
  dataAsm     := ziskAccountAddBalanceDataSection
}

/-! ## selfdestruct_balance_transfer -- SELFDESTRUCT account-RLP balance move

    Apply the balance mutation from post-Cancun SELFDESTRUCT to already-loaded
    originator and beneficiary account RLP values. This mirrors
    execution-specs v0.5.0's
    `move_ether(originator, beneficiary, originator_balance)`:

    * different beneficiary: originator balance becomes zero; beneficiary is
      credited by the originator's pre-transfer balance;
    * same beneficiary: net no-op, including when the originator was created
      in this transaction. End-of-transaction deletion clears the account
      while preserving this balance.

    Calling convention:
      a0 = origin account ptr       a1 = origin account len
      a2 = beneficiary account ptr  a3 = beneficiary account len
      a4 = same-address flag        a5 = origin-created-in-tx flag
      a6 = output base

    Output layout at `a6`:
      +0    origin result len
      +8    beneficiary result len
      +16   origin result account bytes
      +128  beneficiary result account bytes

    a0 returns 0 on success, 1 on parse/splice failure. -/
def selfdestructBalanceTransfer_prog : Program :=
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
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .SD .x22 .x0 (0 : BitVec 12),
    .SD .x22 .x0 (8 : BitVec 12),
    .ADDI .x23 .x22 (16 : BitVec 12),
    .BNE .x20 .x0 (160 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.aab_bal32 (GuestAddrs.selfdestruct_balance_transfer + 92)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aab_bal32 (GuestAddrs.selfdestruct_balance_transfer + 92)),
    .JAL .x1 (jalOff GuestAddrs.account_extract_balance (GuestAddrs.selfdestruct_balance_transfer + 100)),
    .BNE .x10 .x0 (280 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.aab_bal32 (GuestAddrs.selfdestruct_balance_transfer + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aab_bal32 (GuestAddrs.selfdestruct_balance_transfer + 108)),
    .AUIPC .x6 (laHi GuestAddrs.sdbt_delta32 (GuestAddrs.selfdestruct_balance_transfer + 116)),
    .ADDI .x6 .x6 (laLo GuestAddrs.sdbt_delta32 (GuestAddrs.selfdestruct_balance_transfer + 116)),
    .LD .x7 .x5 (0 : BitVec 12),
    .SD .x6 .x7 (0 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .SD .x6 .x7 (8 : BitVec 12),
    .LD .x7 .x5 (16 : BitVec 12),
    .SD .x6 .x7 (16 : BitVec 12),
    .LD .x7 .x5 (24 : BitVec 12),
    .SD .x6 .x7 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.aab_bal32 (GuestAddrs.selfdestruct_balance_transfer + 168)),
    .ADDI .x13 .x13 (laLo GuestAddrs.aab_bal32 (GuestAddrs.selfdestruct_balance_transfer + 168)),
    .LI .x14 (0 : Word),
    .MV .x15 .x23,
    .MV .x16 .x22,
    .JAL .x1 (jalOff GuestAddrs.account_set_uint_field (GuestAddrs.selfdestruct_balance_transfer + 188)),
    .BNE .x10 .x0 (192 : BitVec 13),
    .ADDI .x5 .x22 (128 : BitVec 12),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.sdbt_delta32 (GuestAddrs.selfdestruct_balance_transfer + 208)),
    .ADDI .x12 .x12 (laLo GuestAddrs.sdbt_delta32 (GuestAddrs.selfdestruct_balance_transfer + 208)),
    .MV .x13 .x5,
    .ADDI .x14 .x22 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.account_add_balance (GuestAddrs.selfdestruct_balance_transfer + 224)),
    .BNE .x10 .x0 (156 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (152 : BitVec 21),
    .ADDI .x0 .x0 (0 : BitVec 12),
    .SD .x22 .x9 (0 : BitVec 12),
    .SD .x22 .x9 (8 : BitVec 12),
    .MV .x10 .x23,
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.selfdestruct_balance_transfer + 264)),
    .ADDI .x10 .x22 (128 : BitVec 12),
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.selfdestruct_balance_transfer + 280)),
    .LI .x10 (0 : Word),
    .JAL .x0 (100 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.aab_bal32 (GuestAddrs.selfdestruct_balance_transfer + 292)),
    .ADDI .x5 .x5 (laLo GuestAddrs.aab_bal32 (GuestAddrs.selfdestruct_balance_transfer + 292)),
    .SD .x5 .x0 (0 : BitVec 12),
    .SD .x5 .x0 (8 : BitVec 12),
    .SD .x5 .x0 (16 : BitVec 12),
    .SD .x5 .x0 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (1 : Word),
    .MV .x13 .x5,
    .LI .x14 (0 : Word),
    .MV .x15 .x23,
    .MV .x16 .x22,
    .JAL .x1 (jalOff GuestAddrs.account_set_uint_field (GuestAddrs.selfdestruct_balance_transfer + 344)),
    .BNE .x10 .x0 (36 : BitVec 13),
    .LD .x5 .x22 (0 : BitVec 12),
    .SD .x22 .x5 (8 : BitVec 12),
    .ADDI .x10 .x22 (128 : BitVec 12),
    .MV .x11 .x23,
    .MV .x12 .x5,
    .JAL .x1 (jalOff GuestAddrs.mset_memcpy (GuestAddrs.selfdestruct_balance_transfer + 372)),
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
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `selfdestructBalanceTransfer_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def selfdestructBalanceTransfer_relocs : RelocTable :=
  [ (23, .la .x12 "aab_bal32"),
    (25, .jal .x1 "account_extract_balance"),
    (27, .la .x5 "aab_bal32"),
    (29, .la .x6 "sdbt_delta32"),
    (42, .la .x13 "aab_bal32"),
    (47, .jal .x1 "account_set_uint_field"),
    (52, .la .x12 "sdbt_delta32"),
    (56, .jal .x1 "account_add_balance"),
    (66, .jal .x1 "mset_memcpy"),
    (70, .jal .x1 "mset_memcpy"),
    (73, .la .x5 "aab_bal32"),
    (86, .jal .x1 "account_set_uint_field"),
    (93, .jal .x1 "mset_memcpy") ]

def selfdestructBalanceTransferFunction : String :=
  "selfdestruct_balance_transfer:\n" ++ emitProgramR selfdestructBalanceTransfer_prog selfdestructBalanceTransfer_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `selfdestructBalanceTransfer_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem selfdestructBalanceTransferFunction_eq_prog :
    selfdestructBalanceTransferFunction = "selfdestruct_balance_transfer:\n" ++ emitProgramR selfdestructBalanceTransfer_prog selfdestructBalanceTransfer_relocs := rfl

#guard selfdestructBalanceTransferFunction.startsWith "selfdestruct_balance_transfer:\n"
#guard selfdestructBalanceTransfer_prog.length = 108
/-- `zisk_selfdestruct_balance_transfer`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8   origin_len
      +16  beneficiary_len
      +24  same-address flag
      +32  origin-created-in-tx flag
      +40  origin account RLP bytes, fixed 512-byte slot
      +552 beneficiary account RLP bytes
    Output layout:
      OUTPUT+0    origin result len
      OUTPUT+8    beneficiary result len
      OUTPUT+16   origin result account RLP
      OUTPUT+128  beneficiary result account RLP
      OUTPUT+248  status -/
def ziskSelfdestructBalanceTransferPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # origin_len\n" ++
  "  ld a3, 16(t0)               # beneficiary_len\n" ++
  "  ld a4, 24(t0)               # same-address flag\n" ++
  "  ld a5, 32(t0)               # origin-created-in-tx flag\n" ++
  "  addi a0, t0, 40             # origin account ptr\n" ++
  "  addi a2, t0, 552            # beneficiary account ptr\n" ++
  "  li a6, 0xa0010000           # output base\n" ++
  "  jal ra, selfdestruct_balance_transfer\n" ++
  "  li t0, 0xa00100f8; sd a0, 0(t0)   # status at OUTPUT+248\n" ++
  "  j .Lsdbt_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  -- cursor-walk helpers (account_extract_balance decodes via RlpWalk)
  rlpWalkHelpersClosure ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  selfdestructBalanceTransferFunction ++ "\n" ++
  ".Lsdbt_pdone:"

def ziskSelfdestructBalanceTransferProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSelfdestructBalanceTransferPrologue
  dataAsm     := ziskAccountExtractBalanceDataSection ++ "\n" ++ ziskAccountAddBalanceDataSection ++ "\n" ++
    ".balign 8\nsdbt_delta32:\n  .zero 32"
}

end EvmAsm.Codegen
