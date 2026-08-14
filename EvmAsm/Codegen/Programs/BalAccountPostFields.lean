/-
  EvmAsm.Codegen.Programs.BalAccountPostFields

  BAL AccountChanges post-value extraction for state-root replay.

  AccountChanges RLP =
    [address, storage_changes, storage_reads, balance_changes, nonce_changes, code_changes]

  For state replay we need the final post-value for each account field. The BAL
  lists are ordered by blockAccessIndex, so the final account balance/nonce is
  the last entry in each corresponding change list. This helper extracts those
  two optional integers as raw canonical big-endian byte strings.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_post_fields -- BAL AccountChanges -> optional post balance/nonce

    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = out balance bytes ptr (capacity 32)
    a3 = out balance length ptr (u64, UINT64_MAX means absent)
    a4 = out nonce bytes ptr (capacity 32)
    a5 = out nonce length ptr (u64, UINT64_MAX means absent)
    a0 (output) = 0 ok / 1 parse fail or value length > 32.

    For each nonempty change list, extracts the final item and then field 1 of
    that item. A zero post-value is represented by length 0, distinct from the
    absent sentinel. -/
def balAccountPostFields_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .LI .x5 (-1 : Word),
    .SD .x19 .x5 (0 : BitVec 12),
    .SD .x21 .x5 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_post_fields + 76)),
    .BNE .x12 .x0 (508 : BitVec 13),
    .SD .x2 .x10 (56 : BitVec 12),
    .SD .x2 .x11 (64 : BitVec 12),
    .LD .x10 .x2 (56 : BitVec 12),
    .LD .x11 .x2 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 100)),
    .BNE .x11 .x0 (484 : BitVec 13),
    .SD .x2 .x10 (56 : BitVec 12),
    .LD .x10 .x2 (56 : BitVec 12),
    .LD .x11 .x2 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 120)),
    .BNE .x11 .x0 (464 : BitVec 13),
    .SD .x2 .x10 (56 : BitVec 12),
    .LD .x10 .x2 (56 : BitVec 12),
    .LD .x11 .x2 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 140)),
    .BNE .x11 .x0 (444 : BitVec 13),
    .SD .x2 .x10 (56 : BitVec 12),
    .LD .x10 .x2 (56 : BitVec 12),
    .LD .x11 .x2 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 160)),
    .BNE .x11 .x0 (424 : BitVec 13),
    .SD .x2 .x10 (56 : BitVec 12),
    .SUB .x5 .x10 .x12,
    .MV .x6 .x12,
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_post_fields + 188)),
    .BNE .x12 .x0 (396 : BitVec 13),
    .BEQ .x10 .x11 (172 : BitVec 13),
    .SD .x2 .x10 (72 : BitVec 12),
    .SD .x2 .x11 (80 : BitVec 12),
    .LD .x5 .x2 (72 : BitVec 12),
    .LD .x6 .x2 (80 : BitVec 12),
    .BEQ .x5 .x6 (40 : BitVec 13),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 228)),
    .BNE .x11 .x0 (356 : BitVec 13),
    .SD .x2 .x10 (72 : BitVec 12),
    .SUB .x5 .x10 .x12,
    .SD .x2 .x5 (88 : BitVec 12),
    .SD .x2 .x12 (96 : BitVec 12),
    .JAL .x0 (-44 : BitVec 21),
    .LD .x10 .x2 (88 : BitVec 12),
    .LD .x11 .x2 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_post_fields + 264)),
    .BNE .x12 .x0 (320 : BitVec 13),
    .SD .x2 .x10 (72 : BitVec 12),
    .SD .x2 .x11 (80 : BitVec 12),
    .LD .x10 .x2 (72 : BitVec 12),
    .LD .x11 .x2 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 288)),
    .BNE .x11 .x0 (296 : BitVec 13),
    .SD .x2 .x10 (72 : BitVec 12),
    .LD .x10 .x2 (72 : BitVec 12),
    .LD .x11 .x2 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 308)),
    .BNE .x11 .x0 (276 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x7 .x12,
    .LI .x28 (32 : Word),
    .BLTU .x28 .x7 (260 : BitVec 13),
    .SD .x19 .x7 (0 : BitVec 12),
    .MV .x29 .x18,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x30 .x5 (0 : BitVec 12),
    .SB .x29 .x30 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LD .x10 .x2 (56 : BitVec 12),
    .LD .x11 .x2 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 376)),
    .BNE .x11 .x0 (208 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x6 .x12,
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_post_fields + 400)),
    .BNE .x12 .x0 (184 : BitVec 13),
    .BEQ .x10 .x11 (172 : BitVec 13),
    .SD .x2 .x10 (72 : BitVec 12),
    .SD .x2 .x11 (80 : BitVec 12),
    .LD .x5 .x2 (72 : BitVec 12),
    .LD .x6 .x2 (80 : BitVec 12),
    .BEQ .x5 .x6 (40 : BitVec 13),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 440)),
    .BNE .x11 .x0 (144 : BitVec 13),
    .SD .x2 .x10 (72 : BitVec 12),
    .SUB .x5 .x10 .x12,
    .SD .x2 .x5 (88 : BitVec 12),
    .SD .x2 .x12 (96 : BitVec 12),
    .JAL .x0 (-44 : BitVec 21),
    .LD .x10 .x2 (88 : BitVec 12),
    .LD .x11 .x2 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_post_fields + 476)),
    .BNE .x12 .x0 (108 : BitVec 13),
    .SD .x2 .x10 (72 : BitVec 12),
    .SD .x2 .x11 (80 : BitVec 12),
    .LD .x10 .x2 (72 : BitVec 12),
    .LD .x11 .x2 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 500)),
    .BNE .x11 .x0 (84 : BitVec 13),
    .SD .x2 .x10 (72 : BitVec 12),
    .LD .x10 .x2 (72 : BitVec 12),
    .LD .x11 .x2 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_post_fields + 520)),
    .BNE .x11 .x0 (64 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x7 .x12,
    .LI .x28 (32 : Word),
    .BLTU .x28 .x7 (48 : BitVec 13),
    .SD .x21 .x7 (0 : BitVec 12),
    .MV .x29 .x20,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .LBU .x30 .x5 (0 : BitVec 12),
    .SB .x29 .x30 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
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
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountPostFields_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountPostFields_relocs : RelocTable :=
  [ (19, .jal .x1 "rlp_walk_init"),
    (25, .jal .x1 "rlp_walk_next"),
    (30, .jal .x1 "rlp_walk_next"),
    (35, .jal .x1 "rlp_walk_next"),
    (40, .jal .x1 "rlp_walk_next"),
    (47, .jal .x1 "rlp_walk_init"),
    (57, .jal .x1 "rlp_walk_next"),
    (66, .jal .x1 "rlp_walk_init"),
    (72, .jal .x1 "rlp_walk_next"),
    (77, .jal .x1 "rlp_walk_next"),
    (94, .jal .x1 "rlp_walk_next"),
    (100, .jal .x1 "rlp_walk_init"),
    (110, .jal .x1 "rlp_walk_next"),
    (119, .jal .x1 "rlp_walk_init"),
    (125, .jal .x1 "rlp_walk_next"),
    (130, .jal .x1 "rlp_walk_next") ]

def balAccountPostFieldsFunction : String :=
  "bal_account_post_fields:\n" ++ emitProgramR balAccountPostFields_prog balAccountPostFields_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountPostFields_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountPostFieldsFunction_eq_prog :
    balAccountPostFieldsFunction = "bal_account_post_fields:\n" ++ emitProgramR balAccountPostFields_prog balAccountPostFields_relocs := rfl

#guard balAccountPostFieldsFunction.startsWith "bal_account_post_fields:\n"
/-- `zisk_bal_account_post_fields`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  AccountChanges RLP length (u64)
      +16 AccountChanges RLP bytes
    Output layout:
      OUTPUT+0  : status
      OUTPUT+8  : balance length (UINT64_MAX absent, 0 zero, otherwise byte len)
      OUTPUT+16 : balance bytes (32-byte capacity, only first len significant)
      OUTPUT+48 : nonce length (UINT64_MAX absent, 0 zero, otherwise byte len)
      OUTPUT+56 : nonce bytes (32-byte capacity, only first len significant) -/
def ziskBalAccountPostFieldsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sd zero, 56(t0)\n" ++
  "  sd zero, 64(t0); sd zero, 72(t0); sd zero, 80(t0)\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account-change RLP length\n" ++
  "  addi a0, t0, 16             # account-change RLP ptr\n" ++
  "  li a2, 0xa0010010           # balance bytes at OUTPUT+16\n" ++
  "  li a3, 0xa0010008           # balance length at OUTPUT+8\n" ++
  "  li a4, 0xa0010038           # nonce bytes at OUTPUT+56\n" ++
  "  li a5, 0xa0010030           # nonce length at OUTPUT+48\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)   # status at OUTPUT+0\n" ++
  "  j .Lbpf_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  ".Lbpf_pdone:"

def ziskBalAccountPostFieldsDataSection : String :=
  ""


end EvmAsm.Codegen
