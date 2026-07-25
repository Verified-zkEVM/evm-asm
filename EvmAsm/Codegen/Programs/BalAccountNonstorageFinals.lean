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
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_nonstorage_finals
    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length   a2 = out ptr (88 B)
    a0 (output) = 0 ok / 1 parse failure (conservative).
    Output layout (all u64/native unless noted):
      +0  has_balance (1 if balance_changes non-empty)
      +8  post_balance (32-byte big-endian, right-aligned)
      +40 has_nonce
      +48 post_nonce (u64)
      +56 has_code
      +64 code_off  (offset of the final code field RELATIVE to a0; 0 if none)
      +72 code_len  (byte length of the final code field content) -/
def balAccountNonstorageFinals_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (40 : BitVec 12),
    .SD .x18 .x0 (56 : BitVec 12),
    .SD .x18 .x0 (64 : BitVec 12),
    .SD .x18 .x0 (72 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .SD .x18 .x0 (32 : BitVec 12),
    .SD .x18 .x0 (48 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 88)),
    .BNE .x12 .x0 (640 : BitVec 13),
    .SD .x2 .x10 (48 : BitVec 12),
    .SD .x2 .x11 (56 : BitVec 12),
    .LD .x10 .x2 (48 : BitVec 12),
    .LD .x11 .x2 (56 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 112)),
    .BNE .x11 .x0 (616 : BitVec 13),
    .SD .x2 .x10 (48 : BitVec 12),
    .LD .x10 .x2 (48 : BitVec 12),
    .LD .x11 .x2 (56 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 132)),
    .BNE .x11 .x0 (596 : BitVec 13),
    .SD .x2 .x10 (48 : BitVec 12),
    .LD .x10 .x2 (48 : BitVec 12),
    .LD .x11 .x2 (56 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 152)),
    .BNE .x11 .x0 (576 : BitVec 13),
    .SD .x2 .x10 (48 : BitVec 12),
    .LD .x10 .x2 (48 : BitVec 12),
    .LD .x11 .x2 (56 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 172)),
    .BNE .x11 .x0 (556 : BitVec 13),
    .SD .x2 .x10 (48 : BitVec 12),
    .SUB .x19 .x10 .x12,
    .MV .x20 .x12,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 200)),
    .BNE .x12 .x0 (528 : BitVec 13),
    .BEQ .x10 .x11 (144 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .SD .x2 .x11 (72 : BitVec 12),
    .LD .x5 .x2 (64 : BitVec 12),
    .LD .x6 .x2 (72 : BitVec 12),
    .BEQ .x5 .x6 (36 : BitVec 13),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 240)),
    .BNE .x11 .x0 (488 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .SUB .x19 .x10 .x12,
    .MV .x20 .x12,
    .JAL .x0 (-40 : BitVec 21),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 272)),
    .BNE .x12 .x0 (456 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .SD .x2 .x11 (72 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 296)),
    .BNE .x11 .x0 (432 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 316)),
    .BNE .x11 .x0 (412 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (GuestAddrs.bal_account_nonstorage_finals + 336)),
    .BNE .x10 .x0 (392 : BitVec 13),
    .LI .x5 (1 : Word),
    .SD .x18 .x5 (0 : BitVec 12),
    .LD .x10 .x2 (48 : BitVec 12),
    .LD .x11 .x2 (56 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 360)),
    .BNE .x11 .x0 (368 : BitVec 13),
    .SD .x2 .x10 (48 : BitVec 12),
    .SUB .x19 .x10 .x12,
    .MV .x20 .x12,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 388)),
    .BNE .x12 .x0 (340 : BitVec 13),
    .BEQ .x10 .x11 (144 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .SD .x2 .x11 (72 : BitVec 12),
    .LD .x5 .x2 (64 : BitVec 12),
    .LD .x6 .x2 (72 : BitVec 12),
    .BEQ .x5 .x6 (36 : BitVec 13),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 428)),
    .BNE .x11 .x0 (300 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .SUB .x19 .x10 .x12,
    .MV .x20 .x12,
    .JAL .x0 (-40 : BitVec 21),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 460)),
    .BNE .x12 .x0 (268 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .SD .x2 .x11 (72 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 484)),
    .BNE .x11 .x0 (244 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 504)),
    .BNE .x11 .x0 (224 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.bal_account_nonstorage_finals + 520)),
    .BNE .x11 .x0 (208 : BitVec 13),
    .SD .x18 .x10 (48 : BitVec 12),
    .LI .x5 (1 : Word),
    .SD .x18 .x5 (40 : BitVec 12),
    .LD .x10 .x2 (48 : BitVec 12),
    .LD .x11 .x2 (56 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 548)),
    .BNE .x11 .x0 (180 : BitVec 13),
    .SUB .x19 .x10 .x12,
    .MV .x20 .x12,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 572)),
    .BNE .x12 .x0 (156 : BitVec 13),
    .BEQ .x10 .x11 (144 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .SD .x2 .x11 (72 : BitVec 12),
    .LD .x5 .x2 (64 : BitVec 12),
    .LD .x6 .x2 (72 : BitVec 12),
    .BEQ .x5 .x6 (36 : BitVec 13),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 612)),
    .BNE .x11 .x0 (116 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .SUB .x19 .x10 .x12,
    .MV .x20 .x12,
    .JAL .x0 (-40 : BitVec 21),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_account_nonstorage_finals + 644)),
    .BNE .x12 .x0 (84 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .SD .x2 .x11 (72 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 668)),
    .BNE .x11 .x0 (60 : BitVec 13),
    .SD .x2 .x10 (64 : BitVec 12),
    .LD .x28 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .MV .x10 .x28,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_account_nonstorage_finals + 692)),
    .BNE .x11 .x0 (36 : BitVec 13),
    .SUB .x29 .x10 .x12,
    .SUB .x29 .x29 .x8,
    .SD .x18 .x29 (64 : BitVec 12),
    .SD .x18 .x12 (72 : BitVec 12),
    .LI .x5 (1 : Word),
    .SD .x18 .x5 (56 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balAccountNonstorageFinals_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balAccountNonstorageFinals_relocs : RelocTable :=
  [ (22, .jal .x1 "rlp_walk_init"),
    (28, .jal .x1 "rlp_walk_next"),
    (33, .jal .x1 "rlp_walk_next"),
    (38, .jal .x1 "rlp_walk_next"),
    (43, .jal .x1 "rlp_walk_next"),
    (50, .jal .x1 "rlp_walk_init"),
    (60, .jal .x1 "rlp_walk_next"),
    (68, .jal .x1 "rlp_walk_init"),
    (74, .jal .x1 "rlp_walk_next"),
    (79, .jal .x1 "rlp_walk_next"),
    (84, .jal .x1 "rlp_content_to_u256_be"),
    (90, .jal .x1 "rlp_walk_next"),
    (97, .jal .x1 "rlp_walk_init"),
    (107, .jal .x1 "rlp_walk_next"),
    (115, .jal .x1 "rlp_walk_init"),
    (121, .jal .x1 "rlp_walk_next"),
    (126, .jal .x1 "rlp_walk_next"),
    (130, .jal .x1 "rlp_content_to_u64"),
    (137, .jal .x1 "rlp_walk_next"),
    (143, .jal .x1 "rlp_walk_init"),
    (153, .jal .x1 "rlp_walk_next"),
    (161, .jal .x1 "rlp_walk_init"),
    (167, .jal .x1 "rlp_walk_next"),
    (173, .jal .x1 "rlp_walk_next") ]

def balAccountNonstorageFinalsFunction : String :=
  "bal_account_nonstorage_finals:\n" ++ emitProgramR balAccountNonstorageFinals_prog balAccountNonstorageFinals_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balAccountNonstorageFinals_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balAccountNonstorageFinalsFunction_eq_prog :
    balAccountNonstorageFinalsFunction = "bal_account_nonstorage_finals:\n" ++ emitProgramR balAccountNonstorageFinals_prog balAccountNonstorageFinals_relocs := rfl

#guard balAccountNonstorageFinalsFunction.startsWith "bal_account_nonstorage_finals:\n"
#guard balAccountNonstorageFinals_prog.length = 192

/-- Select the latest `code_changes` tuple visible at a block access index.
    The ordinary finals helper intentionally returns the block-final code; the
    dispatcher instead needs the code visible before the current user tx. -/
def balAccountCodeAtOrBeforeFunction : String :=
  "bal_account_code_at_or_before:\n" ++
  "  addi sp, sp, -160\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 56(s2); sd zero, 64(s2); sd zero, 72(s2); sd zero, 152(sp)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5; addi a3, sp, 80; addi a4, sp, 88; jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbcab_fail\n" ++
  "  ld t0, 80(sp); add s4, s0, t0; ld s5, 88(sp)\n" ++
  "  mv a0, s4; mv a1, s5; addi a2, sp, 96; jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbcab_fail\n" ++
  "  li s6, 0; li s7, 0\n" ++
  ".Lbcab_loop:\n" ++
  "  ld t0, 96(sp); beq s6, t0, .Lbcab_done\n" ++
  "  mv a0, s4; mv a1, s5; mv a2, s6; addi a3, sp, 104; addi a4, sp, 112; jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbcab_fail\n" ++
  "  ld t0, 104(sp); add s8, s4, t0; ld t1, 112(sp)\n" ++
  "  mv a0, s8; mv a1, t1; li a2, 0; addi a3, sp, 120; jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lbcab_fail\n" ++
  "  ld t0, 120(sp); bgtu t0, s3, .Lbcab_next; bltu t0, s7, .Lbcab_next\n" ++
  "  sd t0, 152(sp); mv a0, s8; ld a1, 112(sp); li a2, 1; addi a3, sp, 128; addi a4, sp, 136; jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbcab_fail\n" ++
  "  ld t1, 128(sp); add t1, s8, t1; sub t1, t1, s0; sd t1, 64(s2); ld t1, 136(sp); sd t1, 72(s2); li t1, 1; sd t1, 56(s2); ld s7, 152(sp)\n" ++
  ".Lbcab_next:\n" ++
  "  addi s6, s6, 1; j .Lbcab_loop\n" ++
  ".Lbcab_done:\n" ++
  "  li a0, 0; j .Lbcab_ret\n" ++
  ".Lbcab_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbcab_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  addi sp, sp, 160; ret"
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

def ziskBalAccountNonstorageFinalsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountNonstorageFinalsPrologue
  dataAsm     := ziskBalAccountNonstorageFinalsDataSection
}

end EvmAsm.Codegen
