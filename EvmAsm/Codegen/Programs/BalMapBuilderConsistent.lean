/-
  EvmAsm.Codegen.Programs.BalMapBuilderConsistent

  DIR A only (#11183 / #10612): guest-internal fail-safe that the account_writes
  map finals match the reduced highest-BAI builder balance/nonce/code rows.
  Map finals are NOT serialised (serializer emits builder rows only), so a
  map↔builder desync can trip while rebuilt==supplied and the hash still
  matches — the binding gate does not replace this check.

  DIR B/C (builder↔supplied BAL body) retired: every field they compared is
  emitted into the hashed BAL, so their rejection set ⊆ bal_serializer_verify
  (60/61). Spec fork.py:390 only hashes the BUILT list; no supplied-body compare.
  Helpers for B/C remain below for the probe unit only; the guest-linked top
  level does not call them and takes no BAL pointer.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.BlockAccessListBuilder
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! Probe-only local PC placeholders.  These functions are not linked into the
    monolithic guest, so their concrete verification Programs use a fixed local
    origin while `emitProgramR` keeps cross-image relocs symbolic. -/
def balMapBuilderHasRowPc : Nat := 0x80000000
def balMapAccountMatchesPc : Nat := 0x80000000

/-! `bal_map_builder_has_row` searches the builder stream selected by `a3`:
    1 = balance (64-byte rows), 2 = nonce (40-byte rows), 3 = code (64-byte
    rows).  The caller supplies the canonical BE20 address, BAI, and value
    pointer/length. -/
def balMapBuilderHasRow_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
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
    .LI .x5 (1 : Word),
    .BNE .x20 .x5 (brOff (balMapBuilderHasRowPc + 216) (balMapBuilderHasRowPc + 56)),
    .LI .x5 (32 : Word),
    .BNE .x19 .x5 (brOff (balMapBuilderHasRowPc + 504) (balMapBuilderHasRowPc + 64)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_balance_count (balMapBuilderHasRowPc + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_balance_count (balMapBuilderHasRowPc + 68)),
    .LD .x20 .x5 (0 : BitVec 12),
    .AUIPC .x21 (laHi GuestAddrs.bal_builder_balance_changes (balMapBuilderHasRowPc + 80)),
    .ADDI .x21 .x21 (laLo GuestAddrs.bal_builder_balance_changes (balMapBuilderHasRowPc + 80)),
    .LI .x5 (0 : Word),
    .BGEU .x5 .x20 (brOff (balMapBuilderHasRowPc + 504) (balMapBuilderHasRowPc + 92)),
    .SLLI .x6 .x5 (6 : BitVec 6),
    .ADD .x7 .x21 .x6,
    .LI .x28 (0 : Word),
    .LI .x29 (20 : Word),
    .BEQ .x28 .x29 (32 : BitVec 13),
    .ADD .x29 .x7 .x28,
    .ADD .x30 .x8 .x28,
    .LBU .x31 .x29 (0 : BitVec 12),
    .LBU .x14 .x30 (0 : BitVec 12),
    .BNE .x31 .x14 (brOff (balMapBuilderHasRowPc + 208) (balMapBuilderHasRowPc + 132)),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LD .x6 .x7 (24 : BitVec 12),
    .BNE .x6 .x9 (60 : BitVec 13),
    .LD .x6 .x7 (32 : BitVec 12),
    .LD .x28 .x18 (0 : BitVec 12),
    .BNE .x6 .x28 (48 : BitVec 13),
    .LD .x6 .x7 (40 : BitVec 12),
    .LD .x28 .x18 (8 : BitVec 12),
    .BNE .x6 .x28 (36 : BitVec 13),
    .LD .x6 .x7 (48 : BitVec 12),
    .LD .x28 .x18 (16 : BitVec 12),
    .BNE .x6 .x28 (24 : BitVec 13),
    .LD .x6 .x7 (56 : BitVec 12),
    .LD .x28 .x18 (24 : BitVec 12),
    .BNE .x6 .x28 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (jalOff (balMapBuilderHasRowPc + 508) (balMapBuilderHasRowPc + 204)),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (jalOff (balMapBuilderHasRowPc + 92) (balMapBuilderHasRowPc + 212)),
    .LI .x5 (2 : Word),
    .BNE .x20 .x5 (brOff (balMapBuilderHasRowPc + 352) (balMapBuilderHasRowPc + 220)),
    .LI .x5 (8 : Word),
    .BNE .x19 .x5 (brOff (balMapBuilderHasRowPc + 504) (balMapBuilderHasRowPc + 228)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_nonce_count (balMapBuilderHasRowPc + 232)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_nonce_count (balMapBuilderHasRowPc + 232)),
    .LD .x20 .x5 (0 : BitVec 12),
    .AUIPC .x21 (laHi GuestAddrs.bal_builder_nonce_changes (balMapBuilderHasRowPc + 244)),
    .ADDI .x21 .x21 (laLo GuestAddrs.bal_builder_nonce_changes (balMapBuilderHasRowPc + 244)),
    .LI .x5 (0 : Word),
    .BGEU .x5 .x20 (brOff (balMapBuilderHasRowPc + 504) (balMapBuilderHasRowPc + 256)),
    .SLLI .x6 .x5 (5 : BitVec 6),
    .SLLI .x28 .x5 (3 : BitVec 6),
    .ADD .x6 .x6 .x28,
    .ADD .x7 .x21 .x6,
    .LI .x28 (0 : Word),
    .LI .x29 (20 : Word),
    .BEQ .x28 .x29 (32 : BitVec 13),
    .ADD .x29 .x7 .x28,
    .ADD .x30 .x8 .x28,
    .LBU .x31 .x29 (0 : BitVec 12),
    .LBU .x14 .x30 (0 : BitVec 12),
    .BNE .x31 .x14 (40 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LD .x6 .x7 (24 : BitVec 12),
    .BNE .x6 .x9 (24 : BitVec 13),
    .LD .x6 .x7 (32 : BitVec 12),
    .LD .x28 .x18 (0 : BitVec 12),
    .BNE .x6 .x28 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (jalOff (balMapBuilderHasRowPc + 508) (balMapBuilderHasRowPc + 340)),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (jalOff (balMapBuilderHasRowPc + 256) (balMapBuilderHasRowPc + 348)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_code_count (balMapBuilderHasRowPc + 352)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_code_count (balMapBuilderHasRowPc + 352)),
    .LD .x20 .x5 (0 : BitVec 12),
    .AUIPC .x21 (laHi GuestAddrs.bal_builder_code_changes (balMapBuilderHasRowPc + 364)),
    .ADDI .x21 .x21 (laLo GuestAddrs.bal_builder_code_changes (balMapBuilderHasRowPc + 364)),
    .LI .x5 (0 : Word),
    .BGEU .x5 .x20 (brOff (balMapBuilderHasRowPc + 504) (balMapBuilderHasRowPc + 376)),
    .SLLI .x6 .x5 (6 : BitVec 6),
    .ADD .x7 .x21 .x6,
    .LI .x28 (0 : Word),
    .LI .x29 (20 : Word),
    .BEQ .x28 .x29 (32 : BitVec 13),
    .ADD .x29 .x7 .x28,
    .ADD .x30 .x8 .x28,
    .LBU .x31 .x29 (0 : BitVec 12),
    .LBU .x14 .x30 (0 : BitVec 12),
    .BNE .x31 .x14 (brOff (balMapBuilderHasRowPc + 488) (balMapBuilderHasRowPc + 416)),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LD .x6 .x7 (24 : BitVec 12),
    .BNE .x6 .x9 (56 : BitVec 13),
    .LD .x6 .x7 (40 : BitVec 12),
    .BNE .x6 .x19 (48 : BitVec 13),
    .LD .x6 .x7 (32 : BitVec 12),
    .MV .x28 .x18,
    .LI .x29 (0 : Word),
    .BEQ .x29 .x19 (40 : BitVec 13),
    .ADD .x30 .x6 .x29,
    .ADD .x31 .x28 .x29,
    .LBU .x14 .x30 (0 : BitVec 12),
    .LBU .x15 .x31 (0 : BitVec 12),
    .BNE .x14 .x15 (12 : BitVec 13),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (jalOff (balMapBuilderHasRowPc + 376) (balMapBuilderHasRowPc + 492)),
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
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balMapBuilderHasRow_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balMapBuilderHasRow_relocs : RelocTable :=
  [ (17, .la .x5 "bal_builder_balance_count"),
    (20, .la .x21 "bal_builder_balance_changes"),
    (58, .la .x5 "bal_builder_nonce_count"),
    (61, .la .x21 "bal_builder_nonce_changes"),
    (88, .la .x5 "bal_builder_code_count"),
    (91, .la .x21 "bal_builder_code_changes") ]

def balMapBuilderHasRowFunction : String :=
  "bal_map_builder_has_row:\n" ++ emitProgramR balMapBuilderHasRow_prog balMapBuilderHasRow_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balMapBuilderHasRow_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balMapBuilderHasRowFunction_eq_prog :
    balMapBuilderHasRowFunction = "bal_map_builder_has_row:\n" ++ emitProgramR balMapBuilderHasRow_prog balMapBuilderHasRow_relocs := rfl

#guard balMapBuilderHasRowFunction.startsWith "bal_map_builder_has_row:\n"
#guard balMapBuilderHasRow_prog.length = 136
/-! Parse one AccountChanges item and check every tuple in one selected field
    against the builder.  Empty fields are accepted; malformed RLP is rejected. -/
def balMapCheckAccountFieldFunction : String :=
  "bal_map_check_account_field:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init; bnez a2, .Lbmacf_parse\n" ++
  "  sd a0, 40(sp); sd a1, 48(sp)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2\n" ++
  "  li t2, 1; beq s3, t2, .Lbmacf_field\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2\n" ++
  "  li t2, 2; beq s3, t2, .Lbmacf_field\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; sd a0, 40(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2\n" ++
  ".Lbmacf_field:\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init; bnez a2, .Lbmacf_parse; mv s0, a0; mv s1, a1\n" ++
  ".Lbmacf_loop:\n" ++
  "  beq s0, s1, .Lbmacf_ok; mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2; sd s0, 40(sp); sd s1, 48(sp)\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init; bnez a2, .Lbmacf_parse; mv s0, a0; mv s1, a1; sd s0, 56(sp); sd s1, 64(sp)\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2; mv a0, t0; mv a1, t1; jal ra, rlp_content_to_u64_strict; bnez a1, .Lbmacf_parse; sd a0, 72(sp)\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmacf_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2\n" ++
  "  li t2, 3; beq s3, t2, .Lbmacf_code\n" ++
  "  li t2, 1; bne s3, t2, .Lbmacf_nonce; mv a0, t0; mv a1, t1; la a2, bame_value; jal ra, rlp_content_to_u256_be; bnez a0, .Lbmacf_parse; mv a0, s2; ld a1, 72(sp); la a2, bame_value; li a3, 32; li a4, 1; jal ra, bal_map_builder_has_row; bnez a0, .Lbmacf_bad\n" ++
  "  j .Lbmacf_next_tuple\n" ++
  ".Lbmacf_nonce:\n" ++
  "  mv a0, t0; mv a1, t1; jal ra, rlp_content_to_u64_strict; bnez a1, .Lbmacf_parse; la t2, bame_nonce; sd a0, 0(t2); mv a0, s2; ld a1, 72(sp); mv a2, t2; li a3, 8; li a4, 2; jal ra, bal_map_builder_has_row; bnez a0, .Lbmacf_bad\n" ++
  "  j .Lbmacf_next_tuple\n" ++
  ".Lbmacf_code:\n" ++
  "  mv a0, s2; ld a1, 72(sp); mv a2, t0; mv a3, t1; li a4, 3; jal ra, bal_map_builder_has_row; bnez a0, .Lbmacf_bad\n" ++
  ".Lbmacf_next_tuple:\n" ++
  "  ld s0, 40(sp); ld s1, 48(sp); j .Lbmacf_loop\n" ++
  ".Lbmacf_bad:\n  li a0, 1; j .Lbmacf_ret\n" ++
  ".Lbmacf_ok:\n  li a0, 0; j .Lbmacf_ret\n" ++
  ".Lbmacf_parse:\n  li a0, 2\n" ++
  ".Lbmacf_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 80; ret\n"

/-! Search the supplied BAL for one exact builder row. -/
def balMapFindSuppliedFunction : String :=
  "bal_map_find_supplied:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init; bnez a2, .Lbmfs_parse\n" ++
  "  sd a0, 64(sp); sd a1, 72(sp)\n" ++
  ".Lbmfs_loop:\n" ++
  "  ld t0, 64(sp); ld t1, 72(sp); beq t0, t1, .Lbmfs_miss; mv a0, t0; mv a1, t1; jal ra, rlp_walk_next; bnez a1, .Lbmfs_parse; sd a0, 64(sp); sub t2, a0, a2; mv t3, a2\n" ++
  "  mv a0, t2; mv a1, t3; mv a2, s0; mv a3, s1; mv a4, s2; mv a5, s3; mv a6, s4; jal ra, bal_map_account_matches; beqz a0, .Lbmfs_hit; li t4, 2; beq a0, t4, .Lbmfs_parse; j .Lbmfs_loop\n" ++
  ".Lbmfs_hit:\n  li a0, 0; j .Lbmfs_ret\n" ++
  ".Lbmfs_miss:\n  li a0, 1; j .Lbmfs_ret\n" ++
  ".Lbmfs_parse:\n  li a0, 2\n" ++
  ".Lbmfs_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 96; ret\n"

/-! Account matcher used by the builder→supplied direction. -/
def balMapAccountMatches_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
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
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balMapAccountMatchesPc + 72)),
    .BNE .x12 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 76)),
    .SD .x2 .x10 (64 : BitVec 12),
    .SD .x2 .x11 (72 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balMapAccountMatchesPc + 96)),
    .BNE .x11 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 100)),
    .LI .x5 (20 : Word),
    .BNE .x12 .x5 (brOff (balMapAccountMatchesPc + 668) (balMapAccountMatchesPc + 108)),
    .SUB .x5 .x10 .x12,
    .LI .x6 (0 : Word),
    .LI .x31 (20 : Word),
    .BEQ .x6 .x31 (32 : BitVec 13),
    .ADD .x7 .x5 .x6,
    .ADD .x28 .x18 .x6,
    .LBU .x29 .x7 (0 : BitVec 12),
    .LBU .x30 .x28 (0 : BitVec 12),
    .BNE .x29 .x30 (brOff (balMapAccountMatchesPc + 668) (balMapAccountMatchesPc + 144)),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .SD .x2 .x10 (64 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balMapAccountMatchesPc + 168)),
    .BNE .x11 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 172)),
    .SD .x2 .x10 (64 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balMapAccountMatchesPc + 188)),
    .BNE .x11 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 192)),
    .SD .x2 .x10 (64 : BitVec 12),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balMapAccountMatchesPc + 208)),
    .BNE .x11 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 212)),
    .SD .x2 .x10 (64 : BitVec 12),
    .MV .x5 .x10,
    .SUB .x5 .x5 .x12,
    .MV .x6 .x12,
    .LI .x7 (1 : Word),
    .BEQ .x22 .x7 (brOff (balMapAccountMatchesPc + 312) (balMapAccountMatchesPc + 236)),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balMapAccountMatchesPc + 248)),
    .BNE .x11 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 252)),
    .SD .x2 .x10 (64 : BitVec 12),
    .MV .x5 .x10,
    .SUB .x5 .x5 .x12,
    .MV .x6 .x12,
    .LI .x7 (2 : Word),
    .BEQ .x22 .x7 (36 : BitVec 13),
    .LD .x10 .x2 (64 : BitVec 12),
    .LD .x11 .x2 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balMapAccountMatchesPc + 288)),
    .BNE .x11 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 292)),
    .SD .x2 .x10 (64 : BitVec 12),
    .MV .x5 .x10,
    .SUB .x5 .x5 .x12,
    .MV .x6 .x12,
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balMapAccountMatchesPc + 320)),
    .BNE .x12 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 324)),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .BEQ .x8 .x9 (brOff (balMapAccountMatchesPc + 668) (balMapAccountMatchesPc + 336)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balMapAccountMatchesPc + 348)),
    .BNE .x11 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 352)),
    .MV .x8 .x10,
    .SUB .x5 .x10 .x12,
    .MV .x6 .x12,
    .SD .x2 .x8 (64 : BitVec 12),
    .SD .x2 .x9 (72 : BitVec 12),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (balMapAccountMatchesPc + 384)),
    .BNE .x12 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 388)),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .SD .x2 .x8 (80 : BitVec 12),
    .SD .x2 .x9 (88 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balMapAccountMatchesPc + 416)),
    .BNE .x11 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 420)),
    .MV .x8 .x10,
    .SUB .x5 .x10 .x12,
    .MV .x6 .x12,
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (balMapAccountMatchesPc + 444)),
    .BNE .x11 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 448)),
    .BNE .x10 .x19 (brOff (balMapAccountMatchesPc + 648) (balMapAccountMatchesPc + 452)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (balMapAccountMatchesPc + 464)),
    .BNE .x11 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 468)),
    .MV .x8 .x10,
    .SUB .x5 .x10 .x12,
    .MV .x6 .x12,
    .LI .x7 (1 : Word),
    .BEQ .x22 .x7 (52 : BitVec 13),
    .LI .x7 (2 : Word),
    .BEQ .x22 .x7 (brOff (balMapAccountMatchesPc + 624) (balMapAccountMatchesPc + 496)),
    .BNE .x6 .x21 (brOff (balMapAccountMatchesPc + 648) (balMapAccountMatchesPc + 500)),
    .LI .x7 (0 : Word),
    .BEQ .x7 .x21 (brOff (balMapAccountMatchesPc + 660) (balMapAccountMatchesPc + 508)),
    .ADD .x28 .x5 .x7,
    .ADD .x29 .x20 .x7,
    .LBU .x30 .x28 (0 : BitVec 12),
    .LBU .x31 .x29 (0 : BitVec 12),
    .BNE .x30 .x31 (brOff (balMapAccountMatchesPc + 648) (balMapAccountMatchesPc + 528)),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .AUIPC .x12 (laHi 0 (balMapAccountMatchesPc + 548)),
    .ADDI .x12 .x12 (laLo 0 (balMapAccountMatchesPc + 548)),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be (balMapAccountMatchesPc + 556)),
    .BNE .x10 .x0 (brOff (balMapAccountMatchesPc + 676) (balMapAccountMatchesPc + 560)),
    .AUIPC .x31 (laHi 0 (balMapAccountMatchesPc + 564)),
    .ADDI .x31 .x31 (laLo 0 (balMapAccountMatchesPc + 564)),
    .LD .x7 .x31 (0 : BitVec 12),
    .LD .x28 .x20 (0 : BitVec 12),
    .BNE .x7 .x28 (brOff (balMapAccountMatchesPc + 648) (balMapAccountMatchesPc + 580)),
    .LD .x7 .x31 (8 : BitVec 12),
    .LD .x28 .x20 (8 : BitVec 12),
    .BNE .x7 .x28 (56 : BitVec 13),
    .LD .x7 .x31 (16 : BitVec 12),
    .LD .x28 .x20 (16 : BitVec 12),
    .BNE .x7 .x28 (44 : BitVec 13),
    .LD .x7 .x31 (24 : BitVec 12),
    .LD .x28 .x20 (24 : BitVec 12),
    .BNE .x7 .x28 (32 : BitVec 13),
    .JAL .x0 (40 : BitVec 21),
    .MV .x10 .x5,
    .MV .x11 .x6,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (balMapAccountMatchesPc + 632)),
    .BNE .x11 .x0 (40 : BitVec 13),
    .LD .x7 .x20 (0 : BitVec 12),
    .BEQ .x10 .x7 (16 : BitVec 13),
    .LD .x8 .x2 (64 : BitVec 12),
    .LD .x9 .x2 (72 : BitVec 12),
    .JAL .x0 (jalOff (balMapAccountMatchesPc + 336) (balMapAccountMatchesPc + 656)),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balMapAccountMatches_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balMapAccountMatches_relocs : RelocTable :=
  [ (18, .jal .x1 "rlp_walk_init"),
    (24, .jal .x1 "rlp_walk_next"),
    (42, .jal .x1 "rlp_walk_next"),
    (47, .jal .x1 "rlp_walk_next"),
    (52, .jal .x1 "rlp_walk_next"),
    (62, .jal .x1 "rlp_walk_next"),
    (72, .jal .x1 "rlp_walk_next"),
    (80, .jal .x1 "rlp_walk_init"),
    (87, .jal .x1 "rlp_walk_next"),
    (96, .jal .x1 "rlp_walk_init"),
    (104, .jal .x1 "rlp_walk_next"),
    (111, .jal .x1 "rlp_content_to_u64_strict"),
    (116, .jal .x1 "rlp_walk_next"),
    (137, .la .x12 "bame_value"),
    (139, .jal .x1 "rlp_content_to_u256_be"),
    (141, .la .x31 "bame_value"),
    (158, .jal .x1 "rlp_content_to_u64_strict") ]

def balMapAccountMatchesFunction : String :=
  "bal_map_account_matches:\n" ++ emitProgramR balMapAccountMatches_prog balMapAccountMatches_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balMapAccountMatches_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balMapAccountMatchesFunction_eq_prog :
    balMapAccountMatchesFunction = "bal_map_account_matches:\n" ++ emitProgramR balMapAccountMatches_prog balMapAccountMatches_relocs := rfl

#guard balMapAccountMatchesFunction.startsWith "bal_map_account_matches:\n"
#guard balMapAccountMatches_prog.length = 180
/-! Compare a block-map final value with the reduced highest-BAI builder rows
    for the same address/component.  Balance and code use the last row at that
    BAI; nonce uses the maximum nonce at that BAI, matching the Amsterdam
    builder reducers.  A map row can be touched and then return to the
    pre-state, so the absence of a surviving builder row is accepted; the
    builder-side direction below remains the authority for rows that survive. -/
def balMapFinalValueMatches_prog : Program :=
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
    .LI .x5 (1 : Word),
    .BEQ .x9 .x5 (24 : BitVec 13),
    .LI .x5 (2 : Word),
    .BEQ .x9 .x5 (brOff (GuestAddrs.bal_map_final_value_matches + 264) (GuestAddrs.bal_map_final_value_matches + 60)),
    .LI .x5 (3 : Word),
    .BEQ .x9 .x5 (brOff (GuestAddrs.bal_map_final_value_matches + 440) (GuestAddrs.bal_map_final_value_matches + 68)),
    .JAL .x0 (jalOff (GuestAddrs.bal_map_final_value_matches + 632) (GuestAddrs.bal_map_final_value_matches + 72)),
    .LD .x5 .x8 (112 : BitVec 12),
    .LI .x6 (1 : Word),
    .AND .x5 .x5 .x6,
    .BEQ .x5 .x0 (brOff (GuestAddrs.bal_map_final_value_matches + 624) (GuestAddrs.bal_map_final_value_matches + 88)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_map_final_value_matches + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_map_final_value_matches + 92)),
    .LD .x18 .x5 (0 : BitVec 12),
    .AUIPC .x19 (laHi GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_map_final_value_matches + 104)),
    .ADDI .x19 .x19 (laLo GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_map_final_value_matches + 104)),
    .LI .x20 (0 : Word),
    .LI .x23 (0 : Word),
    .BGEU .x20 .x18 (brOff (GuestAddrs.bal_map_final_value_matches + 208) (GuestAddrs.bal_map_final_value_matches + 120)),
    .SLLI .x5 .x20 (6 : BitVec 6),
    .ADD .x6 .x19 .x5,
    .LI .x7 (20 : Word),
    .MV .x28 .x6,
    .MV .x29 .x8,
    .BEQ .x7 .x0 (32 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .LBU .x31 .x29 (0 : BitVec 12),
    .BNE .x30 .x31 (44 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x7 .x6 (24 : BitVec 12),
    .BEQ .x23 .x0 (8 : BitVec 13),
    .BLTU .x7 .x22 (16 : BitVec 13),
    .MV .x21 .x6,
    .MV .x22 .x7,
    .LI .x23 (1 : Word),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_map_final_value_matches + 120) (GuestAddrs.bal_map_final_value_matches + 204)),
    .BEQ .x23 .x0 (brOff (GuestAddrs.bal_map_final_value_matches + 624) (GuestAddrs.bal_map_final_value_matches + 208)),
    .LD .x5 .x8 (32 : BitVec 12),
    .LD .x6 .x21 (32 : BitVec 12),
    .BNE .x5 .x6 (brOff (GuestAddrs.bal_map_final_value_matches + 632) (GuestAddrs.bal_map_final_value_matches + 220)),
    .LD .x5 .x8 (40 : BitVec 12),
    .LD .x6 .x21 (40 : BitVec 12),
    .BNE .x5 .x6 (brOff (GuestAddrs.bal_map_final_value_matches + 632) (GuestAddrs.bal_map_final_value_matches + 232)),
    .LD .x5 .x8 (48 : BitVec 12),
    .LD .x6 .x21 (48 : BitVec 12),
    .BNE .x5 .x6 (brOff (GuestAddrs.bal_map_final_value_matches + 632) (GuestAddrs.bal_map_final_value_matches + 244)),
    .LD .x5 .x8 (56 : BitVec 12),
    .LD .x6 .x21 (56 : BitVec 12),
    .BNE .x5 .x6 (brOff (GuestAddrs.bal_map_final_value_matches + 632) (GuestAddrs.bal_map_final_value_matches + 256)),
    .JAL .x0 (jalOff (GuestAddrs.bal_map_final_value_matches + 624) (GuestAddrs.bal_map_final_value_matches + 260)),
    .LD .x5 .x8 (112 : BitVec 12),
    .LI .x6 (2 : Word),
    .AND .x5 .x5 .x6,
    .BEQ .x5 .x0 (brOff (GuestAddrs.bal_map_final_value_matches + 624) (GuestAddrs.bal_map_final_value_matches + 276)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_map_final_value_matches + 280)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_map_final_value_matches + 280)),
    .LD .x18 .x5 (0 : BitVec 12),
    .AUIPC .x19 (laHi GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_map_final_value_matches + 292)),
    .ADDI .x19 .x19 (laLo GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_map_final_value_matches + 292)),
    .LI .x20 (0 : Word),
    .LI .x23 (0 : Word),
    .BGEU .x20 .x18 (brOff (GuestAddrs.bal_map_final_value_matches + 420) (GuestAddrs.bal_map_final_value_matches + 308)),
    .SLLI .x5 .x20 (5 : BitVec 6),
    .SLLI .x7 .x20 (3 : BitVec 6),
    .ADD .x5 .x5 .x7,
    .ADD .x6 .x19 .x5,
    .LI .x7 (20 : Word),
    .MV .x28 .x6,
    .MV .x29 .x8,
    .BEQ .x7 .x0 (32 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .LBU .x31 .x29 (0 : BitVec 12),
    .BNE .x30 .x31 (60 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x7 .x6 (24 : BitVec 12),
    .BEQ .x23 .x0 (24 : BitVec 13),
    .BLTU .x7 .x22 (32 : BitVec 13),
    .BNE .x7 .x22 (16 : BitVec 13),
    .LD .x28 .x6 (32 : BitVec 12),
    .LD .x29 .x21 (32 : BitVec 12),
    .BGEU .x29 .x28 (16 : BitVec 13),
    .MV .x21 .x6,
    .MV .x22 .x7,
    .LI .x23 (1 : Word),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_map_final_value_matches + 308) (GuestAddrs.bal_map_final_value_matches + 416)),
    .BEQ .x23 .x0 (brOff (GuestAddrs.bal_map_final_value_matches + 624) (GuestAddrs.bal_map_final_value_matches + 420)),
    .LD .x5 .x8 (64 : BitVec 12),
    .LD .x6 .x21 (32 : BitVec 12),
    .BNE .x5 .x6 (brOff (GuestAddrs.bal_map_final_value_matches + 632) (GuestAddrs.bal_map_final_value_matches + 432)),
    .JAL .x0 (jalOff (GuestAddrs.bal_map_final_value_matches + 624) (GuestAddrs.bal_map_final_value_matches + 436)),
    .LD .x5 .x8 (112 : BitVec 12),
    .LI .x6 (4 : Word),
    .AND .x5 .x5 .x6,
    .BEQ .x5 .x0 (brOff (GuestAddrs.bal_map_final_value_matches + 624) (GuestAddrs.bal_map_final_value_matches + 452)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_code_count (GuestAddrs.bal_map_final_value_matches + 456)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_code_count (GuestAddrs.bal_map_final_value_matches + 456)),
    .LD .x18 .x5 (0 : BitVec 12),
    .AUIPC .x19 (laHi GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_map_final_value_matches + 468)),
    .ADDI .x19 .x19 (laLo GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_map_final_value_matches + 468)),
    .LI .x20 (0 : Word),
    .LI .x23 (0 : Word),
    .BGEU .x20 .x18 (brOff (GuestAddrs.bal_map_final_value_matches + 572) (GuestAddrs.bal_map_final_value_matches + 484)),
    .SLLI .x5 .x20 (6 : BitVec 6),
    .ADD .x6 .x19 .x5,
    .LI .x7 (20 : Word),
    .MV .x28 .x6,
    .MV .x29 .x8,
    .BEQ .x7 .x0 (32 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .LBU .x31 .x29 (0 : BitVec 12),
    .BNE .x30 .x31 (44 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LD .x7 .x6 (24 : BitVec 12),
    .BEQ .x23 .x0 (8 : BitVec 13),
    .BLTU .x7 .x22 (16 : BitVec 13),
    .MV .x21 .x6,
    .MV .x22 .x7,
    .LI .x23 (1 : Word),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_map_final_value_matches + 484) (GuestAddrs.bal_map_final_value_matches + 568)),
    .BEQ .x23 .x0 (52 : BitVec 13),
    .LD .x18 .x8 (88 : BitVec 12),
    .LD .x19 .x8 (80 : BitVec 12),
    .LD .x22 .x21 (32 : BitVec 12),
    .LI .x20 (0 : Word),
    .BEQ .x20 .x18 (32 : BitVec 13),
    .ADD .x5 .x19 .x20,
    .ADD .x6 .x22 .x20,
    .LBU .x7 .x5 (0 : BitVec 12),
    .LBU .x28 .x6 (0 : BitVec 12),
    .BNE .x7 .x28 (20 : BitVec 13),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
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

/-- Reloc side-table for `balMapFinalValueMatches_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balMapFinalValueMatches_relocs : RelocTable :=
  [ (23, .la .x5 "bal_builder_balance_count"),
    (26, .la .x19 "bal_builder_balance_changes"),
    (70, .la .x5 "bal_builder_nonce_count"),
    (73, .la .x19 "bal_builder_nonce_changes"),
    (114, .la .x5 "bal_builder_code_count"),
    (117, .la .x19 "bal_builder_code_changes") ]

def balMapFinalValueMatchesFunction : String :=
  "bal_map_final_value_matches:\n" ++ emitProgramR balMapFinalValueMatches_prog balMapFinalValueMatches_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balMapFinalValueMatches_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balMapFinalValueMatchesFunction_eq_prog :
    balMapFinalValueMatchesFunction = "bal_map_final_value_matches:\n" ++ emitProgramR balMapFinalValueMatches_prog balMapFinalValueMatches_relocs := rfl

#guard balMapFinalValueMatchesFunction.startsWith "bal_map_final_value_matches:\n"
#guard balMapFinalValueMatches_prog.length = 170
/-! Top-level DIR A only (#11183): map finals ↔ highest-BAI builder reduction.
    No supplied-BAL arguments; a0/a1 ignored. Returns 0 ok / 1 desync. -/
def balMapBuilderConsistent_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.bal_map_builder_consistent + 16)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.bal_map_builder_consistent + 16)),
    .LD .x8 .x5 (0 : BitVec 12),
    .LI .x9 (0 : Word),
    .BGEU .x9 .x8 (48 : BitVec 13),
    .SLLI .x6 .x9 (7 : BitVec 6),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .ADD .x7 .x7 .x6,
    .MV .x10 .x7,
    .LI .x11 (1 : Word),
    .JAL .x1 (jalOff GuestAddrs.bal_map_final_value_matches (GuestAddrs.bal_map_builder_consistent + 64)),
    .BNE .x10 .x0 (brOff (GuestAddrs.bal_map_builder_consistent + 216) (GuestAddrs.bal_map_builder_consistent + 68)),
    .ADDI .x9 .x9 (1 : BitVec 12),
    .JAL .x0 (-44 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.bal_map_builder_consistent + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.bal_map_builder_consistent + 80)),
    .LD .x8 .x5 (0 : BitVec 12),
    .LI .x9 (0 : Word),
    .BGEU .x9 .x8 (48 : BitVec 13),
    .SLLI .x6 .x9 (7 : BitVec 6),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .ADD .x7 .x7 .x6,
    .MV .x10 .x7,
    .LI .x11 (2 : Word),
    .JAL .x1 (jalOff GuestAddrs.bal_map_final_value_matches (GuestAddrs.bal_map_builder_consistent + 128)),
    .BNE .x10 .x0 (brOff (GuestAddrs.bal_map_builder_consistent + 216) (GuestAddrs.bal_map_builder_consistent + 132)),
    .ADDI .x9 .x9 (1 : BitVec 12),
    .JAL .x0 (-44 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.account_writes_count (GuestAddrs.bal_map_builder_consistent + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.account_writes_count (GuestAddrs.bal_map_builder_consistent + 144)),
    .LD .x8 .x5 (0 : BitVec 12),
    .LI .x9 (0 : Word),
    .BGEU .x9 .x8 (48 : BitVec 13),
    .SLLI .x6 .x9 (7 : BitVec 6),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (1975 : BitVec 12),
    .SLLI .x7 .x7 (19 : BitVec 6),
    .ADD .x7 .x7 .x6,
    .MV .x10 .x7,
    .LI .x11 (3 : Word),
    .JAL .x1 (jalOff GuestAddrs.bal_map_final_value_matches (GuestAddrs.bal_map_builder_consistent + 192)),
    .BNE .x10 .x0 (20 : BitVec 13),
    .ADDI .x9 .x9 (1 : BitVec 12),
    .JAL .x0 (-44 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balMapBuilderConsistent_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balMapBuilderConsistent_relocs : RelocTable :=
  [ (4, .la .x5 "account_writes_count"),
    (16, .jal .x1 "bal_map_final_value_matches"),
    (20, .la .x5 "account_writes_count"),
    (32, .jal .x1 "bal_map_final_value_matches"),
    (36, .la .x5 "account_writes_count"),
    (48, .jal .x1 "bal_map_final_value_matches") ]

def balMapBuilderConsistentFunction : String :=
  "bal_map_builder_consistent:\n" ++ emitProgramR balMapBuilderConsistent_prog balMapBuilderConsistent_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balMapBuilderConsistent_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balMapBuilderConsistentFunction_eq_prog :
    balMapBuilderConsistentFunction = "bal_map_builder_consistent:\n" ++ emitProgramR balMapBuilderConsistent_prog balMapBuilderConsistent_relocs := rfl

#guard balMapBuilderConsistentFunction.startsWith "bal_map_builder_consistent:\n"
#guard balMapBuilderConsistent_prog.length = 60
/-! Account-side reverse direction. -/
def balMapAccountCheckFunction : String :=
  "bal_map_account_check:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a0; mv s3, a1; mv a0, s0; mv a1, s1; jal ra, rlp_walk_init; bnez a2, .Lbmacc_fail; sd a0, 40(sp); sd a1, 48(sp)\n" ++
  "  ld a0, 40(sp); ld a1, 48(sp); jal ra, rlp_walk_next; bnez a1, .Lbmacc_fail; li t0, 20; bne a2, t0, .Lbmacc_fail; sub t0, a0, a2; sd t0, 56(sp)\n" ++
  "  mv a0, s0; mv a1, s1; ld a2, 56(sp); li a3, 1; jal ra, bal_map_check_account_field; bnez a0, .Lbmacc_fail\n" ++
  "  mv a0, s0; mv a1, s1; ld a2, 56(sp); li a3, 2; jal ra, bal_map_check_account_field; bnez a0, .Lbmacc_fail\n" ++
  "  mv a0, s0; mv a1, s1; ld a2, 56(sp); li a3, 3; jal ra, bal_map_check_account_field; bnez a0, .Lbmacc_fail; li a0, 0; j .Lbmacc_ret\n" ++
  ".Lbmacc_fail:\n  li a0, 1\n" ++
  ".Lbmacc_ret:\n  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 64; ret\n"

/-- Guest-linked: DIR A only. No RLP / supplied-BAL helpers. -/
def balMapBuilderConsistentFunctions : String :=
  balMapFinalValueMatchesFunction ++ "\n" ++
  balMapBuilderConsistentFunction ++ "\n"

/-- Probe-only B/C helpers (retired from guest top-level; keep for unit tests). -/
def balMapBuilderConsistentProbeHelpers : String :=
  balMapBuilderHasRowFunction ++ "\n" ++
  balMapCheckAccountFieldFunction ++ "\n" ++
  balMapFindSuppliedFunction ++ "\n" ++
  balMapAccountMatchesFunction ++ "\n" ++
  balMapAccountCheckFunction ++ "\n"

def balMapBuilderConsistentDataSection : String :=
  ".balign 8\n" ++
  "bame_value:\n  .zero 32\n" ++
  "bame_nonce:\n  .zero 8\n"

/-! Probe DIR A (#11183): map finals match highest-BAI builder → a0=0; desynced
    map balance value → a0=1; restored match → a0=0. No supplied-BAL body. -/
def ziskBalMapBuilderConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, bal_builder_balance_changes; li t1, 0x11; li t2, 20\n" ++
  ".Lbmprobe_addr:\n  beqz t2, .Lbmprobe_addr_done; sb t1, 0(t0); addi t0, t0, 1; addi t2, t2, -1; j .Lbmprobe_addr\n" ++
  ".Lbmprobe_addr_done:\n" ++
  "  la t0, bal_builder_balance_changes; li t1, 1; sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sb t1, 63(t0); sd t1, 24(t0)\n" ++
  "  la t0, bal_builder_balance_count; sd t1, 0(t0)\n" ++
  "  li t0, 0xbdb80000; la t2, bal_builder_balance_changes; li t3, 20\n" ++
  ".Lbmprobe_map_addr:\n  beqz t3, .Lbmprobe_map_fields; lbu t4, 0(t2); sb t4, 0(t0); addi t2, t2, 1; addi t0, t0, 1; addi t3, t3, -1; j .Lbmprobe_map_addr\n" ++
  ".Lbmprobe_map_fields:\n  li t0, 0xbdb80000; sd zero, 32(t0); sd zero, 40(t0); sd zero, 48(t0); sb t1, 63(t0); li t2, 1; sd t2, 112(t0); la t0, account_writes_count; sd t2, 0(t0)\n" ++
  -- match: map final == builder highest-BAI balance
  "  jal ra, bal_map_builder_consistent; li t1, 0xa0010000; sd a0, 0(t1)\n" ++
  -- desync: flip map balance low byte
  "  li t0, 0xbdb80000; li t1, 2; sb t1, 63(t0)\n" ++
  "  jal ra, bal_map_builder_consistent; li t1, 0xa0010000; sd a0, 8(t1)\n" ++
  -- restore match
  "  li t0, 0xbdb80000; li t1, 1; sb t1, 63(t0)\n" ++
  "  jal ra, bal_map_builder_consistent; li t1, 0xa0010000; sd a0, 16(t1)\n" ++
  "  j .Lbmprobe_done\n" ++
  balMapBuilderConsistentFunctions ++ "\n" ++
  ".Lbmprobe_done:"

def ziskBalMapBuilderConsistentDataSection : String :=
  ".balign 8\n" ++
  "account_writes_count:\n  .zero 8\n" ++
  "bal_builder_balance_count:\n  .zero 8\n" ++
  "bal_builder_balance_changes:\n  .zero 64\n" ++
  "bal_builder_nonce_count:\n  .zero 8\n" ++
  "bal_builder_nonce_changes:\n  .zero 40\n" ++
  "bal_builder_code_count:\n  .zero 8\n" ++
  "bal_builder_code_changes:\n  .zero 64\n" ++
  balMapBuilderConsistentDataSection

def ziskBalMapBuilderConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalMapBuilderConsistentPrologue
  dataAsm     := ziskBalMapBuilderConsistentDataSection
}

#guard (balMapBuilderConsistentFunctions.splitOn "bal_map_builder_consistent:").length == 2
#guard (balMapBuilderConsistentFunctions.splitOn "bal_map_final_value_matches:").length == 2
#guard (balMapBuilderConsistentFunctions.splitOn "bal_map_builder_has_row:").length == 1
#guard (balMapBuilderConsistentProbeHelpers.splitOn "bal_map_builder_has_row:").length == 2
#guard !(balMapBuilderConsistentFunction.contains "bv_bal_start")
#guard !(balMapBuilderConsistentFunction.contains "bv_bal_len")
#guard !(balMapBuilderConsistentFunction.contains "rlp_walk")
#guard !(balMapBuilderConsistentFunction.contains "bal_map_find_supplied")
#guard !(balMapBuilderConsistentFunction.contains "bal_map_account_check")
#guard ziskBalMapBuilderConsistentPrologue.contains "bal_map_builder_consistent"

end EvmAsm.Codegen
