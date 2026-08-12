/-
  EvmAsm.Codegen.Programs.BalSerializerTail

  Tail of BalSerializer split to keep Codegen/Programs files under the 1500-line cap.
-/

import EvmAsm.Codegen.Programs.BalSerializer

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Emit this account's `storage_changes` field into a keccak context.

    a0 = keccak ctx, a1 = address ptr (20 BE bytes), a2 = scratch (>= 33 bytes).

    Walks the same rows in the same order as `bal_serializer_measure_storage` and takes
    every nested length from `bal_serializer_measure_slot`, so the two passes cannot
    disagree about a header. Emission is streaming -- bytes are absorbed, never buffered
    -- so a header written before its payload cannot be backpatched, which is exactly
    why the lengths have to come from the shared measurer rather than from a local count.

    THE ADDRESS IS NOT EMITTED HERE and this routine must not use
    `bal_rlp_emit_address`: that helper REVERSES its input (`src[19-i]`), because it
    expects the address in the low bytes of an LE stack word. Builder rows hold the
    address big-endian already -- which is why `bal_serializer_addr_matches_be` exists --
    so passing a row through it would silently reverse every address. -/
def balSerializerEmitStorage_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
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
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_serializer_emit_storage + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_storage_change_count (GuestAddrs.bal_serializer_emit_storage + 56)),
    .LD .x19 .x5 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.bal_serializer_emit_storage + 432) (GuestAddrs.bal_serializer_emit_storage + 72)),
    .LI .x5 (96 : Word),
    .MUL .x6 .x20 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_emit_storage + 84)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_emit_storage + 84)),
    .ADD .x21 .x7 .x6,
    .MV .x10 .x9,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_emit_storage + 104)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_storage + 424) (GuestAddrs.bal_serializer_emit_storage + 108)),
    .MV .x10 .x9,
    .MV .x11 .x21,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_seen_before (GuestAddrs.bal_serializer_emit_storage + 124)),
    .BNE .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_storage + 424) (GuestAddrs.bal_serializer_emit_storage + 128)),
    .MV .x10 .x9,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_slot (GuestAddrs.bal_serializer_emit_storage + 140)),
    .MV .x22 .x10,
    .MV .x23 .x11,
    .MV .x10 .x8,
    .MV .x11 .x22,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_storage + 164)),
    .ADDI .x10 .x21 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_to_le (GuestAddrs.bal_serializer_emit_storage + 172)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_slot_le (GuestAddrs.bal_serializer_emit_storage + 180)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_slot_le (GuestAddrs.bal_serializer_emit_storage + 180)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_storage + 192)),
    .MV .x10 .x8,
    .MV .x11 .x23,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_storage + 208)),
    .LI .x24 (0 : Word),
    .BGEU .x24 .x19 (brOff (GuestAddrs.bal_serializer_emit_storage + 424) (GuestAddrs.bal_serializer_emit_storage + 216)),
    .LI .x5 (96 : Word),
    .MUL .x6 .x24 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_emit_storage + 228)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_storage_changes (GuestAddrs.bal_serializer_emit_storage + 228)),
    .ADD .x28 .x7 .x6,
    .SD .x2 .x28 (80 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_emit_storage + 252)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_storage + 416) (GuestAddrs.bal_serializer_emit_storage + 256)),
    .LD .x28 .x2 (80 : BitVec 12),
    .ADDI .x10 .x21 (32 : BitVec 12),
    .ADDI .x11 .x28 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_eq (GuestAddrs.bal_serializer_emit_storage + 272)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_storage + 416) (GuestAddrs.bal_serializer_emit_storage + 276)),
    .LD .x28 .x2 (80 : BitVec 12),
    .LD .x11 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 288)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 288)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_storage + 296)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 300)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 300)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_storage + 308)),
    .SD .x2 .x10 (88 : BitVec 12),
    .LD .x28 .x2 (80 : BitVec 12),
    .ADDI .x10 .x28 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_storage + 324)),
    .LD .x29 .x2 (88 : BitVec 12),
    .ADD .x29 .x29 .x10,
    .SD .x2 .x29 (88 : BitVec 12),
    .MV .x10 .x8,
    .LD .x11 .x2 (88 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_storage + 352)),
    .AUIPC .x5 (laHi GuestAddrs.bv_bal_shadow_emit_storage_changes (GuestAddrs.bal_serializer_emit_storage + 356)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_bal_shadow_emit_storage_changes (GuestAddrs.bal_serializer_emit_storage + 356)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 380)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_storage + 380)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_storage + 392)),
    .LD .x28 .x2 (80 : BitVec 12),
    .MV .x10 .x8,
    .ADDI .x11 .x28 (64 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_storage + 412)),
    .ADDI .x24 .x24 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_storage + 216) (GuestAddrs.bal_serializer_emit_storage + 420)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_storage + 72) (GuestAddrs.bal_serializer_emit_storage + 428)),
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
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitStorage_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitStorage_relocs : RelocTable :=
  [ (14, .la .x5 "bal_builder_storage_change_count"),
    (21, .la .x7 "bal_builder_storage_changes"),
    (26, .jal .x1 "bal_serializer_addr_matches_be"),
    (31, .jal .x1 "bal_serializer_slot_seen_before"),
    (35, .jal .x1 "bal_serializer_measure_slot"),
    (41, .jal .x1 "bal_rlp_emit_list_header"),
    (43, .jal .x1 "bal_serializer_slot_to_le"),
    (45, .la .x11 "bal_serializer_slot_le"),
    (48, .jal .x1 "bal_rlp_emit_scalar"),
    (52, .jal .x1 "bal_rlp_emit_list_header"),
    (57, .la .x7 "bal_builder_storage_changes"),
    (63, .jal .x1 "bal_serializer_addr_matches_be"),
    (68, .jal .x1 "bal_serializer_slot_eq"),
    (72, .la .x10 "bal_serializer_u64_field"),
    (74, .jal .x1 "bal_serializer_u64_to_field"),
    (75, .la .x10 "bal_serializer_u64_field"),
    (77, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (81, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (88, .jal .x1 "bal_rlp_emit_list_header"),
    (89, .la .x5 "bv_bal_shadow_emit_storage_changes"),
    (95, .la .x11 "bal_serializer_u64_field"),
    (98, .jal .x1 "bal_rlp_emit_scalar"),
    (103, .jal .x1 "bal_rlp_emit_scalar") ]

def balSerializerEmitStorageFunction : String :=
  "bal_serializer_emit_storage:\n" ++ emitProgramR balSerializerEmitStorage_prog balSerializerEmitStorage_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitStorage_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitStorageFunction_eq_prog :
    balSerializerEmitStorageFunction = "bal_serializer_emit_storage:\n" ++ emitProgramR balSerializerEmitStorage_prog balSerializerEmitStorage_relocs := rfl

#guard balSerializerEmitStorageFunction.startsWith "bal_serializer_emit_storage:\n"
#guard balSerializerEmitStorage_prog.length = 120
/-- Emit `storage_reads`: a flat list of slot scalars. a0 = ctx, a1 = address, a2 = scratch.

    Mirrors `bal_serializer_measure_reads`, including its use of
    `bal_serializer_addr_matches` -- the REVERSING comparator -- rather than the `_be`
    one. Read rows come from the exec log at `0xa1908780` and hold the address in the low
    bytes of an LE stack word, unlike the builder rows, which are big-endian. The two
    comparators are not interchangeable and picking the wrong one silently matches
    nothing. -/
def balSerializerEmitReads_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.storage_reads_count (GuestAddrs.bal_serializer_emit_reads + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.storage_reads_count (GuestAddrs.bal_serializer_emit_reads + 40)),
    .LD .x19 .x5 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.bal_serializer_emit_reads + 172) (GuestAddrs.bal_serializer_emit_reads + 56)),
    .LUI .x5 (20 : BitVec 20),
    .ADDIW .x5 .x5 (801 : BitVec 12),
    .SLLI .x5 .x5 (15 : BitVec 6),
    .ADDI .x5 .x5 (1920 : BitVec 12),
    .SLLI .x6 .x20 (6 : BitVec 6),
    .ADD .x29 .x5 .x6,
    .SD .x2 .x29 (48 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x29,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches (GuestAddrs.bal_serializer_emit_reads + 96)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_reads + 164) (GuestAddrs.bal_serializer_emit_reads + 100)),
    .LD .x29 .x2 (48 : BitVec 12),
    .ADDI .x10 .x29 (32 : BitVec 12),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_slot_written (GuestAddrs.bal_serializer_emit_reads + 116)),
    .BNE .x10 .x0 (44 : BitVec 13),
    .LD .x29 .x2 (48 : BitVec 12),
    .MV .x10 .x8,
    .ADDI .x11 .x29 (32 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_reads + 140)),
    .AUIPC .x5 (laHi GuestAddrs.bv_bal_shadow_emit_storage_reads (GuestAddrs.bal_serializer_emit_reads + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_bal_shadow_emit_storage_reads (GuestAddrs.bal_serializer_emit_reads + 144)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_reads + 56) (GuestAddrs.bal_serializer_emit_reads + 168)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitReads_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitReads_relocs : RelocTable :=
  [ (10, .la .x5 "storage_reads_count"),
    (24, .jal .x1 "bal_serializer_addr_matches"),
    (29, .jal .x1 "bal_serializer_slot_written"),
    (35, .jal .x1 "bal_rlp_emit_scalar"),
    (36, .la .x5 "bv_bal_shadow_emit_storage_reads") ]

def balSerializerEmitReadsFunction : String :=
  "bal_serializer_emit_reads:\n" ++ emitProgramR balSerializerEmitReads_prog balSerializerEmitReads_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitReads_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitReadsFunction_eq_prog :
    balSerializerEmitReadsFunction = "bal_serializer_emit_reads:\n" ++ emitProgramR balSerializerEmitReads_prog balSerializerEmitReads_relocs := rfl

#guard balSerializerEmitReadsFunction.startsWith "bal_serializer_emit_reads:\n"
#guard balSerializerEmitReads_prog.length = 51
/-- Emit `balance_changes`: one `[block_access_index, post_balance]` list per row.
    a0 = ctx, a1 = address, a2 = scratch. Mirrors `bal_serializer_measure_balance`. -/
def balSerializerEmitBalance_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_serializer_emit_balance + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_balance_count (GuestAddrs.bal_serializer_emit_balance + 40)),
    .LD .x19 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_builder_count (GuestAddrs.bal_serializer_emit_balance + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_builder_count (GuestAddrs.bal_serializer_emit_balance + 52)),
    .SD .x5 .x19 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.bal_serializer_emit_balance + 292) (GuestAddrs.bal_serializer_emit_balance + 68)),
    .LI .x5 (64 : Word),
    .MUL .x6 .x20 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_serializer_emit_balance + 80)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_balance_changes (GuestAddrs.bal_serializer_emit_balance + 80)),
    .ADD .x28 .x7 .x6,
    .SD .x2 .x28 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_bal_cmp_attempts (GuestAddrs.bal_serializer_emit_balance + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_bal_cmp_attempts (GuestAddrs.bal_serializer_emit_balance + 96)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x28 .x2 (48 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_emit_balance + 128)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_balance + 284) (GuestAddrs.bal_serializer_emit_balance + 132)),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 144)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 144)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_balance + 152)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 156)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 156)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_balance + 164)),
    .SD .x2 .x10 (56 : BitVec 12),
    .LD .x28 .x2 (48 : BitVec 12),
    .ADDI .x10 .x28 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_balance_to_le (GuestAddrs.bal_serializer_emit_balance + 180)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_emit_balance + 184)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_emit_balance + 184)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_balance + 192)),
    .LD .x29 .x2 (56 : BitVec 12),
    .ADD .x29 .x29 .x10,
    .SD .x2 .x29 (56 : BitVec 12),
    .MV .x10 .x8,
    .LD .x11 .x2 (56 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_balance + 220)),
    .AUIPC .x5 (laHi GuestAddrs.bv_bal_shadow_emit_balance_changes (GuestAddrs.bal_serializer_emit_balance + 224)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_bal_shadow_emit_balance_changes (GuestAddrs.bal_serializer_emit_balance + 224)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 248)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_balance + 248)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_balance + 260)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_emit_balance + 268)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_balance_le (GuestAddrs.bal_serializer_emit_balance + 268)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_balance + 280)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_balance + 68) (GuestAddrs.bal_serializer_emit_balance + 288)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitBalance_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitBalance_relocs : RelocTable :=
  [ (10, .la .x5 "bal_builder_balance_count"),
    (13, .la .x5 "bald_bal_builder_count"),
    (20, .la .x7 "bal_builder_balance_changes"),
    (24, .la .x5 "bald_bal_cmp_attempts"),
    (32, .jal .x1 "bal_serializer_addr_matches_be"),
    (36, .la .x10 "bal_serializer_u64_field"),
    (38, .jal .x1 "bal_serializer_u64_to_field"),
    (39, .la .x10 "bal_serializer_u64_field"),
    (41, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (45, .jal .x1 "bal_serializer_balance_to_le"),
    (46, .la .x10 "bal_serializer_balance_le"),
    (48, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (55, .jal .x1 "bal_rlp_emit_list_header"),
    (56, .la .x5 "bv_bal_shadow_emit_balance_changes"),
    (62, .la .x11 "bal_serializer_u64_field"),
    (65, .jal .x1 "bal_rlp_emit_scalar"),
    (67, .la .x11 "bal_serializer_balance_le"),
    (70, .jal .x1 "bal_rlp_emit_scalar") ]

def balSerializerEmitBalanceFunction : String :=
  "bal_serializer_emit_balance:\n" ++ emitProgramR balSerializerEmitBalance_prog balSerializerEmitBalance_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitBalance_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitBalanceFunction_eq_prog :
    balSerializerEmitBalanceFunction = "bal_serializer_emit_balance:\n" ++ emitProgramR balSerializerEmitBalance_prog balSerializerEmitBalance_relocs := rfl

#guard balSerializerEmitBalanceFunction.startsWith "bal_serializer_emit_balance:\n"
#guard balSerializerEmitBalance_prog.length = 81
/-- Emit `nonce_changes`: one `[block_access_index, new_nonce]` list per row. Both members
    are u64s widened through the scalar field, so BOTH need the widener -- unlike balance,
    whose post value is already a 32-byte field. a0 = ctx, a1 = address, a2 = scratch. -/
def balSerializerEmitNonce_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_serializer_emit_nonce + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_nonce_count (GuestAddrs.bal_serializer_emit_nonce + 40)),
    .LD .x19 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_non_builder_count (GuestAddrs.bal_serializer_emit_nonce + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_non_builder_count (GuestAddrs.bal_serializer_emit_nonce + 52)),
    .SD .x5 .x19 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.bal_serializer_emit_nonce + 344) (GuestAddrs.bal_serializer_emit_nonce + 68)),
    .SLLI .x6 .x20 (5 : BitVec 6),
    .SLLI .x7 .x20 (3 : BitVec 6),
    .ADD .x6 .x6 .x7,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_serializer_emit_nonce + 84)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_nonce_changes (GuestAddrs.bal_serializer_emit_nonce + 84)),
    .ADD .x28 .x7 .x6,
    .SD .x2 .x28 (48 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bald_non_cmp_attempts (GuestAddrs.bal_serializer_emit_nonce + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bald_non_cmp_attempts (GuestAddrs.bal_serializer_emit_nonce + 100)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x28 .x2 (48 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_emit_nonce + 132)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_nonce + 336) (GuestAddrs.bal_serializer_emit_nonce + 136)),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 148)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 148)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_nonce + 156)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 160)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 160)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_nonce + 168)),
    .SD .x2 .x10 (56 : BitVec 12),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (32 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 184)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 184)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_nonce + 192)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 196)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 196)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_nonce + 204)),
    .LD .x29 .x2 (56 : BitVec 12),
    .ADD .x29 .x29 .x10,
    .SD .x2 .x29 (56 : BitVec 12),
    .MV .x10 .x8,
    .LD .x11 .x2 (56 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_nonce + 232)),
    .AUIPC .x5 (laHi GuestAddrs.bv_bal_shadow_emit_nonce_changes (GuestAddrs.bal_serializer_emit_nonce + 236)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_bal_shadow_emit_nonce_changes (GuestAddrs.bal_serializer_emit_nonce + 236)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 264)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 264)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_nonce + 272)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 280)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 280)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_nonce + 292)),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (32 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 304)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 304)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_nonce + 312)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 320)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_nonce + 320)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_nonce + 332)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_nonce + 68) (GuestAddrs.bal_serializer_emit_nonce + 340)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitNonce_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitNonce_relocs : RelocTable :=
  [ (10, .la .x5 "bal_builder_nonce_count"),
    (13, .la .x5 "bald_non_builder_count"),
    (21, .la .x7 "bal_builder_nonce_changes"),
    (25, .la .x5 "bald_non_cmp_attempts"),
    (33, .jal .x1 "bal_serializer_addr_matches_be"),
    (37, .la .x10 "bal_serializer_u64_field"),
    (39, .jal .x1 "bal_serializer_u64_to_field"),
    (40, .la .x10 "bal_serializer_u64_field"),
    (42, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (46, .la .x10 "bal_serializer_u64_field"),
    (48, .jal .x1 "bal_serializer_u64_to_field"),
    (49, .la .x10 "bal_serializer_u64_field"),
    (51, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (58, .jal .x1 "bal_rlp_emit_list_header"),
    (59, .la .x5 "bv_bal_shadow_emit_nonce_changes"),
    (66, .la .x10 "bal_serializer_u64_field"),
    (68, .jal .x1 "bal_serializer_u64_to_field"),
    (70, .la .x11 "bal_serializer_u64_field"),
    (73, .jal .x1 "bal_rlp_emit_scalar"),
    (76, .la .x10 "bal_serializer_u64_field"),
    (78, .jal .x1 "bal_serializer_u64_to_field"),
    (80, .la .x11 "bal_serializer_u64_field"),
    (83, .jal .x1 "bal_rlp_emit_scalar") ]

def balSerializerEmitNonceFunction : String :=
  "bal_serializer_emit_nonce:\n" ++ emitProgramR balSerializerEmitNonce_prog balSerializerEmitNonce_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitNonce_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitNonceFunction_eq_prog :
    balSerializerEmitNonceFunction = "bal_serializer_emit_nonce:\n" ++ emitProgramR balSerializerEmitNonce_prog balSerializerEmitNonce_relocs := rfl

#guard balSerializerEmitNonceFunction.startsWith "bal_serializer_emit_nonce:\n"
#guard balSerializerEmitNonce_prog.length = 94
/-- Emit `code_changes`: one `[block_access_index, new_code]` list per row, where the code
    is a byte string rather than a scalar. a0 = ctx, a1 = address, a2 = scratch.

    The code length is measured through the throwaway-keccak route, exactly as
    `bal_serializer_measure_code` does, because a byte string's encoded size is not
    derivable from a fixed field width. -/
def balSerializerEmitCode_prog : Program :=
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
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_code_count (GuestAddrs.bal_serializer_emit_code + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_code_count (GuestAddrs.bal_serializer_emit_code + 40)),
    .LD .x19 .x5 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.bal_serializer_emit_code + 276) (GuestAddrs.bal_serializer_emit_code + 56)),
    .SLLI .x6 .x20 (6 : BitVec 6),
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_serializer_emit_code + 64)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_code_changes (GuestAddrs.bal_serializer_emit_code + 64)),
    .ADD .x28 .x7 .x6,
    .SD .x2 .x28 (48 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_addr_matches_be (GuestAddrs.bal_serializer_emit_code + 88)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.bal_serializer_emit_code + 268) (GuestAddrs.bal_serializer_emit_code + 92)),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x11 .x28 (24 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 104)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 104)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_u64_to_field (GuestAddrs.bal_serializer_emit_code + 112)),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 116)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 116)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_scalar_rlp_len (GuestAddrs.bal_serializer_emit_code + 124)),
    .SD .x2 .x10 (56 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.bal_serializer_throwaway_ctx (GuestAddrs.bal_serializer_emit_code + 132)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bal_serializer_throwaway_ctx (GuestAddrs.bal_serializer_emit_code + 132)),
    .AUIPC .x11 (laHi GuestAddrs.bal_rlp_emit_bytes (GuestAddrs.bal_serializer_emit_code + 140)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_rlp_emit_bytes (GuestAddrs.bal_serializer_emit_code + 140)),
    .LD .x28 .x2 (48 : BitVec 12),
    .LD .x12 .x28 (32 : BitVec 12),
    .LD .x13 .x28 (40 : BitVec 12),
    .AUIPC .x14 (laHi GuestAddrs.bal_serializer_hdr_scratch (GuestAddrs.bal_serializer_emit_code + 160)),
    .ADDI .x14 .x14 (laLo GuestAddrs.bal_serializer_hdr_scratch (GuestAddrs.bal_serializer_emit_code + 160)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_measure_into_throwaway (GuestAddrs.bal_serializer_emit_code + 168)),
    .LD .x29 .x2 (56 : BitVec 12),
    .ADD .x29 .x29 .x10,
    .SD .x2 .x29 (56 : BitVec 12),
    .MV .x10 .x8,
    .LD .x11 .x2 (56 : BitVec 12),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_code + 196)),
    .AUIPC .x5 (laHi GuestAddrs.bv_bal_shadow_emit_code_changes (GuestAddrs.bal_serializer_emit_code + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_bal_shadow_emit_code_changes (GuestAddrs.bal_serializer_emit_code + 200)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 224)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_u64_field (GuestAddrs.bal_serializer_emit_code + 224)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_scalar (GuestAddrs.bal_serializer_emit_code + 236)),
    .LD .x28 .x2 (48 : BitVec 12),
    .MV .x10 .x8,
    .LD .x11 .x28 (32 : BitVec 12),
    .LD .x12 .x28 (40 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.bal_serializer_hdr_scratch (GuestAddrs.bal_serializer_emit_code + 256)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bal_serializer_hdr_scratch (GuestAddrs.bal_serializer_emit_code + 256)),
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_bytes (GuestAddrs.bal_serializer_emit_code + 264)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_emit_code + 56) (GuestAddrs.bal_serializer_emit_code + 272)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitCode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitCode_relocs : RelocTable :=
  [ (10, .la .x5 "bal_builder_code_count"),
    (16, .la .x7 "bal_builder_code_changes"),
    (22, .jal .x1 "bal_serializer_addr_matches_be"),
    (26, .la .x10 "bal_serializer_u64_field"),
    (28, .jal .x1 "bal_serializer_u64_to_field"),
    (29, .la .x10 "bal_serializer_u64_field"),
    (31, .jal .x1 "bal_rlp_scalar_rlp_len"),
    (33, .la .x10 "bal_serializer_throwaway_ctx"),
    (35, .la .x11 "bal_rlp_emit_bytes"),
    (40, .la .x14 "bal_serializer_hdr_scratch"),
    (42, .jal .x1 "bal_rlp_measure_into_throwaway"),
    (49, .jal .x1 "bal_rlp_emit_list_header"),
    (50, .la .x5 "bv_bal_shadow_emit_code_changes"),
    (56, .la .x11 "bal_serializer_u64_field"),
    (59, .jal .x1 "bal_rlp_emit_scalar"),
    (64, .la .x13 "bal_serializer_hdr_scratch"),
    (66, .jal .x1 "bal_rlp_emit_bytes") ]

def balSerializerEmitCodeFunction : String :=
  "bal_serializer_emit_code:\n" ++ emitProgramR balSerializerEmitCode_prog balSerializerEmitCode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitCode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitCodeFunction_eq_prog :
    balSerializerEmitCodeFunction = "bal_serializer_emit_code:\n" ++ emitProgramR balSerializerEmitCode_prog balSerializerEmitCode_relocs := rfl

#guard balSerializerEmitCodeFunction.startsWith "bal_serializer_emit_code:\n"
#guard balSerializerEmitCode_prog.length = 77
/-- Emit one account's `AccountChanges`. a0 = ctx, a1 = address, a2 = scratch.

    `bal_serializer_measure_account` MUST have run for this address first: every header
    here is read from the length table, never recomputed. The five field headers come
    from table entries +8..+40 and the account header from +0.

    FIELD ORDER, verified against the `AccountChanges` class definition at
    `block_access_lists.py:174-208` rather than taken from prose: `address`,
    `storage_changes`, `storage_reads`, `balance_changes`, `nonce_changes`,
    `code_changes`. An RLP list is positional, so a swapped pair is a well-formed
    account with two fields exchanged -- and if both are empty lists, byte-identical.
    That is why the order is cited to the class rather than to a docstring.

    Accounts are NOT filtered: `_build_from_builder` appends every entry in
    `builder.accounts`, so an account whose fields are all empty still emits as five
    empty lists. `emit_outer` walks every account for the same reason. -/
def balSerializerEmitAccount_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 32)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 52)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (20 : Word),
    .MV .x13 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_bytes (GuestAddrs.bal_serializer_emit_account + 72)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 76)),
    .LD .x11 .x5 (8 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 96)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_storage (GuestAddrs.bal_serializer_emit_account + 112)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 116)),
    .LD .x11 .x5 (16 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 136)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_reads (GuestAddrs.bal_serializer_emit_account + 152)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 156)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 156)),
    .LD .x11 .x5 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 176)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_balance (GuestAddrs.bal_serializer_emit_account + 192)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 196)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 196)),
    .LD .x11 .x5 (32 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 216)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_nonce (GuestAddrs.bal_serializer_emit_account + 232)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 236)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_len_table (GuestAddrs.bal_serializer_emit_account + 236)),
    .LD .x11 .x5 (40 : BitVec 12),
    .MV .x10 .x8,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_account + 256)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_code (GuestAddrs.bal_serializer_emit_account + 272)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitAccount_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitAccount_relocs : RelocTable :=
  [ (8, .la .x5 "bal_serializer_len_table"),
    (13, .jal .x1 "bal_rlp_emit_list_header"),
    (18, .jal .x1 "bal_rlp_emit_bytes"),
    (19, .la .x5 "bal_serializer_len_table"),
    (24, .jal .x1 "bal_rlp_emit_list_header"),
    (28, .jal .x1 "bal_serializer_emit_storage"),
    (29, .la .x5 "bal_serializer_len_table"),
    (34, .jal .x1 "bal_rlp_emit_list_header"),
    (38, .jal .x1 "bal_serializer_emit_reads"),
    (39, .la .x5 "bal_serializer_len_table"),
    (44, .jal .x1 "bal_rlp_emit_list_header"),
    (48, .jal .x1 "bal_serializer_emit_balance"),
    (49, .la .x5 "bal_serializer_len_table"),
    (54, .jal .x1 "bal_rlp_emit_list_header"),
    (58, .jal .x1 "bal_serializer_emit_nonce"),
    (59, .la .x5 "bal_serializer_len_table"),
    (64, .jal .x1 "bal_rlp_emit_list_header"),
    (68, .jal .x1 "bal_serializer_emit_code") ]

def balSerializerEmitAccountFunction : String :=
  "bal_serializer_emit_account:\n" ++ emitProgramR balSerializerEmitAccount_prog balSerializerEmitAccount_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitAccount_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitAccountFunction_eq_prog :
    balSerializerEmitAccountFunction = "bal_serializer_emit_account:\n" ++ emitProgramR balSerializerEmitAccount_prog balSerializerEmitAccount_relocs := rfl

#guard balSerializerEmitAccountFunction.startsWith "bal_serializer_emit_account:\n"
#guard balSerializerEmitAccount_prog.length = 75
/-- Outer accumulation: the BAL is a list of `AccountChanges`, so its payload is the sum
    of each account's ENCODED size, not of their payloads. a0 (out) = that sum, also
    stored to `bal_serializer_outer_payload`.

    Summing payloads instead of encoded sizes is the same error the account measurer
    guards against one level down, and it is silent in exactly the same way: the result
    is a well-formed list whose header is short by one header per account. -/
def balSerializerMeasureOuter_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_account_count (GuestAddrs.bal_serializer_measure_outer + 24)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_account_count (GuestAddrs.bal_serializer_measure_outer + 24)),
    .LD .x9 .x5 (0 : BitVec 12),
    .LI .x18 (0 : Word),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x9 (56 : BitVec 13),
    .LI .x5 (24 : Word),
    .MUL .x6 .x19 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_accounts (GuestAddrs.bal_serializer_measure_outer + 56)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_accounts (GuestAddrs.bal_serializer_measure_outer + 56)),
    .ADD .x8 .x7 .x6,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_account (GuestAddrs.bal_serializer_measure_outer + 72)),
    .MV .x30 .x10,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_list_header_len (GuestAddrs.bal_serializer_measure_outer + 80)),
    .ADD .x18 .x18 .x30,
    .ADD .x18 .x18 .x10,
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-52 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_outer_payload (GuestAddrs.bal_serializer_measure_outer + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_outer_payload (GuestAddrs.bal_serializer_measure_outer + 100)),
    .SD .x5 .x18 (0 : BitVec 12),
    .MV .x10 .x18,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerMeasureOuter_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerMeasureOuter_relocs : RelocTable :=
  [ (6, .la .x5 "bal_builder_account_count"),
    (14, .la .x7 "bal_builder_accounts"),
    (18, .jal .x1 "bal_serializer_measure_account"),
    (20, .jal .x1 "bal_rlp_list_header_len"),
    (25, .la .x5 "bal_serializer_outer_payload") ]

def balSerializerMeasureOuterFunction : String :=
  "bal_serializer_measure_outer:\n" ++ emitProgramR balSerializerMeasureOuter_prog balSerializerMeasureOuter_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerMeasureOuter_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerMeasureOuterFunction_eq_prog :
    balSerializerMeasureOuterFunction = "bal_serializer_measure_outer:\n" ++ emitProgramR balSerializerMeasureOuter_prog balSerializerMeasureOuter_relocs := rfl

#guard balSerializerMeasureOuterFunction.startsWith "bal_serializer_measure_outer:\n"
#guard balSerializerMeasureOuter_prog.length = 36
/-- Emit the whole block access list. a0 = keccak ctx, a1 = scratch (>= 33 bytes).

    THE ACCOUNT LIST MUST ALREADY BE IN CANONICAL ORDER. EIP-7928 sorts accounts by
    address, and this walks `bal_builder_accounts` in storage order -- it does not sort.
    Ordering is `bal_canonical_sort`'s job and must happen before this runs; emitting an
    unsorted list produces a perfectly well-formed BAL with the wrong hash, which is the
    one failure the digest comparison cannot localise.

    Each account is re-measured immediately before it is emitted, because the length
    table holds ONE account at a time and the emitters read their headers from it. -/
def balSerializerEmitOuter_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_outer (GuestAddrs.bal_serializer_emit_outer + 32)),
    .MV .x10 .x8,
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_outer_payload (GuestAddrs.bal_serializer_emit_outer + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_outer_payload (GuestAddrs.bal_serializer_emit_outer + 40)),
    .LD .x11 .x5 (0 : BitVec 12),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.bal_rlp_emit_list_header (GuestAddrs.bal_serializer_emit_outer + 56)),
    .AUIPC .x5 (laHi GuestAddrs.bal_builder_account_count (GuestAddrs.bal_serializer_emit_outer + 60)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_builder_account_count (GuestAddrs.bal_serializer_emit_outer + 60)),
    .LD .x18 .x5 (0 : BitVec 12),
    .LI .x19 (0 : Word),
    .BGEU .x19 .x18 (brOff (GuestAddrs.bal_serializer_emit_outer + 140) (GuestAddrs.bal_serializer_emit_outer + 76)),
    .LI .x5 (24 : Word),
    .MUL .x6 .x19 .x5,
    .AUIPC .x7 (laHi GuestAddrs.bal_builder_accounts (GuestAddrs.bal_serializer_emit_outer + 88)),
    .ADDI .x7 .x7 (laLo GuestAddrs.bal_builder_accounts (GuestAddrs.bal_serializer_emit_outer + 88)),
    .ADD .x28 .x7 .x6,
    .SD .x2 .x28 (40 : BitVec 12),
    .MV .x10 .x28,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_measure_account (GuestAddrs.bal_serializer_emit_outer + 108)),
    .LD .x28 .x2 (40 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x28,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_emit_account (GuestAddrs.bal_serializer_emit_outer + 128)),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-60 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerEmitOuter_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerEmitOuter_relocs : RelocTable :=
  [ (8, .jal .x1 "bal_serializer_measure_outer"),
    (10, .la .x5 "bal_serializer_outer_payload"),
    (14, .jal .x1 "bal_rlp_emit_list_header"),
    (15, .la .x5 "bal_builder_account_count"),
    (22, .la .x7 "bal_builder_accounts"),
    (27, .jal .x1 "bal_serializer_measure_account"),
    (32, .jal .x1 "bal_serializer_emit_account") ]

def balSerializerEmitOuterFunction : String :=
  "bal_serializer_emit_outer:\n" ++ emitProgramR balSerializerEmitOuter_prog balSerializerEmitOuter_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerEmitOuter_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerEmitOuterFunction_eq_prog :
    balSerializerEmitOuterFunction = "bal_serializer_emit_outer:\n" ++ emitProgramR balSerializerEmitOuter_prog balSerializerEmitOuter_relocs := rfl

#guard balSerializerEmitOuterFunction.startsWith "bal_serializer_emit_outer:\n"
#guard balSerializerEmitOuter_prog.length = 42
/-- Sort the accounts into canonical order and hash the rebuilt BAL.
    a0 = scratch (>= 33 bytes), a1 = 32-byte output pointer.
    `bal_serializer_rebuild_hash` returns 0, or the canonical sort's OWN nonzero status
    (1, 2 or 3). It deliberately does NOT normalise: `bal_serializer_verify` is the
    routine that maps any nonzero to its own code 2, and the specific sort code stays in
    `bal_serializer_sort_status`. Naming the routine in this sentence is deliberate --
    the two contracts sit twelve lines apart and both describe an a0-out with small
    integer codes, which is enough for proximity to substitute for attribution.

    Split out from `bal_serializer_verify` so it can be executed on its own: the probe
    seeds the accounts OUT of order and checks the digest still matches the in-order one,
    which is the only way to demonstrate that the sort actually runs. Verifying that
    through the full comparator would need a real SSZ payload for the supplied side.

    THE SORT LIVES HERE, NOT IN A CALLER. Ordering is part of the encoding: an unsorted
    emission is a well-formed BAL with the wrong hash, and it is the single failure a
    digest comparison cannot localise, because every byte is individually correct and
    only the sequence is wrong. Leaving it to a caller makes the one unlocalisable
    failure the easiest to cause.

    Accounts are 20-byte rows sorted on one BIG-ENDIAN 20-byte segment: offset byte 0,
    width byte 0x94 -- that is `0x80 | 20`, the 0x80 being the big-endian flag -- so the
    descriptor is 0x9400 (GH #11054: this used to cite `bal_sort_account_writes`, which
    passed the same value and has since been deleted as unreachable -- the CONSTANT is the
    contract here, not that routine). Writing 0x1400
    instead declares a big-endian address little-endian; it does not sort wrongly and
    carry on, it faults on a bad pointer inside the sort. -/
def balSerializerRebuildHashFunction : String :=
  "bal_serializer_rebuild_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  -- `_build_from_builder` first folds the block account-read set into the
  -- builder as empty touched-account entries.  This must precede every sort:
  -- the account walk below is the single source of outer BAL rows.
  "  jal ra, bal_builder_incorporate_touched_accounts\n" ++
  -- SEVEN ORDERING RULES (block_access_lists.py:539-579), all of them here so the
  -- emitters can stay order-free. Every stride below is 8-ALIGNED, per the rule on
  -- `balBuilderAccountRowBytes` -- the sort swaps rows with ld/sd.
  --
  -- The storage sort carries TWO rules in one pass: sorting the change rows by
  -- (address, slot, block_access_index) makes slots ascend within an account AND
  -- changes ascend by index within a slot, because the emitter walks rows in order and
  -- takes each slot at its first occurrence. `balSortBuilderStorageSegments` is exactly
  -- that key and already exists -- offset 0 width 20 BE, offset 32 width 32 BE, offset
  -- 24 width 8 LE.
  "  la a0, bal_builder_storage_changes\n" ++
  "  la t0, bal_builder_storage_change_count; ld a1, 0(t0)\n" ++
  "  li a2, 96; li a3, 0x0818a0209400; li a4, 3; li a5, " ++
  toString balBuilderStorageChangeCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbsrh_ret\n" ++
  -- storage_reads by slot value. The read row's slot is an LE stack word at +32, so the
  -- segment carries no BE flag: offset 0x20, width 0x20.
  "  li a0, 0xa1908780\n" ++
  "  la t0, storage_reads_count; ld a1, 0(t0)\n" ++
  "  li a2, 64; li a3, 0x2020; li a4, 1; li a5, " ++
  toString balBuilderStorageReadsCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbsrh_ret\n" ++
  -- balance, nonce and code each by (address, block_access_index): segment 0 is the
  -- BE20 address, segment 1 the native-LE u64 index at +24 -> 0x08189400.
  "  la a0, bal_builder_balance_changes\n" ++
  "  la t0, bal_builder_balance_count; ld a1, 0(t0)\n" ++
  "  li a2, 64; li a3, 0x08189400; li a4, 2; li a5, " ++
  toString balBuilderBalanceCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbsrh_ret\n" ++
  "  la a0, bal_builder_nonce_changes\n" ++
  "  la t0, bal_builder_nonce_count; ld a1, 0(t0)\n" ++
  "  li a2, 40; li a3, 0x08189400; li a4, 2; li a5, " ++
  toString balBuilderNonceCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbsrh_ret\n" ++
  "  la a0, bal_builder_code_changes\n" ++
  "  la t0, bal_builder_code_count; ld a1, 0(t0)\n" ++
  "  li a2, 64; li a3, 0x08189400; li a4, 2; li a5, " ++
  toString balBuilderCodeCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbsrh_ret\n" ++
  "  la a0, bal_builder_accounts\n" ++
  "  la t0, bal_builder_account_count; ld a1, 0(t0)\n" ++
  "  li a2, 24; li a3, 0x9400; li a4, 1; li a5, " ++
  toString balBuilderAccountCapacity ++ "\n" ++
  "  jal ra, bal_canonical_sort\n" ++
  "  la t0, bal_serializer_sort_status; sd a0, 0(t0)\n" ++
  "  beqz a0, .Lbsrh_sorted\n" ++
  "  j .Lbsrh_ret\n" ++
  ".Lbsrh_sorted:\n" ++
  -- Streaming: nothing is buffered, so no size bound applies to the rebuilt BAL.
  "  la a0, bal_serializer_rebuilt_ctx; jal ra, keccak_init\n" ++
  "  la a0, bal_serializer_rebuilt_ctx; mv a1, s0; jal ra, bal_serializer_emit_outer\n" ++
  "  la a0, bal_serializer_rebuilt_ctx; mv a1, s1; jal ra, keccak_final\n" ++
  "  li a0, 0\n" ++
  ".Lbsrh_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n"

/-- Rebuild the block access list and compare its hash against the supplied one.
    a0 = SSZ_BASE, a1 = scratch (>= 33 bytes).
    `bal_serializer_verify` returns 0 if the rebuilt BAL hashes to the supplied BAL's
    hash, 1 if it does not, and 2 if the canonical sort failed -- normalising ANY nonzero
    from `bal_serializer_rebuild_hash` (which may be 1, 2 or 3) to 2, and leaving the
    specific code in `bal_serializer_sort_status`.

    This is the spec's own check rather than an approximation of it: EIP-7928 commits the
    BAL through a hash, so agreeing on the hash is agreeing on every byte. Nothing weaker
    substitutes -- matching lengths, counts and field sets are all satisfiable by a BAL
    that hashes differently.

    WIRED AND BINDING since GH #10680 (see GH #11258 for the history of this
    docstring claiming otherwise). Called from the shadow-verify block in
    `BlockVerdictReceiptsTail.lean` (`jal ra, bal_serializer_verify`); its return is
    stored to `bv_bal_shadow_status`; and the status is bound into the verdict there --
    a digest mismatch rejects with `bv_fail_code = 60`, a rebuild failure with `61`,
    checked on ACCEPT paths only (the ACCEPT-only guard is what keeps the FR delta
    attributable). The binding contract is pinned by `#guard`s at the bottom of that
    file, so an edit cannot loosen it silently. -/
def balSerializerVerify_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .MV .x10 .x11,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_rebuilt_hash (GuestAddrs.bal_serializer_verify + 20)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_rebuilt_hash (GuestAddrs.bal_serializer_verify + 20)),
    .JAL .x1 (jalOff GuestAddrs.bal_serializer_rebuild_hash (GuestAddrs.bal_serializer_verify + 28)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (2 : Word),
    .JAL .x0 (jalOff (GuestAddrs.bal_serializer_verify + 136) (GuestAddrs.bal_serializer_verify + 40)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bal_serializer_supplied_hash (GuestAddrs.bal_serializer_verify + 48)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bal_serializer_supplied_hash (GuestAddrs.bal_serializer_verify + 48)),
    .JAL .x1 (jalOff GuestAddrs.block_access_list_hash (GuestAddrs.bal_serializer_verify + 56)),
    .AUIPC .x5 (laHi GuestAddrs.bal_serializer_rebuilt_hash (GuestAddrs.bal_serializer_verify + 60)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bal_serializer_rebuilt_hash (GuestAddrs.bal_serializer_verify + 60)),
    .AUIPC .x6 (laHi GuestAddrs.bal_serializer_supplied_hash (GuestAddrs.bal_serializer_verify + 68)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bal_serializer_supplied_hash (GuestAddrs.bal_serializer_verify + 68)),
    .LD .x7 .x5 (0 : BitVec 12),
    .LD .x28 .x6 (0 : BitVec 12),
    .BNE .x7 .x28 (48 : BitVec 13),
    .LD .x7 .x5 (8 : BitVec 12),
    .LD .x28 .x6 (8 : BitVec 12),
    .BNE .x7 .x28 (36 : BitVec 13),
    .LD .x7 .x5 (16 : BitVec 12),
    .LD .x28 .x6 (16 : BitVec 12),
    .BNE .x7 .x28 (24 : BitVec 13),
    .LD .x7 .x5 (24 : BitVec 12),
    .LD .x28 .x6 (24 : BitVec 12),
    .BNE .x7 .x28 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balSerializerVerify_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balSerializerVerify_relocs : RelocTable :=
  [ (5, .la .x11 "bal_serializer_rebuilt_hash"),
    (7, .jal .x1 "bal_serializer_rebuild_hash"),
    (12, .la .x11 "bal_serializer_supplied_hash"),
    (14, .jal .x1 "block_access_list_hash"),
    (15, .la .x5 "bal_serializer_rebuilt_hash"),
    (17, .la .x6 "bal_serializer_supplied_hash") ]

def balSerializerVerifyFunction : String :=
  "bal_serializer_verify:\n" ++ emitProgramR balSerializerVerify_prog balSerializerVerify_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balSerializerVerify_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balSerializerVerifyFunction_eq_prog :
    balSerializerVerifyFunction = "bal_serializer_verify:\n" ++ emitProgramR balSerializerVerify_prog balSerializerVerify_relocs := rfl

#guard balSerializerVerifyFunction.startsWith "bal_serializer_verify:\n"
#guard balSerializerVerify_prog.length = 38
/-! ## Guards on the RETURN CODES against their documented contracts

    A guard class this file did not have. Every other guard here pins emitted text or
    field selection; none pinned what a routine RETURNS against what its docstring says
    it returns. That gap is not hypothetical: a reviewer read `verify`'s 0/1/2 contract
    as applying to `rebuild_hash`'s bail path and reported a defect that was not there,
    because nothing in the code said which routine owned which contract. -/

-- `verify` NORMALISES. Without this the conversion looks redundant -- rebuild_hash
-- already returns nonzero -- and deleting it would silently widen verify's contract to
-- leak sort codes 1 and 3, where 1 collides with "hash does not match". The generated
-- Program length pin above plus the fixture byte-identity check protect this branch
-- after conversion (the old source-level semicolon guard no longer matches the
-- one-instruction-per-line rendering).

-- `rebuild_hash` does NOT normalise: it propagates the sort's own code, as its contract
-- says. Stated as the ABSENCE of the conversion, because absence is site-independent
-- while presence could be satisfied by any `li a0, 2` elsewhere in the def.
#guard (balSerializerRebuildHashFunction.splitOn "li a0, 2").length == 1


end EvmAsm.Codegen
