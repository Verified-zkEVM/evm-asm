/-
  EvmAsm.Codegen.Programs.BloomAddValue

  Atomic log-bloom helper split out of `Bloom.lean`.

  Hosts:
    K148  bloom_add_value

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestLayout
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bloom_add_value -- PR-K148

    Add a single value to a 2048-bit (256-byte) Ethereum log
    bloom filter, following the yellow-paper / EIP-2718
    definition:

      1. h = keccak256(value)
      2. for idx in {0, 2, 4}:
           raw     = u16(h[idx..idx+2]) & 0x7FF      -- low 11 bits
           bit     = 0x7FF - raw                     -- inverted
           byte_i  = bit / 8
           bit_pos = 7 - (bit mod 8)                 -- MSB-first in byte
           bloom[byte_i] |= 1 << bit_pos

    Called twice for each log:
      * once with `value = log.address` (20 bytes)
      * once per topic with `value = topic` (32 bytes)

    Building block for `logs_bloom` construction in receipt
    encoding, which in turn feeds `block.bloom` (the per-block
    bloom = OR of every receipt's bloom). Used by:
      * `apply_body` when assembling each tx's receipt.
      * `block_validate_logs_bloom` to recompute the header's
        bloom field from receipts.

    Composes:
      - `zkvm_keccak256` (HashBridge) — hashes the value.

    Calling convention:
      a0 (input)  : bloom ptr (256 bytes, mutable, in-place OR)
      a1 (input)  : value ptr
      a2 (input)  : value byte length
      ra (input)  : return
      a0 (output) : 0 (always succeeds).

    Bloom is mutated in place; the caller owns the buffer and
    is responsible for zero-initialising it before the first
    `bloom_add_value` call of a logs sequence.

    Layout is a parameter (GH #10753): this module imports only the
    stable `GuestLayout` type, not the generated `GuestAddrs` instance. -/
def bloomAddValue_prog (L : GuestLayout) : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x9,
    .MV .x11 .x18,
    .AUIPC .x12 (laHi L.bav_hash (L.bloom_add_value + 40)),
    .ADDI .x12 .x12 (laLo L.bav_hash (L.bloom_add_value + 40)),
    .JAL .x1 (jalOff L.zkvm_keccak256 (L.bloom_add_value + 48)),
    .AUIPC .x5 (laHi L.bav_hash (L.bloom_add_value + 52)),
    .ADDI .x5 .x5 (laLo L.bav_hash (L.bloom_add_value + 52)),
    .LI .x6 (0 : Word),
    .LI .x7 (6 : Word),
    .BGE .x6 .x7 (84 : BitVec 13),
    .ADD .x28 .x5 .x6,
    .LBU .x29 .x28 (0 : BitVec 12),
    .LBU .x30 .x28 (1 : BitVec 12),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .OR .x29 .x29 .x30,
    .LI .x30 (2047 : Word),
    .AND .x29 .x29 .x30,
    .SUB .x29 .x30 .x29,
    .SRLI .x30 .x29 (3 : BitVec 6),
    .ANDI .x31 .x29 (7 : BitVec 12),
    .LI .x29 (7 : Word),
    .SUB .x31 .x29 .x31,
    .LI .x29 (1 : Word),
    .SLL .x31 .x29 .x31,
    .ADD .x30 .x8 .x30,
    .LBU .x29 .x30 (0 : BitVec 12),
    .OR .x29 .x29 .x31,
    .SB .x30 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (2 : BitVec 12),
    .JAL .x0 (-84 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bloomAddValue_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bloomAddValue_relocs : RelocTable :=
  [ (10, .la .x12 "bav_hash"),
    (12, .jal .x1 "zkvm_keccak256"),
    (13, .la .x5 "bav_hash") ]

/-- Emission uses `GuestLayout.zero`: `emitProgramR` keeps `la`/`jal` symbolic
    via `bloomAddValue_relocs`, so concrete immediates do not appear in the string. -/
def bloomAddValueFunction : String :=
  "bloom_add_value:\n" ++ emitProgramR (bloomAddValue_prog .zero) bloomAddValue_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bloomAddValue_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp.
    Guard is keyed on the emitted string, not on a routine identifier. -/
theorem bloomAddValueFunction_eq_prog :
    bloomAddValueFunction =
      "bloom_add_value:\n" ++ emitProgramR (bloomAddValue_prog .zero) bloomAddValue_relocs := rfl

#guard bloomAddValueFunction.startsWith "bloom_add_value:\n"
#guard (bloomAddValue_prog .zero).length = 45

end EvmAsm.Codegen

