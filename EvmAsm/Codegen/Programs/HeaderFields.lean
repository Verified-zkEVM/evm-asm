/-
  EvmAsm.Codegen.Programs.HeaderFields

  Single-32B-field (and one 20B beneficiary) extractors carved
  out of `EvmAsm.Codegen.Programs.Header` per the file-size
  hard cap. Hosts the K201..K208 family:

    K201  header_extract_state_root         (field 3)
    K202  header_extract_parent_hash        (field 0)
    K203  header_extract_receipts_root      (field 5)
    K204  header_extract_transactions_root  (field 4)
    K205  header_extract_withdrawals_root   (field 16)
    K206  header_extract_ommers_hash        (field 1)
    K207  header_extract_prev_randao        (field 13)
    K208  header_extract_beneficiary        (field 2, 20B)

  The migrated state-root, receipts-root, and withdrawals-root functions
  use one strict `rlp_walk_init` plus sequential `rlp_walk_next` calls,
  followed by a fixed-size memcpy + status code (0/1/2). The remaining
  functions still use K20 `rlp_list_nth_item`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## header_extract_state_root -- PR-K201

    Extract `state_root` (field 3, 32 bytes) from a header RLP
    and copy it to a caller-supplied 32-byte output buffer.

    `header_minimal_decode` already extracts state_root as part
    of a 4-field bundle (parent_hash + state_root + number +
    timestamp); this primitive is the tight standalone variant
    for callers that only need the state_root.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 3 missing
        2 : field 3 length != 32 -/
def headerExtractStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.header_extract_state_root + 40)),
    .BNE .x12 .x0 (brOff (GuestAddrs.header_extract_state_root + 236) (GuestAddrs.header_extract_state_root + 44)),
    .SD .x2 .x10 (32 : BitVec 12),
    .SD .x2 .x11 (40 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_state_root + 64)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_state_root + 236) (GuestAddrs.header_extract_state_root + 68)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_state_root + 84)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_state_root + 236) (GuestAddrs.header_extract_state_root + 88)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_state_root + 104)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_state_root + 236) (GuestAddrs.header_extract_state_root + 108)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_state_root + 124)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_state_root + 236) (GuestAddrs.header_extract_state_root + 128)),
    .SUB .x6 .x10 .x12,
    .SUB .x6 .x6 .x8,
    .AUIPC .x5 (laHi GuestAddrs.hesr_offset (GuestAddrs.header_extract_state_root + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hesr_offset (GuestAddrs.header_extract_state_root + 140)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.hesr_length (GuestAddrs.header_extract_state_root + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hesr_length (GuestAddrs.header_extract_state_root + 152)),
    .SD .x5 .x12 (0 : BitVec 12),
    .JAL .x0 (4 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.hesr_length (GuestAddrs.header_extract_state_root + 168)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hesr_length (GuestAddrs.header_extract_state_root + 168)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BNE .x6 .x7 (60 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.hesr_offset (GuestAddrs.header_extract_state_root + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hesr_offset (GuestAddrs.header_extract_state_root + 188)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .LBU .x29 .x28 (0 : BitVec 12),
    .SB .x18 .x29 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerExtractStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerExtractStateRoot_relocs : RelocTable :=
  [ (10, .jal .x1 "rlp_walk_init"),
    (16, .jal .x1 "rlp_walk_next"),
    (21, .jal .x1 "rlp_walk_next"),
    (26, .jal .x1 "rlp_walk_next"),
    (31, .jal .x1 "rlp_walk_next"),
    (35, .la .x5 "hesr_offset"),
    (38, .la .x5 "hesr_length"),
    (42, .la .x5 "hesr_length"),
    (47, .la .x5 "hesr_offset") ]

def headerExtractStateRootFunction : String :=
  "header_extract_state_root:\n" ++ emitProgramR headerExtractStateRoot_prog headerExtractStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerExtractStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerExtractStateRootFunction_eq_prog :
    headerExtractStateRootFunction = "header_extract_state_root:\n" ++ emitProgramR headerExtractStateRoot_prog headerExtractStateRoot_relocs := rfl

#guard headerExtractStateRootFunction.startsWith "header_extract_state_root:\n"
#guard headerExtractStateRoot_prog.length = 68

/-! ## header_extract_parent_hash -- PR-K202

    Extract `parent_hash` (field 0, 32 bytes) from a header
    RLP and copy it to a caller-supplied 32-byte output buffer.
    Standalone variant of the field-0 access already inside
    K17 / K94 / K173 / K183.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 0 missing
        2 : field 0 length != 32 -/
def headerExtractParentHashFunction : String :=
  "header_extract_parent_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, heph_offset; la a4, heph_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lheph_parse_fail\n" ++
  "  la t0, heph_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lheph_size_fail\n" ++
  "  la t0, heph_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lheph_ret\n" ++
  ".Lheph_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lheph_ret\n" ++
  ".Lheph_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lheph_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-! ## header_extract_receipts_root -- PR-K203

    Extract `receipts_root` (field 5, 32 bytes) from a header
    RLP and copy it to a caller-supplied 32-byte output buffer.

    Tight standalone analogue of K201 (state_root, field 3)
    and K202 (parent_hash, field 0).

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 5 missing
        2 : field 5 length != 32 -/
def headerExtractReceiptsRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.header_extract_receipts_root + 40)),
    .BNE .x12 .x0 (brOff (GuestAddrs.header_extract_receipts_root + 276) (GuestAddrs.header_extract_receipts_root + 44)),
    .SD .x2 .x10 (32 : BitVec 12),
    .SD .x2 .x11 (40 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_receipts_root + 64)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_receipts_root + 276) (GuestAddrs.header_extract_receipts_root + 68)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_receipts_root + 84)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_receipts_root + 276) (GuestAddrs.header_extract_receipts_root + 88)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_receipts_root + 104)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_receipts_root + 276) (GuestAddrs.header_extract_receipts_root + 108)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_receipts_root + 124)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_receipts_root + 276) (GuestAddrs.header_extract_receipts_root + 128)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_receipts_root + 144)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_receipts_root + 276) (GuestAddrs.header_extract_receipts_root + 148)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_receipts_root + 164)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_receipts_root + 276) (GuestAddrs.header_extract_receipts_root + 168)),
    .SUB .x6 .x10 .x12,
    .SUB .x6 .x6 .x8,
    .AUIPC .x5 (laHi GuestAddrs.herr_offset (GuestAddrs.header_extract_receipts_root + 180)),
    .ADDI .x5 .x5 (laLo GuestAddrs.herr_offset (GuestAddrs.header_extract_receipts_root + 180)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.herr_length (GuestAddrs.header_extract_receipts_root + 192)),
    .ADDI .x5 .x5 (laLo GuestAddrs.herr_length (GuestAddrs.header_extract_receipts_root + 192)),
    .SD .x5 .x12 (0 : BitVec 12),
    .JAL .x0 (4 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.herr_length (GuestAddrs.header_extract_receipts_root + 208)),
    .ADDI .x5 .x5 (laLo GuestAddrs.herr_length (GuestAddrs.header_extract_receipts_root + 208)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BNE .x6 .x7 (60 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.herr_offset (GuestAddrs.header_extract_receipts_root + 228)),
    .ADDI .x5 .x5 (laLo GuestAddrs.herr_offset (GuestAddrs.header_extract_receipts_root + 228)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .LBU .x29 .x28 (0 : BitVec 12),
    .SB .x18 .x29 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerExtractReceiptsRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerExtractReceiptsRoot_relocs : RelocTable :=
  [ (10, .jal .x1 "rlp_walk_init"),
    (16, .jal .x1 "rlp_walk_next"),
    (21, .jal .x1 "rlp_walk_next"),
    (26, .jal .x1 "rlp_walk_next"),
    (31, .jal .x1 "rlp_walk_next"),
    (36, .jal .x1 "rlp_walk_next"),
    (41, .jal .x1 "rlp_walk_next"),
    (45, .la .x5 "herr_offset"),
    (48, .la .x5 "herr_length"),
    (52, .la .x5 "herr_length"),
    (57, .la .x5 "herr_offset") ]

def headerExtractReceiptsRootFunction : String :=
  "header_extract_receipts_root:\n" ++ emitProgramR headerExtractReceiptsRoot_prog headerExtractReceiptsRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerExtractReceiptsRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerExtractReceiptsRootFunction_eq_prog :
    headerExtractReceiptsRootFunction = "header_extract_receipts_root:\n" ++ emitProgramR headerExtractReceiptsRoot_prog headerExtractReceiptsRoot_relocs := rfl

#guard headerExtractReceiptsRootFunction.startsWith "header_extract_receipts_root:\n"
#guard headerExtractReceiptsRoot_prog.length = 78

/-! ## header_extract_transactions_root -- PR-K204

    Extract `transactions_root` (field 4, 32 bytes) from a
    header RLP. Tight standalone analogue of K201 / K202 / K203.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 4 missing
        2 : field 4 length != 32 -/
def headerExtractTransactionsRootFunction : String :=
  "header_extract_transactions_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  la a3, hetr_offset; la a4, hetr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhetr_parse_fail\n" ++
  "  la t0, hetr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhetr_size_fail\n" ++
  "  la t0, hetr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhetr_ret\n" ++
  ".Lhetr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhetr_ret\n" ++
  ".Lhetr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhetr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-! ## header_extract_withdrawals_root -- PR-K205

    Extract `withdrawals_root` (field 16, 32 bytes) from a
    Shanghai+ header RLP. Tight standalone analogue of K201..
    K204 for the post-Shanghai field 16.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 16 missing (pre-Shanghai)
        2 : field 16 length != 32 -/
def headerExtractWithdrawalsRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.header_extract_withdrawals_root + 40)),
    .BNE .x12 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 44)),
    .SD .x2 .x10 (32 : BitVec 12),
    .SD .x2 .x11 (40 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 64)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 68)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 84)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 88)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 104)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 108)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 124)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 128)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 144)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 148)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 164)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 168)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 184)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 188)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 204)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 208)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 224)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 228)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 244)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 248)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 264)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 268)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 284)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 288)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 304)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 308)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 324)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 328)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 344)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 348)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 364)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 368)),
    .SD .x2 .x10 (32 : BitVec 12),
    .LD .x10 .x2 (32 : BitVec 12),
    .LD .x11 .x2 (40 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extract_withdrawals_root + 384)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extract_withdrawals_root + 496) (GuestAddrs.header_extract_withdrawals_root + 388)),
    .SUB .x6 .x10 .x12,
    .SUB .x6 .x6 .x8,
    .AUIPC .x5 (laHi GuestAddrs.hewr_offset (GuestAddrs.header_extract_withdrawals_root + 400)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hewr_offset (GuestAddrs.header_extract_withdrawals_root + 400)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.hewr_length (GuestAddrs.header_extract_withdrawals_root + 412)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hewr_length (GuestAddrs.header_extract_withdrawals_root + 412)),
    .SD .x5 .x12 (0 : BitVec 12),
    .JAL .x0 (4 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.hewr_length (GuestAddrs.header_extract_withdrawals_root + 428)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hewr_length (GuestAddrs.header_extract_withdrawals_root + 428)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BNE .x6 .x7 (60 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.hewr_offset (GuestAddrs.header_extract_withdrawals_root + 448)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hewr_offset (GuestAddrs.header_extract_withdrawals_root + 448)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .LBU .x29 .x28 (0 : BitVec 12),
    .SB .x18 .x29 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerExtractWithdrawalsRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerExtractWithdrawalsRoot_relocs : RelocTable :=
  [ (10, .jal .x1 "rlp_walk_init"),
    (16, .jal .x1 "rlp_walk_next"),
    (21, .jal .x1 "rlp_walk_next"),
    (26, .jal .x1 "rlp_walk_next"),
    (31, .jal .x1 "rlp_walk_next"),
    (36, .jal .x1 "rlp_walk_next"),
    (41, .jal .x1 "rlp_walk_next"),
    (46, .jal .x1 "rlp_walk_next"),
    (51, .jal .x1 "rlp_walk_next"),
    (56, .jal .x1 "rlp_walk_next"),
    (61, .jal .x1 "rlp_walk_next"),
    (66, .jal .x1 "rlp_walk_next"),
    (71, .jal .x1 "rlp_walk_next"),
    (76, .jal .x1 "rlp_walk_next"),
    (81, .jal .x1 "rlp_walk_next"),
    (86, .jal .x1 "rlp_walk_next"),
    (91, .jal .x1 "rlp_walk_next"),
    (96, .jal .x1 "rlp_walk_next"),
    (100, .la .x5 "hewr_offset"),
    (103, .la .x5 "hewr_length"),
    (107, .la .x5 "hewr_length"),
    (112, .la .x5 "hewr_offset") ]

def headerExtractWithdrawalsRootFunction : String :=
  "header_extract_withdrawals_root:\n" ++ emitProgramR headerExtractWithdrawalsRoot_prog headerExtractWithdrawalsRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerExtractWithdrawalsRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerExtractWithdrawalsRootFunction_eq_prog :
    headerExtractWithdrawalsRootFunction = "header_extract_withdrawals_root:\n" ++ emitProgramR headerExtractWithdrawalsRoot_prog headerExtractWithdrawalsRoot_relocs := rfl

#guard headerExtractWithdrawalsRootFunction.startsWith "header_extract_withdrawals_root:\n"
#guard headerExtractWithdrawalsRoot_prog.length = 133

/-! ## header_extract_ommers_hash -- PR-K206

    Extract `ommers_hash` (field 1, 32 bytes) -- post-merge
    always equal to `keccak256(rlp([])) = 0x1dcc4de8...`. Tight
    standalone analogue of K201..K205. -/
def headerExtractOmmersHashFunction : String :=
  "header_extract_ommers_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, heoh_offset; la a4, heoh_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lheoh_parse_fail\n" ++
  "  la t0, heoh_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lheoh_size_fail\n" ++
  "  la t0, heoh_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lheoh_ret\n" ++
  ".Lheoh_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lheoh_ret\n" ++
  ".Lheoh_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lheoh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-! ## header_extract_prev_randao -- PR-K207

    Extract `prev_randao` (field 13, 32 bytes; was `mix_hash`
    pre-merge). Source of post-merge randomness. Tight
    standalone analogue of the field-1/3/5 extractors. -/
def headerExtractPrevRandaoFunction : String :=
  "header_extract_prev_randao:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 13\n" ++
  "  la a3, hepr_offset; la a4, hepr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhepr_parse_fail\n" ++
  "  la t0, hepr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhepr_size_fail\n" ++
  "  la t0, hepr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhepr_ret\n" ++
  ".Lhepr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhepr_ret\n" ++
  ".Lhepr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhepr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-! ## header_extract_beneficiary -- PR-K208

    Extract `beneficiary` / `coinbase` (field 2, 20 bytes) from
    a header RLP. The 20-byte analogue of the K201..K207 family
    of 32-byte single-field extractors.

    Note: K68 `coinbase_extract_from_header` already exists and
    handles the same field; this is the canonical
    `header_extract_*` shape for consistency with the
    K201..K207 naming convention.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 20-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 20 -/
def headerExtractBeneficiaryFunction : String :=
  "header_extract_beneficiary:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, hebe_offset; la a4, hebe_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhebe_parse_fail\n" ++
  "  la t0, hebe_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lhebe_size_fail\n" ++
  "  la t0, hebe_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  # 20 bytes = 2 × ld + 1 × lwu / sw\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  lwu t4, 16(t3); sw t4, 16(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhebe_ret\n" ++
  ".Lhebe_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhebe_ret\n" ++
  ".Lhebe_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhebe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-! ## header_root_is_empty_trie -- PR-K161

    Predicate: does `header.field[i]` equal `EMPTY_TRIE_ROOT`?

      EMPTY_TRIE_ROOT = keccak256(rlp(b''))
                      = 0x56e81f171bcc55a6ff8345e692c0f86e5b48e
                          01b996cadc001622fb5e363b421

    The header carries several 32-byte trie-root fields:

      field 4  : transactions_root
      field 5  : receipts_root
      field 16 : withdrawals_root (post-Shanghai)

    Each of these equals `EMPTY_TRIE_ROOT` exactly when the
    corresponding logical list (transactions / receipts /
    withdrawals) is empty. Common cases:

      * Empty block (no txs): `transactions_root` ==
        EMPTY_TRIE_ROOT.
      * Withdrawal-free post-Shanghai block: `withdrawals_root`
        == EMPTY_TRIE_ROOT.
      * Receipt-free block (impossible for a non-empty block,
        but the predicate is still defined): `receipts_root`
        == EMPTY_TRIE_ROOT.

    The verifier uses this to short-circuit MPT-root recomputation
    for the common empty-list case rather than running the
    full multi-leaf builder against an empty list.

    Composes:
      - PR-K20 `rlp_list_nth_item` on the supplied field index

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : field index (u64; typically 4 / 5 / 16)
      a3 (input)  : u64 out ptr
                    (1 if root == EMPTY_TRIE_ROOT, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : RLP parse failure / field missing
        2 : field length != 32 -/
def headerRootIsEmptyTrieFunction : String :=
  "header_root_is_empty_trie:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a3                   # is_equal out ptr\n" ++
  "  # ---- Extract field i ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  # a2 is already the field index\n" ++
  "  la a3, hriet_offset; la a4, hriet_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhriet_fail\n" ++
  "  la t0, hriet_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhriet_size_fail\n" ++
  "  la t0, hriet_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1                              # &root bytes\n" ++
  "  # ---- Compare 4 × 8-byte words to EMPTY_TRIE_ROOT ----\n" ++
  "  la t4, hriet_empty_trie_root\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lhriet_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lhriet_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lhriet_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lhriet_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhriet_ret\n" ++
  ".Lhriet_neq:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhriet_ret\n" ++
  ".Lhriet_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhriet_ret\n" ++
  ".Lhriet_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhriet_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-! ## chain_extract_first_last_beneficiary -- PR-K256

    Extract `(headers[0].beneficiary, headers[N-1].beneficiary)`
    from an N-element header chain. The 20-byte `beneficiary`
    field (header field 2) is the validator/coinbase that earned
    the block's fees. Useful for proposer-rotation analytics
    across a chain segment. Companion to the K250..K255 endpoint
    family.

    Composes K208 `header_extract_beneficiary` at head and tail
    headers (placed here for adjacency).

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 20-byte out (first_beneficiary)
      a4 (input)  : 20-byte out (last_beneficiary)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse fail at head or tail header -/
def chainExtractFirstLastBeneficiaryFunction : String :=
  "chain_extract_first_last_beneficiary:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceflb_empty\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_beneficiary\n" ++
  "  bnez a0, .Lceflb_parse_fail\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceflb_skip:\n" ++
  "  beqz t3, .Lceflb_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceflb_skip\n" ++
  ".Lceflb_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, header_extract_beneficiary\n" ++
  "  bnez a0, .Lceflb_parse_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lceflb_ret\n" ++
  ".Lceflb_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lceflb_ret\n" ++
  ".Lceflb_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lceflb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## header_extract_parent_beacon_block_root -- PR-K281

    Extract `parent_beacon_block_root` (header field 19, Cancun+,
    32 bytes) from a header RLP and copy it to a caller-supplied
    32-byte output buffer. Per EIP-4788, this field commits to
    the parent beacon block's hash_tree_root and is exposed in
    the EL via the beacon-roots contract at 0xBEAC0000...0002.

    Pre-Cancun headers (<20 fields) raise parse-failure status.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 19 missing
        2 : field 19 length != 32 -/
def headerExtractParentBeaconBlockRootFunction : String :=
  "header_extract_parent_beacon_block_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 19\n" ++
  "  la a3, hepbbr_offset; la a4, hepbbr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhepbbr_parse_fail\n" ++
  "  la t0, hepbbr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhepbbr_size_fail\n" ++
  "  la t0, hepbbr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhepbbr_ret\n" ++
  ".Lhepbbr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhepbbr_ret\n" ++
  ".Lhepbbr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhepbbr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-! ## header_extract_requests_hash -- PR-K283

    Extract `requests_hash` (header field 20, Prague+, 32 bytes)
    from a header RLP and copy it to a caller-supplied 32-byte
    output buffer. Per EIP-7685, this field commits to the
    keccak256(sha256(req_0_data) ++ sha256(req_1_data) ++ ...)
    of the per-request lists (deposits, withdrawals,
    consolidations).

    Pre-Prague headers (<21 fields) raise parse-failure status.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 20 missing
        2 : field 20 length != 32 -/
def headerExtractRequestsHashFunction : String :=
  "header_extract_requests_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 20\n" ++
  "  la a3, herh_offset; la a4, herh_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lherh_parse_fail\n" ++
  "  la t0, herh_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lherh_size_fail\n" ++
  "  la t0, herh_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lherh_ret\n" ++
  ".Lherh_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lherh_ret\n" ++
  ".Lherh_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lherh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

end EvmAsm.Codegen
