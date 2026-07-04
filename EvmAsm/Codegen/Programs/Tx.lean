/-
  EvmAsm.Codegen.Programs.Tx

  Tx-decoding stack lifted out of `EvmAsm.Codegen.Programs` to
  keep the registry hub manageable (file-size hard cap, see
  `Programs.lean` bottom).

  Contains three contiguous slabs as they appeared in
  `Programs.lean`:

  1. **rlp-field shims + account extractors + legacy-tx
     decoders / signature extractors** (PR-K34 / K121 / K35 /
     K120 / K123 / K36 / K37 / K138 / K139).

  2. **u256-BE arithmetic / comparison / pricing helpers**
     (PR-K51 / K52 / K56 / K58 / K59 / K60 / K61 / K62 / K70 /
     K53 / K54) used pervasively by tx validation and fee
     computation.

  3. **u256-BE truncation + tx type / extract / EIP-decode
     family + intrinsic-gas + validate-transaction**
     (PR-K57 / K40 / K102 / K101 / K103 / K104 / K108 / K41 /
     K42 / K44 / K45 / K87 / K88 / K92 / K46 / K66 / K76 / K80
     and adjacent helpers).

  The module is named after the dominant cluster (tx) even
  though slabs (2) and a couple of cross-cutting helpers
  (`rlp_field_to_u*`, account extractors, u256 arithmetic) live
  here alongside it. Grouping them in one submodule reflects
  the fact that the verifier's tx-validation pipeline pulls in
  exactly this collection of helpers; splitting them further is
  a future refactor when this file in turn becomes too large.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## rlp_field_to_u64 -- PR-K34 RLP field → u64 wrapper

    Extract the N-th field of an RLP list and decode its
    big-endian byte string as a u64. Used by future
    transaction-decode and header-decode steps for fields like
    nonce, gas_limit, block_number, v.

    Calling convention:
      a0 (input)  : container RLP bytes ptr (e.g. tx_rlp)
      a1 (input)  : container RLP byte length
      a2 (input)  : field index (0-based)
      a3 (input)  : u64 output ptr (LE-stored u64)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse failure /
                    2 field too long (> 8 bytes)

    Composes PR-K20 `rlp_list_nth_item` + per-byte BE decode.
    The output is stored as a native LE u64 at *a3. -/
def rlpFieldToU64_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x13,
    .AUIPC .x13 (laHi GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64 + 24)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64 + 24)),
    .AUIPC .x14 (laHi GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64 + 32)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64 + 32)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.rlp_field_to_u64 + 40)),
    .BNE .x10 .x0 (96 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64 + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64 + 48)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (8 : Word),
    .BLTU .x7 .x6 (64 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64 + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64 + 68)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .LI .x7 (0 : Word),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .SLLI .x7 .x7 (8 : BitVec 6),
    .LBU .x29 .x28 (0 : BitVec 12),
    .OR .x7 .x7 .x29,
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .SD .x9 .x7 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .SD .x9 .x0 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JAL .x0 (12 : BitVec 21),
    .SD .x9 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `rlpFieldToU64_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def rlpFieldToU64_relocs : RelocTable :=
  [ (6, .la .x13 "rfu_offset"),
    (8, .la .x14 "rfu_length"),
    (10, .jal .x1 "rlp_list_nth_item"),
    (12, .la .x5 "rfu_length"),
    (17, .la .x5 "rfu_offset") ]

def rlpFieldToU64Function : String :=
  "rlp_field_to_u64:\n" ++ emitProgramR rlpFieldToU64_prog rlpFieldToU64_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `rlpFieldToU64_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem rlpFieldToU64Function_eq_prog :
    rlpFieldToU64Function = "rlp_field_to_u64:\n" ++ emitProgramR rlpFieldToU64_prog rlpFieldToU64_relocs := rfl

#guard rlpFieldToU64Function.startsWith "rlp_field_to_u64:\n"
#guard rlpFieldToU64_prog.length = 42
/-- `zisk_rlp_field_to_u64`: probe BuildUnit. Reads
    (container_len, field_index, container_bytes) from host
    input, writes (status, u64) to OUTPUT. -/
def ziskRlpFieldToU64Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # container_len\n" ++
  "  ld a2, 16(a4)               # field_index\n" ++
  "  addi a0, a4, 24             # container ptr\n" ++
  "  li a3, 0xa0010008           # u64 out at OUTPUT + 8\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lrfu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lrfu_pdone:"

def ziskRlpFieldToU64DataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskRlpFieldToU64ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpFieldToU64Prologue
  dataAsm     := ziskRlpFieldToU64DataSection
}


/-! ## rlp_field_to_u256_be -- PR-K35

    Extract the N-th field of an RLP list and right-align its
    big-endian byte string into a 32-byte BE u256 buffer.
    Parallel of PR-K34 `rlp_field_to_u64` for u256 fields like
    balance / tx.value / header.difficulty.

    Calling convention:
      a0 (input)  : container RLP bytes ptr
      a1 (input)  : container RLP byte length
      a2 (input)  : field index (0-based)
      a3 (input)  : 32-byte u256 BE output ptr (right-aligned)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail /
                    2 field too long (> 32 bytes)

    Composes PR-K20 `rlp_list_nth_item`; reuses K34's
    `rfu_offset` / `rfu_length` scratch slots. -/
def rlpFieldToU256Be_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x13,
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u256_be + 40)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u256_be + 40)),
    .AUIPC .x14 (laHi GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u256_be + 48)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u256_be + 48)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.rlp_field_to_u256_be + 56)),
    .BNE .x10 .x0 (92 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u256_be + 64)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u256_be + 64)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BLTU .x7 .x6 (64 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u256_be + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u256_be + 84)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .SUB .x7 .x7 .x6,
    .ADD .x29 .x9 .x7,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .SB .x29 .x30 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `rlpFieldToU256Be_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def rlpFieldToU256Be_relocs : RelocTable :=
  [ (10, .la .x13 "rfu_offset"),
    (12, .la .x14 "rfu_length"),
    (14, .jal .x1 "rlp_list_nth_item"),
    (16, .la .x5 "rfu_length"),
    (21, .la .x5 "rfu_offset") ]

def rlpFieldToU256BeFunction : String :=
  "rlp_field_to_u256_be:\n" ++ emitProgramR rlpFieldToU256Be_prog rlpFieldToU256Be_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `rlpFieldToU256Be_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem rlpFieldToU256BeFunction_eq_prog :
    rlpFieldToU256BeFunction = "rlp_field_to_u256_be:\n" ++ emitProgramR rlpFieldToU256Be_prog rlpFieldToU256Be_relocs := rfl

#guard rlpFieldToU256BeFunction.startsWith "rlp_field_to_u256_be:\n"
#guard rlpFieldToU256Be_prog.length = 44
/-- `zisk_rlp_field_to_u256_be`: probe BuildUnit. Reads
    (container_len, field_index, container_bytes), writes
    (status, u256 BE) to OUTPUT. -/
def ziskRlpFieldToU256BePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # container_len\n" ++
  "  ld a2, 16(a4)               # field_index\n" ++
  "  addi a0, a4, 24             # container ptr\n" ++
  "  li a3, 0xa0010008           # u256 out at OUTPUT + 8\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lrf256_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  ".Lrf256_pdone:"

def ziskRlpFieldToU256BeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskRlpFieldToU256BeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpFieldToU256BePrologue
  dataAsm     := ziskRlpFieldToU256BeDataSection
}


/-! ## tx_legacy_decode -- PR-K36 full 9-field decoder

    Decode an RLP-encoded legacy Ethereum transaction into a
    196-byte flat output struct. Uses the cursor-advancing walker
    pair (`EvmAsm.Codegen.Programs.RlpWalk`) instead of the
    index-based `rlp_field_to_*` wrappers, so all 9 fields are
    decoded in a single left-to-right pass (9 item visits) rather
    than 0+1+...+8 = 36 re-walks. The (cursor, end) pair is held
    in callee-saved registers across the chain.

    Output struct (196 bytes):
       0..  8  nonce (u64 LE)
       8.. 40  gas_price (u256 BE)
      40.. 48  gas_limit (u64 LE)
      48.. 68  to (20-byte address; zero on creation)
      68.. 76  to_present (u64; 0 = creation, 1 = call)
      76..108  value (u256 BE)
     108..116  data_offset (within tx_rlp)
     116..124  data_length
     124..132  v (u64 LE)
     132..164  r (u256 BE)
     164..196  s (u256 BE)

    Calling convention:
      a0 (input)  : tx_rlp ptr
      a1 (input)  : tx_rlp byte length
      a2 (input)  : output struct ptr (196 bytes)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail -/
def txLegacyDecodeFunction : String :=
  "tx_legacy_decode:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                  # tx_rlp ptr (list base)\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  jal ra, rlp_walk_init      # a0=cursor, a1=end, a2=status\n" ++
  "  bnez a2, .Ltxd_fail\n" ++
  "  mv s1, a1                  # end\n" ++
  "  mv s3, a0                  # cursor\n" ++
  "  # Field 0: nonce (u64 at offset 0)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next      # a0=advanced, a1=status, a2=content_len\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sub a0, a0, a2             # content_ptr = advanced - len\n" ++
  "  mv a1, a2                  # content_len\n" ++
  "  jal ra, rlp_content_to_u64 # a0=u64, a1=status\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sd a0, 0(s2)\n" ++
  "  # Field 1: gas_price (u256 BE at offset 8)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 8\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  # Field 2: gas_limit (u64 at offset 40)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sd a0, 40(s2)\n" ++
  "  # Field 3: to (0 or 20 bytes at offset 48; to_present u64 at 68)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  beqz a2, .Ltxd_to_creation\n" ++
  "  li t0, 20\n" ++
  "  bne a2, t0, .Ltxd_fail\n" ++
  "  sub t3, a0, a2             # content_ptr\n" ++
  "  addi t4, s2, 48\n" ++
  "  ld t5,  0(t3); sd t5, 0(t4)\n" ++
  "  ld t5,  8(t3); sd t5, 8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  li t5, 1\n" ++
  "  sd t5, 68(s2)              # to_present = 1\n" ++
  "  j .Ltxd_after_to\n" ++
  ".Ltxd_to_creation:\n" ++
  "  addi t4, s2, 48\n" ++
  "  sd zero, 0(t4); sd zero, 8(t4); sw zero, 16(t4)\n" ++
  "  sd zero, 68(s2)            # to_present = 0\n" ++
  ".Ltxd_after_to:\n" ++
  "  # Field 4: value (u256 BE at offset 76)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 76\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  # Field 5: data (offset+length u64 at 108/116)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sub t3, a0, a2             # content_ptr\n" ++
  "  sub t1, t3, s0             # offset = content_ptr - base\n" ++
  "  sd t1, 108(s2)\n" ++
  "  sd a2, 116(s2)             # content_len\n" ++
  "  # Field 6: v (u64 at offset 124)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sd a0, 124(s2)\n" ++
  "  # Field 7: r (u256 BE at offset 132)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 132\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  # Field 8: s (u256 BE at offset 164)\n" ++
  "  mv a0, s3; mv a1, s1\n" ++
  "  jal ra, rlp_walk_next\n" ++
  "  mv s3, a0\n" ++
  "  bnez a1, .Ltxd_fail\n" ++
  "  sub a0, a0, a2; mv a1, a2\n" ++
  "  addi a2, s2, 164\n" ++
  "  jal ra, rlp_content_to_u256_be\n" ++
  "  bnez a0, .Ltxd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Ltxd_ret\n" ++
  ".Ltxd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltxd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_tx_legacy_decode`: probe BuildUnit. Reads
    (tx_len, tx_bytes) from host input, writes
    (status, 196-byte struct) to OUTPUT.
    Total output = 204 bytes; fits in ziskemu's 256-byte cap. -/
def ziskTxLegacyDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # tx_len\n" ++
  "  addi a0, a3, 16             # tx ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 196 bytes (24 × 8 + 4 trailing)\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 24\n" ++
  ".Ltxd_zinit:\n" ++
  "  beqz t1, .Ltxd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltxd_zinit\n" ++
  ".Ltxd_zdone:\n" ++
  "  sw zero, 0(t0)\n" ++
  "  jal ra, tx_legacy_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltxd_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  txLegacyDecodeFunction ++ "\n" ++
  ".Ltxd_pdone:"

/-- The decoder holds (cursor, end) in callee-saved registers and
    derives every content pointer arithmetically, so it needs no
    `.data` scratch. -/
def ziskTxLegacyDecodeDataSection : String := ""

def ziskTxLegacyDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxLegacyDecodePrologue
  dataAsm     := ziskTxLegacyDecodeDataSection
}

/-! ## derive_chain_id_from_v -- PR-K37 EIP-155 helper

    Split a legacy-transaction `v` signature parity byte into
    `(chain_id, is_eip155)` per EIP-155:

      v == 27 → pre-EIP-155: chain_id = 0, is_eip155 = 0
      v == 28 → pre-EIP-155: chain_id = 0, is_eip155 = 0
      else    → EIP-155: chain_id = (v - 35) / 2, is_eip155 = 1

    This is the routing logic the signing-hash builder uses to
    pick between the 6-field (pre-155) and 9-field (155+
    chain_id, 0, 0) signing payloads.

    Calling convention:
      a0 (input)  : v (u64)
      a1 (input)  : chain_id u64 output ptr
      a2 (input)  : is_eip155 u64 output ptr
      ra (input)  : return
      a0 (output) : 0 (always success; no validation here --
                    invalid v values just produce wrong
                    chain_id; the signing-hash check catches
                    them later) -/
def deriveChainIdFromV_prog : Program :=
  [ .LI .x5 (27 : Word),
    .BEQ .x10 .x5 (40 : BitVec 13),
    .LI .x5 (28 : Word),
    .BEQ .x10 .x5 (32 : BitVec 13),
    .ADDI .x6 .x10 (-35 : BitVec 12),
    .SRLI .x6 .x6 (1 : BitVec 6),
    .SD .x11 .x6 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .SD .x12 .x7 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x11 .x0 (0 : BitVec 12),
    .SD .x12 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def deriveChainIdFromVFunction : String :=
  "derive_chain_id_from_v:\n" ++ emitProgram deriveChainIdFromV_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `deriveChainIdFromV_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem deriveChainIdFromVFunction_eq_prog :
    deriveChainIdFromVFunction = "derive_chain_id_from_v:\n" ++ emitProgram deriveChainIdFromV_prog := rfl

#guard deriveChainIdFromVFunction.startsWith "derive_chain_id_from_v:\n"
#guard deriveChainIdFromV_prog.length = 15
/-- `zisk_derive_chain_id_from_v`: probe BuildUnit. Reads
    (v, padding) from host input, writes (chain_id, is_eip155)
    to OUTPUT. -/
def ziskDeriveChainIdFromVPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # v\n" ++
  "  li a1, 0xa0010000           # chain_id out\n" ++
  "  li a2, 0xa0010008           # is_eip155 out\n" ++
  "  jal ra, derive_chain_id_from_v\n" ++
  "  j .Ldcid_pdone\n" ++
  deriveChainIdFromVFunction ++ "\n" ++
  ".Ldcid_pdone:"

def ziskDeriveChainIdFromVDataSection : String :=
  ".section .data\n" ++
  "dcid_pad:\n" ++
  "  .zero 8"

def ziskDeriveChainIdFromVProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskDeriveChainIdFromVPrologue
  dataAsm     := ziskDeriveChainIdFromVDataSection
}


/-! ## blob_gas_used_from_versioned_hashes -- PR-K64

    Compute the EIP-4844 `blob_gas_used` field as:

      blob_gas_used = len(tx.blob_versioned_hashes) × GAS_PER_BLOB

    where `GAS_PER_BLOB = 131072 = 0x20000` per spec. The
    `gas_per_blob` constant is parameterized so the helper works
    across forks that might adjust it.

    Direct use case — validating header.blob_gas_used and
    rejecting blob-fee under-pays:

      header.blob_gas_used  ==  sum(tx.blob_versioned_hashes count
                                    × GAS_PER_BLOB
                                    for tx in block.txs
                                    if tx.is_blob)

    Composes PR-K47 `rlp_list_count_items` (#5532) + a `mul`.
    `rlp_list_count_items` is inlined into the probe BuildUnit.

    Calling convention:
      a0 (input)  : blob_versioned_hashes_rlp ptr (whole encoded
                    sub-list as returned by PR-K45
                    `tx_eip4844_decode` field 10)
      a1 (input)  : blob_versioned_hashes_rlp byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet)
      a3 (input)  : u64 out ptr (receives blob_gas_used)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (output zeroed).

    Uses 8 bytes of `.data` scratch (`bgvh_count_scratch`). -/
def blobGasUsedFromVersionedHashesFunction : String :=
  "blob_gas_used_from_versioned_hashes:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a2                   # gas_per_blob\n" ++
  "  mv s1, a3                   # out ptr\n" ++
  "  la a2, bgvh_count_scratch\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbgvh_fail\n" ++
  "  la t0, bgvh_count_scratch; ld t1, 0(t0)\n" ++
  "  mul t2, t1, s0\n" ++
  "  sd t2, 0(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbgvh_ret\n" ++
  ".Lbgvh_fail:\n" ++
  "  sd zero, 0(s1)\n" ++
  "  li a0, 1\n" ++
  ".Lbgvh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- `zisk_blob_gas_used_from_versioned_hashes`: probe BuildUnit.
    Reads (list_len, gas_per_blob, list_bytes) from host input,
    writes (status, blob_gas_used) to OUTPUT (16 bytes total). -/
def ziskBlobGasUsedFromVersionedHashesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # list_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # list ptr\n" ++
  "  li a3, 0xa0010008           # out at OUTPUT + 8\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, blob_gas_used_from_versioned_hashes\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbgvh_pdone\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  ".Lbgvh_pdone:"

def ziskBlobGasUsedFromVersionedHashesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bgvh_count_scratch:\n" ++
  "  .zero 8"

def ziskBlobGasUsedFromVersionedHashesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlobGasUsedFromVersionedHashesPrologue
  dataAsm     := ziskBlobGasUsedFromVersionedHashesDataSection
}

/-! ## tx_validate_against_block -- PR-K69

    Combine three u64 tx-validation invariants into one helper:

      1. tx.chain_id == block.chain_id
      2. tx.gas_limit <= block.gas_limit
      3. tx.nonce == account.nonce

    These are the cheapest tx-validation checks (pre-EVM
    execution); a tx that fails any of them is rejected without
    further work. Mirrors three of the assertions in Python's
    `validate_transaction`:

      assert tx.chain_id == chain.chain_id
      assert tx.gas <= block.gas_limit
      assert tx.nonce == account.nonce

    Pure u64 compares; no scratch memory; leaf-callable.

    Calling convention:
      a0 (input)  : tx.chain_id      (u64)
      a1 (input)  : block.chain_id   (u64)
      a2 (input)  : tx.gas_limit     (u64)
      a3 (input)  : block.gas_limit  (u64)
      a4 (input)  : tx.nonce         (u64)
      a5 (input)  : account.nonce    (u64)
      ra (input)  : return
      a0 (output) :
        0  : all three invariants hold
        1  : chain_id mismatch
        2  : tx.gas_limit > block.gas_limit
        3  : tx.nonce != account.nonce

    Distinct codes let callers pinpoint which check fired
    without re-running individual asserts. -/
def txValidateAgainstBlock_prog : Program :=
  [ .BNE .x10 .x11 (20 : BitVec 13),
    .BLTU .x13 .x12 (24 : BitVec 13),
    .BNE .x14 .x15 (28 : BitVec 13),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (3 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def txValidateAgainstBlockFunction : String :=
  "tx_validate_against_block:\n" ++ emitProgram txValidateAgainstBlock_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `txValidateAgainstBlock_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem txValidateAgainstBlockFunction_eq_prog :
    txValidateAgainstBlockFunction = "tx_validate_against_block:\n" ++ emitProgram txValidateAgainstBlock_prog := rfl

#guard txValidateAgainstBlockFunction.startsWith "tx_validate_against_block:\n"
#guard txValidateAgainstBlock_prog.length = 11
/-- `zisk_tx_validate_against_block`: probe BuildUnit. Reads
    (tx_chain, block_chain, tx_gas, block_gas, tx_nonce,
    account_nonce) as 6 u64 LE words from host input, writes
    8-byte status to OUTPUT. -/
def ziskTxValidateAgainstBlockPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0,  8(t0)               # tx.chain_id\n" ++
  "  ld a1, 16(t0)               # block.chain_id\n" ++
  "  ld a2, 24(t0)               # tx.gas_limit\n" ++
  "  ld a3, 32(t0)               # block.gas_limit\n" ++
  "  ld a4, 40(t0)               # tx.nonce\n" ++
  "  ld a5, 48(t0)               # account.nonce\n" ++
  "  jal ra, tx_validate_against_block\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltvab_pdone\n" ++
  txValidateAgainstBlockFunction ++ "\n" ++
  ".Ltvab_pdone:"

def ziskTxValidateAgainstBlockDataSection : String :=
  ".section .data\n" ++
  "tvab_pad:\n" ++
  "  .zero 8"

def ziskTxValidateAgainstBlockProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxValidateAgainstBlockPrologue
  dataAsm     := ziskTxValidateAgainstBlockDataSection
}

/-! ## u256-BE arithmetic + pricing helpers (K51/K52/K56/K58/K59/K60/K61/K62/K70/K53/K54/K57/K160) — moved to `Programs/U256.lean` (file-size hard cap). -/

/-! ## intrinsic_gas_legacy -- PR-K46 base + creation + data gas

    Compute the intrinsic gas cost portion of a legacy /
    EIP-2930 / EIP-1559 transaction that depends only on the
    `data` payload and the creation flag. Higher-fork-specific
    extras (access-list address/slot costs, EIP-7702 auth
    entries, EIP-7623 floor data cost) are NOT included here --
    callers compose them.

    Formula (EIP-2028 / EIP-2 base):

      gas = 21000
          + (32000 if creation else 0)
          + sum(4 if b == 0 else 16 for b in data)

    Calling convention:
      a0 (input)  : data ptr
      a1 (input)  : data byte length
      a2 (input)  : is_creation (0 = call, 1 = creation)
      ra (input)  : return
      a0 (output) : u64 intrinsic gas

    Pure register arithmetic, no scratch memory, leaf-callable.
    Cannot overflow u64 in practice: even at max gas_limit ~30M,
    data length << 2^59, so 16 * data_len is well within u64. -/
def intrinsicGasLegacy_prog : Program :=
  [ .LUI .x5 (5 : BitVec 20),
    .ADDIW .x5 .x5 (520 : BitVec 12),
    .BEQ .x12 .x0 (16 : BitVec 13),
    .LUI .x6 (8 : BitVec 20),
    .ADDIW .x6 .x6 (-768 : BitVec 12),
    .ADD .x5 .x5 .x6,
    .MV .x7 .x10,
    .ADD .x28 .x10 .x11,
    .BGEU .x7 .x28 (32 : BitVec 13),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BEQ .x29 .x0 (12 : BitVec 13),
    .ADDI .x5 .x5 (16 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x5 .x5 (4 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .MV .x10 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def intrinsicGasLegacyFunction : String :=
  "intrinsic_gas_legacy:\n" ++ emitProgram intrinsicGasLegacy_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `intrinsicGasLegacy_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem intrinsicGasLegacyFunction_eq_prog :
    intrinsicGasLegacyFunction = "intrinsic_gas_legacy:\n" ++ emitProgram intrinsicGasLegacy_prog := rfl

#guard intrinsicGasLegacyFunction.startsWith "intrinsic_gas_legacy:\n"
#guard intrinsicGasLegacy_prog.length = 18
/-- `zisk_intrinsic_gas_legacy`: probe BuildUnit. Reads
    (data_len, is_creation, data_bytes) from host input, writes
    the u64 intrinsic gas to OUTPUT. -/
def ziskIntrinsicGasLegacyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # data_len\n" ++
  "  ld a2, 16(a3)               # is_creation\n" ++
  "  addi a0, a3, 24             # data ptr\n" ++
  "  jal ra, intrinsic_gas_legacy\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # gas\n" ++
  "  j .Ligl_pdone\n" ++
  intrinsicGasLegacyFunction ++ "\n" ++
  ".Ligl_pdone:"

def ziskIntrinsicGasLegacyDataSection : String :=
  ".section .data\n" ++
  "igl_pad:\n" ++
  "  .zero 8"

def ziskIntrinsicGasLegacyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskIntrinsicGasLegacyPrologue
  dataAsm     := ziskIntrinsicGasLegacyDataSection
}

/-! ## tx_validate_intrinsic_gas_legacy -- PR-K66

    Compose PR-K46 `intrinsic_gas_legacy` with the standard tx
    validation check `intrinsic_gas <= tx.gas_limit`. Mirrors
    Python's check in `validate_transaction`:

      if tx.gas < calculate_intrinsic_gas(tx):
          raise InvalidTransaction

    Returns the actual intrinsic-gas value via an out pointer so
    callers don't have to re-call PR-K46; this lets downstream
    `process_transaction` deduct it from the tx's gas allowance.

    Calling convention:
      a0 (input)  : data ptr
      a1 (input)  : data byte length
      a2 (input)  : is_creation (0 or 1)
      a3 (input)  : tx.gas_limit (u64)
      a4 (input)  : u64 out ptr (receives intrinsic_gas)
      ra (input)  : return
      a0 (output) : 0 ok / 1 intrinsic_gas > tx.gas_limit (reject)

    The `out` pointer always receives the computed intrinsic gas,
    even on reject — callers can record it for receipt purposes
    or further analysis. -/
def txValidateIntrinsicGasLegacyFunction : String :=
  "tx_validate_intrinsic_gas_legacy:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a3                   # tx.gas_limit\n" ++
  "  mv s1, a4                   # out ptr\n" ++
  "  jal ra, intrinsic_gas_legacy # a0 = intrinsic_gas\n" ++
  "  sd a0, 0(s1)                # write to out, regardless of reject\n" ++
  "  bltu s0, a0, .Ltvil_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Ltvil_ret\n" ++
  ".Ltvil_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltvil_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_tx_validate_intrinsic_gas_legacy`: probe BuildUnit.
    Reads (data_len, is_creation, gas_limit, data_bytes) from
    host input, writes (status, intrinsic_gas) to OUTPUT (16
    bytes total). -/
def ziskTxValidateIntrinsicGasLegacyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # data_len\n" ++
  "  ld a2, 16(a5)               # is_creation\n" ++
  "  ld a3, 24(a5)               # tx.gas_limit\n" ++
  "  addi a0, a5, 32             # data ptr\n" ++
  "  li a4, 0xa0010008           # out ptr for intrinsic_gas\n" ++
  "  sd zero, 0(a4)\n" ++
  "  jal ra, tx_validate_intrinsic_gas_legacy\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltvil_pdone\n" ++
  intrinsicGasLegacyFunction ++ "\n" ++
  txValidateIntrinsicGasLegacyFunction ++ "\n" ++
  ".Ltvil_pdone:"

def ziskTxValidateIntrinsicGasLegacyDataSection : String :=
  ".section .data\n" ++
  "tvil_pad:\n" ++
  "  .zero 8"

def ziskTxValidateIntrinsicGasLegacyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxValidateIntrinsicGasLegacyPrologue
  dataAsm     := ziskTxValidateIntrinsicGasLegacyDataSection
}

/-! ## validate_transaction_basic -- PR-K76 cheap pre-EVM tx validation

    Run the two cheap u64-level transaction validation checks in
    sequence and return a composite status:

      1. PR-K69 `tx_validate_against_block`        — chain_id, gas_limit, nonce
      2. PR-K66 `tx_validate_intrinsic_gas_legacy` — intrinsic_gas ≤ tx.gas_limit

    These are the cheapest pre-EVM checks; a tx that fails any
    of them is rejected without invoking the EVM. Mirrors the
    `chain_id == ...`, `tx.gas <= block.gas_limit`, `tx.nonce ==
    account.nonce`, and `intrinsic_gas <= tx.gas` assertions in
    Python's `validate_transaction`.

    The intrinsic_gas check applies to legacy / EIP-2930 / EIP-1559
    txs sharing the base + creation + per-byte data formula.
    EIP-2930+ access-list and EIP-7702 authorization-list gas
    additions land in follow-up PRs that compose this helper
    with K48 + future authorization counters.

    Status encoding (analogous to PR-K75 validate_header_full):

      0          : all checks pass
      101..103   : step 1 (K69) failed (chain_id / gas_limit / nonce)
      201        : step 2 (K66) failed (intrinsic_gas > tx.gas_limit)

    The intrinsic_gas value is also written to an out pointer
    regardless of the verdict — callers can deduct it from
    tx.gas_limit on the success path or record it for analysis.

    Calling convention:
      a0 (input)  : tx.chain_id (u64)
      a1 (input)  : block.chain_id (u64)
      a2 (input)  : tx.gas_limit (u64)
      a3 (input)  : block.gas_limit (u64)
      a4 (input)  : tx.nonce (u64)
      a5 (input)  : account.nonce (u64)
      a6 (input)  : data ptr
      a7 (input)  : packed input: low bits = data_len, bit 63 = is_creation
      ra (input)  : return
      a0 (output) : composite status code

    The `a7` packing avoids needing an 8th and 9th register
    (RV64 has only 8 arg regs). data_len in the low 32 bits is
    plenty (mainnet caps tx data well below 4 GiB), and
    is_creation is one bit.

    Note: this helper does NOT take an intrinsic_gas out
    pointer — the cost of forwarding through the stack adds
    register pressure. Callers that need the intrinsic gas can
    call PR-K46 `intrinsic_gas_legacy` directly. -/
def validateTransactionBasicFunction : String :=
  "validate_transaction_basic:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  # Save data ptr, gas_limit, and a7 for step 2.\n" ++
  "  mv s0, a6                   # data ptr\n" ++
  "  mv s1, a2                   # tx.gas_limit\n" ++
  "  mv s2, a7                   # packed: low 32 = data_len, bit 63 = is_creation\n" ++
  "  # Step 1: K69 tx_validate_against_block(chain, block_chain, gas, block_gas, nonce, acct_nonce)\n" ++
  "  jal ra, tx_validate_against_block\n" ++
  "  beqz a0, .Lvtb_s2\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvtb_ret\n" ++
  ".Lvtb_s2:\n" ++
  "  # Step 2: K66 tx_validate_intrinsic_gas_legacy(data, len, is_creation, gas_limit, gas_out)\n" ++
  "  mv a0, s0\n" ++
  "  li t0, 0xffffffff           # mask for low 32 bits (data_len)\n" ++
  "  and a1, s2, t0\n" ++
  "  srli a2, s2, 63             # is_creation = high bit\n" ++
  "  mv a3, s1                   # tx.gas_limit\n" ++
  "  la a4, vtb_gas_scratch      # intrinsic_gas out (scratch, unused by caller)\n" ++
  "  jal ra, tx_validate_intrinsic_gas_legacy\n" ++
  "  beqz a0, .Lvtb_ret\n" ++
  "  li t0, 200\n" ++
  "  add a0, a0, t0\n" ++
  ".Lvtb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_validate_transaction_basic`: probe BuildUnit. Reads
    (tx_chain, block_chain, tx_gas, block_gas, tx_nonce,
    account_nonce, is_creation, data_len, data_bytes) from host
    input, writes 8-byte composite status to OUTPUT. -/
def ziskValidateTransactionBasicPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0,  8(t0)               # tx.chain_id\n" ++
  "  ld a1, 16(t0)               # block.chain_id\n" ++
  "  ld a2, 24(t0)               # tx.gas_limit\n" ++
  "  ld a3, 32(t0)               # block.gas_limit\n" ++
  "  ld a4, 40(t0)               # tx.nonce\n" ++
  "  ld a5, 48(t0)               # account.nonce\n" ++
  "  ld t1, 56(t0)               # is_creation (u64)\n" ++
  "  ld t2, 64(t0)               # data_len (u64; low 32 used)\n" ++
  "  addi a6, t0, 72             # data ptr\n" ++
  "  # Pack t1 (is_creation, 0 or 1) and t2 (data_len) into a7.\n" ++
  "  slli t1, t1, 63\n" ++
  "  li t3, 0xffffffff\n" ++
  "  and t2, t2, t3\n" ++
  "  or  a7, t1, t2\n" ++
  "  jal ra, validate_transaction_basic\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvtb_pdone\n" ++
  txValidateAgainstBlockFunction ++ "\n" ++
  intrinsicGasLegacyFunction ++ "\n" ++
  txValidateIntrinsicGasLegacyFunction ++ "\n" ++
  validateTransactionBasicFunction ++ "\n" ++
  ".Lvtb_pdone:"

def ziskValidateTransactionBasicDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "vtb_gas_scratch:\n" ++
  "  .zero 8"

def ziskValidateTransactionBasicProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateTransactionBasicPrologue
  dataAsm     := ziskValidateTransactionBasicDataSection
}
/-! ## tx_cost_compute -- PR-K71

    Compute the full upfront cost of a transaction:

      tx_cost = gas_limit × effective_gas_price + value

    This is the value that must not exceed `account.balance` for
    the tx to be valid. Mirrors the Python check in
    `validate_transaction` / `process_transaction`:

      max_gas_fee = tx.gas * effective_gas_price
      if sender.balance < max_gas_fee + tx.value:
          raise InsufficientBalance

    Composes:
      - PR-K54 `u256_mul_u64_be` for the multiplication step
      - PR-K51 `u256_add_be` for adding `value`

    Reports overflow on either step via `status=1`. In practice
    `effective_gas_price ≤ max_fee_per_gas` is u128-sized at
    most, so the multiplicand fits comfortably; overflow is a
    "garbage input" safety net.

    BE storage convention: byte 0 = MSB, byte 31 = LSB.

    Calling convention:
      a0 (input)  : effective_gas_price ptr (32 B BE)
      a1 (input)  : gas_limit (u64)
      a2 (input)  : value ptr (32 B BE)
      a3 (input)  : out ptr (32 B BE; receives tx_cost)
      ra (input)  : return
      a0 (output) : 0 success / 1 overflow on mul or add. -/
def txCostComputeFunction : String :=
  "tx_cost_compute:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a2                   # value ptr\n" ++
  "  mv s1, a3                   # out ptr\n" ++
  "  # Step 1: out = effective_gas_price × gas_limit.\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Ltcc_fail\n" ++
  "  # Step 2: out = out + value.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Ltcc_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Ltcc_ret\n" ++
  ".Ltcc_fail:\n" ++
  "  li a0, 1\n" ++
  ".Ltcc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_tx_cost_compute`: probe BuildUnit. Reads (32B egp, 8B
    gas_limit LE, 32B value) from host input, writes (status,
    32B tx_cost BE) to OUTPUT (40 bytes total). -/
def ziskTxCostComputePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # egp ptr\n" ++
  "  ld a1, 40(a4)               # gas_limit (u64)\n" ++
  "  addi a2, a4, 48             # value ptr\n" ++
  "  li a3, 0xa0010008           # out ptr\n" ++
  "  mv t0, a3; li t1, 4\n" ++
  ".Ltcc_zout:\n" ++
  "  beqz t1, .Ltcc_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Ltcc_zout\n" ++
  ".Ltcc_zout_done:\n" ++
  "  jal ra, tx_cost_compute\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ltcc_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  txCostComputeFunction ++ "\n" ++
  ".Ltcc_pdone:"

def ziskTxCostComputeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40"

def ziskTxCostComputeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxCostComputePrologue
  dataAsm     := ziskTxCostComputeDataSection
}

/-! ## validate_transaction_balance -- PR-K79

    Verify that the sender's account balance covers the
    worst-case (pre-execution) tx cost:

      tx_cost = tx.max_fee_per_gas × tx.gas_limit + tx.value
      assert sender.balance >= tx_cost

    This is the pre-flight check from Python's
    `validate_transaction`:

      max_gas_fee = tx.gas * tx.max_fee_per_gas
      if sender.balance < max_gas_fee + tx.value:
          raise InsufficientBalance

    Note: this uses `max_fee_per_gas` (the absolute cap), not
    `effective_gas_price` — the worst-case cost the sender could
    incur. Post-execution, the actual cost uses the lower
    effective_gas_price.

    Composes PR-K71 `tx_cost_compute` (#5723) + an inline
    byte-walk `>=` comparison (no dependency on still-pending
    PR-K50 `u256_lt`).

    Calling convention:
      a0 (input)  : max_fee_per_gas ptr (32 B BE)
      a1 (input)  : gas_limit (u64)
      a2 (input)  : value ptr (32 B BE)
      a3 (input)  : sender.balance ptr (32 B BE)
      ra (input)  : return
      a0 (output) :
        0  : balance >= tx_cost (ok)
        1  : tx_cost computation overflowed u256
        2  : balance < tx_cost (insufficient funds)

    Uses 32 bytes of `.data` scratch (`vtbal_cost_scratch`). -/
def validateTransactionBalanceFunction : String :=
  "validate_transaction_balance:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a3                   # save balance ptr\n" ++
  "  # tx_cost = tx_cost_compute(max_fee, gas_limit, value, vtbal_cost_scratch)\n" ++
  "  la a3, vtbal_cost_scratch\n" ++
  "  jal ra, tx_cost_compute\n" ++
  "  bnez a0, .Lvtbal_overflow\n" ++
  "  # Inline byte-walk: balance >= cost (MSB→LSB).\n" ++
  "  la t0, vtbal_cost_scratch   # cost ptr\n" ++
  "  mv t1, s0                   # balance ptr\n" ++
  "  li t2, 0\n" ++
  "  li t3, 32\n" ++
  ".Lvtbal_cmp:\n" ++
  "  beq t2, t3, .Lvtbal_ok      # all 32 bytes equal → balance == cost → ok\n" ++
  "  add t4, t1, t2\n" ++
  "  add t5, t0, t2\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  lbu a7, 0(t5)\n" ++
  "  bltu t6, a7, .Lvtbal_lt\n" ++
  "  bgtu t6, a7, .Lvtbal_ok\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lvtbal_cmp\n" ++
  ".Lvtbal_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lvtbal_ret\n" ++
  ".Lvtbal_lt:\n" ++
  "  li a0, 2\n" ++
  "  j .Lvtbal_ret\n" ++
  ".Lvtbal_overflow:\n" ++
  "  li a0, 1\n" ++
  ".Lvtbal_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_validate_transaction_balance`: probe BuildUnit. Reads
    (32B max_fee, 8B gas_limit LE, 32B value, 32B balance) from
    host input, writes 8-byte status to OUTPUT. -/
def ziskValidateTransactionBalancePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # max_fee ptr\n" ++
  "  ld a1, 40(a4)               # gas_limit (u64)\n" ++
  "  addi a2, a4, 48             # value ptr\n" ++
  "  addi a3, a4, 80             # balance ptr\n" ++
  "  jal ra, validate_transaction_balance\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvtbal_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  txCostComputeFunction ++ "\n" ++
  validateTransactionBalanceFunction ++ "\n" ++
  ".Lvtbal_pdone:"

def ziskValidateTransactionBalanceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "vtbal_cost_scratch:\n" ++
  "  .zero 32"

def ziskValidateTransactionBalanceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateTransactionBalancePrologue
  dataAsm     := ziskValidateTransactionBalanceDataSection
}


/-! ## validate_transaction_full -- PR-K80

    Top-level pre-EVM tx validator: compose all the cheap u64
    checks with the u256-arithmetic balance check.

      1. PR-K76 `validate_transaction_basic`   — chain_id / gas_limit /
                                                  nonce / intrinsic_gas
      2. PR-K79 `validate_transaction_balance` — balance >= max_fee * gas + value

    If any sub-step fails, this helper returns immediately with
    a composite status code (analogous to PR-K75 and K76):

      0          : all checks pass — tx ready for EVM dispatch
      101..103   : K76 step 1 (chain_id / gas_limit / nonce)
      201        : K76 step 2 (intrinsic_gas > gas_limit)
      301        : K79 step 1 (tx_cost overflow)
      302        : K79 step 2 (balance < tx_cost)

    Distinct decades let callers `floor(status/100)` to identify
    the failing layer.

    The argument packing follows K76 (a7 = (is_creation << 63) |
    data_len) and inserts a `max_fee_per_gas ptr` / `value ptr` /
    `balance ptr` triple in saved registers since RV64 has only
    8 arg regs.

    Calling convention:
      a0 (input)  : tx.chain_id (u64)
      a1 (input)  : block.chain_id (u64)
      a2 (input)  : tx.gas_limit (u64)
      a3 (input)  : block.gas_limit (u64)
      a4 (input)  : tx.nonce (u64)
      a5 (input)  : account.nonce (u64)
      a6 (input)  : data ptr
      a7 (input)  : packed input: low 32 = data_len, bit 63 = is_creation
      ra (input)  : return

    The three 32-byte pointers (max_fee_per_gas, value, balance)
    are passed through fixed `.data` slots that the caller
    populates BEFORE invoking this helper:
      vtf_max_fee  : 32 B u256 BE
      vtf_value    : 32 B u256 BE
      vtf_balance  : 32 B u256 BE

    a0 (output) : composite status code (see encoding above). -/
def validateTransactionFullFunction : String :=
  "validate_transaction_full:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  # Save tx.gas_limit (a2) for step 2 — K76 will not preserve\n" ++
  "  # caller's args, and step 2 needs it as a1 input.\n" ++
  "  mv s0, a2                   # tx.gas_limit\n" ++
  "  # Step 1: K76 validate_transaction_basic — args already in a0..a7.\n" ++
  "  jal ra, validate_transaction_basic\n" ++
  "  beqz a0, .Lvtf_s2\n" ++
  "  # Forward K76's code (100..201) directly — it's already in the\n" ++
  "  # K80 status table since K76 and K80 share the same decades.\n" ++
  "  j .Lvtf_ret\n" ++
  ".Lvtf_s2:\n" ++
  "  # Step 2: K79 validate_transaction_balance(max_fee, gas_limit,\n" ++
  "  #                                         value, balance)\n" ++
  "  la a0, vtf_max_fee\n" ++
  "  mv a1, s0                   # restored tx.gas_limit\n" ++
  "  la a2, vtf_value\n" ++
  "  la a3, vtf_balance\n" ++
  "  jal ra, validate_transaction_balance\n" ++
  "  beqz a0, .Lvtf_ret\n" ++
  "  li t0, 300\n" ++
  "  add a0, a0, t0\n" ++
  ".Lvtf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_validate_transaction_full`: probe BuildUnit. Reads
    (tx_chain, block_chain, tx_gas, block_gas, tx_nonce,
    account_nonce, is_creation, data_len, max_fee, value,
    balance, data_bytes) from host input; sets up the .data
    slots and a-regs; writes 8-byte composite status. -/
def ziskValidateTransactionFullPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0,  8(t0)               # tx.chain_id\n" ++
  "  ld a1, 16(t0)               # block.chain_id\n" ++
  "  ld a2, 24(t0)               # tx.gas_limit\n" ++
  "  ld a3, 32(t0)               # block.gas_limit\n" ++
  "  ld a4, 40(t0)               # tx.nonce\n" ++
  "  ld a5, 48(t0)               # account.nonce\n" ++
  "  ld t1, 56(t0)               # is_creation\n" ++
  "  ld t2, 64(t0)               # data_len\n" ++
  "  # Copy max_fee (offset 72..104) → vtf_max_fee\n" ++
  "  la t3, vtf_max_fee\n" ++
  "  addi t4, t0, 72\n" ++
  "  ld t5,  0(t4); sd t5,  0(t3)\n" ++
  "  ld t5,  8(t4); sd t5,  8(t3)\n" ++
  "  ld t5, 16(t4); sd t5, 16(t3)\n" ++
  "  ld t5, 24(t4); sd t5, 24(t3)\n" ++
  "  # Copy value (offset 104..136) → vtf_value\n" ++
  "  la t3, vtf_value\n" ++
  "  addi t4, t0, 104\n" ++
  "  ld t5,  0(t4); sd t5,  0(t3)\n" ++
  "  ld t5,  8(t4); sd t5,  8(t3)\n" ++
  "  ld t5, 16(t4); sd t5, 16(t3)\n" ++
  "  ld t5, 24(t4); sd t5, 24(t3)\n" ++
  "  # Copy balance (offset 136..168) → vtf_balance\n" ++
  "  la t3, vtf_balance\n" ++
  "  addi t4, t0, 136\n" ++
  "  ld t5,  0(t4); sd t5,  0(t3)\n" ++
  "  ld t5,  8(t4); sd t5,  8(t3)\n" ++
  "  ld t5, 16(t4); sd t5, 16(t3)\n" ++
  "  ld t5, 24(t4); sd t5, 24(t3)\n" ++
  "  addi a6, t0, 168            # data ptr (after balance)\n" ++
  "  # Pack a7\n" ++
  "  slli t1, t1, 63\n" ++
  "  li t6, 0xffffffff\n" ++
  "  and t2, t2, t6\n" ++
  "  or  a7, t1, t2\n" ++
  "  jal ra, validate_transaction_full\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvtf_pdone\n" ++
  txValidateAgainstBlockFunction ++ "\n" ++
  intrinsicGasLegacyFunction ++ "\n" ++
  txValidateIntrinsicGasLegacyFunction ++ "\n" ++
  validateTransactionBasicFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  txCostComputeFunction ++ "\n" ++
  validateTransactionBalanceFunction ++ "\n" ++
  validateTransactionFullFunction ++ "\n" ++
  ".Lvtf_pdone:"

def ziskValidateTransactionFullDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "vtbal_cost_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "vtb_gas_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "vtf_max_fee:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "vtf_value:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "vtf_balance:\n" ++
  "  .zero 32"

def ziskValidateTransactionFullProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateTransactionFullPrologue
  dataAsm     := ziskValidateTransactionFullDataSection
}


end EvmAsm.Codegen
