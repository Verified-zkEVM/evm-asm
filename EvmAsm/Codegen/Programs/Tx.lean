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
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.RlpFieldToU64StrictProgram
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.RlpFieldToU256BeOfflineAddrs

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
def rlpFieldToU64_legacy_prog : Program :=
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

/-! Historical lenient K34 wrapper. It preserves the original 32-byte ABI frame
    and `rfu_offset`/`rfu_length` scratch footprint, delegating to the lenient
    scalar decoder used by header/chain and account/BAL witness paths. -/
def rlpFieldToU64Wrapper_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x13,
    .SD .x9 .x0 (0 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64 + 28)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64 + 28)),
    .AUIPC .x14 (laHi GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64 + 36)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64 + 36)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.rlp_field_to_u64 + 44)),
    .BNE .x10 .x0 (brOff (GuestAddrs.rlp_field_to_u64 + 116) (GuestAddrs.rlp_field_to_u64 + 48)),
    .AUIPC .x5 (laHi GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64 + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64 + 52)),
    .LD .x10 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x10,
    .AUIPC .x5 (laHi GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64 + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64 + 68)),
    .LD .x11 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64
      (GuestAddrs.rlp_field_to_u64 + 80)),
    .BNE .x11 .x0 (16 : BitVec 13),
    .SD .x9 .x10 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x5 (2 : Word),
    .BEQ .x11 .x5 (20 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpFieldToU64_prog : Program :=
  rlpFieldToU64Wrapper_prog

#guard rlpFieldToU64_prog.length = 37

/-- Reloc side-table for the lenient K34 wrapper. -/
def rlpFieldToU64_relocs : RelocTable :=
  [ (7, .la .x13 "rfu_offset"),
    (9, .la .x14 "rfu_length"),
    (11, .jal .x1 "rlp_list_nth_item"),
    (13, .la .x5 "rfu_offset"),
    (17, .la .x5 "rfu_length"),
    (20, .jal .x1 "rlp_content_to_u64") ]

/-- The historical lenient K34 label retained for header/chain-number paths. -/
def rlpFieldToU64Function : String :=
  "rlp_field_to_u64:\n" ++ emitProgramR rlpFieldToU64_prog rlpFieldToU64_relocs

theorem rlpFieldToU64Function_eq_prog :
    rlpFieldToU64Function =
      "rlp_field_to_u64:\n" ++ emitProgramR rlpFieldToU64_prog rlpFieldToU64_relocs := rfl

#guard rlpFieldToU64Function.startsWith "rlp_field_to_u64:\n"

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
    .AUIPC .x13 (laHi GuestAddrs.rfu_offset (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 40)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rfu_offset (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 40)),
    .AUIPC .x14 (laHi GuestAddrs.rfu_length (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 48)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rfu_length (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 48)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 56)),
    .BNE .x10 .x0 (92 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rfu_length (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 64)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rfu_length (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 64)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BLTU .x7 .x6 (64 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.rfu_offset (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rfu_offset (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 84)),
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
/-- Probe-only entry PC: `tx_legacy_decode` is not a symbol in the linked
    `stateless_guest` image at this ref.  The emitted string keeps all
    cross-image calls symbolic; this placeholder only anchors the concrete
    verification `Program`, as for the other unlinked probe routines. -/
def txLegacyDecodePc : Nat := 0x80000000

def txLegacyDecode_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x18 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (txLegacyDecodePc + 32)),
    .BNE .x12 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 36)),
    .MV .x9 .x11,
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (txLegacyDecodePc + 56)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 64)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (txLegacyDecodePc + 76)),
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 80)),
    .SD .x18 .x10 (0 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (txLegacyDecodePc + 96)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 104)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (txLegacyDecodePc + 120)),
    .BNE .x10 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 124)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (txLegacyDecodePc + 136)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 144)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (txLegacyDecodePc + 156)),
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 160)),
    .SD .x18 .x10 (40 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (txLegacyDecodePc + 176)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 184)),
    .BEQ .x12 .x0 (56 : BitVec 13),
    .LI .x5 (20 : Word),
    .BNE .x12 .x5 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 196)),
    .SUB .x28 .x10 .x12,
    .ADDI .x29 .x18 (48 : BitVec 12),
    .LD .x30 .x28 (0 : BitVec 12),
    .SD .x29 .x30 (0 : BitVec 12),
    .LD .x30 .x28 (8 : BitVec 12),
    .SD .x29 .x30 (8 : BitVec 12),
    .LWU .x30 .x28 (16 : BitVec 12),
    .SW .x29 .x30 (16 : BitVec 12),
    .LI .x30 (1 : Word),
    .SD .x18 .x30 (68 : BitVec 12),
    .JAL .x0 (24 : BitVec 21),
    .ADDI .x29 .x18 (48 : BitVec 12),
    .SD .x29 .x0 (0 : BitVec 12),
    .SD .x29 .x0 (8 : BitVec 12),
    .SW .x29 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (68 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (txLegacyDecodePc + 272)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 280)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (76 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (txLegacyDecodePc + 296)),
    .BNE .x10 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 300)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (txLegacyDecodePc + 312)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 320)),
    .SUB .x28 .x10 .x12,
    .SUB .x6 .x28 .x8,
    .SD .x18 .x6 (108 : BitVec 12),
    .SD .x18 .x12 (116 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (txLegacyDecodePc + 348)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 356)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (txLegacyDecodePc + 368)),
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 372)),
    .SD .x18 .x10 (124 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (txLegacyDecodePc + 388)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (txLegacyDecodePc + 468) (txLegacyDecodePc + 396)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (132 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (txLegacyDecodePc + 412)),
    .BNE .x10 .x0 (52 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (txLegacyDecodePc + 428)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (32 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (164 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (txLegacyDecodePc + 452)),
    .BNE .x10 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txLegacyDecode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txLegacyDecode_relocs : RelocTable :=
  [ (8, .jal .x1 "rlp_walk_init"),
    (14, .jal .x1 "rlp_walk_next"),
    (19, .jal .x1 "rlp_content_to_u64_strict"),
    (24, .jal .x1 "rlp_walk_next"),
    (30, .jal .x1 "rlp_content_to_u256_be_strict"),
    (34, .jal .x1 "rlp_walk_next"),
    (39, .jal .x1 "rlp_content_to_u64_strict"),
    (44, .jal .x1 "rlp_walk_next"),
    (68, .jal .x1 "rlp_walk_next"),
    (74, .jal .x1 "rlp_content_to_u256_be_strict"),
    (78, .jal .x1 "rlp_walk_next"),
    (87, .jal .x1 "rlp_walk_next"),
    (92, .jal .x1 "rlp_content_to_u64_strict"),
    (97, .jal .x1 "rlp_walk_next"),
    (103, .jal .x1 "rlp_content_to_u256_be_strict"),
    (107, .jal .x1 "rlp_walk_next"),
    (113, .jal .x1 "rlp_content_to_u256_be_strict") ]

def txLegacyDecodeFunction : String :=
  "tx_legacy_decode:\n" ++ emitProgramR txLegacyDecode_prog txLegacyDecode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txLegacyDecode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). This entry is probe-only at the current link,
    so the concrete Program uses `txLegacyDecodePc`; symbolic assemble identity
    is the applicable coverage gate. -/
theorem txLegacyDecodeFunction_eq_prog :
    txLegacyDecodeFunction = "tx_legacy_decode:\n" ++ emitProgramR txLegacyDecode_prog txLegacyDecode_relocs := rfl

#guard txLegacyDecodeFunction.startsWith "tx_legacy_decode:\n"
#guard txLegacyDecode_prog.length = 125

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

    Composes PR-K47 `rlp_list_count_items` (#5532) via `jal`, then a `mul`
    by `gas_per_blob`. `rlp_list_count_items` is called, not inlined
    (separate linked symbol; see #12512).

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
/-! Probe-only local PC placeholder. -/
def blobGasUsedFromVersionedHashesPc : Nat := 0x80000000

def blobGasUsedFromVersionedHashes_prog : Program :=
  [ .ADDI .x2 .x2 (-24 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .AUIPC .x12 (laHi GuestAddrs.bgvh_count_scratch (blobGasUsedFromVersionedHashesPc + 24)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bgvh_count_scratch (blobGasUsedFromVersionedHashesPc + 24)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (blobGasUsedFromVersionedHashesPc + 32)),
    .BNE .x10 .x0 (32 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.bgvh_count_scratch (blobGasUsedFromVersionedHashesPc + 40)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bgvh_count_scratch (blobGasUsedFromVersionedHashesPc + 40)),
    .LD .x6 .x5 (0 : BitVec 12),
    .MUL .x7 .x6 .x8,
    .SD .x9 .x7 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .SD .x9 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (24 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blobGasUsedFromVersionedHashes_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blobGasUsedFromVersionedHashes_relocs : RelocTable :=
  [ (6, .la .x12 "bgvh_count_scratch"),
    (8, .jal .x1 "rlp_list_count_items"),
    (10, .la .x5 "bgvh_count_scratch") ]

def blobGasUsedFromVersionedHashesFunction : String :=
  "blob_gas_used_from_versioned_hashes:\n" ++ emitProgramR blobGasUsedFromVersionedHashes_prog blobGasUsedFromVersionedHashes_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blobGasUsedFromVersionedHashes_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blobGasUsedFromVersionedHashesFunction_eq_prog :
    blobGasUsedFromVersionedHashesFunction = "blob_gas_used_from_versioned_hashes:\n" ++ emitProgramR blobGasUsedFromVersionedHashes_prog blobGasUsedFromVersionedHashes_relocs := rfl

#guard blobGasUsedFromVersionedHashesFunction.startsWith "blob_gas_used_from_versioned_hashes:\n"
#guard blobGasUsedFromVersionedHashes_prog.length = 24

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

end EvmAsm.Codegen
