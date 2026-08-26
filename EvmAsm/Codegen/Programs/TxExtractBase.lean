/-
  EvmAsm.Codegen.Programs.TxExtractBase

  Per-field transaction extractors + typed-tx dispatcher carved
  out of `EvmAsm.Codegen.Programs.Tx` per the file-size hard cap.
  Hosts:

    K40   tx_type_dispatch         (typed-tx prefix detector)
    K101  tx_extract_to_address    (to address)
    K102  tx_extract_nonce_and_gas (nonce + gas_limit)
    K103  tx_extract_value         (value u256)
    K104  tx_extract_data_section  (calldata bytes)
    K108  tx_extract_gas_pricing   (gas_price / max_fee / priority_fee)

  Each takes a tx-bytes ptr + length and returns the specific
  field via caller-supplied output buffer(s). Newer extractors use
  `RlpWalk.lean` cursor helpers for ordered field access; older
  access-list helpers still compose K20 / K34 / K35 helpers from
  `RlpRead.lean` + `Tx.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.U256GasPricing

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

private def repeatAsm : Nat -> String -> String
  | 0, _ => ""
  | n + 1, s => s ++ repeatAsm n s

private def txExtractWalkSkipAsm (failLabel : String) (n : Nat) : String :=
  repeatAsm n <|
    "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, " ++ failLabel ++ "; mv s5, a0\n"

private def txExtractWalkFieldAsm (failLabel : String) (n : Nat) : String :=
  txExtractWalkSkipAsm failLabel n ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, " ++ failLabel ++ "\n" ++
  "  sub t6, a0, a2              # content ptr\n"

/-! ## tx_type_dispatch -- PR-K40 typed-tx prefix detector

    Read the first byte of an RLP/typed-tx-encoded transaction
    and return the type code + inner-RLP offset:

      byte 0 in 0xc0..0xfe → legacy (type=0, inner_offset=0)
      byte 0 == 0x01    → EIP-2930 access list (type=1, inner_offset=1)
      byte 0 == 0x02    → EIP-1559 dynamic fee  (type=2, inner_offset=1)
      byte 0 == 0x03    → EIP-4844 blob         (type=3, inner_offset=1)
      byte 0 == 0x04    → EIP-7702 set code     (type=4, inner_offset=1)
      else              → invalid (status=1)

    Callers consume `inner_offset` to skip the type prefix
    before passing the remaining bytes to the type-specific
    decoder.

    Calling convention:
      a0 (input)  : tx_bytes ptr
      a1 (input)  : tx_bytes byte length
      a2 (input)  : u64 type code out
      a3 (input)  : u64 inner_offset out
      ra (input)  : return
      a0 (output) : 0 success / 1 unknown / empty input

    Leaf-callable, no scratch. -/
def txTypeDispatch_prog : Program :=
  [ .BEQ .x11 .x0 (164 : BitVec 13),
    .LBU .x5 .x10 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BGEU .x5 .x6 (brOff (GuestAddrs.tx_type_dispatch + 180) (GuestAddrs.tx_type_dispatch + 12)),
    .LI .x6 (1 : Word),
    .BEQ .x5 .x6 (48 : BitVec 13),
    .LI .x6 (2 : Word),
    .BEQ .x5 .x6 (64 : BitVec 13),
    .LI .x6 (3 : Word),
    .BEQ .x5 .x6 (80 : BitVec 13),
    .LI .x6 (4 : Word),
    .BEQ .x5 .x6 (96 : BitVec 13),
    .JAL .x0 (116 : BitVec 21),
    .SD .x12 .x0 (0 : BitVec 12),
    .SD .x13 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (1 : Word),
    .SD .x12 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x13 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (2 : Word),
    .SD .x12 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x13 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (3 : Word),
    .SD .x12 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x13 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (4 : Word),
    .SD .x12 .x5 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x13 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x12 .x0 (0 : BitVec 12),
    .SD .x13 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x6 (255 : Word),
    .BEQ .x5 .x6 (-20 : BitVec 13),
    .JAL .x0 (-136 : BitVec 21) ]

def txTypeDispatchFunction : String :=
  "tx_type_dispatch:\n" ++ emitProgram txTypeDispatch_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `txTypeDispatch_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem txTypeDispatchFunction_eq_prog :
    txTypeDispatchFunction = "tx_type_dispatch:\n" ++ emitProgram txTypeDispatch_prog := rfl

#guard txTypeDispatchFunction.startsWith "tx_type_dispatch:\n"
#guard txTypeDispatch_prog.length = 48

/-! ## tx_extract_nonce_and_gas -- PR-K102

    Extract the (`nonce`, `gas_limit`) pair from any encoded tx
    type. Both are u64-bounded by EIP-2681 / EIP-1559 / EIP-4844.

    Per-type field indices (post type-byte stripping):

      type 0 legacy   : nonce = 0,  gas_limit = 2
      type 1 EIP-2930 : nonce = 1,  gas_limit = 3
      type 2 EIP-1559 : nonce = 1,  gas_limit = 4
      type 3 EIP-4844 : nonce = 1,  gas_limit = 4
      type 4 EIP-7702 : nonce = 1,  gas_limit = 4

    Composes:
      - PR-K40 `tx_type_dispatch`  — typed-tx detector
      - RlpWalk cursor helpers     — ordered field extraction
      - canonical content-to-u64   — u64 decoding

    Useful as a fast prelude to `check_transaction` (nonce
    ordering + gas-availability) without a full per-type decode.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : u64 nonce out ptr
      a3 (input)  : u64 gas_limit out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : nonce field extraction failed
        3 : gas_limit field extraction failed
        4 : nonce exceeds EIP-2681 maximum (`2^64 - 2`)

    Both outputs are zeroed on failure. Uses two 8-byte `.data`
    scratch slots (`teng_type`, `teng_inner_off`). -/
def txExtractNonceAndGas_prog : Program :=
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
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.teng_type (GuestAddrs.tx_extract_nonce_and_gas + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teng_type (GuestAddrs.tx_extract_nonce_and_gas + 72)),
    .AUIPC .x13 (laHi GuestAddrs.teng_inner_off (GuestAddrs.tx_extract_nonce_and_gas + 80)),
    .ADDI .x13 .x13 (laLo GuestAddrs.teng_inner_off (GuestAddrs.tx_extract_nonce_and_gas + 80)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_extract_nonce_and_gas + 88)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_nonce_and_gas + 492) (GuestAddrs.tx_extract_nonce_and_gas + 100)),
    .AUIPC .x5 (laHi GuestAddrs.teng_type (GuestAddrs.tx_extract_nonce_and_gas + 104)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teng_type (GuestAddrs.tx_extract_nonce_and_gas + 104)),
    .LD .x20 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teng_inner_off (GuestAddrs.tx_extract_nonce_and_gas + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teng_inner_off (GuestAddrs.tx_extract_nonce_and_gas + 116)),
    .LD .x30 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x30,
    .SUB .x11 .x9 .x30,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_extract_nonce_and_gas + 136)),
    .BNE .x12 .x0 (brOff (GuestAddrs.tx_extract_nonce_and_gas + 244) (GuestAddrs.tx_extract_nonce_and_gas + 140)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .LI .x5 (0 : Word),
    .BEQ .x20 .x5 (48 : BitVec 13),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_nonce_and_gas + 168)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_nonce_and_gas + 244) (GuestAddrs.tx_extract_nonce_and_gas + 172)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_nonce_and_gas + 188)),
    .BNE .x11 .x0 (52 : BitVec 13),
    .SUB .x31 .x10 .x12,
    .JAL .x0 (24 : BitVec 21),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_nonce_and_gas + 212)),
    .BNE .x11 .x0 (28 : BitVec 13),
    .SUB .x31 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x31,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_extract_nonce_and_gas + 236)),
    .BEQ .x11 .x0 (16 : BitVec 13),
    .SD .x18 .x0 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_nonce_and_gas + 492) (GuestAddrs.tx_extract_nonce_and_gas + 252)),
    .SD .x18 .x10 (0 : BitVec 12),
    .LD .x5 .x18 (0 : BitVec 12),
    .LI .x6 (-1 : Word),
    .BNE .x5 .x6 (16 : BitVec 13),
    .SD .x18 .x0 (0 : BitVec 12),
    .LI .x10 (4 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_nonce_and_gas + 492) (GuestAddrs.tx_extract_nonce_and_gas + 280)),
    .MV .x21 .x23,
    .LI .x5 (0 : Word),
    .BEQ .x20 .x5 (brOff (GuestAddrs.tx_extract_nonce_and_gas + 368) (GuestAddrs.tx_extract_nonce_and_gas + 292)),
    .LI .x5 (1 : Word),
    .BEQ .x20 .x5 (brOff (GuestAddrs.tx_extract_nonce_and_gas + 412) (GuestAddrs.tx_extract_nonce_and_gas + 300)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_nonce_and_gas + 312)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_nonce_and_gas + 468) (GuestAddrs.tx_extract_nonce_and_gas + 316)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_nonce_and_gas + 332)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_nonce_and_gas + 468) (GuestAddrs.tx_extract_nonce_and_gas + 336)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_nonce_and_gas + 352)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_nonce_and_gas + 468) (GuestAddrs.tx_extract_nonce_and_gas + 356)),
    .SUB .x31 .x10 .x12,
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_nonce_and_gas + 452) (GuestAddrs.tx_extract_nonce_and_gas + 364)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_nonce_and_gas + 376)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_nonce_and_gas + 468) (GuestAddrs.tx_extract_nonce_and_gas + 380)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_nonce_and_gas + 396)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_nonce_and_gas + 468) (GuestAddrs.tx_extract_nonce_and_gas + 400)),
    .SUB .x31 .x10 .x12,
    .JAL .x0 (44 : BitVec 21),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_nonce_and_gas + 420)),
    .BNE .x11 .x0 (44 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_nonce_and_gas + 440)),
    .BNE .x11 .x0 (24 : BitVec 13),
    .SUB .x31 .x10 .x12,
    .MV .x10 .x31,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.tx_extract_nonce_and_gas + 460)),
    .BEQ .x11 .x0 (16 : BitVec 13),
    .SD .x19 .x0 (0 : BitVec 12),
    .LI .x10 (3 : Word),
    .JAL .x0 (16 : BitVec 21),
    .SD .x19 .x10 (0 : BitVec 12),
    .JAL .x0 (4 : BitVec 21),
    .LI .x10 (0 : Word),
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

/-- Reloc side-table for `txExtractNonceAndGas_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txExtractNonceAndGas_relocs : RelocTable :=
  [ (18, .la .x12 "teng_type"),
    (20, .la .x13 "teng_inner_off"),
    (22, .jal .x1 "tx_type_dispatch"),
    (26, .la .x5 "teng_type"),
    (29, .la .x5 "teng_inner_off"),
    (34, .jal .x1 "rlp_walk_init"),
    (42, .jal .x1 "rlp_walk_next"),
    (47, .jal .x1 "rlp_walk_next"),
    (53, .jal .x1 "rlp_walk_next"),
    (59, .jal .x1 "rlp_content_to_u64_strict"),
    (78, .jal .x1 "rlp_walk_next"),
    (83, .jal .x1 "rlp_walk_next"),
    (88, .jal .x1 "rlp_walk_next"),
    (94, .jal .x1 "rlp_walk_next"),
    (99, .jal .x1 "rlp_walk_next"),
    (105, .jal .x1 "rlp_walk_next"),
    (110, .jal .x1 "rlp_walk_next"),
    (115, .jal .x1 "rlp_content_to_u64_strict") ]

def txExtractNonceAndGasFunction : String :=
  "tx_extract_nonce_and_gas:\n" ++ emitProgramR txExtractNonceAndGas_prog txExtractNonceAndGas_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txExtractNonceAndGas_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txExtractNonceAndGasFunction_eq_prog :
    txExtractNonceAndGasFunction = "tx_extract_nonce_and_gas:\n" ++ emitProgramR txExtractNonceAndGas_prog txExtractNonceAndGas_relocs := rfl

#guard txExtractNonceAndGasFunction.startsWith "tx_extract_nonce_and_gas:\n"
#guard txExtractNonceAndGas_prog.length = 134
/-! ## tx_extract_to_address -- PR-K101

    For any encoded tx (legacy or typed), extract the `to`
    (recipient) field and a contract-creation flag:

      is_creation = (to_field_length == 0)
      to_bytes    = 20 raw bytes when not creation, zeros otherwise

    Per-type RLP layout — the field index of `to`:

      type 0 legacy   : field 3 of the outer list
      type 1 EIP-2930 : field 4 of the inner RLP
      type 2 EIP-1559 : field 5 of the inner RLP
      type 3 EIP-4844 : field 5 of the inner RLP
      type 4 EIP-7702 : field 5 of the inner RLP

    Composes:
      - PR-K40 `tx_type_dispatch`   — typed-tx detector
      - RlpWalk cursor helpers      — field extractor

    Useful for `apply_body` (CREATE vs CALL routing) and for any
    pre-EVM check that needs the recipient without doing a full
    per-type decode.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : 20-byte output ptr (zeros on creation / fail)
      a3 (input)  : u64 out ptr (is_creation flag, 0 or 1)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : `to` field extraction failed (not 0 or 20 B)

    Uses two 8-byte `.data` scratch slots (`tea_type` + `tea_inner_off`). -/
def txExtractToAddress_prog : Program :=
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
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SW .x18 .x0 (16 : BitVec 12),
    .SD .x19 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.tea_type (GuestAddrs.tx_extract_to_address + 80)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tea_type (GuestAddrs.tx_extract_to_address + 80)),
    .AUIPC .x13 (laHi GuestAddrs.tea_inner_off (GuestAddrs.tx_extract_to_address + 88)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tea_inner_off (GuestAddrs.tx_extract_to_address + 88)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_extract_to_address + 96)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_to_address + 556) (GuestAddrs.tx_extract_to_address + 108)),
    .AUIPC .x5 (laHi GuestAddrs.tea_type (GuestAddrs.tx_extract_to_address + 112)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tea_type (GuestAddrs.tx_extract_to_address + 112)),
    .LD .x20 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tea_inner_off (GuestAddrs.tx_extract_to_address + 124)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tea_inner_off (GuestAddrs.tx_extract_to_address + 124)),
    .LD .x30 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x30,
    .SUB .x11 .x9 .x30,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_extract_to_address + 144)),
    .BNE .x12 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 148)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .LI .x5 (0 : Word),
    .BEQ .x20 .x5 (brOff (GuestAddrs.tx_extract_to_address + 300) (GuestAddrs.tx_extract_to_address + 164)),
    .LI .x5 (1 : Word),
    .BEQ .x20 .x5 (brOff (GuestAddrs.tx_extract_to_address + 384) (GuestAddrs.tx_extract_to_address + 172)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 184)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 188)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 204)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 208)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 224)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 228)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 244)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 248)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 264)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 268)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 284)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 288)),
    .SUB .x31 .x10 .x12,
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_to_address + 484) (GuestAddrs.tx_extract_to_address + 296)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 308)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 312)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 328)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 332)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 348)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 352)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 368)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 372)),
    .SUB .x31 .x10 .x12,
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_to_address + 484) (GuestAddrs.tx_extract_to_address + 380)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 392)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 396)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 412)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 416)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 432)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 436)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 452)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 456)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_to_address + 472)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_to_address + 552) (GuestAddrs.tx_extract_to_address + 476)),
    .SUB .x31 .x10 .x12,
    .MV .x7 .x12,
    .BEQ .x7 .x0 (48 : BitVec 13),
    .LI .x6 (20 : Word),
    .BNE .x7 .x6 (56 : BitVec 13),
    .LD .x5 .x31 (0 : BitVec 12),
    .SD .x18 .x5 (0 : BitVec 12),
    .LD .x5 .x31 (8 : BitVec 12),
    .SD .x18 .x5 (8 : BitVec 12),
    .LWU .x5 .x31 (16 : BitVec 12),
    .SW .x18 .x5 (16 : BitVec 12),
    .SD .x19 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x5 (1 : Word),
    .SD .x19 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
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
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txExtractToAddress_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txExtractToAddress_relocs : RelocTable :=
  [ (20, .la .x12 "tea_type"),
    (22, .la .x13 "tea_inner_off"),
    (24, .jal .x1 "tx_type_dispatch"),
    (28, .la .x5 "tea_type"),
    (31, .la .x5 "tea_inner_off"),
    (36, .jal .x1 "rlp_walk_init"),
    (46, .jal .x1 "rlp_walk_next"),
    (51, .jal .x1 "rlp_walk_next"),
    (56, .jal .x1 "rlp_walk_next"),
    (61, .jal .x1 "rlp_walk_next"),
    (66, .jal .x1 "rlp_walk_next"),
    (71, .jal .x1 "rlp_walk_next"),
    (77, .jal .x1 "rlp_walk_next"),
    (82, .jal .x1 "rlp_walk_next"),
    (87, .jal .x1 "rlp_walk_next"),
    (92, .jal .x1 "rlp_walk_next"),
    (98, .jal .x1 "rlp_walk_next"),
    (103, .jal .x1 "rlp_walk_next"),
    (108, .jal .x1 "rlp_walk_next"),
    (113, .jal .x1 "rlp_walk_next"),
    (118, .jal .x1 "rlp_walk_next") ]

def txExtractToAddressFunction : String :=
  "tx_extract_to_address:\n" ++ emitProgramR txExtractToAddress_prog txExtractToAddress_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txExtractToAddress_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txExtractToAddressFunction_eq_prog :
    txExtractToAddressFunction = "tx_extract_to_address:\n" ++ emitProgramR txExtractToAddress_prog txExtractToAddress_relocs := rfl

#guard txExtractToAddressFunction.startsWith "tx_extract_to_address:\n"
#guard txExtractToAddress_prog.length = 150
/-! ## tx_extract_value -- PR-K103

    Extract the `value` field (u256 BE) from any encoded tx type.
    `value` is the amount of wei the tx transfers to its `to`
    recipient (or contributes to the new account's balance on
    CREATE).

    Per-type RLP layout — the field index of `value`:

      type 0 legacy   : field 4 of the outer list
      type 1 EIP-2930 : field 5 of the inner RLP
      type 2 EIP-1559 : field 6 of the inner RLP
      type 3 EIP-4844 : field 6 of the inner RLP
      type 4 EIP-7702 : field 6 of the inner RLP

    Composes:
      - PR-K40 `tx_type_dispatch`        — typed-tx detector
      - RlpWalk cursor helpers           — field extraction
      - canonical content-to-u256 helper — u256 BE decoding

    Useful for balance checks (`sender_balance >= value + gas_cost`)
    and for the priority-fee credit path. Together with PR-K101
    (`to` address) and PR-K102 (nonce + gas), this covers the
    fields `check_transaction` and `process_transaction` need from
    a tx without doing a full per-type decode.

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : 32-byte output ptr (u256 BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed (unknown / empty input)
        2 : value field extraction failed (parse error or > 256 bits)

    Output zeroed on failure. Uses two 8-byte `.data` scratch
    slots (`tev_type`, `tev_inner_off`). -/
def txExtractValue_prog : Program :=
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
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.tev_type (GuestAddrs.tx_extract_value + 76)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tev_type (GuestAddrs.tx_extract_value + 76)),
    .AUIPC .x13 (laHi GuestAddrs.tev_inner_off (GuestAddrs.tx_extract_value + 84)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tev_inner_off (GuestAddrs.tx_extract_value + 84)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_extract_value + 92)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_value + 588) (GuestAddrs.tx_extract_value + 104)),
    .AUIPC .x5 (laHi GuestAddrs.tev_type (GuestAddrs.tx_extract_value + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tev_type (GuestAddrs.tx_extract_value + 108)),
    .LD .x19 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tev_inner_off (GuestAddrs.tx_extract_value + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tev_inner_off (GuestAddrs.tx_extract_value + 120)),
    .LD .x30 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x30,
    .SUB .x11 .x9 .x30,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_extract_value + 140)),
    .BNE .x12 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 144)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .LI .x5 (0 : Word),
    .BEQ .x19 .x5 (brOff (GuestAddrs.tx_extract_value + 316) (GuestAddrs.tx_extract_value + 160)),
    .LI .x5 (1 : Word),
    .BEQ .x19 .x5 (brOff (GuestAddrs.tx_extract_value + 420) (GuestAddrs.tx_extract_value + 168)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 180)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 184)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 200)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 204)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 220)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 224)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 240)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 244)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 260)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 264)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 280)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 284)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 300)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 304)),
    .SUB .x31 .x10 .x12,
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_value + 540) (GuestAddrs.tx_extract_value + 312)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 324)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 328)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 344)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 348)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 364)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 368)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 384)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 388)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 404)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 408)),
    .SUB .x31 .x10 .x12,
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_value + 540) (GuestAddrs.tx_extract_value + 416)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 428)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 432)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 448)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 452)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 468)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 472)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 488)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_value + 560) (GuestAddrs.tx_extract_value + 492)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 508)),
    .BNE .x11 .x0 (48 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_value + 528)),
    .BNE .x11 .x0 (28 : BitVec 13),
    .SUB .x31 .x10 .x12,
    .MV .x10 .x31,
    .MV .x11 .x12,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_extract_value + 552)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .LI .x10 (2 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
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

/-- Reloc side-table for `txExtractValue_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txExtractValue_relocs : RelocTable :=
  [ (19, .la .x12 "tev_type"),
    (21, .la .x13 "tev_inner_off"),
    (23, .jal .x1 "tx_type_dispatch"),
    (27, .la .x5 "tev_type"),
    (30, .la .x5 "tev_inner_off"),
    (35, .jal .x1 "rlp_walk_init"),
    (45, .jal .x1 "rlp_walk_next"),
    (50, .jal .x1 "rlp_walk_next"),
    (55, .jal .x1 "rlp_walk_next"),
    (60, .jal .x1 "rlp_walk_next"),
    (65, .jal .x1 "rlp_walk_next"),
    (70, .jal .x1 "rlp_walk_next"),
    (75, .jal .x1 "rlp_walk_next"),
    (81, .jal .x1 "rlp_walk_next"),
    (86, .jal .x1 "rlp_walk_next"),
    (91, .jal .x1 "rlp_walk_next"),
    (96, .jal .x1 "rlp_walk_next"),
    (101, .jal .x1 "rlp_walk_next"),
    (107, .jal .x1 "rlp_walk_next"),
    (112, .jal .x1 "rlp_walk_next"),
    (117, .jal .x1 "rlp_walk_next"),
    (122, .jal .x1 "rlp_walk_next"),
    (127, .jal .x1 "rlp_walk_next"),
    (132, .jal .x1 "rlp_walk_next"),
    (138, .jal .x1 "rlp_content_to_u256_be_strict") ]

def txExtractValueFunction : String :=
  "tx_extract_value:\n" ++ emitProgramR txExtractValue_prog txExtractValue_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txExtractValue_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txExtractValueFunction_eq_prog :
    txExtractValueFunction = "tx_extract_value:\n" ++ emitProgramR txExtractValue_prog txExtractValue_relocs := rfl

#guard txExtractValueFunction.startsWith "tx_extract_value:\n"
#guard txExtractValue_prog.length = 158
/-! ## tx_extract_data_section -- PR-K104

    Extract the `data` (calldata / init-code) field's absolute
    pointer and byte length from any encoded tx type. The data
    field is variable-length: 0 bytes for value transfers, up to
    `MAX_INIT_CODE_SIZE` bytes for contract creations, longer for
    `CALL`-style payloads.

    Per-type RLP layout — the field index of `data`:

      type 0 legacy   : field 5 of the outer list
      type 1 EIP-2930 : field 6 of the inner RLP
      type 2 EIP-1559 : field 7 of the inner RLP
      type 3 EIP-4844 : field 7 of the inner RLP
      type 4 EIP-7702 : field 7 of the inner RLP

    Composes:
      - PR-K40 `tx_type_dispatch`   — typed-tx detector
      - RlpWalk cursor helpers      — byte-string content bounds

    Useful for:
    - intrinsic-gas pricing (zero/non-zero byte counts)
    - EIP-3860 init-code size check (CREATE / CREATE2)
    - feeding the EVM's `calldata` region pre-execution

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : u64 out ptr (data_ptr — absolute address)
      a3 (input)  : u64 out ptr (data_len)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : data field extraction failed (parse error)

    Both outputs zeroed on failure. Uses two 8-byte `.data`
    scratch slots (`teds_type`, `teds_inner_off`). -/
def txExtractDataSection_prog : Program :=
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
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.teds_type (GuestAddrs.tx_extract_data_section + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teds_type (GuestAddrs.tx_extract_data_section + 72)),
    .AUIPC .x13 (laHi GuestAddrs.teds_inner_off (GuestAddrs.tx_extract_data_section + 80)),
    .ADDI .x13 .x13 (laLo GuestAddrs.teds_inner_off (GuestAddrs.tx_extract_data_section + 80)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_extract_data_section + 88)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_data_section + 616) (GuestAddrs.tx_extract_data_section + 100)),
    .AUIPC .x5 (laHi GuestAddrs.teds_type (GuestAddrs.tx_extract_data_section + 104)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teds_type (GuestAddrs.tx_extract_data_section + 104)),
    .LD .x20 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.teds_inner_off (GuestAddrs.tx_extract_data_section + 116)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teds_inner_off (GuestAddrs.tx_extract_data_section + 116)),
    .LD .x30 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x30,
    .SUB .x11 .x9 .x30,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_extract_data_section + 136)),
    .BNE .x12 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 140)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .LI .x5 (0 : Word),
    .BEQ .x20 .x5 (brOff (GuestAddrs.tx_extract_data_section + 332) (GuestAddrs.tx_extract_data_section + 156)),
    .LI .x5 (1 : Word),
    .BEQ .x20 .x5 (brOff (GuestAddrs.tx_extract_data_section + 456) (GuestAddrs.tx_extract_data_section + 164)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 176)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 180)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 196)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 200)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 216)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 220)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 236)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 240)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 256)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 260)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 276)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 280)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 296)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 300)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 316)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 320)),
    .SUB .x31 .x10 .x12,
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_data_section + 596) (GuestAddrs.tx_extract_data_section + 328)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 340)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 344)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 360)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 364)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 380)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 384)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 400)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 404)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 420)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 424)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 440)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 444)),
    .SUB .x31 .x10 .x12,
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_data_section + 596) (GuestAddrs.tx_extract_data_section + 452)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 464)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 468)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 484)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 488)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 504)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 508)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 524)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 528)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 544)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_data_section + 612) (GuestAddrs.tx_extract_data_section + 548)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 564)),
    .BNE .x11 .x0 (44 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_data_section + 584)),
    .BNE .x11 .x0 (24 : BitVec 13),
    .SUB .x31 .x10 .x12,
    .SD .x18 .x31 (0 : BitVec 12),
    .SD .x19 .x12 (0 : BitVec 12),
    .LI .x10 (0 : Word),
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
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txExtractDataSection_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txExtractDataSection_relocs : RelocTable :=
  [ (18, .la .x12 "teds_type"),
    (20, .la .x13 "teds_inner_off"),
    (22, .jal .x1 "tx_type_dispatch"),
    (26, .la .x5 "teds_type"),
    (29, .la .x5 "teds_inner_off"),
    (34, .jal .x1 "rlp_walk_init"),
    (44, .jal .x1 "rlp_walk_next"),
    (49, .jal .x1 "rlp_walk_next"),
    (54, .jal .x1 "rlp_walk_next"),
    (59, .jal .x1 "rlp_walk_next"),
    (64, .jal .x1 "rlp_walk_next"),
    (69, .jal .x1 "rlp_walk_next"),
    (74, .jal .x1 "rlp_walk_next"),
    (79, .jal .x1 "rlp_walk_next"),
    (85, .jal .x1 "rlp_walk_next"),
    (90, .jal .x1 "rlp_walk_next"),
    (95, .jal .x1 "rlp_walk_next"),
    (100, .jal .x1 "rlp_walk_next"),
    (105, .jal .x1 "rlp_walk_next"),
    (110, .jal .x1 "rlp_walk_next"),
    (116, .jal .x1 "rlp_walk_next"),
    (121, .jal .x1 "rlp_walk_next"),
    (126, .jal .x1 "rlp_walk_next"),
    (131, .jal .x1 "rlp_walk_next"),
    (136, .jal .x1 "rlp_walk_next"),
    (141, .jal .x1 "rlp_walk_next"),
    (146, .jal .x1 "rlp_walk_next") ]

def txExtractDataSectionFunction : String :=
  "tx_extract_data_section:\n" ++ emitProgramR txExtractDataSection_prog txExtractDataSection_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txExtractDataSection_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txExtractDataSectionFunction_eq_prog :
    txExtractDataSectionFunction = "tx_extract_data_section:\n" ++ emitProgramR txExtractDataSection_prog txExtractDataSection_relocs := rfl

#guard txExtractDataSectionFunction.startsWith "tx_extract_data_section:\n"
#guard txExtractDataSection_prog.length = 165
/-! ## tx_extract_gas_pricing -- PR-K108

    Extract a tx's gas-pricing fields, normalised to the EIP-1559
    `(max_priority_fee, max_fee)` shape. For pre-EIP-1559 tx types
    that carry a single `gas_price`, both outputs receive the same
    value.

    Per-type RLP layout:

      type 0 legacy   : gas_price = field 1 → fill both outputs
      type 1 EIP-2930 : gas_price = field 2 → fill both outputs
      type 2 EIP-1559 : max_priority_fee = field 2, max_fee = field 3
      type 3 EIP-4844 : max_priority_fee = field 2, max_fee = field 3
      type 4 EIP-7702 : max_priority_fee = field 2, max_fee = field 3

    Both outputs are 32-byte big-endian (u256). Useful for
    `priority_fee_per_gas` (K62), `effective_gas_price` (K70),
    and `tx_cost_compute` (K71) which take this pair as input.

    Composes:
      - PR-K40 `tx_type_dispatch`        — typed-tx detector
      - RlpWalk cursor helpers           — field bounds
      - `rlp_content_to_u256_be_strict` helper  — canonical u256 content decoder

    Calling convention:
      a0 (input)  : tx_bytes ptr (encoded form)
      a1 (input)  : tx_bytes byte length
      a2 (input)  : 32-byte out (max_priority_fee BE)
      a3 (input)  : 32-byte out (max_fee BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx_type_dispatch failed
        2 : first u256 field extraction failed
        3 : max_fee field extraction failed (typed only)

    Both outputs zeroed on failure. Uses two 8-byte `.data`
    scratch slots (`tegp_type`, `tegp_inner_off`). Non-canonical integer
    encodings are rejected by the content decoder. -/
def txExtractGasPricing_prog : Program :=
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
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (8 : BitVec 12),
    .SD .x19 .x0 (16 : BitVec 12),
    .SD .x19 .x0 (24 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.tegp_type (GuestAddrs.tx_extract_gas_pricing + 96)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tegp_type (GuestAddrs.tx_extract_gas_pricing + 96)),
    .AUIPC .x13 (laHi GuestAddrs.tegp_inner_off (GuestAddrs.tx_extract_gas_pricing + 104)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tegp_inner_off (GuestAddrs.tx_extract_gas_pricing + 104)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_extract_gas_pricing + 112)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_gas_pricing + 456) (GuestAddrs.tx_extract_gas_pricing + 124)),
    .AUIPC .x5 (laHi GuestAddrs.tegp_type (GuestAddrs.tx_extract_gas_pricing + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tegp_type (GuestAddrs.tx_extract_gas_pricing + 128)),
    .LD .x20 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tegp_inner_off (GuestAddrs.tx_extract_gas_pricing + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tegp_inner_off (GuestAddrs.tx_extract_gas_pricing + 140)),
    .LD .x30 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x30,
    .SUB .x11 .x9 .x30,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_extract_gas_pricing + 160)),
    .BNE .x12 .x0 (brOff (GuestAddrs.tx_extract_gas_pricing + 312) (GuestAddrs.tx_extract_gas_pricing + 164)),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .LI .x5 (0 : Word),
    .BEQ .x20 .x5 (brOff (GuestAddrs.tx_extract_gas_pricing + 248) (GuestAddrs.tx_extract_gas_pricing + 180)),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_gas_pricing + 192)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_gas_pricing + 312) (GuestAddrs.tx_extract_gas_pricing + 196)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_gas_pricing + 212)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_gas_pricing + 312) (GuestAddrs.tx_extract_gas_pricing + 216)),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_gas_pricing + 232)),
    .BNE .x11 .x0 (brOff (GuestAddrs.tx_extract_gas_pricing + 312) (GuestAddrs.tx_extract_gas_pricing + 236)),
    .SUB .x31 .x10 .x12,
    .JAL .x0 (44 : BitVec 21),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_gas_pricing + 256)),
    .BNE .x11 .x0 (52 : BitVec 13),
    .MV .x21 .x10,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_gas_pricing + 276)),
    .BNE .x11 .x0 (32 : BitVec 13),
    .SUB .x31 .x10 .x12,
    .MV .x23 .x10,
    .MV .x10 .x31,
    .MV .x11 .x12,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_extract_gas_pricing + 304)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .LI .x10 (2 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_gas_pricing + 456) (GuestAddrs.tx_extract_gas_pricing + 332)),
    .LI .x5 (2 : Word),
    .BGEU .x20 .x5 (44 : BitVec 13),
    .LD .x5 .x18 (0 : BitVec 12),
    .SD .x19 .x5 (0 : BitVec 12),
    .LD .x5 .x18 (8 : BitVec 12),
    .SD .x19 .x5 (8 : BitVec 12),
    .LD .x5 .x18 (16 : BitVec 12),
    .SD .x19 .x5 (16 : BitVec 12),
    .LD .x5 .x18 (24 : BitVec 12),
    .SD .x19 .x5 (24 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_extract_gas_pricing + 456) (GuestAddrs.tx_extract_gas_pricing + 380)),
    .MV .x21 .x23,
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_extract_gas_pricing + 396)),
    .BNE .x11 .x0 (28 : BitVec 13),
    .SUB .x31 .x10 .x12,
    .MV .x10 .x31,
    .MV .x11 .x12,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.tx_extract_gas_pricing + 420)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (8 : BitVec 12),
    .SD .x19 .x0 (16 : BitVec 12),
    .SD .x19 .x0 (24 : BitVec 12),
    .LI .x10 (3 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
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

/-- Reloc side-table for `txExtractGasPricing_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txExtractGasPricing_relocs : RelocTable :=
  [ (24, .la .x12 "tegp_type"),
    (26, .la .x13 "tegp_inner_off"),
    (28, .jal .x1 "tx_type_dispatch"),
    (32, .la .x5 "tegp_type"),
    (35, .la .x5 "tegp_inner_off"),
    (40, .jal .x1 "rlp_walk_init"),
    (48, .jal .x1 "rlp_walk_next"),
    (53, .jal .x1 "rlp_walk_next"),
    (58, .jal .x1 "rlp_walk_next"),
    (64, .jal .x1 "rlp_walk_next"),
    (69, .jal .x1 "rlp_walk_next"),
    (76, .jal .x1 "rlp_content_to_u256_be_strict"),
    (99, .jal .x1 "rlp_walk_next"),
    (105, .jal .x1 "rlp_content_to_u256_be_strict") ]

def txExtractGasPricingFunction : String :=
  "tx_extract_gas_pricing:\n" ++ emitProgramR txExtractGasPricing_prog txExtractGasPricing_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txExtractGasPricing_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txExtractGasPricingFunction_eq_prog :
    txExtractGasPricingFunction = "tx_extract_gas_pricing:\n" ++ emitProgramR txExtractGasPricing_prog txExtractGasPricing_relocs := rfl

#guard txExtractGasPricingFunction.startsWith "tx_extract_gas_pricing:\n"
#guard txExtractGasPricing_prog.length = 125

end EvmAsm.Codegen
