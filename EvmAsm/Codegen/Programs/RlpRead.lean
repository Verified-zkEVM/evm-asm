/-
  EvmAsm.Codegen.Programs.RlpRead

  Standalone Lean strings for the RLP primitives -- read side
  (`rlp_list_nth_item` PR-K20, `rlp_list_count_items` PR-K47) and
  write side (`rlp_encode_uint_be` PR-K30, `rlp_encode_bytes`
  PR-K128, `rlp_encode_list_prefix` PR-K129).

  Lifted out of `EvmAsm.Codegen.Programs` so MPT / tx / header /
  block consumers can import them without pulling the full
  registry hub.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## rlp_list_nth_item -- PR-K20 walk RLP list to extract
    the N-th item's content bounds.

    Foundation for MPT node decoding. Handles all RLP item
    forms: single bytes, short strings (0x80..0xb7), long
    strings (0xb8..0xbf), short lists (0xc0..0xf7), long lists
    (0xf8..0xff with length-of-length in [1..8]).

    Calling convention:
      a0 (input)  : list bytes ptr (start of outer RLP list
                    prefix)
      a1 (input)  : total list byte length
      a2 (input)  : index N (0-based)
      a3 (input)  : u64 out ptr (content offset within list bytes)
      a4 (input)  : u64 out ptr (content byte length)
      ra (input)  : return
      a0 (output) : 0 on hit, 1 on parse error / OOB.

    Content interpretation:
      * Single byte (0x00..0x7f)   : offset = item_start; len = 1
      * Short string (0x80..0xb7)  : offset = item_start+1; len = b - 0x80
      * Long string (0xb8..0xbf)   : offset = item_start+1+lol; len = decoded
      * Short list (0xc0..0xf7)    : offset = item_start; len = full encoded length
      * Long list (0xf8..0xff)     : offset = item_start; len = full encoded length

    Byte-string items have their RLP prefix stripped; sub-list
    items are returned in full (so callers can recurse with
    another call to `rlp_list_nth_item`).

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def rlpListNthItem_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .ADD .x9 .x10 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .BGEU .x8 .x9 (540 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (528 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (24 : BitVec 13),
    .LI .x6 (247 : Word),
    .SUB .x7 .x5 .x6,
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADD .x21 .x8 .x7,
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x21 .x8 (1 : BitVec 12),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x18 (224 : BitVec 13),
    .BGEU .x21 .x9 (484 : BitVec 13),
    .LBU .x5 .x21 (0 : BitVec 12),
    .LI .x6 (128 : Word),
    .BLTU .x5 .x6 (196 : BitVec 13),
    .LI .x6 (184 : Word),
    .BLTU .x5 .x6 (168 : BitVec 13),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (96 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (68 : BitVec 13),
    .LI .x6 (247 : Word),
    .SUB .x7 .x5 .x6,
    .LI .x28 (0 : Word),
    .MV .x29 .x7,
    .ADDI .x30 .x21 (1 : BitVec 12),
    .BEQ .x29 .x0 (28 : BitVec 13),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x31 .x30 (0 : BitVec 12),
    .OR .x28 .x28 .x31,
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x31 .x7 (1 : BitVec 12),
    .ADD .x31 .x31 .x28,
    .ADD .x21 .x21 .x31,
    .JAL .x0 (112 : BitVec 21),
    .LI .x6 (192 : Word),
    .SUB .x31 .x5 .x6,
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADD .x21 .x21 .x31,
    .JAL .x0 (92 : BitVec 21),
    .LI .x6 (183 : Word),
    .SUB .x7 .x5 .x6,
    .LI .x28 (0 : Word),
    .MV .x29 .x7,
    .ADDI .x30 .x21 (1 : BitVec 12),
    .BEQ .x29 .x0 (28 : BitVec 13),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x31 .x30 (0 : BitVec 12),
    .OR .x28 .x28 .x31,
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x31 .x7 (1 : BitVec 12),
    .ADD .x31 .x31 .x28,
    .ADD .x21 .x21 .x31,
    .JAL .x0 (28 : BitVec 21),
    .LI .x6 (128 : Word),
    .SUB .x31 .x5 .x6,
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADD .x21 .x21 .x31,
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-220 : BitVec 21),
    .BGEU .x21 .x9 (264 : BitVec 13),
    .LBU .x5 .x21 (0 : BitVec 12),
    .LI .x6 (128 : Word),
    .BLTU .x5 .x6 (228 : BitVec 13),
    .LI .x6 (184 : Word),
    .BLTU .x5 .x6 (192 : BitVec 13),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (112 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (76 : BitVec 13),
    .LI .x6 (247 : Word),
    .SUB .x7 .x5 .x6,
    .LI .x28 (0 : Word),
    .MV .x29 .x7,
    .ADDI .x30 .x21 (1 : BitVec 12),
    .BEQ .x29 .x0 (28 : BitVec 13),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x31 .x30 (0 : BitVec 12),
    .OR .x28 .x28 .x31,
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x31 .x7 (1 : BitVec 12),
    .ADD .x31 .x31 .x28,
    .SUB .x6 .x21 .x8,
    .SD .x19 .x6 (0 : BitVec 12),
    .SD .x20 .x31 (0 : BitVec 12),
    .JAL .x0 (148 : BitVec 21),
    .LI .x6 (192 : Word),
    .SUB .x31 .x5 .x6,
    .ADDI .x31 .x31 (1 : BitVec 12),
    .SUB .x6 .x21 .x8,
    .SD .x19 .x6 (0 : BitVec 12),
    .SD .x20 .x31 (0 : BitVec 12),
    .JAL .x0 (120 : BitVec 21),
    .LI .x6 (183 : Word),
    .SUB .x7 .x5 .x6,
    .LI .x28 (0 : Word),
    .MV .x29 .x7,
    .ADDI .x30 .x21 (1 : BitVec 12),
    .BEQ .x29 .x0 (28 : BitVec 13),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x31 .x30 (0 : BitVec 12),
    .OR .x28 .x28 .x31,
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x31 .x7 (1 : BitVec 12),
    .ADD .x31 .x31 .x21,
    .SUB .x31 .x31 .x8,
    .SD .x19 .x31 (0 : BitVec 12),
    .SD .x20 .x28 (0 : BitVec 12),
    .JAL .x0 (48 : BitVec 21),
    .ADDI .x31 .x21 (1 : BitVec 12),
    .SUB .x31 .x31 .x8,
    .SD .x19 .x31 (0 : BitVec 12),
    .LI .x6 (128 : Word),
    .SUB .x6 .x5 .x6,
    .SD .x20 .x6 (0 : BitVec 12),
    .JAL .x0 (20 : BitVec 21),
    .SUB .x6 .x21 .x8,
    .SD .x19 .x6 (0 : BitVec 12),
    .LI .x6 (1 : Word),
    .SD .x20 .x6 (0 : BitVec 12),
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
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpListNthItemFunction : String :=
  "rlp_list_nth_item:\n" ++ emitProgram rlpListNthItem_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpListNthItem_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpListNthItemFunction_eq_prog :
    rlpListNthItemFunction = "rlp_list_nth_item:\n" ++ emitProgram rlpListNthItem_prog := rfl

#guard rlpListNthItemFunction.startsWith "rlp_list_nth_item:\n"
#guard rlpListNthItem_prog.length = 160
/-! ## rlp_list_count_items -- PR-K47 top-level item counter

    Walk an RLP-encoded list once and return the number of
    top-level items it contains. Building block for callers
    that need cardinality but not the items themselves:
    `access_list_count`, `authorization_list_count`,
    `blob_versioned_hashes_count`, `tx_count_per_block`.

    Mirrors the item-skip logic in PR-K20 `rlp_list_nth_item`
    but doesn't track a target index; counts every item it
    can walk past until the list payload ends.

    Calling convention:
      a0 (input)  : list bytes ptr (start of outer RLP list
                    prefix, byte 0xc0..0xff)
      a1 (input)  : total list byte length (full encoded item
                    incl. prefix)
      a2 (input)  : u64 out ptr (receives count on success)
      ra (input)  : return
      a0 (output) : 0 on success, 1 on parse error
                    (not a list, truncated, item runs past end)

    Pure register arithmetic except for the count store; no
    scratch memory; leaf-callable. -/
def rlpListCountItems_prog : Program :=
  [ .BEQ .x11 .x0 (292 : BitVec 13),
    .LBU .x5 .x10 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (280 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (24 : BitVec 13),
    .LI .x6 (247 : Word),
    .SUB .x7 .x5 .x6,
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADD .x28 .x10 .x7,
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x28 .x10 (1 : BitVec 12),
    .ADD .x29 .x10 .x11,
    .LI .x30 (0 : Word),
    .BEQ .x28 .x29 (224 : BitVec 13),
    .BLTU .x29 .x28 (232 : BitVec 13),
    .LBU .x5 .x28 (0 : BitVec 12),
    .LI .x6 (128 : Word),
    .BLTU .x5 .x6 (196 : BitVec 13),
    .LI .x6 (184 : Word),
    .BLTU .x5 .x6 (168 : BitVec 13),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (96 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (68 : BitVec 13),
    .LI .x6 (247 : Word),
    .SUB .x7 .x5 .x6,
    .LI .x13 (0 : Word),
    .MV .x14 .x7,
    .ADDI .x15 .x28 (1 : BitVec 12),
    .BEQ .x14 .x0 (28 : BitVec 13),
    .SLLI .x13 .x13 (8 : BitVec 6),
    .LBU .x16 .x15 (0 : BitVec 12),
    .OR .x13 .x13 .x16,
    .ADDI .x15 .x15 (1 : BitVec 12),
    .ADDI .x14 .x14 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x16 .x7 (1 : BitVec 12),
    .ADD .x16 .x16 .x13,
    .ADD .x28 .x28 .x16,
    .JAL .x0 (112 : BitVec 21),
    .LI .x6 (192 : Word),
    .SUB .x16 .x5 .x6,
    .ADDI .x16 .x16 (1 : BitVec 12),
    .ADD .x28 .x28 .x16,
    .JAL .x0 (92 : BitVec 21),
    .LI .x6 (183 : Word),
    .SUB .x7 .x5 .x6,
    .LI .x13 (0 : Word),
    .MV .x14 .x7,
    .ADDI .x15 .x28 (1 : BitVec 12),
    .BEQ .x14 .x0 (28 : BitVec 13),
    .SLLI .x13 .x13 (8 : BitVec 6),
    .LBU .x16 .x15 (0 : BitVec 12),
    .OR .x13 .x13 .x16,
    .ADDI .x15 .x15 (1 : BitVec 12),
    .ADDI .x14 .x14 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x16 .x7 (1 : BitVec 12),
    .ADD .x16 .x16 .x13,
    .ADD .x28 .x28 .x16,
    .JAL .x0 (28 : BitVec 21),
    .LI .x6 (128 : Word),
    .SUB .x16 .x5 .x6,
    .ADDI .x16 .x16 (1 : BitVec 12),
    .ADD .x28 .x28 .x16,
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .JAL .x0 (-220 : BitVec 21),
    .SD .x12 .x30 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SD .x12 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpListCountItemsFunction : String :=
  "rlp_list_count_items:\n" ++ emitProgram rlpListCountItems_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpListCountItems_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpListCountItemsFunction_eq_prog :
    rlpListCountItemsFunction = "rlp_list_count_items:\n" ++ emitProgram rlpListCountItems_prog := rfl

#guard rlpListCountItemsFunction.startsWith "rlp_list_count_items:\n"
#guard rlpListCountItems_prog.length = 76
/-! ## rlp_encode_list_prefix -- PR-K129

    Write the RLP list-header prefix bytes for a list whose total
    pre-encoded payload size is `payload_length`. Matches the yellow
    paper §B "list" rule:

      payload_length < 56  → 0xc0 + payload_length   (1 byte)
      else                 → 0xf7 + bc, then `bc`-byte BE length
                             (`bc` = effective byte count of
                             `payload_length`, 1..8)

    Companion to PR-K128 `rlp_encode_bytes` (the string version)
    and PR-K30 `rlp_encode_uint_be` (the uint version). Together
    these three primitives cover the encoder side of the trie /
    node / header / tx serialisation pipeline.

    Calling convention:
      a0 (input)  : payload_length (u64)
      a1 (input)  : output bytes ptr (caller supplies ≥ 9 bytes)
      a2 (input)  : u64 out ptr (prefix byte length)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls. -/
def rlpEncodeListPrefix_prog : Program :=
  [ .LI .x5 (56 : Word),
    .BGEU .x10 .x5 (28 : BitVec 13),
    .ADDI .x6 .x10 (192 : BitVec 12),
    .SB .x11 .x6 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .SD .x12 .x7 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x28 (1 : Word),
    .LI .x29 (256 : Word),
    .BLTU .x10 .x29 (80 : BitVec 13),
    .LI .x28 (2 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x10 .x29 (68 : BitVec 13),
    .LI .x28 (3 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x10 .x29 (56 : BitVec 13),
    .LI .x28 (4 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x10 .x29 (44 : BitVec 13),
    .LI .x28 (5 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x10 .x29 (32 : BitVec 13),
    .LI .x28 (6 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x10 .x29 (20 : BitVec 13),
    .LI .x28 (7 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x10 .x29 (8 : BitVec 13),
    .LI .x28 (8 : Word),
    .ADDI .x29 .x28 (247 : BitVec 12),
    .SB .x11 .x29 (0 : BitVec 12),
    .MV .x30 .x11,
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x29 .x28 (-1 : BitVec 12),
    .BLT .x29 .x0 (28 : BitVec 13),
    .SLLI .x31 .x29 (3 : BitVec 6),
    .SRL .x5 .x10 .x31,
    .SB .x30 .x5 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x30 .x28 (1 : BitVec 12),
    .SD .x12 .x30 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpEncodeListPrefixFunction : String :=
  "rlp_encode_list_prefix:\n" ++ emitProgram rlpEncodeListPrefix_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpEncodeListPrefix_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpEncodeListPrefixFunction_eq_prog :
    rlpEncodeListPrefixFunction = "rlp_encode_list_prefix:\n" ++ emitProgram rlpEncodeListPrefix_prog := rfl

#guard rlpEncodeListPrefixFunction.startsWith "rlp_encode_list_prefix:\n"
#guard rlpEncodeListPrefix_prog.length = 46
/-! ## rlp_encode_uint_be -- PR-K30 RLP canonical-form encoder

    Strip leading zeros from a big-endian byte array and emit
    the canonical RLP encoding:

      value == 0       → 0x80 (1 byte; RLP empty bytes)
      value < 0x80     → single byte = value
      else (1..32 B)   → 0x80 + len  +  stripped BE bytes

    Building block for `account_encode` (PR-K31+), which calls
    this for the nonce / balance fields, and for state-root
    recompute after MPT mutation.

    Calling convention:
      a0 (input)  : src bytes ptr (BE, possibly with leading zeros)
      a1 (input)  : src byte length (any; typical: 8 for u64,
                    32 for u256)
      a2 (input)  : output buffer ptr (≥ a1 + 1 bytes capacity)
      ra (input)  : return
      a0 (output) : number of bytes written

    Pure register arithmetic, no scratch, leaf-callable. -/
def rlpEncodeUintBe_prog : Program :=
  [ .MV .x5 .x10,
    .MV .x6 .x11,
    .BEQ .x6 .x0 (24 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .BNE .x28 .x0 (32 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LI .x28 (128 : Word),
    .SB .x12 .x28 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .MV .x31 .x6,
    .LI .x28 (1 : Word),
    .BNE .x6 .x28 (28 : BitVec 13),
    .LBU .x29 .x5 (0 : BitVec 12),
    .LI .x30 (128 : Word),
    .BGEU .x29 .x30 (16 : BitVec 13),
    .SB .x12 .x29 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x28 (128 : Word),
    .ADD .x28 .x28 .x31,
    .SB .x12 .x28 (0 : BitVec 12),
    .ADDI .x29 .x12 (1 : BitVec 12),
    .MV .x6 .x31,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x30 .x5 (0 : BitVec 12),
    .SB .x29 .x30 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x10 .x31 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpEncodeUintBeFunction : String :=
  "rlp_encode_uint_be:\n" ++ emitProgram rlpEncodeUintBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpEncodeUintBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpEncodeUintBeFunction_eq_prog :
    rlpEncodeUintBeFunction = "rlp_encode_uint_be:\n" ++ emitProgram rlpEncodeUintBe_prog := rfl

#guard rlpEncodeUintBeFunction.startsWith "rlp_encode_uint_be:\n"
#guard rlpEncodeUintBe_prog.length = 35
/-! ## rlp_encode_bytes -- PR-K128

    Generic RLP encoder for a raw byte string. Matches the
    `rlp.encode(bytes)` reference (Ethereum yellow-paper §B):

      len == 1 AND byte < 0x80   → single byte (no prefix)
      len < 56                   → 0x80 + len, then `len` bytes
      else                       → 0xb7 + bc, then `bc`-byte BE
                                   length, then `len` bytes
                                   (`bc` = effective byte count of
                                    `len`, no leading zeros, 1..8)

    PR-K30 `rlp_encode_uint_be` covers the *uint* shape (BE bytes
    + canonical-form leading-zero stripping); K128 covers the
    *arbitrary bytes* shape, which doesn't strip leading zeros and
    handles the single-byte-no-prefix short-cut. Together they're
    the two RLP-string primitives needed for trie / node /
    header / tx re-encoding.

    Calling convention:
      a0 (input)  : data ptr
      a1 (input)  : data byte length
      a2 (input)  : output bytes ptr
                    (caller must have space for `9 + len` bytes)
      a3 (input)  : u64 out ptr (output byte length)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls. -/
def rlpEncodeBytes_prog : Program :=
  [ .MV .x5 .x10,
    .MV .x6 .x11,
    .MV .x7 .x12,
    .LI .x28 (1 : Word),
    .BNE .x6 .x28 (36 : BitVec 13),
    .LBU .x29 .x5 (0 : BitVec 12),
    .LI .x30 (128 : Word),
    .BGEU .x29 .x30 (24 : BitVec 13),
    .SB .x7 .x29 (0 : BitVec 12),
    .LI .x31 (1 : Word),
    .SD .x13 .x31 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x28 (56 : Word),
    .BGEU .x6 .x28 (64 : BitVec 13),
    .ADDI .x28 .x6 (128 : BitVec 12),
    .SB .x7 .x28 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .MV .x29 .x6,
    .BEQ .x29 .x0 (28 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x7 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x31 .x6 (1 : BitVec 12),
    .SD .x13 .x31 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x28 (1 : Word),
    .LI .x29 (256 : Word),
    .BLTU .x6 .x29 (80 : BitVec 13),
    .LI .x28 (2 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x6 .x29 (68 : BitVec 13),
    .LI .x28 (3 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x6 .x29 (56 : BitVec 13),
    .LI .x28 (4 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x6 .x29 (44 : BitVec 13),
    .LI .x28 (5 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x6 .x29 (32 : BitVec 13),
    .LI .x28 (6 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x6 .x29 (20 : BitVec 13),
    .LI .x28 (7 : Word),
    .SLLI .x29 .x29 (8 : BitVec 6),
    .BLTU .x6 .x29 (8 : BitVec 13),
    .LI .x28 (8 : Word),
    .ADDI .x29 .x28 (183 : BitVec 12),
    .SB .x7 .x29 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x29 .x28 (-1 : BitVec 12),
    .BLT .x29 .x0 (28 : BitVec 13),
    .SLLI .x30 .x29 (3 : BitVec 6),
    .SRL .x31 .x6 .x30,
    .SB .x7 .x31 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x29 .x6,
    .BEQ .x29 .x0 (28 : BitVec 13),
    .LBU .x30 .x5 (0 : BitVec 12),
    .SB .x7 .x30 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x30 .x28 (1 : BitVec 12),
    .ADD .x30 .x30 .x6,
    .SD .x13 .x30 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpEncodeBytesFunction : String :=
  "rlp_encode_bytes:\n" ++ emitProgram rlpEncodeBytes_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpEncodeBytes_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpEncodeBytesFunction_eq_prog :
    rlpEncodeBytesFunction = "rlp_encode_bytes:\n" ++ emitProgram rlpEncodeBytes_prog := rfl

#guard rlpEncodeBytesFunction.startsWith "rlp_encode_bytes:\n"
#guard rlpEncodeBytes_prog.length = 76
/-- `zisk_rlp_encode_bytes`: probe BuildUnit. Reads (data_len,
    data_bytes) from host input, writes (status, out_len,
    out_bytes...) to OUTPUT. -/
def ziskRlpEncodeBytesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # data length\n" ++
  "  addi a0, a4, 16             # data ptr\n" ++
  "  li a2, 0xa0010010           # out bytes\n" ++
  "  li a3, 0xa0010008           # out_len out\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lreb_pdone\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  ".Lreb_pdone:"

def ziskRlpEncodeBytesDataSection : String :=
  ".section .data\n" ++
  "reb_scratch:\n" ++
  "  .zero 8"

def ziskRlpEncodeBytesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpEncodeBytesPrologue
  dataAsm     := ziskRlpEncodeBytesDataSection
}

/-! ## rlp_item_size / rlp_item_span (PR: full byte-span of an RLP item)

    `rlp_list_nth_item` returns the item's CONTENT offset/length for string
    items (e.g. a `0xa0||hash` ref -> offset after `0xa0`, length 32) but the
    FULL span for embedded-list items -- inconsistent, so it can't be used to
    copy a branch slot verbatim. `rlp_item_span` returns the FULL encoded span
    (start offset incl. prefix, total size) of list item `i` for EVERY item
    type, which is what mpt_set's branch-slot reconstruction needs. -/

/-- `rlp_item_size`: a0 = ptr to one RLP item -> a0 = its full encoded size.
    Leaf; clobbers t0..t6 only (preserves all s-registers and ra). -/
def rlpItemSize_prog : Program :=
  [ .LBU .x5 .x10 (0 : BitVec 12),
    .LI .x6 (0x80 : Word),
    .BGEU .x5 .x6 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x6 (0xb8 : Word),
    .BGEU .x5 .x6 (16 : BitVec 13),
    .ADDI .x10 .x5 (-128 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x6 (0xc0 : Word),
    .BGEU .x5 .x6 (16 : BitVec 13),
    .LI .x6 (0xb7 : Word),
    .SUB .x7 .x5 .x6,
    .JAL .x0 (32 : BitVec 21),
    .LI .x6 (0xf8 : Word),
    .BGEU .x5 .x6 (16 : BitVec 13),
    .ADDI .x10 .x5 (-192 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x6 (0xf7 : Word),
    .SUB .x7 .x5 .x6,
    .LI .x28 (0 : Word),
    .ADDI .x29 .x10 (1 : BitVec 12),
    .MV .x30 .x7,
    .BEQ .x30 .x0 (28 : BitVec 13),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x31 .x29 (0 : BitVec 12),
    .OR .x28 .x28 .x31,
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x10 .x7 (1 : BitVec 12),
    .ADD .x10 .x10 .x28,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpItemSizeFunction : String :=
  "rlp_item_size:\n" ++ emitProgram rlpItemSize_prog

theorem rlpItemSizeFunction_eq_prog :
    rlpItemSizeFunction = "rlp_item_size:\n" ++ emitProgram rlpItemSize_prog := rfl

#guard rlpItemSizeFunction.startsWith "rlp_item_size:\n"
#guard rlpItemSize_prog.length = 35

/-- `rlp_item_span`: a0 = list ptr, a1 = list len, a2 = item index i,
    a3 = out_start_ptr (u64, item start offset incl. its prefix, relative to
    list ptr), a4 = out_size_ptr (u64, full encoded size). Returns a0 = 0 on
    success, 1 on parse failure / i out of range. The cursor is kept in a
    callee-saved register because `rlp_item_size` clobbers the temporaries. -/
def rlpItemSpanFunction : String :=
  "rlp_item_span:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; add s1, a0, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  bgeu s0, s1, .Lrisp_fail\n" ++
  "  lbu t0, 0(s0)\n" ++
  "  li t1, 0xc0; bltu t0, t1, .Lrisp_fail\n" ++   -- outer must be a list
  "  li t1, 0xf8; bltu t0, t1, .Lrisp_short_outer\n" ++
  "  li t1, 0xf7; sub t2, t0, t1; addi t2, t2, 1\n" ++
  "  add s5, s0, t2; j .Lrisp_walk\n" ++
  ".Lrisp_short_outer:\n" ++
  "  addi s5, s0, 1\n" ++                          -- cursor at first item
  ".Lrisp_walk:\n" ++
  "  li s6, 0\n" ++                                -- index
  ".Lrisp_loop:\n" ++
  "  beq s6, s2, .Lrisp_target\n" ++
  "  bgeu s5, s1, .Lrisp_fail\n" ++
  "  mv a0, s5; jal ra, rlp_item_size\n" ++
  "  add s5, s5, a0; addi s6, s6, 1; j .Lrisp_loop\n" ++
  ".Lrisp_target:\n" ++
  "  bgeu s5, s1, .Lrisp_fail\n" ++
  "  mv a0, s5; jal ra, rlp_item_size\n" ++
  "  sub t1, s5, s0; sd t1, 0(s3); sd a0, 0(s4)\n" ++
  "  li a0, 0; j .Lrisp_ret\n" ++
  ".Lrisp_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lrisp_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64; ret"

/-- `zisk_rlp_item_span`: probe. Input: bytes 0..8 list_len, 8..16 index i,
    16.. list bytes. Output: 0..8 status, 8..16 item start offset, 16..24
    item full size. -/
def ziskRlpItemSpanPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # list_len\n" ++
  "  ld a2, 16(a5)               # index i\n" ++
  "  addi a0, a5, 24             # list ptr\n" ++
  "  li a3, 0xa0010008           # out_start\n" ++
  "  li a4, 0xa0010010           # out_size\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lrisp_pdone\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  ".Lrisp_pdone:"

def ziskRlpItemSpanDataSection : String :=
  ".section .data\n" ++
  "ris_scratch:\n" ++
  "  .zero 8"

def ziskRlpItemSpanProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskRlpItemSpanPrologue
  dataAsm     := ziskRlpItemSpanDataSection
}


end EvmAsm.Codegen
