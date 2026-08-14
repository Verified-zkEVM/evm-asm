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
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
-- #10780: the core-side copy of `rlpItemSize_prog` that the long-form length-loop
-- lemmas are stated over. Core may not import `Codegen`, so the loop proof cannot
-- reach the definition below; the drift guard beneath it is what keeps the two honest.
import EvmAsm.Rv64.RLP.ItemSizeLenLoop

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
def rlpListNthItem_legacy_prog : Program :=
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

/-- Strict, spec-aligned K20 wrapper. The verified `rlp_walk_init` and
    `rlp_walk_next` bodies are embedded after the wrapper so every existing
    textual K20 closure stays self-contained. The wrapper returns before the
    embedded bodies and reaches them only through local PC-relative calls. -/
def rlpListNthItemWrapper_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x12,
    .MV .x18 .x13,
    .MV .x19 .x14,
    .JAL .x1 (104 : BitVec 21),
    .BNE .x12 .x0 (60 : BitVec 13),
    .MV .x20 .x11,
    .LI .x21 (0 : Word),
    .MV .x11 .x20,
    .JAL .x1 (296 : BitVec 21),
    .BNE .x11 .x0 (40 : BitVec 13),
    .BEQ .x21 .x9 (12 : BitVec 13),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .SUB .x5 .x10 .x12,
    .SUB .x5 .x5 .x8,
    .SD .x18 .x5 (0 : BitVec 12),
    .SD .x19 .x12 (0 : BitVec 12),
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

def rlpListNthItem_prog : Program :=
  (show List Instr from rlpListNthItemWrapper_prog) ++ EvmAsm.Rv64.RLP.rlp_walk_init_prog ++
    EvmAsm.Rv64.RLP.rlp_walk_next_prog

#guard (rlpListNthItem_prog.drop rlpListNthItemWrapper_prog.length).take
    EvmAsm.Rv64.RLP.rlp_walk_init_prog.length = EvmAsm.Rv64.RLP.rlp_walk_init_prog
#guard rlpListNthItem_prog.drop
    (rlpListNthItemWrapper_prog.length + EvmAsm.Rv64.RLP.rlp_walk_init_prog.length) =
      EvmAsm.Rv64.RLP.rlp_walk_next_prog

def rlpListNthItemFunction : String :=
  "rlp_list_nth_item:\n" ++ emitProgram rlpListNthItem_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpListNthItem_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpListNthItemFunction_eq_prog :
    rlpListNthItemFunction = "rlp_list_nth_item:\n" ++ emitProgram rlpListNthItem_prog := rfl

#guard rlpListNthItemFunction.startsWith "rlp_list_nth_item:\n"
#guard rlpListNthItem_prog.length = 194
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

    The framed wrapper embeds the verified strict walk initializer and item
    decoder so every standalone closure remains self-contained. -/
def rlpListCountItemsWrapper_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x12,
    .JAL .x1 (88 : BitVec 21),
    .BNE .x12 .x0 (48 : BitVec 13),
    .MV .x18 .x11,
    .LI .x19 (0 : Word),
    .BEQ .x10 .x18 (24 : BitVec 13),
    .MV .x11 .x18,
    .JAL .x1 (276 : BitVec 21),
    .BNE .x11 .x0 (24 : BitVec 13),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .SD .x9 .x19 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .SD .x9 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Strict count re-emission: a small framed counting loop followed by exact
    copies of the verified strict list initializer and item walker. -/
def rlpListCountItems_prog : Program :=
  (show List Instr from rlpListCountItemsWrapper_prog) ++
    EvmAsm.Rv64.RLP.rlp_walk_init_prog ++ EvmAsm.Rv64.RLP.rlp_walk_next_prog

def rlpListCountItemsFunction : String :=
  "rlp_list_count_items:\n" ++ emitProgram rlpListCountItems_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `rlpListCountItems_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem rlpListCountItemsFunction_eq_prog :
    rlpListCountItemsFunction = "rlp_list_count_items:\n" ++ emitProgram rlpListCountItems_prog := rfl

#guard rlpListCountItemsFunction.startsWith "rlp_list_count_items:\n"
#guard rlpListCountItems_prog.length = 186
#guard (rlpListCountItems_prog.drop rlpListCountItemsWrapper_prog.length).take
    EvmAsm.Rv64.RLP.rlp_walk_init_prog.length = EvmAsm.Rv64.RLP.rlp_walk_init_prog
#guard rlpListCountItems_prog.drop
    (rlpListCountItemsWrapper_prog.length + EvmAsm.Rv64.RLP.rlp_walk_init_prog.length) =
      EvmAsm.Rv64.RLP.rlp_walk_next_prog
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
      else (1..55 B)   → 0x80 + len  +  stripped BE bytes

    Building block for `account_encode` (PR-K31+), which calls
    this for the nonce / balance fields, and for state-root
    recompute after MPT mutation.

    Calling convention:
      a0 (input)  : src bytes ptr (BE, possibly with leading zeros)
      a1 (input)  : src byte length, **≤ 55** — see the domain
                    note below (typical: 8 for u64, 32 for u256)
      a2 (input)  : output buffer ptr (≥ a1 + 1 bytes capacity)
      ra (input)  : return
      a0 (output) : number of bytes written

    **Domain: `a1 ≤ 55`.**  Instructions [21]-[23] write the header
    as `0x80 + len` unconditionally, whereas RLP requires the
    `0xb7 + lenlen` long form once the stripped payload reaches 56
    bytes.  So this routine is a *short-form* encoder and callers
    must bound `a1`; it is not "any length".  Every production
    caller passes 8 or 32, or guards dynamically — the call-site
    enumeration and its one unbounded exception (the `zisk_` probe,
    which is therefore not a sound oracle above 55 bytes) are in
    `RlpEncodeUintBeSAsm.lean`'s module docstring, together with the
    two greps that regenerate it.  Verified there, not here.

    **Verified in** `EvmAsm.Codegen.RlpEncodeUintBeSAsm` (block
    theorems) and `EvmAsm.Codegen.RlpEncodeUintBeComposeSAsm` (the
    whole-routine triple), against the independent RLP model
    `reubOut`.  All 35 instructions are covered by block theorems —
    `reubPrologue`, `reubStripLoop`, `reubEmptyTail`, the three
    `reubDisp*`, `reubSingleTail`, `reubHeaderWrite`, `reubCopyLoop`,
    `reubRetTail` — and those chain into
    `reub_spec_within : cpsTripleWithin (6n + 7L + 17) reubBase
    (ra &&& ~~~1) …`, which says the routine *computes RLP*: `a0` is
    the byte count and the output buffer begins with `reubOut xs`,
    the rest untouched.  `reub_spec_encode_within` restates that as
    `encodeBytes (Nat.toBytesBE (Nat.fromBytesBE xs))`, i.e. against
    the reference encoding rather than the module's own model.  The
    `a1 ≤ 55` domain bound above is load-bearing in exactly one
    place: that composition.

    That pointer is here deliberately: a per-file theorem count of
    *this* module sees only the drift guard below and reads as
    "unspecified", which is how #10779 and #10782 came to be filed
    against finished work.  Grep the routine symbol tree-wide.

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

    Pure-leaf semantics: no scratch memory, no transitive calls.

    **Verified in** `EvmAsm.Codegen.RlpEncodeBytesSAsm` (model layer + the
    `u64ByteLen ↔ toBytesBE` bridge), `…LadderSAsm` (the bc ladder),
    `…BlocksSAsm` (all 76 instructions block-covered), and `…ComposeSAsm`
    (the whole-routine triple): `reb_spec_within` says the routine returns
    status 0, leaves `encodeBytes data` at the front of the output buffer
    with the rest untouched, and writes the encoding's length to `*a3` —
    for EVERY input, both sides of the 55/56 boundary (total function, no
    domain restriction).  `reb_spec_rlpItem_within` restates the output
    region over `RLPItem`, the vocabulary SpecRef's encoders use.

    That pointer is here deliberately: a per-file theorem count of *this*
    module sees only the drift guard below and reads as "unspecified",
    which is how #10779 and #10782 came to be filed against finished work. -/
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

/-- ⭐ **Kernel-checked drift guard for the core-side copy** (#10780).

    `rlp_item_size`'s long-form length loop is proved in `Rv64/RLP/ItemSizeLenLoop.lean`,
    which is verified **core** — and `scripts/check-layering.sh` L1 forbids core importing
    `Codegen`, so that proof cannot be stated over the definition above. It therefore
    carries its own copy of the 35 instructions, exactly as `rlp_walk_init_prog` does
    (declared core-side in `WalkInit.lean`, emitted from here).

    ⚠️ A duplicated program with nothing tying the copies together is a silent-drift
    surface: edit one and every proof still closes, against the wrong machine. This `rfl`
    is that tie, and it is the same role `rlpWalkNextCoreFunction_eq_verified_prog` plays
    for the walker's emitted core.

    The tidier end state is for this definition to *be* the core one (as `rlp_walk_init`
    manages, having no Codegen-side copy at all). That is a rename touching every
    consumer of `rlpItemSize_prog`, so it is left as follow-up — but it must not be left
    without this guard in the meantime. -/
theorem rlpItemSize_prog_eq_verified_prog :
    rlpItemSize_prog = EvmAsm.Rv64.RLP.rlp_item_size_prog := rfl

/-- `rlp_item_span`: a0 = list ptr, a1 = list len, a2 = item index i,
    a3 = out_start_ptr (u64, item start offset incl. its prefix, relative to
    list ptr), a4 = out_size_ptr (u64, full encoded size). Returns a0 = 0 on
    success, 1 on parse failure / i out of range. The cursor is kept in a
    callee-saved register because `rlp_item_size` clobbers the temporaries. -/
def rlpItemSpan_prog : Program :=
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
    .BGEU .x8 .x9 (112 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (100 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (24 : BitVec 13),
    .LI .x6 (247 : Word),
    .SUB .x7 .x5 .x6,
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADD .x21 .x8 .x7,
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x21 .x8 (1 : BitVec 12),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x18 (28 : BitVec 13),
    .BGEU .x21 .x9 (56 : BitVec 13),
    .MV .x10 .x21,
    .JAL .x1 (jalOff GuestAddrs.rlp_item_size (GuestAddrs.rlp_item_span + 120)),
    .ADD .x21 .x21 .x10,
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .BGEU .x21 .x9 (32 : BitVec 13),
    .MV .x10 .x21,
    .JAL .x1 (jalOff GuestAddrs.rlp_item_size (GuestAddrs.rlp_item_span + 144)),
    .SUB .x6 .x21 .x8,
    .SD .x19 .x6 (0 : BitVec 12),
    .SD .x20 .x10 (0 : BitVec 12),
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

/-- Reloc side-table for `rlpItemSpan_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def rlpItemSpan_relocs : RelocTable :=
  [ (30, .jal .x1 "rlp_item_size"),
    (36, .jal .x1 "rlp_item_size") ]

def rlpItemSpanFunction : String :=
  "rlp_item_span:\n" ++ emitProgramR rlpItemSpan_prog rlpItemSpan_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `rlpItemSpan_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem rlpItemSpanFunction_eq_prog :
    rlpItemSpanFunction = "rlp_item_span:\n" ++ emitProgramR rlpItemSpan_prog rlpItemSpan_relocs := rfl

#guard rlpItemSpanFunction.startsWith "rlp_item_span:\n"

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



end EvmAsm.Codegen
