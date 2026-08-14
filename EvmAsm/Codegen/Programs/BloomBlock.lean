/-
  EvmAsm.Codegen.Programs.BloomBlock

  Block-level logs-bloom composites split from Bloom.lean. The atomic
  bloom helpers stay in Bloom.lean; this module composes them over receipt
  lists and header validation.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## block_logs_bloom_from_receipts_list -- PR-K158

    Given an RLP-encoded list of receipts, compute the block-level
    `logs_bloom` by OR-accumulating each receipt's `logs_bloom`
    field. End-to-end composite tying together the four atomic
    bloom helpers shipped in PR-K151..K154:

      bzero(block_bloom)
      for receipt in receipts:
        receipt_extract_logs_bloom(receipt, scratch)   # K152
        bloom_or_into(block_bloom, scratch)            # K151

    Used by `block_validate_logs_bloom` (combined with K153 to
    extract the header's claimed bloom and K154 to compare).

    Empty receipts list (`0xc0`) is valid and leaves the output
    bloom untouched. Per-receipt parse failures propagate via the
    return code.

    Composes:
      - PR-K20 `rlp_list_nth_item`       -- walk each receipt
      - PR-K47 `rlp_list_count_items`    -- list cardinality
      - PR-K152 `receipt_extract_logs_bloom`
      - PR-K151 `bloom_or_into`

    Calling convention:
      a0 (input)  : receipts_rlp_list ptr (RLP list of receipts)
      a1 (input)  : receipts_rlp_list byte length
      a2 (input)  : 256-byte output bloom ptr
                    (mutable, caller zero-inits)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure (outer list malformed or a
            receipt isn't a proper RLP list)
        2 : a receipt's `logs_bloom` field length != 256 -/
def blockLogsBloomFromReceiptsList_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.blbr_count (GuestAddrs.block_logs_bloom_from_receipts_list + 48)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blbr_count (GuestAddrs.block_logs_bloom_from_receipts_list + 48)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.block_logs_bloom_from_receipts_list + 56)),
    .BNE .x10 .x0 (brOff (GuestAddrs.block_logs_bloom_from_receipts_list + 308) (GuestAddrs.block_logs_bloom_from_receipts_list + 60)),
    .AUIPC .x5 (laHi GuestAddrs.blbr_count (GuestAddrs.block_logs_bloom_from_receipts_list + 64)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blbr_count (GuestAddrs.block_logs_bloom_from_receipts_list + 64)),
    .LD .x19 .x5 (0 : BitVec 12),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x19 (brOff (GuestAddrs.block_logs_bloom_from_receipts_list + 300) (GuestAddrs.block_logs_bloom_from_receipts_list + 80)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x20,
    .AUIPC .x13 (laHi GuestAddrs.blbr_offset (GuestAddrs.block_logs_bloom_from_receipts_list + 96)),
    .ADDI .x13 .x13 (laLo GuestAddrs.blbr_offset (GuestAddrs.block_logs_bloom_from_receipts_list + 96)),
    .AUIPC .x14 (laHi GuestAddrs.blbr_length (GuestAddrs.block_logs_bloom_from_receipts_list + 104)),
    .ADDI .x14 .x14 (laLo GuestAddrs.blbr_length (GuestAddrs.block_logs_bloom_from_receipts_list + 104)),
    .JAL .x1 (jalOff GuestAddrs.rlp_item_span (GuestAddrs.block_logs_bloom_from_receipts_list + 112)),
    .BNE .x10 .x0 (brOff (GuestAddrs.block_logs_bloom_from_receipts_list + 308) (GuestAddrs.block_logs_bloom_from_receipts_list + 116)),
    .AUIPC .x5 (laHi GuestAddrs.blbr_offset (GuestAddrs.block_logs_bloom_from_receipts_list + 120)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blbr_offset (GuestAddrs.block_logs_bloom_from_receipts_list + 120)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.blbr_length (GuestAddrs.block_logs_bloom_from_receipts_list + 132)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blbr_length (GuestAddrs.block_logs_bloom_from_receipts_list + 132)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x6,
    .MV .x11 .x7,
    .LI .x28 (1 : Word),
    .BNE .x7 .x28 (brOff (GuestAddrs.block_logs_bloom_from_receipts_list + 260) (GuestAddrs.block_logs_bloom_from_receipts_list + 156)),
    .LBU .x28 .x10 (0 : BitVec 12),
    .BEQ .x28 .x0 (brOff (GuestAddrs.block_logs_bloom_from_receipts_list + 260) (GuestAddrs.block_logs_bloom_from_receipts_list + 164)),
    .LI .x29 (4 : Word),
    .BLTU .x29 .x28 (brOff (GuestAddrs.block_logs_bloom_from_receipts_list + 260) (GuestAddrs.block_logs_bloom_from_receipts_list + 172)),
    .ADDI .x28 .x20 (1 : BitVec 12),
    .BGEU .x28 .x19 (brOff (GuestAddrs.block_logs_bloom_from_receipts_list + 308) (GuestAddrs.block_logs_bloom_from_receipts_list + 180)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x28,
    .AUIPC .x13 (laHi GuestAddrs.blbr_next_offset (GuestAddrs.block_logs_bloom_from_receipts_list + 196)),
    .ADDI .x13 .x13 (laLo GuestAddrs.blbr_next_offset (GuestAddrs.block_logs_bloom_from_receipts_list + 196)),
    .AUIPC .x14 (laHi GuestAddrs.blbr_next_length (GuestAddrs.block_logs_bloom_from_receipts_list + 204)),
    .ADDI .x14 .x14 (laLo GuestAddrs.blbr_next_length (GuestAddrs.block_logs_bloom_from_receipts_list + 204)),
    .JAL .x1 (jalOff GuestAddrs.rlp_item_span (GuestAddrs.block_logs_bloom_from_receipts_list + 212)),
    .BNE .x10 .x0 (brOff (GuestAddrs.block_logs_bloom_from_receipts_list + 308) (GuestAddrs.block_logs_bloom_from_receipts_list + 216)),
    .AUIPC .x5 (laHi GuestAddrs.blbr_next_offset (GuestAddrs.block_logs_bloom_from_receipts_list + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blbr_next_offset (GuestAddrs.block_logs_bloom_from_receipts_list + 220)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.blbr_next_length (GuestAddrs.block_logs_bloom_from_receipts_list + 232)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blbr_next_length (GuestAddrs.block_logs_bloom_from_receipts_list + 232)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x6,
    .MV .x11 .x7,
    .ADDI .x20 .x20 (2 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.blbr_scratch_bloom (GuestAddrs.block_logs_bloom_from_receipts_list + 264)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blbr_scratch_bloom (GuestAddrs.block_logs_bloom_from_receipts_list + 264)),
    .JAL .x1 (jalOff GuestAddrs.receipt_extract_logs_bloom (GuestAddrs.block_logs_bloom_from_receipts_list + 272)),
    .BNE .x10 .x0 (40 : BitVec 13),
    .MV .x10 .x18,
    .AUIPC .x11 (laHi GuestAddrs.blbr_scratch_bloom (GuestAddrs.block_logs_bloom_from_receipts_list + 284)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blbr_scratch_bloom (GuestAddrs.block_logs_bloom_from_receipts_list + 284)),
    .JAL .x1 (jalOff GuestAddrs.bloom_or_into (GuestAddrs.block_logs_bloom_from_receipts_list + 292)),
    .JAL .x0 (jalOff (GuestAddrs.block_logs_bloom_from_receipts_list + 80) (GuestAddrs.block_logs_bloom_from_receipts_list + 296)),
    .LI .x10 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (4 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockLogsBloomFromReceiptsList_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockLogsBloomFromReceiptsList_relocs : RelocTable :=
  [ (12, .la .x12 "blbr_count"),
    (14, .jal .x1 "rlp_list_count_items"),
    (16, .la .x5 "blbr_count"),
    (24, .la .x13 "blbr_offset"),
    (26, .la .x14 "blbr_length"),
    (28, .jal .x1 "rlp_item_span"),
    (30, .la .x5 "blbr_offset"),
    (33, .la .x5 "blbr_length"),
    (49, .la .x13 "blbr_next_offset"),
    (51, .la .x14 "blbr_next_length"),
    (53, .jal .x1 "rlp_item_span"),
    (55, .la .x5 "blbr_next_offset"),
    (58, .la .x5 "blbr_next_length"),
    (66, .la .x12 "blbr_scratch_bloom"),
    (68, .jal .x1 "receipt_extract_logs_bloom"),
    (71, .la .x11 "blbr_scratch_bloom"),
    (73, .jal .x1 "bloom_or_into") ]

def blockLogsBloomFromReceiptsListFunction : String :=
  "block_logs_bloom_from_receipts_list:\n" ++ emitProgramR blockLogsBloomFromReceiptsList_prog blockLogsBloomFromReceiptsList_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockLogsBloomFromReceiptsList_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockLogsBloomFromReceiptsListFunction_eq_prog :
    blockLogsBloomFromReceiptsListFunction = "block_logs_bloom_from_receipts_list:\n" ++ emitProgramR blockLogsBloomFromReceiptsList_prog blockLogsBloomFromReceiptsList_relocs := rfl

#guard blockLogsBloomFromReceiptsListFunction.startsWith "block_logs_bloom_from_receipts_list:\n"
#guard blockLogsBloomFromReceiptsList_prog.length = 87
/-- `zisk_block_logs_bloom_from_receipts_list`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : receipts_list_rlp_len
      bytes  8..   : receipts_list_rlp
    Output layout (256 B, ziskemu cap):
      bytes  0..256 : accumulated logs_bloom (zero-initialised
                       by the probe before invoking the helper). -/
def ziskBlockLogsBloomFromReceiptsListPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # receipts_list_rlp_len\n" ++
  "  addi a0, a3, 16             # receipts_list_rlp ptr\n" ++
  "  li a2, 0xa0010000           # output bloom ptr (256 B)\n" ++
  "  # Zero output bloom (32 × sd zero).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 32\n" ++
  ".Lblbr_zero_loop:\n" ++
  "  beqz t1, .Lblbr_zero_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lblbr_zero_loop\n" ++
  ".Lblbr_zero_done:\n" ++
  "  jal ra, block_logs_bloom_from_receipts_list\n" ++
  "  j .Lblbr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  receiptExtractLogsBloomFunction ++ "\n" ++
  bloomOrIntoFunction ++ "\n" ++
  blockLogsBloomFromReceiptsListFunction ++ "\n" ++
  ".Lblbr_pdone:"

def ziskBlockLogsBloomFromReceiptsListDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "relb_offset:\n" ++
  "  .zero 8\n" ++
  "relb_length:\n" ++
  "  .zero 8\n" ++
  "blbr_count:\n" ++
  "  .zero 8\n" ++
  "blbr_offset:\n" ++
  "  .zero 8\n" ++
  "blbr_length:\n" ++
  "  .zero 8\n" ++
  "blbr_next_offset:\n" ++
  "  .zero 8\n" ++
  "blbr_next_length:\n" ++
  "  .zero 8\n" ++
  "blbr_scratch_bloom:\n" ++
  "  .zero 256"


/-! ## block_validate_logs_bloom -- PR-K159

    End-to-end block-level `logs_bloom` validation: given the
    header RLP and the RLP list of receipts, recompute the
    block's bloom from receipts and check it byte-equals the
    header's claimed bloom.

      header_bloom = header_extract_logs_bloom(header_rlp)
      computed_bloom = block_logs_bloom_from_receipts_list(receipts)
      is_valid = bloom_eq(header_bloom, computed_bloom)

    Single-call entry point for callers that want the verdict
    without managing the scratch buffers themselves. The verdict
    is returned via an out pointer (1 if valid, 0 if not).

    Composes:
      - PR-K153 `header_extract_logs_bloom`        -- read header
      - PR-K158 `block_logs_bloom_from_receipts_list` -- recompute
      - PR-K154 `bloom_eq`                          -- compare

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : receipts_rlp_list ptr
      a3 (input)  : receipts_rlp_list byte length
      a4 (input)  : u64 out ptr (is_valid: 1 if matches, 0 if not)
      ra (input)  : return
      a0 (output) :
        0 : helpers succeeded -- predicate written
        1 : header parse failure / bloom field width != 256
        2 : receipts-list parse failure or receipt size failure
            (child status from PR-K158 propagated unchanged) -/
def blockValidateLogsBloom_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.bvlb_header_bloom (GuestAddrs.block_validate_logs_bloom + 56)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bvlb_header_bloom (GuestAddrs.block_validate_logs_bloom + 56)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_logs_bloom (GuestAddrs.block_validate_logs_bloom + 64)),
    .BNE .x10 .x0 (92 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.bvlb_computed_bloom (GuestAddrs.block_validate_logs_bloom + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvlb_computed_bloom (GuestAddrs.block_validate_logs_bloom + 72)),
    .LI .x6 (32 : Word),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .SD .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.bvlb_computed_bloom (GuestAddrs.block_validate_logs_bloom + 112)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bvlb_computed_bloom (GuestAddrs.block_validate_logs_bloom + 112)),
    .JAL .x1 (jalOff GuestAddrs.block_logs_bloom_from_receipts_list (GuestAddrs.block_validate_logs_bloom + 120)),
    .BNE .x10 .x0 (48 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.bvlb_header_bloom (GuestAddrs.block_validate_logs_bloom + 128)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bvlb_header_bloom (GuestAddrs.block_validate_logs_bloom + 128)),
    .AUIPC .x11 (laHi GuestAddrs.bvlb_computed_bloom (GuestAddrs.block_validate_logs_bloom + 136)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bvlb_computed_bloom (GuestAddrs.block_validate_logs_bloom + 136)),
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.bloom_eq (GuestAddrs.block_validate_logs_bloom + 148)),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .SD .x20 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (12 : BitVec 21),
    .SD .x20 .x0 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockValidateLogsBloom_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockValidateLogsBloom_relocs : RelocTable :=
  [ (14, .la .x12 "bvlb_header_bloom"),
    (16, .jal .x1 "header_extract_logs_bloom"),
    (18, .la .x5 "bvlb_computed_bloom"),
    (28, .la .x12 "bvlb_computed_bloom"),
    (30, .jal .x1 "block_logs_bloom_from_receipts_list"),
    (32, .la .x10 "bvlb_header_bloom"),
    (34, .la .x11 "bvlb_computed_bloom"),
    (37, .jal .x1 "bloom_eq") ]

def blockValidateLogsBloomFunction : String :=
  "block_validate_logs_bloom:\n" ++ emitProgramR blockValidateLogsBloom_prog blockValidateLogsBloom_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockValidateLogsBloom_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockValidateLogsBloomFunction_eq_prog :
    blockValidateLogsBloomFunction = "block_validate_logs_bloom:\n" ++ emitProgramR blockValidateLogsBloom_prog blockValidateLogsBloom_relocs := rfl

#guard blockValidateLogsBloomFunction.startsWith "block_validate_logs_bloom:\n"
#guard blockValidateLogsBloom_prog.length = 53
/-- `zisk_block_validate_logs_bloom`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : receipts_list_rlp_len
      bytes 16..   : header_rlp || receipts_list_rlp
        (the script appends them with no padding between; the
         prologue computes the second pointer from the first
         length).
    Output layout:
      bytes  0.. 8 : status (0=ok, 1=header fail, 2=receipts fail)
      bytes  8..16 : is_valid (1 if bloom matches, 0 otherwise) -/
def ziskBlockValidateLogsBloomPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # header_rlp_len\n" ++
  "  ld a3, 16(a5)               # receipts_list_rlp_len\n" ++
  "  addi a0, a5, 24             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # receipts_list_rlp ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_logs_bloom\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvlb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  headerExtractLogsBloomFunction ++ "\n" ++
  receiptExtractLogsBloomFunction ++ "\n" ++
  bloomOrIntoFunction ++ "\n" ++
  bloomEqFunction ++ "\n" ++
  blockLogsBloomFromReceiptsListFunction ++ "\n" ++
  blockValidateLogsBloomFunction ++ "\n" ++
  ".Lbvlb_pdone:"

def ziskBlockValidateLogsBloomDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "helb_offset:\n" ++
  "  .zero 8\n" ++
  "helb_length:\n" ++
  "  .zero 8\n" ++
  "relb_offset:\n" ++
  "  .zero 8\n" ++
  "relb_length:\n" ++
  "  .zero 8\n" ++
  "blbr_count:\n" ++
  "  .zero 8\n" ++
  "blbr_offset:\n" ++
  "  .zero 8\n" ++
  "blbr_length:\n" ++
  "  .zero 8\n" ++
  "blbr_next_offset:\n" ++
  "  .zero 8\n" ++
  "blbr_next_length:\n" ++
  "  .zero 8\n" ++
  "blbr_scratch_bloom:\n" ++
  "  .zero 256\n" ++
  "bvlb_header_bloom:\n" ++
  "  .zero 256\n" ++
  "bvlb_computed_bloom:\n" ++
  "  .zero 256"


end EvmAsm.Codegen
