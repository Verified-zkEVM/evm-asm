/-
  EvmAsm.Codegen.Programs.HeaderSummaryStruct

  Header summary-struct codegen probe split from BlockHashPredicates to keep
  the predicate module below the file-size guardrail.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## header_compute_summary_struct -- PR-K214

    Extract a 96-byte block summary struct from a header:

      bytes  0.. 32 : block_hash         (keccak256 of header RLP)
      bytes 32.. 64 : state_root         (field 3)
      bytes 64.. 72 : number             (field 8, u64)
      bytes 72.. 80 : timestamp          (field 11, u64)
      bytes 80.. 88 : gas_used           (field 10, u64)
      bytes 88.. 96 : base_fee_per_gas   (field 15, u64; pre-
                                          London headers fail
                                          and the field stays 0)

    Useful as a chain-indexing primitive: stores the canonical
    "what is this block" tuple in one shot, ready to dump as a
    fixed-size record.

    Composes K172 (block_hash) + a single RLP cursor walk over the
    header fields. The walk directly copies field 3 (state_root), decodes
    fields 8, 10, and 11 with rlp_content_to_u64_strict, and keeps field 15
    on the lenient path for its separate reference type.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 96-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success (all 6 fields written)
        1 : RLP parse failure / required field missing
        2 : some integer field exceeds 8 bytes BE / state_root != 32 -/
def headerComputeSummaryStruct_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
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
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.block_hash_from_header 2147483704),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init 2147483716),
    .BNE .x12 .x0 (brOff 2147484200 2147483720),
    .MV .x19 .x10,
    .MV .x20 .x11,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483740),
    .BNE .x11 .x0 (brOff 2147484200 2147483744),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483760),
    .BNE .x11 .x0 (brOff 2147484200 2147483764),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483780),
    .BNE .x11 .x0 (brOff 2147484200 2147483784),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483800),
    .BNE .x11 .x0 (brOff 2147484200 2147483804),
    .LI .x5 (32 : Word),
    .BNE .x12 .x5 (brOff 2147484208 2147483812),
    .SUB .x6 .x10 .x12,
    .LD .x7 .x6 (0 : BitVec 12),
    .SD .x18 .x7 (32 : BitVec 12),
    .LD .x7 .x6 (8 : BitVec 12),
    .SD .x18 .x7 (40 : BitVec 12),
    .LD .x7 .x6 (16 : BitVec 12),
    .SD .x18 .x7 (48 : BitVec 12),
    .LD .x7 .x6 (24 : BitVec 12),
    .SD .x18 .x7 (56 : BitVec 12),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483864),
    .BNE .x11 .x0 (brOff 2147484200 2147483868),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483884),
    .BNE .x11 .x0 (brOff 2147484200 2147483888),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483904),
    .BNE .x11 .x0 (brOff 2147484200 2147483908),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483924),
    .BNE .x11 .x0 (brOff 2147484200 2147483928),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483944),
    .BNE .x11 .x0 (brOff 2147484200 2147483948),
    .SUB .x5 .x10 .x12,
    .MV .x21 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict 2147483968),
    .BNE .x11 .x0 (brOff 2147484216 2147483972),
    .SD .x18 .x10 (64 : BitVec 12),
    .MV .x19 .x21,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483992),
    .BNE .x11 .x0 (brOff 2147484200 2147483996),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147484012),
    .BNE .x11 .x0 (brOff 2147484200 2147484016),
    .SUB .x5 .x10 .x12,
    .MV .x19 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict 2147484036),
    .BNE .x11 .x0 (brOff 2147484216 2147484040),
    .SD .x18 .x10 (80 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147484056),
    .BNE .x11 .x0 (brOff 2147484200 2147484060),
    .SUB .x5 .x10 .x12,
    .MV .x19 .x10,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict 2147484080),
    .BNE .x11 .x0 (brOff 2147484216 2147484084),
    .SD .x18 .x10 (72 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147484100),
    .BNE .x11 .x0 (brOff 2147484200 2147484104),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147484120),
    .BNE .x11 .x0 (brOff 2147484200 2147484124),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147484140),
    .BNE .x11 .x0 (56 : BitVec 13),
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147484160),
    .BNE .x11 .x0 (36 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .MV .x10 .x5,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64 2147484180),
    .BNE .x11 .x0 (32 : BitVec 13),
    .SD .x18 .x10 (88 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerComputeSummaryStruct_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerComputeSummaryStruct_relocs : RelocTable :=
  [ (14, .jal .x1 "block_hash_from_header"),
    (17, .jal .x1 "rlp_walk_init"),
    (23, .jal .x1 "rlp_walk_next"),
    (28, .jal .x1 "rlp_walk_next"),
    (33, .jal .x1 "rlp_walk_next"),
    (38, .jal .x1 "rlp_walk_next"),
    (54, .jal .x1 "rlp_walk_next"),
    (59, .jal .x1 "rlp_walk_next"),
    (64, .jal .x1 "rlp_walk_next"),
    (69, .jal .x1 "rlp_walk_next"),
    (74, .jal .x1 "rlp_walk_next"),
    (80, .jal .x1 "rlp_content_to_u64_strict"),
    (86, .jal .x1 "rlp_walk_next"),
    (91, .jal .x1 "rlp_walk_next"),
    (97, .jal .x1 "rlp_content_to_u64_strict"),
    (102, .jal .x1 "rlp_walk_next"),
    (108, .jal .x1 "rlp_content_to_u64_strict"),
    (113, .jal .x1 "rlp_walk_next"),
    (118, .jal .x1 "rlp_walk_next"),
    (123, .jal .x1 "rlp_walk_next"),
    (128, .jal .x1 "rlp_walk_next"),
    (133, .jal .x1 "rlp_content_to_u64") ]

def headerComputeSummaryStructFunction : String :=
  "header_compute_summary_struct:\n" ++ emitProgramR headerComputeSummaryStruct_prog headerComputeSummaryStruct_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerComputeSummaryStruct_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerComputeSummaryStructFunction_eq_prog :
    headerComputeSummaryStructFunction = "header_compute_summary_struct:\n" ++ emitProgramR headerComputeSummaryStruct_prog headerComputeSummaryStruct_relocs := rfl

#guard headerComputeSummaryStructFunction.startsWith "header_compute_summary_struct:\n"
#guard headerComputeSummaryStruct_prog.length = 152
/-- `zisk_header_compute_summary_struct`: probe BuildUnit.
    Input layout:
      bytes 0..8 : header_rlp_len
      bytes 8..  : header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..104: 96-byte summary struct -/
def ziskHeaderComputeSummaryStructPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_compute_summary_struct\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhcss_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  headerComputeSummaryStructFunction ++ "\n" ++
  ".Lhcss_pdone:"

def ziskHeaderComputeSummaryStructDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8"

def ziskHeaderComputeSummaryStructProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderComputeSummaryStructPrologue
  dataAsm     := ziskHeaderComputeSummaryStructDataSection
}

end EvmAsm.Codegen
