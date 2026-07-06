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
    header fields. The walk directly copies field 3 (state_root) and
    decodes fields 8, 10, 11, and 15 with rlp_content_to_u64, avoiding
    four full rlp_field_to_u64 rescans of the same header.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 96-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success (all 6 fields written)
        1 : RLP parse failure / required field missing
        2 : some integer field exceeds 8 bytes BE / state_root != 32 -/
def headerComputeSummaryStructFunction : String :=
  "header_compute_summary_struct:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2                            # output struct\n" ++
  "  # 1. block_hash -> out[0..32]\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # 2. Initialize one cursor walk over the header RLP.\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lhcss_parse_fail\n" ++
  "  mv s3, a0                            # cursor\n" ++
  "  mv s4, a1                            # end\n" ++
  "  # Skip fields 0, 1, 2.\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  # Field 3: state_root -> out[32..64].\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail\n" ++
  "  li t0, 32; bne a2, t0, .Lhcss_size_fail\n" ++
  "  sub t1, a0, a2                       # content ptr\n" ++
  "  ld t2,  0(t1); sd t2, 32(s2)\n" ++
  "  ld t2,  8(t1); sd t2, 40(s2)\n" ++
  "  ld t2, 16(t1); sd t2, 48(s2)\n" ++
  "  ld t2, 24(t1); sd t2, 56(s2)\n" ++
  "  mv s3, a0\n" ++
  "  # Skip fields 4, 5, 6, 7.\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  # Field 8: number -> out[64..72].\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail\n" ++
  "  sub t0, a0, a2; mv s5, a0; mv a0, t0; mv a1, a2; jal ra, rlp_content_to_u64; bnez a1, .Lhcss_int_fail\n" ++
  "  sd a0, 64(s2); mv s3, s5\n" ++
  "  # Skip field 9.\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  # Field 10: gas_used -> out[80..88].\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail\n" ++
  "  sub t0, a0, a2; mv s3, a0; mv a0, t0; mv a1, a2; jal ra, rlp_content_to_u64; bnez a1, .Lhcss_int_fail\n" ++
  "  sd a0, 80(s2)\n" ++
  "  # Field 11: timestamp -> out[72..80].\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail\n" ++
  "  sub t0, a0, a2; mv s3, a0; mv a0, t0; mv a1, a2; jal ra, rlp_content_to_u64; bnez a1, .Lhcss_int_fail\n" ++
  "  sd a0, 72(s2)\n" ++
  "  # Skip fields 12, 13, 14.\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail; mv s3, a0\n" ++
  "  # Field 15: base_fee_per_gas -> out[88..96].\n" ++
  "  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next; bnez a1, .Lhcss_parse_fail\n" ++
  "  sub t0, a0, a2; mv a0, t0; mv a1, a2; jal ra, rlp_content_to_u64; bnez a1, .Lhcss_int_fail\n" ++
  "  sd a0, 88(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcss_ret\n" ++
  ".Lhcss_parse_fail:\n" ++
  "  li a0, 1; j .Lhcss_ret\n" ++
  ".Lhcss_size_fail:\n" ++
  "  li a0, 2; j .Lhcss_ret\n" ++
  ".Lhcss_int_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhcss_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

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
