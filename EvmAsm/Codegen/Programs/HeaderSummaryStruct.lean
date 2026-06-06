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

    Composes K172 (block_hash) + K201 (state_root) +
    rlp_field_to_u64 ×4. The integer fields use the same shape
    as K198 / K210 / K211 / K38; the state_root copy uses the
    same 4 × 8B pattern as K201.

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
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2                            # output struct\n" ++
  "  # 1. block_hash -> out[0..32]\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # 2. state_root -> out[32..64]\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  addi a2, s2, 32\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  bnez a0, .Lhcss_propagate_size\n" ++
  "  # 3. number -> out[64..72] (field 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  addi a3, s2, 64\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhcss_propagate_int\n" ++
  "  # 4. timestamp -> out[72..80] (field 11)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 72\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhcss_propagate_int\n" ++
  "  # 5. gas_used -> out[80..88] (field 10)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhcss_propagate_int\n" ++
  "  # 6. base_fee_per_gas -> out[88..96] (field 15)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 15\n" ++
  "  addi a3, s2, 88\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhcss_propagate_int\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcss_ret\n" ++
  ".Lhcss_propagate_size:\n" ++
  "  # state_root status: 1=parse, 2=size. Pass through unchanged.\n" ++
  "  j .Lhcss_ret\n" ++
  ".Lhcss_propagate_int:\n" ++
  "  # rlp_field_to_u64 returns 1=parse, 2=too_long. Map both to\n" ++
  "  # the same code as the upper-level status.\n" ++
  ".Lhcss_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
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
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
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
