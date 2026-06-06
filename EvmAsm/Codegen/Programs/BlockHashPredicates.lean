/-
  EvmAsm.Codegen.Programs.BlockHashPredicates

  Per-block hash predicates + companion extractors carved out of
  `EvmAsm.Codegen.Programs.Header` per the file-size hard cap.
  Hosts:

    K209  block_hash_matches
    K210  header_extract_gas_used
    K211  header_extract_gas_limit
    K212  block_validate_block_hash_pair
    K213  block_hash_and_extract_number
    K214  header_compute_summary_struct

  Compose K172 `block_hash_from_header` (Header.lean), K201
  `header_extract_state_root` (HeaderFields.lean), K20 / K34 from
  RlpRead + Tx, and `zkvm_keccak256` from HashBridge.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.HeaderU64

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_hash_matches -- PR-K209

    Given a header RLP and a caller-supplied claimed 32-byte
    `block_hash`, verify that
    `keccak256(header_rlp) == claimed_block_hash`. Returns the
    predicate via the `is_valid` output.

    Useful for light-client / bridge proofs where the caller
    has a trusted block_hash from elsewhere and wants to confirm
    the locally-held header RLP matches.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : claimed_block_hash ptr (32 bytes)
      a3 (input)  : u64 out (is_valid: 1 if matches, else 0)
      ra (input)  : return
      a0 (output) : 0 (always succeeds; predicate is in is_valid) -/
def blockHashMatchesFunction : String :=
  "block_hash_matches:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # claimed_hash ptr\n" ++
  "  mv s1, a3                   # is_valid out\n" ++
  "  sd zero, 0(s1)\n" ++
  "  # Compute keccak256(header_rlp) into bhm_computed\n" ++
  "  la a2, bhm_computed\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # Compare 32 bytes (4 × 8B)\n" ++
  "  la t0, bhm_computed\n" ++
  "  ld t2,  0(t0); ld t3,  0(s0); bne t2, t3, .Lbhm_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(s0); bne t2, t3, .Lbhm_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(s0); bne t2, t3, .Lbhm_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(s0); bne t2, t3, .Lbhm_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s1)\n" ++
  ".Lbhm_neq:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_hash_matches`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..40 : claimed_block_hash (32 B)
      bytes 40..   : header_rlp
    Output layout:
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : is_valid -/
def ziskBlockHashMatchesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a2, a7, 16             # claimed_hash ptr\n" ++
  "  addi a0, a7, 48             # header_rlp ptr\n" ++
  "  li a3, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_hash_matches\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbhm_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  blockHashMatchesFunction ++ "\n" ++
  ".Lbhm_pdone:"

def ziskBlockHashMatchesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bhm_computed:\n" ++
  "  .zero 32"

def ziskBlockHashMatchesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockHashMatchesPrologue
  dataAsm     := ziskBlockHashMatchesDataSection
}

/-! ## header_extract_gas_used / header_extract_gas_limit -- PR-K210 / K211

    Two more u64 header-field extractors, completing the
    `header_extract_*` u64 family alongside K198
    (base_fee_per_gas):

      K210  header_extract_gas_used   (field 10)
      K211  header_extract_gas_limit  (field 9)

    Each thin-wraps `rlp_field_to_u64` for the specific field
    index. Useful for chain monitoring / fee-market analysis.

    Calling convention (both):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field missing
        2 : field exceeds 8 bytes BE -/
def headerExtractGasUsedFunction : String :=
  "header_extract_gas_used:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 10\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderExtractGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_gas_used\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhegu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractGasUsedFunction ++ "\n" ++
  ".Lhegu_pdone:"

def ziskHeaderExtractGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractGasUsedPrologue
  dataAsm     := ziskHeaderExtractGasUsedDataSection
}

def headerExtractGasLimitFunction : String :=
  "header_extract_gas_limit:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 9\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderExtractGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_gas_limit\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhegl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractGasLimitFunction ++ "\n" ++
  ".Lhegl_pdone:"

def ziskHeaderExtractGasLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractGasLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractGasLimitPrologue
  dataAsm     := ziskHeaderExtractGasLimitDataSection
}

/-! ## block_validate_block_hash_pair -- PR-K212

    Compute both `parent_block_hash` and `child_block_hash`
    AND verify `child.parent_hash == parent_block_hash`. Useful
    for chain-commitment proofs that need both hashes alongside
    the validity bit.

    Composes K172 `block_hash_from_header` (parent + child) +
    K20 `rlp_list_nth_item` (extract child.parent_hash).

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : child_rlp ptr
      a3 (input)  : child_rlp byte length
      a4 (input)  : 32-byte output ptr (parent_block_hash)
      a5 (input)  : 32-byte output ptr (child_block_hash)
      a6 (input)  : u64 out (is_valid: 1 if child.parent_hash
                              == parent_block_hash, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success -- both hashes + predicate written
        1 : child RLP parse failure / field 0 missing
        2 : child.parent_hash length != 32 -/
def blockValidateBlockHashPairFunction : String :=
  "block_validate_block_hash_pair:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # parent\n" ++
  "  mv s2, a2; mv s3, a3                # child\n" ++
  "  mv s4, a4                            # parent_hash out\n" ++
  "  mv s5, a5                            # child_hash out\n" ++
  "  mv s6, a6                            # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # 1. Compute parent block_hash -> s4\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s4\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # 2. Compute child block_hash -> s5\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, s5\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # 3. Extract child.field[0] (parent_hash)\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 0\n" ++
  "  la a3, bvhp_offset; la a4, bvhp_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvhp_parse_fail\n" ++
  "  la t0, bvhp_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbvhp_size_fail\n" ++
  "  # 4. Compare child.parent_hash bytes against s4 (parent_hash)\n" ++
  "  la t0, bvhp_offset; ld t1, 0(t0)\n" ++
  "  add t3, s2, t1\n" ++
  "  ld t4,  0(t3); ld t5,  0(s4); bne t4, t5, .Lbvhp_neq\n" ++
  "  ld t4,  8(t3); ld t5,  8(s4); bne t4, t5, .Lbvhp_neq\n" ++
  "  ld t4, 16(t3); ld t5, 16(s4); bne t4, t5, .Lbvhp_neq\n" ++
  "  ld t4, 24(t3); ld t5, 24(s4); bne t4, t5, .Lbvhp_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s6)\n" ++
  ".Lbvhp_neq:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvhp_ret\n" ++
  ".Lbvhp_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvhp_ret\n" ++
  ".Lbvhp_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvhp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_validate_block_hash_pair`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : child_rlp_len
      bytes 16..   : parent_rlp || child_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid
      bytes 16..48 : parent_block_hash
      bytes 48..80 : child_block_hash -/
def ziskBlockValidateBlockHashPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # parent_len\n" ++
  "  ld a3, 16(a7)               # child_len\n" ++
  "  addi a0, a7, 24             # parent_rlp ptr\n" ++
  "  add a2, a0, a1              # child_rlp ptr\n" ++
  "  li a4, 0xa0010010           # parent_hash out\n" ++
  "  li a5, 0xa0010030           # child_hash out\n" ++
  "  li a6, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_block_hash_pair\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvhp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  blockValidateBlockHashPairFunction ++ "\n" ++
  ".Lbvhp_pdone:"

def ziskBlockValidateBlockHashPairDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bvhp_offset:\n" ++
  "  .zero 8\n" ++
  "bvhp_length:\n" ++
  "  .zero 8"

def ziskBlockValidateBlockHashPairProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateBlockHashPairPrologue
  dataAsm     := ziskBlockValidateBlockHashPairDataSection
}

/-! ## block_hash_and_extract_number -- PR-K213

    From a single header RLP, return both the block_hash (K172)
    and the block number (field 8 as u64). Useful as the
    "labelled block hash" primitive -- callers commonly want
    both together for chain indexing / commitment.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr (block_hash)
      a3 (input)  : u64 out (block number)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 8 missing
        2 : number field exceeds 8 bytes BE -/
def blockHashAndExtractNumberFunction : String :=
  "block_hash_and_extract_number:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a3                            # number out ptr (stash)\n" ++
  "  # 1. block_hash -> a2 (already set by caller)\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # 2. number -> via rlp_field_to_u64(header, len, 8, &out)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_hash_and_extract_number`: probe BuildUnit.
    Input layout:
      bytes 0..8 : header_rlp_len
      bytes 8..  : header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : number
      bytes 16..48 : block_hash -/
def ziskBlockHashAndExtractNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_len\n" ++
  "  addi a0, a7, 16             # header ptr\n" ++
  "  li a2, 0xa0010010           # 32B block_hash out\n" ++
  "  li a3, 0xa0010008           # u64 number out\n" ++
  "  jal ra, block_hash_and_extract_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbhen_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  blockHashAndExtractNumberFunction ++ "\n" ++
  ".Lbhen_pdone:"

def ziskBlockHashAndExtractNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskBlockHashAndExtractNumberProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockHashAndExtractNumberPrologue
  dataAsm     := ziskBlockHashAndExtractNumberDataSection
}

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

/-! ## blockhash_from_witness_headers

    BLOCKHASH-opcode semantics over a stateless witness: given a
    target block number and the `witness.headers` SSZ list
    section, find the header whose `block.number` field matches
    the target, then return `keccak256(header_rlp)`.

    The witness layout is the same as `witness.state` /
    `witness.codes` -- `[N x u32 inner offsets][concat header
    bytes]` -- so the iteration pattern mirrors K19
    `witness_lookup_by_hash`, but with the match criterion
    swapped from a hash compare to a `header_extract_number`
    call.

    Calling convention:
      a0 (input)  : target block number (u64)
      a1 (input)  : witness.headers section ptr
      a2 (input)  : section_len (0 ⇒ guaranteed miss)
      a3 (input)  : 32-byte output buffer (block hash; written on hit only)
      a4 (input)  : u64 out ptr (matched element offset within section; on hit only)
      a5 (input)  : u64 out ptr (matched element length; on hit only)
      ra (input)  : return
      a0 (output) :
        0 hit (output buffer filled, offset/length written)
        1 miss
        2 RLP parse failure on some header along the way
-/
def blockhashFromWitnessHeadersFunction : String :=
  "blockhash_from_witness_headers:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s7, a0                  # target block number\n" ++
  "  mv s0, a1                  # section ptr\n" ++
  "  mv s1, a2                  # section_len\n" ++
  "  mv s2, a3                  # block hash output ptr\n" ++
  "  mv s3, a4                  # offset out ptr\n" ++
  "  mv s4, a5                  # length out ptr\n" ++
  "  beqz s1, .Lbhfwh_miss      # empty section ⇒ miss\n" ++
  "  lwu t0, 0(s0)              # first inner offset = 4 * N\n" ++
  "  srli s5, t0, 2             # s5 = N\n" ++
  "  li s6, 0                   # s6 = i\n" ++
  ".Lbhfwh_loop:\n" ++
  "  beq s6, s5, .Lbhfwh_miss\n" ++
  "  # Compute element i bounds.\n" ++
  "  slli t0, s6, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lbhfwh_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lbhfwh_have_end\n" ++
  ".Lbhfwh_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lbhfwh_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, bhfwh_number_buf\n" ++
  "  jal ra, header_extract_number\n" ++
  "  beqz a0, .Lbhfwh_compare\n" ++
  "  li a0, 2                   # any header that fails to parse number ⇒ status 2\n" ++
  "  j .Lbhfwh_ret\n" ++
  ".Lbhfwh_compare:\n" ++
  "  la t0, bhfwh_number_buf; ld t1, 0(t0)\n" ++
  "  beq t1, s7, .Lbhfwh_match\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lbhfwh_loop\n" ++
  ".Lbhfwh_match:\n" ++
  "  # Recompute (offset, length) since they were clobbered.\n" ++
  "  slli t0, s6, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add a0, s0, t2             # el_start\n" ++
  "  sd t2, 0(s3)               # *out_offset\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lbhfwh_last\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  sub t4, t4, t2             # length\n" ++
  "  j .Lbhfwh_store_len\n" ++
  ".Lbhfwh_last:\n" ++
  "  sub t4, s1, t2\n" ++
  ".Lbhfwh_store_len:\n" ++
  "  sd t4, 0(s4)               # *out_length\n" ++
  "  mv a1, t4                  # length argument for keccak\n" ++
  "  mv a2, s2                  # block hash out ptr\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lbhfwh_ret\n" ++
  ".Lbhfwh_miss:\n" ++
  "  li a0, 1\n" ++
  ".Lbhfwh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_blockhash_from_witness_headers`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : target_block_number (u64 LE)
      bytes 16..24 : section_len (u64 LE)
      bytes 24..   : witness.headers section
    Output layout:
      bytes  0.. 8 : status (0 hit / 1 miss / 2 parse_fail)
      bytes  8..16 : matched offset within section (on hit)
      bytes 16..24 : matched length within section (on hit)
      bytes 24..56 : block hash (on hit; zeros otherwise) -/
def ziskBlockhashFromWitnessHeadersPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a0, 8(a6)                # target block number\n" ++
  "  ld a2, 16(a6)               # section_len\n" ++
  "  addi a1, a6, 24             # section ptr\n" ++
  "  li a3, 0xa0010018           # block hash out (OUTPUT + 24)\n" ++
  "  li a4, 0xa0010008           # offset out  (OUTPUT + 8)\n" ++
  "  li a5, 0xa0010010           # length out  (OUTPUT + 16)\n" ++
  "  # Pre-zero outputs so non-hit cases surface as zeros.\n" ++
  "  sd zero, 0(a4); sd zero, 0(a5)\n" ++
  "  sd zero, 0(a3); sd zero, 8(a3); sd zero, 16(a3); sd zero, 24(a3)\n" ++
  "  jal ra, blockhash_from_witness_headers\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lbhfwh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  blockhashFromWitnessHeadersFunction ++ "\n" ++
  ".Lbhfwh_pdone:"

def ziskBlockhashFromWitnessHeadersDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bhfwh_number_buf:\n" ++
  "  .zero 8"

def ziskBlockhashFromWitnessHeadersProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockhashFromWitnessHeadersPrologue
  dataAsm     := ziskBlockhashFromWitnessHeadersDataSection
}

/-! ## witness_headers_chain_validate

    Verify that an SSZ `witness.headers` list forms a coherent
    chain: for each consecutive pair `(headers[i], headers[i+1])`,
    confirm that
      keccak256(headers[i]) == headers[i+1].parent_hash.

    This is a per-pair generalization of K212
    `block_validate_block_hash_pair` (which handles one pair) to
    the whole witness section. Spec-side, this is the invariant
    that lets `apply_body` trust the witness chain as the
    canonical link from `parent_header` back to an ancestor: a
    chain whose any pair fails this predicate is structurally
    invalid and cannot be used to resolve `BLOCKHASH(n)` for
    older heights without first detecting the break.

    Walks the SSZ list with the same iteration pattern as K19
    `witness_lookup_by_hash` / `blockhash_from_witness_headers`.

    Calling convention:
      a0 (input)  : witness.headers section ptr
      a1 (input)  : section_len (0 ⇒ vacuous-valid)
      a2 (input)  : u64 out ptr (n_pairs_checked; pairs == N-1
                    on full success, or i (the first failing
                    parent index) on mismatch / parse fail)
      a3 (input)  : u64 out ptr (first_mismatch_index;
                    written as 0xFFFFFFFFFFFFFFFF when no
                    mismatch was found, else the parent index i
                    of the failing pair)
      ra (input)  : return
      a0 (output) :
        0 = all consecutive pairs link (or N ≤ 1, vacuous)
        1 = some pair's parent_hash mismatch detected
        2 = RLP parse failure when reading some header's
            `parent_hash` field
-/
def witnessHeadersChainValidateFunction : String :=
  "witness_headers_chain_validate:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # n_pairs_out ptr\n" ++
  "  mv s3, a3                  # mismatch_idx_out ptr\n" ++
  "  # Pre-fill outputs assuming vacuous-success: n=0, mismatch=-1.\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  beqz s1, .Lwchv_ok           # empty section ⇒ vacuous\n" ++
  "  lwu t0, 0(s0)                # first inner offset = 4 * N\n" ++
  "  srli s4, t0, 2               # s4 = N\n" ++
  "  li t1, 1\n" ++
  "  bleu s4, t1, .Lwchv_ok       # N ≤ 1 ⇒ vacuous\n" ++
  "  li s5, 0                     # s5 = i (parent index)\n" ++
  ".Lwchv_loop:\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lwchv_ok        # i+1 == N: all pairs checked\n" ++
  "  # Parent (element s5) bounds.\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)                # parent inner_off\n" ++
  "  add a0, s0, t2               # parent_ptr\n" ++
  "  slli t4, t3, 2               # 4*(i+1)\n" ++
  "  add t4, s0, t4\n" ++
  "  lwu t5, 0(t4)                # next inner_off = parent_end_off\n" ++
  "  sub a1, t5, t2               # parent_len\n" ++
  "  # keccak256(parent_rlp) -> wchv_parent_keccak\n" ++
  "  la a2, wchv_parent_keccak\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Child (element s5+1) bounds.\n" ++
  "  addi t3, s5, 1\n" ++
  "  slli t4, t3, 2\n" ++
  "  add t4, s0, t4\n" ++
  "  lwu t5, 0(t4)                # child inner_off\n" ++
  "  add a0, s0, t5               # child_ptr\n" ++
  "  addi t6, t3, 1\n" ++
  "  beq t6, s4, .Lwchv_use_end\n" ++
  "  slli t6, t6, 2\n" ++
  "  add t6, s0, t6\n" ++
  "  lwu s6, 0(t6)\n" ++
  "  j .Lwchv_have_end\n" ++
  ".Lwchv_use_end:\n" ++
  "  mv s6, s1\n" ++
  ".Lwchv_have_end:\n" ++
  "  sub a1, s6, t5               # child_len\n" ++
  "  la a2, wchv_child_parent_hash\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  beqz a0, .Lwchv_compare\n" ++
  "  # parent_hash extract failed -> status 2.\n" ++
  "  sd s5, 0(s2)\n" ++
  "  sd s5, 0(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lwchv_ret\n" ++
  ".Lwchv_compare:\n" ++
  "  la t0, wchv_parent_keccak\n" ++
  "  la t1, wchv_child_parent_hash\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lwchv_mismatch\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lwchv_mismatch\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lwchv_mismatch\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lwchv_mismatch\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwchv_loop\n" ++
  ".Lwchv_mismatch:\n" ++
  "  sd s5, 0(s2)                 # n_pairs_out = i\n" ++
  "  sd s5, 0(s3)                 # mismatch_idx_out = i\n" ++
  "  li a0, 1\n" ++
  "  j .Lwchv_ret\n" ++
  ".Lwchv_ok:\n" ++
  "  # Write n_pairs = N-1 (or 0 if N<=1; we'll handle below).\n" ++
  "  li t0, 1\n" ++
  "  bleu s4, t0, .Lwchv_n_is_zero\n" ++
  "  addi t0, s4, -1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  j .Lwchv_ok_pred\n" ++
  ".Lwchv_n_is_zero:\n" ++
  "  sd zero, 0(s2)\n" ++
  ".Lwchv_ok_pred:\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  li a0, 0\n" ++
  ".Lwchv_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_witness_headers_chain_validate`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : section_len (u64 LE)
      bytes 16..   : witness.headers section
    Output layout:
      bytes  0.. 8 : status (0 / 1 / 2)
      bytes  8..16 : n_pairs_checked / first failing parent index
      bytes 16..24 : mismatch_index (0xFF..FF on success) -/
def ziskWitnessHeadersChainValidatePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # section_len\n" ++
  "  addi a0, a6, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # n_pairs out\n" ++
  "  li a3, 0xa0010010           # mismatch_idx out\n" ++
  "  jal ra, witness_headers_chain_validate\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lwchv_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  witnessHeadersChainValidateFunction ++ "\n" ++
  ".Lwchv_pdone:"

def ziskWitnessHeadersChainValidateDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "heph_offset:\n" ++
  "  .zero 8\n" ++
  "heph_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "wchv_parent_keccak:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "wchv_child_parent_hash:\n" ++
  "  .zero 32"

def ziskWitnessHeadersChainValidateProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessHeadersChainValidatePrologue
  dataAsm     := ziskWitnessHeadersChainValidateDataSection
}

/-! ## parent_header_matches_witness_first

    Cross-input consistency check: verify that a caller-supplied
    `parent_header_rlp` matches `witness.headers[0]` byte-for-byte.
    Returns `is_match = 1` iff they agree.

    Spec-side rationale: most stateless-guest entry points take
    a `parent_header` argument AND a `witness.headers` SSZ list.
    By convention, `witness.headers[0]` is supposed to be the
    SAME parent header. A mismatch is an input inconsistency
    that should be caught up-front rather than discovered later
    via diverging state_root extractions.

    The check is a byte-equality compare rather than a
    double-keccak: equal byte spans trivially have equal hashes
    AND any non-equality is detected without paying for two
    keccak calls.

    Calling convention:
      a0 (input)  : parent_header_rlp ptr
      a1 (input)  : parent_header_rlp_len
      a2 (input)  : witness.headers section ptr
      a3 (input)  : witness.headers section_len
      a4 (input)  : u64 out (is_match: 1 if first entry equals
                    parent_header_rlp byte-for-byte, else 0)
      ra (input)  : return
      a0 (output) :
        0 = success (is_match holds 0 or 1)
        1 = witness.headers section is empty (is_match = 0)
-/
def parentHeaderMatchesWitnessFirstFunction : String :=
  "parent_header_matches_witness_first:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # parent_header_rlp ptr\n" ++
  "  mv s1, a1                  # parent_header_rlp_len\n" ++
  "  mv s2, a2                  # section ptr\n" ++
  "  mv s3, a3                  # section_len\n" ++
  "  mv s4, a4                  # is_match out ptr\n" ++
  "  sd zero, 0(s4)\n" ++
  "  beqz s3, .Lphmw_empty       # empty section -> status 1\n" ++
  "  # Compute element 0 bounds (SSZ list).\n" ++
  "  lwu t0, 0(s2)\n" ++
  "  srli t0, t0, 2              # N = first_offset / 4\n" ++
  "  beqz t0, .Lphmw_empty      # zero entries\n" ++
  "  lwu t1, 0(s2)               # el_0 inner offset (= 4 * N)\n" ++
  "  add s5, s2, t1              # el_0 start\n" ++
  "  # el_0 end: if N > 1, read offset[1] (4 bytes at offset 4); else use section_end.\n" ++
  "  li t2, 1\n" ++
  "  bgtu t0, t2, .Lphmw_have_next\n" ++
  "  add s6, s2, s3              # el_0_end = section_end\n" ++
  "  j .Lphmw_compare\n" ++
  ".Lphmw_have_next:\n" ++
  "  lwu t2, 4(s2)\n" ++
  "  add s6, s2, t2              # el_0_end = section + inner_off[1]\n" ++
  ".Lphmw_compare:\n" ++
  "  sub t0, s6, s5              # el_0 length\n" ++
  "  # Length must match parent_header_rlp_len.\n" ++
  "  bne t0, s1, .Lphmw_no_match_success\n" ++
  "  # Byte-compare s0..s0+s1 against s5..s6.\n" ++
  "  mv t1, s0\n" ++
  "  mv t2, s5\n" ++
  "  mv t3, s1\n" ++
  ".Lphmw_loop:\n" ++
  "  beqz t3, .Lphmw_match\n" ++
  "  lbu t4, 0(t1)\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  bne t4, t5, .Lphmw_no_match_success\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lphmw_loop\n" ++
  ".Lphmw_match:\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lphmw_ret\n" ++
  ".Lphmw_no_match_success:\n" ++
  "  li a0, 0\n" ++
  "  j .Lphmw_ret\n" ++
  ".Lphmw_empty:\n" ++
  "  li a0, 1\n" ++
  ".Lphmw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_parent_header_matches_witness_first`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : parent_header_rlp_len (u64 LE)
      bytes 16..24 : section_len (u64 LE)
      bytes 24..24+H            : parent_header_rlp
      bytes 24+H..24+H+S        : witness.headers section
    Output layout:
      bytes  0.. 8 : status (0 / 1)
      bytes  8..16 : is_match (u64; 0 or 1) -/
def ziskParentHeaderMatchesWitnessFirstPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # parent_header_rlp_len\n" ++
  "  ld a3, 16(a5)               # section_len\n" ++
  "  addi a0, a5, 24             # parent_header_rlp ptr\n" ++
  "  add a2, a0, a1              # section ptr\n" ++
  "  li a4, 0xa0010008           # is_match out\n" ++
  "  jal ra, parent_header_matches_witness_first\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lphmw_pdone\n" ++
  parentHeaderMatchesWitnessFirstFunction ++ "\n" ++
  ".Lphmw_pdone:"

def ziskParentHeaderMatchesWitnessFirstDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "phmw_pad:\n" ++
  "  .zero 8"

def ziskParentHeaderMatchesWitnessFirstProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskParentHeaderMatchesWitnessFirstPrologue
  dataAsm     := ziskParentHeaderMatchesWitnessFirstDataSection
}

/-! ## witness_headers_min_block_number

    Walk an SSZ `witness.headers` list section and compute the
    minimum `block.number` across all entries. Returns the
    minimum as a u64, or 0xFFFFFFFFFFFFFFFF on an empty section
    (the "no value" sentinel convention).

    Spec-side rationale: EVM's `BLOCKHASH(n)` is only defined
    for the most-recent 256 ancestors of the executing block
    (or the EIP-2935 window in Amsterdam+). A stateless guest
    needs to know the oldest block it can resolve via
    `witness.headers`. That bound is `min(headers[i].number)`.
    Reporting it up-front (rather than discovering it
    mid-`BLOCKHASH`) lets the guest reject out-of-window
    queries cleanly.

    Companion to:
      * PR #7147 `blockhash_from_witness_headers` -- lookup by
        number, doesn't iterate to find min.
      * PR #7158 `witness_headers_chain_validate` -- validates
        parent-hash linkage.
      * K233 `header_extract_number` -- per-header extractor
        used internally.

    Calling convention:
      a0 (input)  : witness.headers section ptr
      a1 (input)  : section_len (0 ⇒ empty)
      a2 (input)  : u64 out ptr (min block number; on empty
                    section the value is MAX_U64)
      a3 (input)  : u64 out ptr (n_processed; total header
                    count on success, or the index of the
                    failing header on a parse fail)
      ra (input)  : return
      a0 (output) :
        0 = success
        2 = some header failed `header_extract_number`
-/
def witnessHeadersMinBlockNumberFunction : String :=
  "witness_headers_min_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # min_out ptr\n" ++
  "  mv s3, a3                  # n_processed out ptr\n" ++
  "  li s7, -1                  # s7 = running min (init to MAX_U64)\n" ++
  "  sd s7, 0(s2)\n" ++
  "  sd zero, 0(s3)\n" ++
  "  beqz s1, .Lwhmbn_ok          # empty section ⇒ min = MAX_U64\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s4, t0, 2               # s4 = N\n" ++
  "  li s5, 0                     # s5 = i\n" ++
  ".Lwhmbn_loop:\n" ++
  "  beq s5, s4, .Lwhmbn_ok\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add a0, s0, t2               # el_i_start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lwhmbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4\n" ++
  "  j .Lwhmbn_have_end\n" ++
  ".Lwhmbn_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lwhmbn_have_end:\n" ++
  "  sub a1, t4, a0               # el_i_len\n" ++
  "  la a2, whmbn_num_buf\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lwhmbn_parse_fail\n" ++
  "  la t0, whmbn_num_buf\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bgeu t1, s7, .Lwhmbn_skip   # current >= running min\n" ++
  "  mv s7, t1\n" ++
  ".Lwhmbn_skip:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwhmbn_loop\n" ++
  ".Lwhmbn_parse_fail:\n" ++
  "  sd s5, 0(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lwhmbn_ret\n" ++
  ".Lwhmbn_ok:\n" ++
  "  sd s7, 0(s2)                 # write min\n" ++
  "  sd s4, 0(s3)                 # n_processed = N (= 0 for empty)\n" ++
  "  li a0, 0\n" ++
  ".Lwhmbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_witness_headers_min_block_number`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : section_len (u64 LE)
      bytes 16..   : witness.headers section
    Output layout:
      bytes  0.. 8 : status (0 ok / 2 parse fail)
      bytes  8..16 : min_block_number (MAX_U64 on empty section)
      bytes 16..24 : n_processed (= N on success;
                     failing index on fail) -/
def ziskWitnessHeadersMinBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  addi a0, a5, 16             # section ptr\n" ++
  "  li a2, 0xa0010008\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, witness_headers_min_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhmbn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  witnessHeadersMinBlockNumberFunction ++ "\n" ++
  ".Lwhmbn_pdone:"

def ziskWitnessHeadersMinBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "whmbn_num_buf:\n" ++
  "  .zero 8"

def ziskWitnessHeadersMinBlockNumberProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessHeadersMinBlockNumberPrologue
  dataAsm     := ziskWitnessHeadersMinBlockNumberDataSection
}

end EvmAsm.Codegen
