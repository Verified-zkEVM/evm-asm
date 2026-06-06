/-
  EvmAsm.Codegen.Programs.HeaderU64

  u64-shaped single-field extractors and predicates carved out
  of `EvmAsm.Codegen.Programs.Header` per the file-size hard cap.
  Hosts:

    K215  header_extract_difficulty       (field 7,  u64)
    K216  header_extract_extra_data       (field 12, ≤32 B)
    K217  header_extract_nonce            (field 14, 8 B BE u64)
    K218  header_validate_nonce_zero      (field 14 all-zero)
    K219  header_validate_difficulty_zero (field 7 length 0)
    K233  header_extract_number           (field 8,  u64)

  All six functions are thin wrappers around `rlp_list_nth_item`
  + `rlp_field_to_u64` (or a small byte-level body), depending
  only on `Programs/Tx.lean` for the shared RLP helpers.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HeaderGasLimits
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## header_extract_difficulty -- PR-K215

    Extract `difficulty` (field 7, u64) from a header RLP. In
    practice difficulty is post-merge always `0` and pre-merge
    a uint256 (so callers needing the full uint256 form should
    use `rlp_field_to_u256` once that exists). This thin wrapper
    suffices for the common post-merge `== 0` check and for the
    fits-in-u64 pre-merge cases.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure
        2 : field 7 exceeds 8 bytes BE -/
def headerExtractDifficultyFunction : String :=
  "header_extract_difficulty:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 7\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderExtractDifficultyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_difficulty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhed_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractDifficultyFunction ++ "\n" ++
  ".Lhed_pdone:"

def ziskHeaderExtractDifficultyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractDifficultyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractDifficultyPrologue
  dataAsm     := ziskHeaderExtractDifficultyDataSection
}

/-! ## header_extract_extra_data -- PR-K216

    Extract `extra_data` (field 12, variable length up to 32
    bytes post-merge) from a header RLP. Caller supplies an
    output buffer + u64 length out. Useful for proposer-tag
    analysis and protocol monitoring.

    Note: K68 `header_validate_extra_data_length` already
    checks the size invariant; K216 is the canonical byte-copy
    extractor for the same field.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : output bytes ptr (caller-supplied ≥ 32 B)
      a3 (input)  : u64 out (extra_data length written)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 12 missing
        2 : extra_data length > 32 (EIP-3675 / pre-merge
            constraint violation) -/
def headerExtractExtraDataFunction : String :=
  "header_extract_extra_data:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # header ptr\n" ++
  "  mv s3, a1                   # header len (stash)\n" ++
  "  mv s1, a2                   # out bytes ptr\n" ++
  "  mv s2, a3                   # out length ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s3; li a2, 12\n" ++
  "  la a3, heed_offset; la a4, heed_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lheed_parse_fail\n" ++
  "  la t0, heed_length; ld t1, 0(t0)\n" ++
  "  li t2, 33\n" ++
  "  bgeu t1, t2, .Lheed_size_fail\n" ++
  "  # Byte-copy field 12 content (t1 = length) to s1\n" ++
  "  la t0, heed_offset; ld t3, 0(t0)\n" ++
  "  add t3, s0, t3              # source ptr\n" ++
  "  sd t1, 0(s2)                # save length\n" ++
  "  beqz t1, .Lheed_done\n" ++
  ".Lheed_copy:\n" ++
  "  lbu t4, 0(t3); sb t4, 0(s1)\n" ++
  "  addi t3, t3, 1; addi s1, s1, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lheed_copy\n" ++
  ".Lheed_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lheed_ret\n" ++
  ".Lheed_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lheed_ret\n" ++
  ".Lheed_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lheed_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- `zisk_header_extract_extra_data`: probe BuildUnit.
    Input layout:
      bytes 0..8 : header_rlp_len
      bytes 8..  : header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : extra_data length
      bytes 16..48 : extra_data bytes (up to 32) -/
def ziskHeaderExtractExtraDataPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010010           # bytes out\n" ++
  "  li a3, 0xa0010008           # length out\n" ++
  "  jal ra, header_extract_extra_data\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lheed_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractExtraDataFunction ++ "\n" ++
  ".Lheed_pdone:"

def ziskHeaderExtractExtraDataDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "heed_offset:\n" ++
  "  .zero 8\n" ++
  "heed_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractExtraDataProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractExtraDataPrologue
  dataAsm     := ziskHeaderExtractExtraDataDataSection
}

/-! ## header_extract_nonce -- PR-K217

    Extract `nonce` (field 14, exactly 8 bytes BE in legacy
    headers; post-merge always all-zero per EIP-3675).

    Unlike `rlp_field_to_u64`-based extractors (K198 / K210 /
    K211 / K215), the nonce field is *always* exactly 8 bytes
    -- never a variable-width canonical integer -- so we copy
    the raw bytes and interpret them as a BE u64 directly.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr (BE-decoded nonce)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 14 missing
        2 : field 14 length != 8 -/
def headerExtractNonceFunction : String :=
  "header_extract_nonce:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2                            # out u64 ptr\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 14\n" ++
  "  la a3, hen_offset; la a4, hen_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhen_parse_fail\n" ++
  "  la t0, hen_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bne t1, t2, .Lhen_size_fail\n" ++
  "  la t0, hen_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1                       # &header[off]\n" ++
  "  # Decode 8 BE bytes -> u64 LE\n" ++
  "  li t4, 0\n" ++
  "  lbu t5, 0(t3); slli t4, t4, 8; or t4, t4, t5\n" ++
  "  lbu t5, 1(t3); slli t4, t4, 8; or t4, t4, t5\n" ++
  "  lbu t5, 2(t3); slli t4, t4, 8; or t4, t4, t5\n" ++
  "  lbu t5, 3(t3); slli t4, t4, 8; or t4, t4, t5\n" ++
  "  lbu t5, 4(t3); slli t4, t4, 8; or t4, t4, t5\n" ++
  "  lbu t5, 5(t3); slli t4, t4, 8; or t4, t4, t5\n" ++
  "  lbu t5, 6(t3); slli t4, t4, 8; or t4, t4, t5\n" ++
  "  lbu t5, 7(t3); slli t4, t4, 8; or t4, t4, t5\n" ++
  "  sd t4, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhen_ret\n" ++
  ".Lhen_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhen_ret\n" ++
  ".Lhen_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhen_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskHeaderExtractNoncePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_nonce\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhen_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractNonceFunction ++ "\n" ++
  ".Lhen_pdone:"

def ziskHeaderExtractNonceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hen_offset:\n" ++
  "  .zero 8\n" ++
  "hen_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractNonceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractNoncePrologue
  dataAsm     := ziskHeaderExtractNonceDataSection
}

/-! ## header_validate_nonce_zero -- PR-K218

    Post-merge predicate: verify the 8-byte `nonce` (field 14)
    is all zero, as required by EIP-3675. The predicate
    complement of K217 -- callers wanting just the post-merge
    sanity check rather than the actual nonce u64 should use
    this primitive.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out (is_valid: 1 if nonce == 0..0)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : RLP parse failure / field 14 missing
        2 : field 14 length != 8 -/
def headerValidateNonceZeroFunction : String :=
  "header_validate_nonce_zero:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2                            # is_valid out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 14\n" ++
  "  la a3, hvnz_offset; la a4, hvnz_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvnz_parse_fail\n" ++
  "  la t0, hvnz_length; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bne t1, t2, .Lhvnz_size_fail\n" ++
  "  la t0, hvnz_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4, 0(t3)                        # load 8 bytes\n" ++
  "  bnez t4, .Lhvnz_nonzero\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  ".Lhvnz_nonzero:\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvnz_ret\n" ++
  ".Lhvnz_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhvnz_ret\n" ++
  ".Lhvnz_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhvnz_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskHeaderValidateNonceZeroPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_validate_nonce_zero\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhvnz_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerValidateNonceZeroFunction ++ "\n" ++
  ".Lhvnz_pdone:"

def ziskHeaderValidateNonceZeroDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hvnz_offset:\n" ++
  "  .zero 8\n" ++
  "hvnz_length:\n" ++
  "  .zero 8"

def ziskHeaderValidateNonceZeroProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateNonceZeroPrologue
  dataAsm     := ziskHeaderValidateNonceZeroDataSection
}

/-! ## header_validate_difficulty_zero -- PR-K219

    Post-merge predicate: verify the `difficulty` (field 7)
    is zero, as required by EIP-3675. Counterpart to K218
    nonce-zero check; together with K179 ommers_hash check
    they cover the three post-merge "must be the zero value"
    invariants the EELS validator enforces.

    For RLP-canonical encoding of integers, zero is the empty
    string, so this is the predicate `length(field 7) == 0`.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out (is_valid: 1 if difficulty == 0)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : RLP parse failure / field 7 missing -/
def headerValidateDifficultyZeroFunction : String :=
  "header_validate_difficulty_zero:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp)\n" ++
  "  mv s0, a2                            # is_valid out\n" ++
  "  sd zero, 0(s0)\n" ++
  "  li a2, 7                            # field 7 = difficulty\n" ++
  "  la a3, hvdz_offset; la a4, hvdz_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvdz_parse_fail\n" ++
  "  la t0, hvdz_length; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lhvdz_nonzero\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s0)\n" ++
  ".Lhvdz_nonzero:\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvdz_ret\n" ++
  ".Lhvdz_parse_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lhvdz_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderValidateDifficultyZeroPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_validate_difficulty_zero\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhvdz_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerValidateDifficultyZeroFunction ++ "\n" ++
  ".Lhvdz_pdone:"

def ziskHeaderValidateDifficultyZeroDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hvdz_offset:\n" ++
  "  .zero 8\n" ++
  "hvdz_length:\n" ++
  "  .zero 8"

def ziskHeaderValidateDifficultyZeroProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateDifficultyZeroPrologue
  dataAsm     := ziskHeaderValidateDifficultyZeroDataSection
}

/-! ## header_extract_number -- PR-K233

    Extract `block.number` (field 8, u64 BE) from a header RLP.
    Cross-fork — every header has a number.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure
        2 : field 8 exceeds 8 bytes BE -/
def headerExtractNumberFunction : String :=
  "header_extract_number:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderExtractNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhenu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  ".Lhenu_pdone:"

def ziskHeaderExtractNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractNumberProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractNumberPrologue
  dataAsm     := ziskHeaderExtractNumberDataSection
}

/-! ## chain_compute_max_gas_used -- PR-K236

    Find the maximum of `gas_used` (header field 10) across an
    N-element header chain. Cross-fork — every header has
    gas_used. Useful for peak-congestion monitoring across a
    chain segment, complementing K196
    `chain_compute_total_gas_used` (sum).

    Vacuous on empty chain: max = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (max)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (in any header)
        2 : gas_used field > 8 bytes BE -/
def chainComputeMaxGasUsedFunction : String :=
  "chain_compute_max_gas_used:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmgu_done\n" ++
  ".Lccmgu_loop:\n" ++
  "  beq s4, s0, .Lccmgu_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 10\n" ++
  "  la a3, ccmgu_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccmgu_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccmgu_size_fail\n" ++
  "  la t0, ccmgu_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t2, t1, .Lccmgu_no_update\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmgu_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmgu_loop\n" ++
  ".Lccmgu_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmgu_ret\n" ++
  ".Lccmgu_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccmgu_ret\n" ++
  ".Lccmgu_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccmgu_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMaxGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_max_gas_used\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmgu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeMaxGasUsedFunction ++ "\n" ++
  ".Lccmgu_pdone:"

def ziskChainComputeMaxGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmgu_field:\n" ++
  "  .zero 8"

def ziskChainComputeMaxGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMaxGasUsedPrologue
  dataAsm     := ziskChainComputeMaxGasUsedDataSection
}

/-! ## header_extract_blob_gas_used -- PR-K241

    Extract `blob_gas_used` (header field 17, u64 BE) from a
    Cancun+ header RLP. The single-field counterpart to K90
    `header_extract_blob_gas_pair` (which extracts the (used,
    excess) tuple); useful when only one of the two is needed.

    Pre-Cancun headers (<18 fields) return parse-failure status.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure (pre-Cancun header)
        2 : field 17 exceeds 8 bytes BE -/
def headerExtractBlobGasUsedFunction : String :=
  "header_extract_blob_gas_used:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 17\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderExtractBlobGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_blob_gas_used\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhebgu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractBlobGasUsedFunction ++ "\n" ++
  ".Lhebgu_pdone:"

def ziskHeaderExtractBlobGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractBlobGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractBlobGasUsedPrologue
  dataAsm     := ziskHeaderExtractBlobGasUsedDataSection
}

/-! ## header_extract_excess_blob_gas -- PR-K244

    Standalone u64 extractor for `excess_blob_gas` (header field
    18, EIP-4844 Cancun+). The single-field counterpart to K90
    `header_extract_blob_gas_pair` and the second half of the
    EIP-4844 pair (alongside K241 `header_extract_blob_gas_used`).

    `excess_blob_gas` is a running counter used by the blob-fee
    adjustment formula; consensus invariant K63
    `calc_excess_blob_gas` defines how it evolves block-to-block.

    Pre-Cancun headers (<19 fields) return parse-failure status.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure (pre-Cancun header)
        2 : field 18 exceeds 8 bytes BE -/
def headerExtractExcessBlobGasFunction : String :=
  "header_extract_excess_blob_gas:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 18\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderExtractExcessBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_excess_blob_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhebg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractExcessBlobGasFunction ++ "\n" ++
  ".Lhebg_pdone:"

def ziskHeaderExtractExcessBlobGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractExcessBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractExcessBlobGasPrologue
  dataAsm     := ziskHeaderExtractExcessBlobGasDataSection
}

end EvmAsm.Codegen
