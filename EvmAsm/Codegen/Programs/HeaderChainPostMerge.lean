/-
  EvmAsm.Codegen.Programs.HeaderChainPostMerge

  Post-merge and full header-chain validators split out from
  EvmAsm.Codegen.Programs.HeaderChain.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HeaderChain

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## validate_header_post_merge_zeros -- PR-K220

    Composite post-merge predicate: verify all three EIP-3675
    "must be the zero value" invariants in one call:

      H1. ommers_hash    == EMPTY_OMMERS_HASH    (K179)
      H2. difficulty     == 0                     (K219)
      H3. nonce          == 8 zero bytes          (K218)

    Returns `is_valid = 1` iff all three hold.

    Per-check status codes let the caller distinguish *which*
    invariant broke vs a hard parse failure.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : RLP parse failure / required field missing
        2 : size mismatch on ommers_hash (!= 32) or nonce (!= 8) -/
def validateHeaderPostMergeZerosFunction : String :=
  "validate_header_post_merge_zeros:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2                            # is_valid out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # 1. ommers_hash == EMPTY_OMMERS_HASH\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, vhpmz_offset; la a4, vhpmz_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lvhpmz_parse\n" ++
  "  la t0, vhpmz_length; ld t1, 0(t0); li t2, 32\n" ++
  "  bne t1, t2, .Lvhpmz_size\n" ++
  "  la t0, vhpmz_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  la t4, vhpmz_empty_ommers\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lvhpmz_pred_false\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lvhpmz_pred_false\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lvhpmz_pred_false\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lvhpmz_pred_false\n" ++
  "  # 2. difficulty == 0  (field 7 has length 0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, vhpmz_offset; la a4, vhpmz_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lvhpmz_parse\n" ++
  "  la t0, vhpmz_length; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lvhpmz_pred_false\n" ++
  "  # 3. nonce == 8 zero bytes (field 14, len == 8, all zero)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 14\n" ++
  "  la a3, vhpmz_offset; la a4, vhpmz_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lvhpmz_parse\n" ++
  "  la t0, vhpmz_length; ld t1, 0(t0); li t2, 8\n" ++
  "  bne t1, t2, .Lvhpmz_size\n" ++
  "  la t0, vhpmz_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4, 0(t3)\n" ++
  "  bnez t4, .Lvhpmz_pred_false\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  ".Lvhpmz_pred_false:\n" ++
  "  li a0, 0\n" ++
  "  j .Lvhpmz_ret\n" ++
  ".Lvhpmz_parse:\n" ++
  "  li a0, 1\n" ++
  "  j .Lvhpmz_ret\n" ++
  ".Lvhpmz_size:\n" ++
  "  li a0, 2\n" ++
  ".Lvhpmz_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskValidateHeaderPostMergeZerosPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, validate_header_post_merge_zeros\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvhpmz_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  validateHeaderPostMergeZerosFunction ++ "\n" ++
  ".Lvhpmz_pdone:"

def ziskValidateHeaderPostMergeZerosDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "vhpmz_offset:\n" ++
  "  .zero 8\n" ++
  "vhpmz_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "vhpmz_empty_ommers:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47"

def ziskValidateHeaderPostMergeZerosProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderPostMergeZerosPrologue
  dataAsm     := ziskValidateHeaderPostMergeZerosDataSection
}

/-! ## chain_validate_post_merge_zeros -- PR-K221

    Iterate `validate_header_post_merge_zeros` (K220) over an
    N-element header chain and verify each header carries the
    three EIP-3675 zero invariants (`ommers_hash`,
    `difficulty`, `nonce`). Reports the first failing index.

    No parent-hash link is checked here -- this is a pure
    per-header iteration. Combine with K175 / K184 for full
    chain validation.

    Vacuous-true on N == 0.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr (u64[N])
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        nonzero : propagated status from K220 for the failing
                  header (1 parse / 2 size mismatch) -/
def chainValidatePostMergeZerosFunction : String :=
  "chain_validate_post_merge_zeros:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # is_valid out\n" ++
  "  mv s4, a4                   # first_bad_index out\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  sd zero, 0(s4)\n" ++
  "  beqz s0, .Lcvpmz_done\n" ++
  "  mv s5, s2                   # current header ptr\n" ++
  "  li s6, 0                    # i\n" ++
  ".Lcvpmz_loop:\n" ++
  "  beq s6, s0, .Lcvpmz_done\n" ++
  "  slli t0, s6, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s5\n" ++
  "  la a2, cvpmz_per_valid\n" ++
  "  jal ra, validate_header_post_merge_zeros\n" ++
  "  bnez a0, .Lcvpmz_status_fail\n" ++
  "  la t0, cvpmz_per_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lcvpmz_pred_false\n" ++
  "  slli t0, s6, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s5, s5, t1\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lcvpmz_loop\n" ++
  ".Lcvpmz_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s6, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvpmz_ret\n" ++
  ".Lcvpmz_status_fail:\n" ++
  "  sd s6, 0(s4)\n" ++
  "  j .Lcvpmz_ret\n" ++
  ".Lcvpmz_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvpmz_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

def ziskChainValidatePostMergeZerosPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_post_merge_zeros\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvpmz_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  validateHeaderPostMergeZerosFunction ++ "\n" ++
  chainValidatePostMergeZerosFunction ++ "\n" ++
  ".Lcvpmz_pdone:"

def ziskChainValidatePostMergeZerosDataSection : String :=
  ziskValidateHeaderPostMergeZerosDataSection ++ "\n" ++
  "cvpmz_per_valid:\n" ++
  "  .zero 8"

def ziskChainValidatePostMergeZerosProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidatePostMergeZerosPrologue
  dataAsm     := ziskChainValidatePostMergeZerosDataSection
}

/-! ## chain_validate_full -- PR-K222

    Composite chain-level validator combining:

      1. K221 `chain_validate_post_merge_zeros` -- verify each
         header in the chain has the three EIP-3675 zero
         invariants (ommers_hash, difficulty, nonce).
      2. K175 `validate_header_chain` -- verify each consecutive
         pair has matching parent_hash + number+1 + timestamp +
         gas_limit ratio.

    Returns `is_valid = 1` iff both pass. On any failure,
    `first_bad_index` reports the first failing index from
    EITHER stage. Stage 1 runs first (per-header), then stage 2
    (pairs), so a header failure shadows a chain-link failure
    at the same position.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0   : success
        nz  : propagated K220/K174 status (1=parse, 2..4=size/
              field-fail variants from the inner predicates) -/
def chainValidateFullFunction : String :=
  "chain_validate_full:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  sd zero, 0(s3); sd zero, 0(s4)\n" ++
  "  # Stage 1: per-header post-merge-zeros\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s4\n" ++
  "  jal ra, chain_validate_post_merge_zeros\n" ++
  "  bnez a0, .Lcvf_ret             # propagate hard fail\n" ++
  "  ld t0, 0(s3); beqz t0, .Lcvf_ret  # zeros stage rejected\n" ++
  "  # Stage 2: chain pair invariants\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s4\n" ++
  "  jal ra, validate_header_chain\n" ++
  ".Lcvf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainValidateFullPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_full\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvf_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  validateHeaderChainFunction ++ "\n" ++
  validateHeaderPostMergeZerosFunction ++ "\n" ++
  chainValidatePostMergeZerosFunction ++ "\n" ++
  chainValidateFullFunction ++ "\n" ++
  ".Lcvf_pdone:"

def ziskChainValidateFullDataSection : String :=
  ziskChainValidatePostMergeZerosDataSection ++ "\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhc_pair_valid:\n" ++
  "  .zero 8"

def ziskChainValidateFullProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateFullPrologue
  dataAsm     := ziskChainValidateFullDataSection
}




end EvmAsm.Codegen
