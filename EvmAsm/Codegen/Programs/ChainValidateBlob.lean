/-
  EvmAsm.Codegen.Programs.ChainValidateBlob

  Blob-related chain-level validators (header fields 17/18,
  Cancun+), carved out of `Programs.ChainValidate` per the
  file-size hard cap. Hosts:

    K274  chain_validate_excess_blob_gas_non_decreasing

  Sister modules for non-blob chain validators stay in
  `Programs.ChainValidate` (timestamps / numbers / gas_used /
  gas_limit / basefee). Future Cancun+ predicates over fields 17
  / 18 / 19 land here.

  All predicates compose K20 `rlp_list_nth_item` + K34
  `rlp_field_to_u64` helpers, shared with the rest of the
  validators.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_validate_excess_blob_gas_non_decreasing -- PR-K274

    Per-pair invariant: `excess_blob_gas[i] <= excess_blob_gas[i+1]`
    for all 0 <= i < N-1 (header field 18, Cancun+). Useful for
    spotting sustained over-target blob windows where the running
    counter grows monotonically.

    Mirrors K267 chain_validate_basefee_non_decreasing in shape;
    differs by field (18 vs 15).

    Pre-Cancun headers (<19 fields) raise parse-failure status.

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : excess_blob_gas field > 8 bytes BE on some header -/
def chainValidateExcessBlobGasNonDecreasingFunction : String :=
  "chain_validate_excess_blob_gas_non_decreasing:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvebnd_done\n" ++
  "  # Extract headers[0].excess_blob_gas into s5 (prev)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 18\n" ++
  "  la a3, cvebnd_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvebnd_propagate\n" ++
  "  la t0, cvebnd_field; ld s5, 0(t0)\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0\n" ++
  "  li t2, 1\n" ++
  ".Lcvebnd_loop:\n" ++
  "  beq t2, s0, .Lcvebnd_done\n" ++
  "  la t0, cvebnd_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvebnd_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvebnd_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 18\n" ++
  "  la a3, cvebnd_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvebnd_propagate\n" ++
  "  la t0, cvebnd_field;        ld t3, 0(t0)\n" ++
  "  la t0, cvebnd_iter_prev;    ld t4, 0(t0)\n" ++
  "  bltu t3, t4, .Lcvebnd_pred_false\n" ++
  "  la t0, cvebnd_iter_child;   ld t1, 0(t0)\n" ++
  "  la t0, cvebnd_iter_i;       ld t2, 0(t0)\n" ++
  "  mv s5, t3\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvebnd_loop\n" ++
  ".Lcvebnd_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvebnd_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvebnd_ret\n" ++
  ".Lcvebnd_propagate:\n" ++
  "  la t0, cvebnd_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvebnd_ret\n" ++
  ".Lcvebnd_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvebnd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateExcessBlobGasNonDecreasingPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_excess_blob_gas_non_decreasing\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvebnd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateExcessBlobGasNonDecreasingFunction ++ "\n" ++
  ".Lcvebnd_pdone:"

def ziskChainValidateExcessBlobGasNonDecreasingDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvebnd_field:\n" ++
  "  .zero 8\n" ++
  "cvebnd_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvebnd_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvebnd_iter_prev:\n" ++
  "  .zero 8"

def ziskChainValidateExcessBlobGasNonDecreasingProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateExcessBlobGasNonDecreasingPrologue
  dataAsm     := ziskChainValidateExcessBlobGasNonDecreasingDataSection
}

/-! ## chain_validate_excess_blob_gas_non_increasing -- PR-K275

    Per-pair invariant: `excess_blob_gas[i] >= excess_blob_gas[i+1]`
    for all 0 <= i < N-1 (header field 18, Cancun+). Min-side
    mirror of K274 chain_validate_excess_blob_gas_non_decreasing;
    useful for sustained under-target blob windows.

    Pre-Cancun headers (<19 fields) raise parse-failure status.

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : excess_blob_gas field > 8 bytes BE on some header -/
def chainValidateExcessBlobGasNonIncreasingFunction : String :=
  "chain_validate_excess_blob_gas_non_increasing:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvebni_done\n" ++
  "  # Extract headers[0].excess_blob_gas into s5 (prev)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 18\n" ++
  "  la a3, cvebni_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvebni_propagate\n" ++
  "  la t0, cvebni_field; ld s5, 0(t0)\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0\n" ++
  "  li t2, 1\n" ++
  ".Lcvebni_loop:\n" ++
  "  beq t2, s0, .Lcvebni_done\n" ++
  "  la t0, cvebni_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvebni_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvebni_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 18\n" ++
  "  la a3, cvebni_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvebni_propagate\n" ++
  "  la t0, cvebni_field;        ld t3, 0(t0)\n" ++
  "  la t0, cvebni_iter_prev;    ld t4, 0(t0)\n" ++
  "  bltu t4, t3, .Lcvebni_pred_false\n" ++
  "  la t0, cvebni_iter_child;   ld t1, 0(t0)\n" ++
  "  la t0, cvebni_iter_i;       ld t2, 0(t0)\n" ++
  "  mv s5, t3\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvebni_loop\n" ++
  ".Lcvebni_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvebni_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvebni_ret\n" ++
  ".Lcvebni_propagate:\n" ++
  "  la t0, cvebni_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvebni_ret\n" ++
  ".Lcvebni_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvebni_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateExcessBlobGasNonIncreasingPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_excess_blob_gas_non_increasing\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvebni_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateExcessBlobGasNonIncreasingFunction ++ "\n" ++
  ".Lcvebni_pdone:"

def ziskChainValidateExcessBlobGasNonIncreasingDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvebni_field:\n" ++
  "  .zero 8\n" ++
  "cvebni_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvebni_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvebni_iter_prev:\n" ++
  "  .zero 8"

def ziskChainValidateExcessBlobGasNonIncreasingProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateExcessBlobGasNonIncreasingPrologue
  dataAsm     := ziskChainValidateExcessBlobGasNonIncreasingDataSection
}

/-! ## chain_validate_blob_gas_used_under_max -- PR-K277

    Per-header invariant: `blob_gas_used <= MAX_BLOB_GAS_PER_BLOCK`
    (field 17, Cancun+). The Amsterdam EEST frontier carries the
    blob schedule in the stateless chain config and currently uses
    `BLOB_SCHEDULE_MAX = 21`, so
    `MAX_BLOB_GAS_PER_BLOCK = 21 * GAS_PER_BLOB = 21 * 131072 = 2752512`.

    Useful as a per-block sanity check on RLP-decoded blob_gas_used
    values. A failure signals corrupted header data or a future
    fork that hasn't been wired in yet.

    Pre-Cancun headers (<18 fields) raise parse-failure status.

    Vacuous-true on N = 0.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : blob_gas_used field > 8 bytes BE on some header -/
def chainValidateBlobGasUsedUnderMaxFunction : String :=
  "chain_validate_blob_gas_used_under_max:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  ".Lcvbgum_loop:\n" ++
  "  beq s5, s0, .Lcvbgum_done\n" ++
  "  la t0, cvbgum_iter_ptr; sd s2, 0(t0)\n" ++
  "  la t0, cvbgum_iter_i;   sd s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, cvbgum_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvbgum_propagate\n" ++
  "  la t0, cvbgum_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvbgum_iter_i;   ld s5, 0(t0)\n" ++
  "  la t0, cvbgum_field;    ld t1, 0(t0)\n" ++
  "  li t2, 2752512            # Amsterdam MAX_BLOB_GAS_PER_BLOCK\n" ++
  "  bgtu t1, t2, .Lcvbgum_violation\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld t4, 0(t3)\n" ++
  "  add s2, s2, t4\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcvbgum_loop\n" ++
  ".Lcvbgum_violation:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvbgum_ret\n" ++
  ".Lcvbgum_propagate:\n" ++
  "  sd s5, 0(s4)\n" ++
  "  j .Lcvbgum_ret\n" ++
  ".Lcvbgum_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvbgum_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateBlobGasUsedUnderMaxPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_blob_gas_used_under_max\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvbgum_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateBlobGasUsedUnderMaxFunction ++ "\n" ++
  ".Lcvbgum_pdone:"

def ziskChainValidateBlobGasUsedUnderMaxDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvbgum_field:\n" ++
  "  .zero 8\n" ++
  "cvbgum_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvbgum_iter_i:\n" ++
  "  .zero 8"

def ziskChainValidateBlobGasUsedUnderMaxProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateBlobGasUsedUnderMaxPrologue
  dataAsm     := ziskChainValidateBlobGasUsedUnderMaxDataSection
}

/-! ## chain_validate_blob_gas_used_multiple -- PR-K278

    Per-header invariant: `blob_gas_used % GAS_PER_BLOB == 0`
    (header field 17, Cancun+). EIP-4844 defines blob_gas_used
    as `len(blob_versioned_hashes) * GAS_PER_BLOB`, so any valid
    Cancun+ header must have `blob_gas_used` as a non-negative
    multiple of `GAS_PER_BLOB = 131072 = 2^17`.

    Checked via the low-17-bits mask (`blob_gas_used & 0x1ffff
    == 0`).

    Pre-Cancun headers (<18 fields) raise parse-failure status.

    Vacuous-true on N = 0.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : blob_gas_used field > 8 bytes BE on some header -/
def chainValidateBlobGasUsedMultipleFunction : String :=
  "chain_validate_blob_gas_used_multiple:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  ".Lcvbgm_loop:\n" ++
  "  beq s5, s0, .Lcvbgm_done\n" ++
  "  la t0, cvbgm_iter_ptr; sd s2, 0(t0)\n" ++
  "  la t0, cvbgm_iter_i;   sd s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, cvbgm_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvbgm_propagate\n" ++
  "  la t0, cvbgm_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvbgm_iter_i;   ld s5, 0(t0)\n" ++
  "  la t0, cvbgm_field;    ld t1, 0(t0)\n" ++
  "  li t2, 0x1ffff            # GAS_PER_BLOB - 1 = 131071\n" ++
  "  and t5, t1, t2\n" ++
  "  bnez t5, .Lcvbgm_violation\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld t4, 0(t3)\n" ++
  "  add s2, s2, t4\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcvbgm_loop\n" ++
  ".Lcvbgm_violation:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvbgm_ret\n" ++
  ".Lcvbgm_propagate:\n" ++
  "  sd s5, 0(s4)\n" ++
  "  j .Lcvbgm_ret\n" ++
  ".Lcvbgm_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvbgm_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateBlobGasUsedMultiplePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_blob_gas_used_multiple\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvbgm_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateBlobGasUsedMultipleFunction ++ "\n" ++
  ".Lcvbgm_pdone:"

def ziskChainValidateBlobGasUsedMultipleDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvbgm_field:\n" ++
  "  .zero 8\n" ++
  "cvbgm_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvbgm_iter_i:\n" ++
  "  .zero 8"

def ziskChainValidateBlobGasUsedMultipleProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateBlobGasUsedMultiplePrologue
  dataAsm     := ziskChainValidateBlobGasUsedMultipleDataSection
}

end EvmAsm.Codegen
