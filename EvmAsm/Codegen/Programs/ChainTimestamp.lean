/-
  EvmAsm.Codegen.Programs.ChainTimestamp

  Timestamp-gap (header field 11) chain-level aggregators, carved
  out of `Programs.Chain` per the file-size hard cap. Hosts:

    K279  chain_compute_max_timestamp_gap

  Future timestamp aggregators (e.g. min gap, avg gap) land here.
  Sister `chain_validate_increasing_timestamps` (K229) stays in
  `Programs.ChainValidate` and `chain_extract_timestamp_range`
  (K239) stays in `Programs.Chain` for adjacency with the other
  range extractors.

  All predicates compose K20 `rlp_list_nth_item` + K34
  `rlp_field_to_u64_strict` helpers, shared with the rest of the chain
  aggregators.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_compute_max_timestamp_gap -- PR-K279

    Compute the maximum `(timestamp[i+1] - timestamp[i])` across
    consecutive headers in an N-element chain (header field 11).
    Useful network-uptime / longest-block-gap metric.

    The subtraction is unsigned. If the chain is not
    monotonically non-decreasing in timestamp (i.e., a violation
    of K229 chain_validate_increasing_timestamps), the function
    aborts with status = 3 and the bad index in a4. Callers that
    have already validated K229 can ignore that error.

    Vacuous on N <= 1: max_gap = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (max gap)
      a4 (input)  : u64 out (bad_index on status==3, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail
        2 : timestamp field > 8 bytes BE
        3 : timestamps not monotonically non-decreasing -/
def chainComputeMaxTimestampGapFunction : String :=
  "chain_compute_max_timestamp_gap:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  sd zero, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lccmtg_done\n" ++
  "  # Extract headers[0].timestamp into s5 (prev_ts)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 11\n" ++
  "  la a3, ccmtg_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lccmtg_propagate\n" ++
  "  la t0, ccmtg_field; ld s5, 0(t0)\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0\n" ++
  "  li t2, 1\n" ++
  ".Lccmtg_loop:\n" ++
  "  beq t2, s0, .Lccmtg_done\n" ++
  "  la t0, ccmtg_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, ccmtg_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, ccmtg_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 11\n" ++
  "  la a3, ccmtg_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lccmtg_propagate\n" ++
  "  la t0, ccmtg_field;       ld t3, 0(t0)\n" ++
  "  la t0, ccmtg_iter_prev;   ld t4, 0(t0)\n" ++
  "  bltu t3, t4, .Lccmtg_monotonic_fail\n" ++
  "  sub t5, t3, t4              # gap = current - prev\n" ++
  "  la t0, ccmtg_iter_child;  ld t1, 0(t0)\n" ++
  "  la t0, ccmtg_iter_i;      ld t2, 0(t0)\n" ++
  "  ld t6, 0(s3)\n" ++
  "  bgeu t6, t5, .Lccmtg_no_update\n" ++
  "  sd t5, 0(s3)\n" ++
  ".Lccmtg_no_update:\n" ++
  "  mv s5, t3\n" ++
  "  slli t6, t2, 3\n" ++
  "  add t6, s1, t6\n" ++
  "  ld t0, 0(t6)\n" ++
  "  add t1, t1, t0\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lccmtg_loop\n" ++
  ".Lccmtg_monotonic_fail:\n" ++
  "  la t0, ccmtg_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 3\n" ++
  "  j .Lccmtg_ret\n" ++
  ".Lccmtg_propagate:\n" ++
  "  la t0, ccmtg_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lccmtg_ret\n" ++
  ".Lccmtg_done:\n" ++
  "  li a0, 0\n" ++
  ".Lccmtg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainComputeMaxTimestampGapPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_compute_max_timestamp_gap\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmtg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMaxTimestampGapFunction ++ "\n" ++
  ".Lccmtg_pdone:"

def ziskChainComputeMaxTimestampGapDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmtg_field:\n" ++
  "  .zero 8\n" ++
  "ccmtg_iter_child:\n" ++
  "  .zero 8\n" ++
  "ccmtg_iter_i:\n" ++
  "  .zero 8\n" ++
  "ccmtg_iter_prev:\n" ++
  "  .zero 8"


/-! ## chain_compute_min_timestamp_gap -- PR-K280

    Compute the minimum `(timestamp[i+1] - timestamp[i])` across
    consecutive headers in an N-element chain (header field 11).
    Useful network-health / shortest-block-gap metric (e.g.
    confirms a chain segment respected the per-fork minimum
    block-time).

    Min counterpart to K279 chain_compute_max_timestamp_gap.

    The subtraction is unsigned. If the chain is not
    monotonically non-decreasing in timestamp, the function
    aborts with status = 3 and the bad index in a4.

    Vacuous on N <= 1: min_gap = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min gap)
      a4 (input)  : u64 out (bad_index on status==3, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail
        2 : timestamp field > 8 bytes BE
        3 : timestamps not monotonically non-decreasing -/
def chainComputeMinTimestampGapFunction : String :=
  "chain_compute_min_timestamp_gap:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  sd zero, 0(s3); sd zero, 0(s4)\n" ++
  "  li s6, 0                # s6 = seen_any (0=no gap seen yet)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lccmintg_done\n" ++
  "  # Extract headers[0].timestamp into s5 (prev_ts)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 11\n" ++
  "  la a3, ccmintg_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lccmintg_propagate\n" ++
  "  la t0, ccmintg_field; ld s5, 0(t0)\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0\n" ++
  "  li t2, 1\n" ++
  ".Lccmintg_loop:\n" ++
  "  beq t2, s0, .Lccmintg_done\n" ++
  "  la t0, ccmintg_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, ccmintg_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, ccmintg_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 11\n" ++
  "  la a3, ccmintg_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lccmintg_propagate\n" ++
  "  la t0, ccmintg_field;       ld t3, 0(t0)\n" ++
  "  la t0, ccmintg_iter_prev;   ld t4, 0(t0)\n" ++
  "  bltu t3, t4, .Lccmintg_monotonic_fail\n" ++
  "  sub t5, t3, t4              # gap = current - prev\n" ++
  "  la t0, ccmintg_iter_child;  ld t1, 0(t0)\n" ++
  "  la t0, ccmintg_iter_i;      ld t2, 0(t0)\n" ++
  "  beqz s6, .Lccmintg_first_gap\n" ++
  "  ld t6, 0(s3)\n" ++
  "  bgeu t5, t6, .Lccmintg_no_update\n" ++
  ".Lccmintg_first_gap:\n" ++
  "  sd t5, 0(s3)\n" ++
  "  li s6, 1\n" ++
  ".Lccmintg_no_update:\n" ++
  "  mv s5, t3\n" ++
  "  slli t6, t2, 3\n" ++
  "  add t6, s1, t6\n" ++
  "  ld t0, 0(t6)\n" ++
  "  add t1, t1, t0\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lccmintg_loop\n" ++
  ".Lccmintg_monotonic_fail:\n" ++
  "  la t0, ccmintg_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 3\n" ++
  "  j .Lccmintg_ret\n" ++
  ".Lccmintg_propagate:\n" ++
  "  la t0, ccmintg_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lccmintg_ret\n" ++
  ".Lccmintg_done:\n" ++
  "  li a0, 0\n" ++
  ".Lccmintg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

def ziskChainComputeMinTimestampGapPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_compute_min_timestamp_gap\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmintg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMinTimestampGapFunction ++ "\n" ++
  ".Lccmintg_pdone:"

def ziskChainComputeMinTimestampGapDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmintg_field:\n" ++
  "  .zero 8\n" ++
  "ccmintg_iter_child:\n" ++
  "  .zero 8\n" ++
  "ccmintg_iter_i:\n" ++
  "  .zero 8\n" ++
  "ccmintg_iter_prev:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
