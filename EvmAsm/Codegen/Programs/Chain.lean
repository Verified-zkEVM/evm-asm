/-
  EvmAsm.Codegen.Programs.Chain

  Chain-level header aggregators and validators carved out of
  `EvmAsm.Codegen.Programs.Header` per the file-size hard cap.
  Hosts:

    K196  chain_compute_total_gas_used
    K197  chain_extract_number_range
    K198  header_extract_basefee
    K199  chain_extract_basefee_range
    K200  chain_block_hashes_commitment
    K229  chain_validate_increasing_timestamps
    K230  chain_validate_consecutive_numbers
    K231  chain_compute_total_blob_gas

  All eight operate on an N-element header chain (or a single
  header in K198's case, kept here for adjacency with K199).
  They compose K20 / K34 RLP helpers plus K172
  `block_hash_from_header` (for K200), which remain in
  `Programs/Header.lean`. `Chain.lean` imports `Header.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_compute_total_blob_gas -- PR-K231

    Aggregate `blob_gas_used` (header field 17, EIP-4844
    Cancun+) across an N-element header chain into a single u64
    sum. Pre-Cancun headers (≤17 fields) yield a parse-failure
    status and the sum is partial.

    Useful for blob-gas market monitoring across a chain segment.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (total_blob_gas_used)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in the chain)
        2 : blob_gas_used field > 8 bytes BE -/
def chainComputeTotalBlobGasFunction : String :=
  "chain_compute_total_blob_gas:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lcctbg_done\n" ++
  ".Lcctbg_loop:\n" ++
  "  beq s4, s0, .Lcctbg_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, cctbg_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcctbg_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcctbg_size_fail\n" ++
  "  la t0, cctbg_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3); add t2, t2, t1; sd t2, 0(s3)\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lcctbg_loop\n" ++
  ".Lcctbg_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcctbg_ret\n" ++
  ".Lcctbg_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcctbg_ret\n" ++
  ".Lcctbg_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcctbg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeTotalBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_total_blob_gas\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcctbg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeTotalBlobGasFunction ++ "\n" ++
  ".Lcctbg_pdone:"

def ziskChainComputeTotalBlobGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cctbg_field:\n" ++
  "  .zero 8"

def ziskChainComputeTotalBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeTotalBlobGasPrologue
  dataAsm     := ziskChainComputeTotalBlobGasDataSection
}

/-! ## chain_compute_max_blob_gas_used -- PR-K237

    Find max(header.blob_gas_used) (field 17, EIP-4844 Cancun+)
    across an N-element header chain. Peak blob-congestion
    monitor, complementing K231 chain_compute_total_blob_gas.

    Pre-Cancun headers (≤17 fields) yield parse-failure status;
    the max is the partial accumulator up to the failure point.
    Vacuous on empty chain: max = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (max blob_gas_used)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : blob_gas_used field > 8 bytes BE -/
def chainComputeMaxBlobGasUsedFunction : String :=
  "chain_compute_max_blob_gas_used:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmbgu_done\n" ++
  ".Lccmbgu_loop:\n" ++
  "  beq s4, s0, .Lccmbgu_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, ccmbgu_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccmbgu_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccmbgu_size_fail\n" ++
  "  la t0, ccmbgu_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t2, t1, .Lccmbgu_no_update\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmbgu_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmbgu_loop\n" ++
  ".Lccmbgu_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmbgu_ret\n" ++
  ".Lccmbgu_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccmbgu_ret\n" ++
  ".Lccmbgu_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccmbgu_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMaxBlobGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_max_blob_gas_used\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmbgu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMaxBlobGasUsedFunction ++ "\n" ++
  ".Lccmbgu_pdone:"

def ziskChainComputeMaxBlobGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmbgu_field:\n" ++
  "  .zero 8"

def ziskChainComputeMaxBlobGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMaxBlobGasUsedPrologue
  dataAsm     := ziskChainComputeMaxBlobGasUsedDataSection
}

/-! ## chain_compute_min_gas_used -- PR-K238

    Find min(header.gas_used) (field 10) across an N-element
    header chain. Lowest-throughput / liveness monitor that
    complements K236 chain_compute_max_gas_used (max) and K196
    chain_compute_total_gas_used (sum).

    Vacuous on empty chain: min = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (in any header)
        2 : gas_used field > 8 bytes BE -/
def chainComputeMinGasUsedFunction : String :=
  "chain_compute_min_gas_used:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccming_done\n" ++
  ".Lccming_loop:\n" ++
  "  beq s4, s0, .Lccming_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 10\n" ++
  "  la a3, ccming_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccming_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccming_size_fail\n" ++
  "  la t0, ccming_field; ld t1, 0(t0)\n" ++
  "  beqz s4, .Lccming_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lccming_no_update\n" ++
  ".Lccming_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccming_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccming_loop\n" ++
  ".Lccming_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccming_ret\n" ++
  ".Lccming_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccming_ret\n" ++
  ".Lccming_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccming_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMinGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_min_gas_used\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccming_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMinGasUsedFunction ++ "\n" ++
  ".Lccming_pdone:"

def ziskChainComputeMinGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccming_field:\n" ++
  "  .zero 8"

def ziskChainComputeMinGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMinGasUsedPrologue
  dataAsm     := ziskChainComputeMinGasUsedDataSection
}

/-! ## chain_extract_timestamp_range -- PR-K239

    Extract `(first_timestamp, last_timestamp)` from an N-element
    header chain. With K229 increasing-timestamps validated, the
    pair is monotonically non-decreasing; callers can use the
    range as a chain-segment duration or epoch identifier. The
    timestamp counterpart to K197 chain_extract_number_range.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (first_timestamp)
      a4 (input)  : u64 out (last_timestamp)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : a header's timestamp field exceeds 8 bytes BE -/
def chainExtractTimestampRange_prog : Program :=
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
    .BEQ .x8 .x0 (brOff 2147483792 2147483696),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x12 (11 : Word),
    .MV .x13 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483716),
    .BNE .x10 .x0 (brOff 2147483800 2147483720),
    .MV .x6 .x18,
    .MV .x7 .x9,
    .ADDI .x28 .x8 (-1 : BitVec 12),
    .BEQ .x28 .x0 (24 : BitVec 13),
    .LD .x29 .x7 (0 : BitVec 12),
    .ADD .x6 .x6 .x29,
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LD .x11 .x7 (0 : BitVec 12),
    .MV .x10 .x6,
    .LI .x12 (11 : Word),
    .MV .x13 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict 2147483776),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainExtractTimestampRange_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractTimestampRange_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_field_to_u64_strict"),
    (32, .jal .x1 "rlp_field_to_u64_strict") ]

def chainExtractTimestampRangeFunction : String :=
  "chain_extract_timestamp_range:\n" ++ emitProgramR chainExtractTimestampRange_prog chainExtractTimestampRange_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractTimestampRange_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractTimestampRangeFunction_eq_prog :
    chainExtractTimestampRangeFunction = "chain_extract_timestamp_range:\n" ++ emitProgramR chainExtractTimestampRange_prog chainExtractTimestampRange_relocs := rfl

#guard chainExtractTimestampRangeFunction.startsWith "chain_extract_timestamp_range:\n"
#guard chainExtractTimestampRange_prog.length = 47
def ziskChainExtractTimestampRangePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_timestamp_range\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcetr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainExtractTimestampRangeFunction ++ "\n" ++
  ".Lcetr_pdone:"

def ziskChainExtractTimestampRangeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskChainExtractTimestampRangeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractTimestampRangePrologue
  dataAsm     := ziskChainExtractTimestampRangeDataSection
}

/-! ## chain_compute_min_blob_gas_used -- PR-K243

    Find min(header.blob_gas_used) (EIP-4844 Cancun+ field 17)
    across an N-element header chain. The min counterpart to
    K237 chain_compute_max_blob_gas_used; useful for spotting
    quiet blocks.

    Pre-Cancun headers (≤17 fields) yield parse-failure status;
    the min is the partial accumulator up to the failure point.
    Vacuous on empty chain: min = 0. First header initialises
    the accumulator; subsequent headers update only when smaller.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min blob_gas_used)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : blob_gas_used field > 8 bytes BE -/
def chainComputeMinBlobGasUsedFunction : String :=
  "chain_compute_min_blob_gas_used:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccminbg_done\n" ++
  ".Lccminbg_loop:\n" ++
  "  beq s4, s0, .Lccminbg_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, ccminbg_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccminbg_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccminbg_size_fail\n" ++
  "  la t0, ccminbg_field; ld t1, 0(t0)\n" ++
  "  beqz s4, .Lccminbg_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lccminbg_no_update\n" ++
  ".Lccminbg_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccminbg_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccminbg_loop\n" ++
  ".Lccminbg_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccminbg_ret\n" ++
  ".Lccminbg_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccminbg_ret\n" ++
  ".Lccminbg_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccminbg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMinBlobGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_min_blob_gas_used\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccminbg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMinBlobGasUsedFunction ++ "\n" ++
  ".Lccminbg_pdone:"

def ziskChainComputeMinBlobGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccminbg_field:\n" ++
  "  .zero 8"

def ziskChainComputeMinBlobGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMinBlobGasUsedPrologue
  dataAsm     := ziskChainComputeMinBlobGasUsedDataSection
}

/-! ## chain_extract_gas_used_range -- PR-K245

    Compute `(min_gas_used, max_gas_used)` over an N-element
    header chain in a single pass. Equivalent to running K238
    chain_compute_min_gas_used and K236 chain_compute_max_gas_used
    separately, but reads each header's RLP only once. Useful
    for throughput-variance dashboards.

    Vacuous on empty chain: min=max=0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min)
      a4 (input)  : u64 out (max)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail
        2 : gas_used field > 8 bytes BE -/
def chainExtractGasUsedRangeFunction : String :=
  "chain_extract_gas_used_range:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  sd zero, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  "  beqz s0, .Lcegur_done\n" ++
  ".Lcegur_loop:\n" ++
  "  beq s5, s0, .Lcegur_done\n" ++
  "  slli t0, s5, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 10\n" ++
  "  la a3, cegur_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcegur_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcegur_size_fail\n" ++
  "  la t0, cegur_field; ld t1, 0(t0)\n" ++
  "  beqz s5, .Lcegur_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lcegur_max\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lcegur_max:\n" ++
  "  ld t2, 0(s4)\n" ++
  "  bgeu t2, t1, .Lcegur_advance\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcegur_advance\n" ++
  ".Lcegur_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  "  sd t1, 0(s4)\n" ++
  ".Lcegur_advance:\n" ++
  "  slli t0, s5, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcegur_loop\n" ++
  ".Lcegur_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcegur_ret\n" ++
  ".Lcegur_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcegur_ret\n" ++
  ".Lcegur_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcegur_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainExtractGasUsedRangePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_gas_used_range\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcegur_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainExtractGasUsedRangeFunction ++ "\n" ++
  ".Lcegur_pdone:"

def ziskChainExtractGasUsedRangeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cegur_field:\n" ++
  "  .zero 8"

def ziskChainExtractGasUsedRangeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractGasUsedRangePrologue
  dataAsm     := ziskChainExtractGasUsedRangeDataSection
}

/-! ## chain_extract_blob_gas_used_range -- PR-K246

    Compute `(min_blob_gas_used, max_blob_gas_used)` over an
    N-element header chain in a single pass. EIP-4844 Cancun+
    sister of K245 `chain_extract_gas_used_range`; equivalent to
    running K237/K243 separately, but reads each header's RLP
    only once.

    Pre-Cancun headers (≤17 fields) yield parse-failure status
    and the (min, max) pair is the partial accumulator up to the
    failure point.

    Vacuous on empty chain: min=max=0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min blob_gas_used)
      a4 (input)  : u64 out (max blob_gas_used)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : blob_gas_used field > 8 bytes BE -/
def chainExtractBlobGasUsedRangeFunction : String :=
  "chain_extract_blob_gas_used_range:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  sd zero, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  "  beqz s0, .Lcebgur_done\n" ++
  ".Lcebgur_loop:\n" ++
  "  beq s5, s0, .Lcebgur_done\n" ++
  "  slli t0, s5, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, cebgur_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcebgur_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcebgur_size_fail\n" ++
  "  la t0, cebgur_field; ld t1, 0(t0)\n" ++
  "  beqz s5, .Lcebgur_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lcebgur_max\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lcebgur_max:\n" ++
  "  ld t2, 0(s4)\n" ++
  "  bgeu t2, t1, .Lcebgur_advance\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcebgur_advance\n" ++
  ".Lcebgur_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  "  sd t1, 0(s4)\n" ++
  ".Lcebgur_advance:\n" ++
  "  slli t0, s5, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcebgur_loop\n" ++
  ".Lcebgur_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcebgur_ret\n" ++
  ".Lcebgur_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcebgur_ret\n" ++
  ".Lcebgur_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcebgur_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainExtractBlobGasUsedRangePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_blob_gas_used_range\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcebgur_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainExtractBlobGasUsedRangeFunction ++ "\n" ++
  ".Lcebgur_pdone:"

def ziskChainExtractBlobGasUsedRangeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cebgur_field:\n" ++
  "  .zero 8"

def ziskChainExtractBlobGasUsedRangeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractBlobGasUsedRangePrologue
  dataAsm     := ziskChainExtractBlobGasUsedRangeDataSection
}

/-! ## chain_extract_basefee_first_last -- PR-K247

    Extract `(first_basefee, last_basefee)` from an N-element
    header chain. Basefee counterpart to K197
    `chain_extract_number_range` and K239
    `chain_extract_timestamp_range`. Useful for measuring
    basefee drift across a chain segment (e.g., EIP-1559
    market-pressure analytics).

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (first_basefee)
      a4 (input)  : u64 out (last_basefee)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : a header's basefee field exceeds 8 bytes BE -/
def chainExtractBasefeeFirstLast_prog : Program :=
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
    .BEQ .x8 .x0 (brOff 2147483792 2147483696),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x12 (15 : Word),
    .MV .x13 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64 2147483716),
    .BNE .x10 .x0 (brOff 2147483800 2147483720),
    .MV .x6 .x18,
    .MV .x7 .x9,
    .ADDI .x28 .x8 (-1 : BitVec 12),
    .BEQ .x28 .x0 (24 : BitVec 13),
    .LD .x29 .x7 (0 : BitVec 12),
    .ADD .x6 .x6 .x29,
    .ADDI .x7 .x7 (8 : BitVec 12),
    .ADDI .x28 .x28 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LD .x11 .x7 (0 : BitVec 12),
    .MV .x10 .x6,
    .LI .x12 (15 : Word),
    .MV .x13 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64 2147483776),
    .BNE .x10 .x0 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainExtractBasefeeFirstLast_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainExtractBasefeeFirstLast_relocs : RelocTable :=
  [ (17, .jal .x1 "rlp_field_to_u64"),
    (32, .jal .x1 "rlp_field_to_u64") ]

def chainExtractBasefeeFirstLastFunction : String :=
  "chain_extract_basefee_first_last:\n" ++ emitProgramR chainExtractBasefeeFirstLast_prog chainExtractBasefeeFirstLast_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainExtractBasefeeFirstLast_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainExtractBasefeeFirstLastFunction_eq_prog :
    chainExtractBasefeeFirstLastFunction = "chain_extract_basefee_first_last:\n" ++ emitProgramR chainExtractBasefeeFirstLast_prog chainExtractBasefeeFirstLast_relocs := rfl

#guard chainExtractBasefeeFirstLastFunction.startsWith "chain_extract_basefee_first_last:\n"
#guard chainExtractBasefeeFirstLast_prog.length = 47
def ziskChainExtractBasefeeFirstLastPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_basefee_first_last\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcebfl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainExtractBasefeeFirstLastFunction ++ "\n" ++
  ".Lcebfl_pdone:"

def ziskChainExtractBasefeeFirstLastDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskChainExtractBasefeeFirstLastProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractBasefeeFirstLastPrologue
  dataAsm     := ziskChainExtractBasefeeFirstLastDataSection
}

/-! ## chain_compute_total_blob_count -- PR-K248

    Sum `blob_gas_used / GAS_PER_BLOB` across an N-element header
    chain — i.e., the total number of blobs in the chain segment.
    EIP-4844 fixes `GAS_PER_BLOB = 131072 = 2^17`, so the per-header
    division is a logical right shift by 17.

    Pre-Cancun headers (≤17 fields) yield parse-failure status and
    the count is the partial accumulator. Vacuous on empty chain:
    count=0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (total blob count)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : blob_gas_used field > 8 bytes BE -/
def chainComputeTotalBlobCountFunction : String :=
  "chain_compute_total_blob_count:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lcctbc_done\n" ++
  ".Lcctbc_loop:\n" ++
  "  beq s4, s0, .Lcctbc_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, cctbc_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcctbc_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcctbc_size_fail\n" ++
  "  la t0, cctbc_field; ld t1, 0(t0)\n" ++
  "  srli t1, t1, 17                # / GAS_PER_BLOB = 2^17\n" ++
  "  ld t2, 0(s3); add t2, t2, t1; sd t2, 0(s3)\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lcctbc_loop\n" ++
  ".Lcctbc_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcctbc_ret\n" ++
  ".Lcctbc_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcctbc_ret\n" ++
  ".Lcctbc_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcctbc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeTotalBlobCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_total_blob_count\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcctbc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeTotalBlobCountFunction ++ "\n" ++
  ".Lcctbc_pdone:"

def ziskChainComputeTotalBlobCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cctbc_field:\n" ++
  "  .zero 8"

def ziskChainComputeTotalBlobCountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeTotalBlobCountPrologue
  dataAsm     := ziskChainComputeTotalBlobCountDataSection
}

/-! ## chain_compute_total_basefee -- PR-K249

    Sum `base_fee_per_gas` (header field 15, London+) across an
    N-element header chain. Useful for time-averaged fee
    analytics; mirror of K196 chain_compute_total_gas_used and
    K231 chain_compute_total_blob_gas.

    Pre-London headers (≤15 fields) yield parse-failure status
    and the sum is the partial accumulator. Vacuous on empty
    chain: sum = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (total basefee)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-London header in chain)
        2 : basefee field > 8 bytes BE -/
def chainComputeTotalBasefeeFunction : String :=
  "chain_compute_total_basefee:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lcctbf_done\n" ++
  ".Lcctbf_loop:\n" ++
  "  beq s4, s0, .Lcctbf_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 15\n" ++
  "  la a3, cctbf_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcctbf_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcctbf_size_fail\n" ++
  "  la t0, cctbf_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3); add t2, t2, t1; sd t2, 0(s3)\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lcctbf_loop\n" ++
  ".Lcctbf_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcctbf_ret\n" ++
  ".Lcctbf_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcctbf_ret\n" ++
  ".Lcctbf_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcctbf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeTotalBasefeePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_total_basefee\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcctbf_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeTotalBasefeeFunction ++ "\n" ++
  ".Lcctbf_pdone:"

def ziskChainComputeTotalBasefeeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cctbf_field:\n" ++
  "  .zero 8"

def ziskChainComputeTotalBasefeeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeTotalBasefeePrologue
  dataAsm     := ziskChainComputeTotalBasefeeDataSection
}

/-! ## chain_compute_max_extra_data_length -- PR-K292

    Compute the maximum `len(extra_data)` (field 12) across an
    N-element header chain. Useful for spotting headers that
    pack extra metadata, or as a corollary statistic to K291
    `chain_validate_extra_data_length` (which checks the 32-byte
    cap).

    Pre-Homestead bound is 32 bytes; some testnets / private
    chains allow longer. This primitive does not enforce the
    cap.

    Vacuous on empty chain: max = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (max extra_data length, in bytes)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail in some header -/
def chainComputeMaxExtraDataLengthFunction : String :=
  "chain_compute_max_extra_data_length:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmedl_done\n" ++
  ".Lccmedl_loop:\n" ++
  "  beq s4, s0, .Lccmedl_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 12\n" ++
  "  la a3, ccmedl_offset; la a4, ccmedl_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lccmedl_parse_fail\n" ++
  "  la t0, ccmedl_length; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t2, t1, .Lccmedl_no_update\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmedl_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmedl_loop\n" ++
  ".Lccmedl_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmedl_ret\n" ++
  ".Lccmedl_parse_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lccmedl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMaxExtraDataLengthPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_max_extra_data_length\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmedl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  chainComputeMaxExtraDataLengthFunction ++ "\n" ++
  ".Lccmedl_pdone:"

def ziskChainComputeMaxExtraDataLengthDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "ccmedl_offset:\n" ++
  "  .zero 8\n" ++
  "ccmedl_length:\n" ++
  "  .zero 8"

def ziskChainComputeMaxExtraDataLengthProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMaxExtraDataLengthPrologue
  dataAsm     := ziskChainComputeMaxExtraDataLengthDataSection
}

end EvmAsm.Codegen
