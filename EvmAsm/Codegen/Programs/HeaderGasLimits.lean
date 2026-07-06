/-
  EvmAsm.Codegen.Programs.HeaderGasLimits

  Chain-level header gas-limit helpers split out of HeaderU64.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_compute_max_gas_limit -- PR-K262

    Find max(`gas_limit`) (header field 9) across an N-element
    header chain. Cross-fork — every header has gas_limit.
    Useful for capacity-planning / network-policy monitoring.

    Mirrors K236 chain_compute_max_gas_used (field 10). The chain-level
    basefee counterparts are K260/K261 (in Programs/ChainBasefee.lean).

    Vacuous on empty chain: max = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (max gas_limit)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (in any header)
        2 : gas_limit field > 8 bytes BE -/
def chainComputeMaxGasLimitFunction : String :=
  "chain_compute_max_gas_limit:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmgl_done\n" ++
  ".Lccmgl_loop:\n" ++
  "  beq s4, s0, .Lccmgl_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 9\n" ++
  "  la a3, ccmgl_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccmgl_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccmgl_size_fail\n" ++
  "  la t0, ccmgl_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t2, t1, .Lccmgl_no_update\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmgl_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmgl_loop\n" ++
  ".Lccmgl_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmgl_ret\n" ++
  ".Lccmgl_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccmgl_ret\n" ++
  ".Lccmgl_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccmgl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMaxGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_max_gas_limit\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmgl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeMaxGasLimitFunction ++ "\n" ++
  ".Lccmgl_pdone:"

def ziskChainComputeMaxGasLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmgl_field:\n" ++
  "  .zero 8"

def ziskChainComputeMaxGasLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMaxGasLimitPrologue
  dataAsm     := ziskChainComputeMaxGasLimitDataSection
}

/-! ## chain_compute_min_gas_limit -- PR-K263

    Find min(`gas_limit`) (header field 9) across an N-element
    header chain. Min counterpart to K262 chain_compute_max_gas_limit.

    Useful for spotting capacity bottlenecks across a chain segment.

    Vacuous on empty chain: min = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min gas_limit)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (in any header)
        2 : gas_limit field > 8 bytes BE -/
def chainComputeMinGasLimitFunction : String :=
  "chain_compute_min_gas_limit:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmingl_done\n" ++
  ".Lccmingl_loop:\n" ++
  "  beq s4, s0, .Lccmingl_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 9\n" ++
  "  la a3, ccmingl_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccmingl_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccmingl_size_fail\n" ++
  "  la t0, ccmingl_field; ld t1, 0(t0)\n" ++
  "  beqz s4, .Lccmingl_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lccmingl_no_update\n" ++
  ".Lccmingl_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmingl_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmingl_loop\n" ++
  ".Lccmingl_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmingl_ret\n" ++
  ".Lccmingl_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccmingl_ret\n" ++
  ".Lccmingl_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccmingl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMinGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_min_gas_limit\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmingl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeMinGasLimitFunction ++ "\n" ++
  ".Lccmingl_pdone:"

def ziskChainComputeMinGasLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmingl_field:\n" ++
  "  .zero 8"

def ziskChainComputeMinGasLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMinGasLimitPrologue
  dataAsm     := ziskChainComputeMinGasLimitDataSection
}

/-! ## chain_compute_total_gas_limit -- PR-K264

    Sum `gas_limit` (header field 9) across an N-element header chain.
    Vacuous on empty chain: sum = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (total gas_limit)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (in any header)
        2 : gas_limit field > 8 bytes BE -/
def chainComputeTotalGasLimitFunction : String :=
  "chain_compute_total_gas_limit:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lcctgl_done\n" ++
  ".Lcctgl_loop:\n" ++
  "  beq s4, s0, .Lcctgl_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 9\n" ++
  "  la a3, cctgl_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcctgl_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcctgl_size_fail\n" ++
  "  la t0, cctgl_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3); add t2, t2, t1; sd t2, 0(s3)\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lcctgl_loop\n" ++
  ".Lcctgl_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcctgl_ret\n" ++
  ".Lcctgl_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcctgl_ret\n" ++
  ".Lcctgl_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcctgl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeTotalGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_total_gas_limit\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcctgl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeTotalGasLimitFunction ++ "\n" ++
  ".Lcctgl_pdone:"

def ziskChainComputeTotalGasLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cctgl_field:\n" ++
  "  .zero 8"

def ziskChainComputeTotalGasLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeTotalGasLimitPrologue
  dataAsm     := ziskChainComputeTotalGasLimitDataSection
}

/-! ## chain_extract_gas_limit_first_last -- PR-K265

    Extract `(first_gas_limit, last_gas_limit)` (header field 9)
    from an N-element header chain.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (first_gas_limit)
      a4 (input)  : u64 out (last_gas_limit)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : a header's gas_limit field exceeds 8 bytes BE -/
def chainExtractGasLimitFirstLastFunction : String :=
  "chain_extract_gas_limit_first_last:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceglfl_empty\n" ++
  "  # first = headers[0].gas_limit (field 9)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 9\n" ++
  "  mv a3, s3\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lceglfl_propagate\n" ++
  "  # Advance to last header\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceglfl_skip:\n" ++
  "  beqz t3, .Lceglfl_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceglfl_skip\n" ++
  ".Lceglfl_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 9\n" ++
  "  mv a3, s4\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lceglfl_propagate\n" ++
  "  li a0, 0\n" ++
  "  j .Lceglfl_ret\n" ++
  ".Lceglfl_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lceglfl_ret\n" ++
  ".Lceglfl_propagate:\n" ++
  "  addi a0, a0, 1\n" ++
  ".Lceglfl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractGasLimitFirstLastPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_gas_limit_first_last\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceglfl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainExtractGasLimitFirstLastFunction ++ "\n" ++
  ".Lceglfl_pdone:"

def ziskChainExtractGasLimitFirstLastDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskChainExtractGasLimitFirstLastProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractGasLimitFirstLastPrologue
  dataAsm     := ziskChainExtractGasLimitFirstLastDataSection
}

/-! ## chain_extract_excess_blob_gas_first_last -- PR-K271

    Extract `(first_excess_blob_gas, last_excess_blob_gas)`
    (header field 18, Cancun+) from an N-element header chain.

    Pre-Cancun headers (<19 fields) raise parse-failure status.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (first_excess_blob_gas)
      a4 (input)  : u64 out (last_excess_blob_gas)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : excess_blob_gas field > 8 bytes BE on some header -/
def chainExtractExcessBlobGasFirstLastFunction : String :=
  "chain_extract_excess_blob_gas_first_last:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  beqz s0, .Lceebgfl_empty\n" ++
  "  # first = headers[0].excess_blob_gas (field 18)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 18\n" ++
  "  mv a3, s3\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lceebgfl_propagate\n" ++
  "  # Advance to last header\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1\n" ++
  ".Lceebgfl_skip:\n" ++
  "  beqz t3, .Lceebgfl_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lceebgfl_skip\n" ++
  ".Lceebgfl_at_last:\n" ++
  "  ld a1, 0(t2)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 18\n" ++
  "  mv a3, s4\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lceebgfl_propagate\n" ++
  "  li a0, 0\n" ++
  "  j .Lceebgfl_ret\n" ++
  ".Lceebgfl_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lceebgfl_ret\n" ++
  ".Lceebgfl_propagate:\n" ++
  "  addi a0, a0, 1\n" ++
  ".Lceebgfl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainExtractExcessBlobGasFirstLastPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_excess_blob_gas_first_last\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lceebgfl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainExtractExcessBlobGasFirstLastFunction ++ "\n" ++
  ".Lceebgfl_pdone:"

def ziskChainExtractExcessBlobGasFirstLastDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskChainExtractExcessBlobGasFirstLastProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractExcessBlobGasFirstLastPrologue
  dataAsm     := ziskChainExtractExcessBlobGasFirstLastDataSection
}

end EvmAsm.Codegen
