/-
  EvmAsm.Codegen.Programs.ChainExcessBlobGas

  Excess-blob-gas (header field 18, Cancun+) chain-level
  aggregators, carved out of `Programs.Chain` per the file-size
  hard cap. Hosts:

    K272  chain_compute_max_excess_blob_gas
    K273  chain_compute_min_excess_blob_gas

  Sister `chain_extract_excess_blob_gas_first_last` (K271) lives
  in `Programs.HeaderU64` alongside `header_extract_excess_blob_gas`
  (K244). Future aggregators over field 18 land here.

  Both compose K20 `rlp_list_nth_item` + K34 `rlp_field_to_u64_strict`
  helpers, shared with the rest of the chain aggregators.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_compute_max_excess_blob_gas -- PR-K272

    Find max(`excess_blob_gas`) (header field 18, Cancun+)
    across an N-element header chain. Max counterpart to K271
    chain_extract_excess_blob_gas_first_last (which surfaces the
    endpoints); mirrors K237 chain_compute_max_blob_gas_used
    (field 17) and K260 chain_compute_max_basefee (field 15).

    Useful for spotting peak blob-fee pressure across a chain
    segment.

    Pre-Cancun headers (<19 fields) yield parse-failure status
    and the max is the partial accumulator.

    Vacuous on empty chain: max = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (max excess_blob_gas)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : excess_blob_gas field > 8 bytes BE -/
def chainComputeMaxExcessBlobGasFunction : String :=
  "chain_compute_max_excess_blob_gas:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmebg_done\n" ++
  ".Lccmebg_loop:\n" ++
  "  beq s4, s0, .Lccmebg_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 18\n" ++
  "  la a3, ccmebg_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccmebg_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccmebg_size_fail\n" ++
  "  la t0, ccmebg_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t2, t1, .Lccmebg_no_update\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmebg_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmebg_loop\n" ++
  ".Lccmebg_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmebg_ret\n" ++
  ".Lccmebg_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccmebg_ret\n" ++
  ".Lccmebg_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccmebg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMaxExcessBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_max_excess_blob_gas\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmebg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMaxExcessBlobGasFunction ++ "\n" ++
  ".Lccmebg_pdone:"

def ziskChainComputeMaxExcessBlobGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmebg_field:\n" ++
  "  .zero 8"


/-! ## chain_compute_min_excess_blob_gas -- PR-K273

    Find min(`excess_blob_gas`) (header field 18, Cancun+) across
    an N-element header chain. Min counterpart to K272
    chain_compute_max_excess_blob_gas; mirrors K243
    chain_compute_min_blob_gas_used (field 17) and K261
    chain_compute_min_basefee (field 15).

    Useful for spotting blob-fee lulls (sustained under-target
    blob count) across a chain segment.

    Pre-Cancun headers (<19 fields) yield parse-failure status
    and the min is the partial accumulator. Vacuous on empty
    chain: min = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min excess_blob_gas)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : excess_blob_gas field > 8 bytes BE -/
def chainComputeMinExcessBlobGasFunction : String :=
  "chain_compute_min_excess_blob_gas:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccminebg_done\n" ++
  ".Lccminebg_loop:\n" ++
  "  beq s4, s0, .Lccminebg_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 18\n" ++
  "  la a3, ccminebg_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccminebg_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccminebg_size_fail\n" ++
  "  la t0, ccminebg_field; ld t1, 0(t0)\n" ++
  "  beqz s4, .Lccminebg_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lccminebg_no_update\n" ++
  ".Lccminebg_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccminebg_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccminebg_loop\n" ++
  ".Lccminebg_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccminebg_ret\n" ++
  ".Lccminebg_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccminebg_ret\n" ++
  ".Lccminebg_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccminebg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMinExcessBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_min_excess_blob_gas\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccminebg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMinExcessBlobGasFunction ++ "\n" ++
  ".Lccminebg_pdone:"

def ziskChainComputeMinExcessBlobGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccminebg_field:\n" ++
  "  .zero 8"


/-! ## chain_compute_total_excess_blob_gas -- PR-K276

    Sum `excess_blob_gas` (header field 18, Cancun+) across an
    N-element header chain. Sum counterpart to K272/K273
    (max/min excess_blob_gas); mirrors K231
    chain_compute_total_blob_gas (field 17) and K249
    chain_compute_total_basefee (field 15).

    Useful as a time-integrated blob-fee pressure metric:
    dividing by N gives the average excess_blob_gas across the
    window.

    Pre-Cancun headers (<19 fields) yield parse-failure status
    and the sum is the partial accumulator.

    Vacuous on empty chain: sum = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (total excess_blob_gas)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : excess_blob_gas field > 8 bytes BE -/
def chainComputeTotalExcessBlobGasFunction : String :=
  "chain_compute_total_excess_blob_gas:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lcctebg_done\n" ++
  ".Lcctebg_loop:\n" ++
  "  beq s4, s0, .Lcctebg_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 18\n" ++
  "  la a3, cctebg_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcctebg_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcctebg_size_fail\n" ++
  "  la t0, cctebg_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3); add t2, t2, t1; sd t2, 0(s3)\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lcctebg_loop\n" ++
  ".Lcctebg_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcctebg_ret\n" ++
  ".Lcctebg_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcctebg_ret\n" ++
  ".Lcctebg_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lcctebg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeTotalExcessBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_total_excess_blob_gas\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcctebg_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeTotalExcessBlobGasFunction ++ "\n" ++
  ".Lcctebg_pdone:"

def ziskChainComputeTotalExcessBlobGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cctebg_field:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
