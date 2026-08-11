/-
  EvmAsm.Codegen.Programs.ChainBlobCount

  Blob-count (header field 17 / GAS_PER_BLOB) chain-level
  aggregators, carved out of `Programs.Chain` per the file-size
  hard cap. Hosts:

    K285  chain_compute_max_blob_count
    K286  chain_compute_min_blob_count

  Companion `chain_compute_total_blob_count` (K248) stays in
  `Programs.Chain` for adjacency with the other total-aggregators
  there. Sister `chain_compute_total_blob_gas` (K231) and
  `chain_compute_max_blob_gas_used` (K237) likewise stay in
  Programs.Chain.

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

/-! ## chain_compute_max_blob_count -- PR-K285

    Find the maximum blob count per block across an N-element
    header chain (header field 17 / GAS_PER_BLOB). EIP-4844
    invariant: blob_gas_used is a multiple of GAS_PER_BLOB =
    131072 = 2^17, so blob_count = blob_gas_used >> 17.

    Useful as a peak-blob-pressure metric: complements K237
    chain_compute_max_blob_gas_used (raw gas).

    Pre-Cancun headers (<18 fields) yield parse-failure status
    and the max is the partial accumulator. Vacuous on empty
    chain: max = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (max blob_count)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : blob_gas_used field > 8 bytes BE -/
def chainComputeMaxBlobCountFunction : String :=
  "chain_compute_max_blob_count:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmbc_done\n" ++
  ".Lccmbc_loop:\n" ++
  "  beq s4, s0, .Lccmbc_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, ccmbc_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccmbc_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccmbc_size_fail\n" ++
  "  la t0, ccmbc_field; ld t1, 0(t0)\n" ++
  "  srli t1, t1, 17            # blob_count = blob_gas_used >> 17\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t2, t1, .Lccmbc_no_update\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmbc_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmbc_loop\n" ++
  ".Lccmbc_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmbc_ret\n" ++
  ".Lccmbc_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccmbc_ret\n" ++
  ".Lccmbc_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccmbc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMaxBlobCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_max_blob_count\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmbc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMaxBlobCountFunction ++ "\n" ++
  ".Lccmbc_pdone:"

def ziskChainComputeMaxBlobCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmbc_field:\n" ++
  "  .zero 8"

def ziskChainComputeMaxBlobCountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMaxBlobCountPrologue
  dataAsm     := ziskChainComputeMaxBlobCountDataSection
}

/-! ## chain_compute_min_blob_count -- PR-K286

    Find the minimum blob count per block across an N-element
    header chain (header field 17 / GAS_PER_BLOB). Min counter-
    part to K285 chain_compute_max_blob_count; useful for
    spotting blob-fee lulls in a chain segment.

    Pre-Cancun headers (<18 fields) yield parse-failure status
    and the min is the partial accumulator. Vacuous on empty
    chain: min = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min blob_count)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-Cancun header in chain)
        2 : blob_gas_used field > 8 bytes BE -/
def chainComputeMinBlobCountFunction : String :=
  "chain_compute_min_blob_count:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccminbc_done\n" ++
  ".Lccminbc_loop:\n" ++
  "  beq s4, s0, .Lccminbc_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, ccminbc_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccminbc_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccminbc_size_fail\n" ++
  "  la t0, ccminbc_field; ld t1, 0(t0)\n" ++
  "  srli t1, t1, 17            # blob_count = blob_gas_used >> 17\n" ++
  "  beqz s4, .Lccminbc_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lccminbc_no_update\n" ++
  ".Lccminbc_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccminbc_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccminbc_loop\n" ++
  ".Lccminbc_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccminbc_ret\n" ++
  ".Lccminbc_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccminbc_ret\n" ++
  ".Lccminbc_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccminbc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMinBlobCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_min_blob_count\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccminbc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMinBlobCountFunction ++ "\n" ++
  ".Lccminbc_pdone:"

def ziskChainComputeMinBlobCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccminbc_field:\n" ++
  "  .zero 8"

def ziskChainComputeMinBlobCountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMinBlobCountPrologue
  dataAsm     := ziskChainComputeMinBlobCountDataSection
}

end EvmAsm.Codegen
