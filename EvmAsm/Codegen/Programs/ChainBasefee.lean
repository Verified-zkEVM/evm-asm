/-
  EvmAsm.Codegen.Programs.ChainBasefee

  Basefee (header field 15, London+) chain-level min/max
  aggregators, carved out of `Programs.Chain` per the file-size
  hard cap. Hosts:

    K260  chain_compute_max_basefee
    K261  chain_compute_min_basefee

  K249 `chain_compute_total_basefee` (sum) remains in
  `Programs.Chain` for adjacency with the other total-aggregators
  there; this module groups the order-statistic aggregators
  introduced after the basefee-total landed.

  Both compose K20 `rlp_list_nth_item` + K34 `rlp_field_to_u64_strict`
  helpers, shared with the sister aggregators in `Programs.Chain`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_compute_max_basefee -- PR-K260

    Find the maximum of `base_fee_per_gas` (header field 15,
    London+) across an N-element header chain. Useful for
    peak-fee monitoring; the max counterpart to K249
    `chain_compute_total_basefee` (sum) and mirrors K236
    `chain_compute_max_gas_used` (over field 10).

    Pre-London headers (≤15 fields) yield parse-failure status
    and the max is the partial accumulator. Vacuous on empty
    chain: max = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (max basefee)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-London header in chain)
        2 : basefee field > 8 bytes BE -/
def chainComputeMaxBasefeeFunction : String :=
  "chain_compute_max_basefee:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccmbf_done\n" ++
  ".Lccmbf_loop:\n" ++
  "  beq s4, s0, .Lccmbf_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 15\n" ++
  "  la a3, ccmbf_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccmbf_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccmbf_size_fail\n" ++
  "  la t0, ccmbf_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t2, t1, .Lccmbf_no_update\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccmbf_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccmbf_loop\n" ++
  ".Lccmbf_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccmbf_ret\n" ++
  ".Lccmbf_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccmbf_ret\n" ++
  ".Lccmbf_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccmbf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMaxBasefeePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_max_basefee\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccmbf_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMaxBasefeeFunction ++ "\n" ++
  ".Lccmbf_pdone:"

def ziskChainComputeMaxBasefeeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccmbf_field:\n" ++
  "  .zero 8"

def ziskChainComputeMaxBasefeeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMaxBasefeePrologue
  dataAsm     := ziskChainComputeMaxBasefeeDataSection
}

/-! ## chain_compute_min_basefee -- PR-K261

    Find min(`base_fee_per_gas`) (header field 15, London+)
    across an N-element header chain. The min counterpart to
    K260 chain_compute_max_basefee and K249
    chain_compute_total_basefee (sum); mirrors K238
    chain_compute_min_gas_used (over field 10).

    Pre-London headers (≤15 fields) yield parse-failure status
    and the min is the partial accumulator. Vacuous on empty
    chain: min = 0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (min basefee)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse fail (pre-London header in chain)
        2 : basefee field > 8 bytes BE -/
def chainComputeMinBasefeeFunction : String :=
  "chain_compute_min_basefee:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lccminbf_done\n" ++
  ".Lccminbf_loop:\n" ++
  "  beq s4, s0, .Lccminbf_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2; li a2, 15\n" ++
  "  la a3, ccminbf_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccminbf_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccminbf_size_fail\n" ++
  "  la t0, ccminbf_field; ld t1, 0(t0)\n" ++
  "  beqz s4, .Lccminbf_first\n" ++
  "  ld t2, 0(s3)\n" ++
  "  bgeu t1, t2, .Lccminbf_no_update\n" ++
  ".Lccminbf_first:\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lccminbf_no_update:\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccminbf_loop\n" ++
  ".Lccminbf_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccminbf_ret\n" ++
  ".Lccminbf_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccminbf_ret\n" ++
  ".Lccminbf_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccminbf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainComputeMinBasefeePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, chain_compute_min_basefee\n" ++
  "  li t0, 0xa0010008\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccminbf_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainComputeMinBasefeeFunction ++ "\n" ++
  ".Lccminbf_pdone:"

def ziskChainComputeMinBasefeeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccminbf_field:\n" ++
  "  .zero 8"

def ziskChainComputeMinBasefeeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeMinBasefeePrologue
  dataAsm     := ziskChainComputeMinBasefeeDataSection
}

end EvmAsm.Codegen
