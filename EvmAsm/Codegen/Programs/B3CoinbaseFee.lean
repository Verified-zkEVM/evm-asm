/-
  EvmAsm.Codegen.Programs.B3CoinbaseFee

  B3.2 helper for the multi-transaction block verdict path: aggregate the
  coinbase fee credit across transactions from per-transaction priority fees
  and receipt gas increments.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## b3_coinbase_fee_credit_sum

    Calling convention:
      a0 = priority_fee_per_gas array ptr (32-byte big-endian elements)
      a1 = receipt_gas_increment array ptr (u64 elements)
      a2 = tx count
      a3 = out credit ptr (32-byte big-endian)

    Effect:
      *a3 = sum_i priority_fee_per_gas[i] * receipt_gas_increment[i].

    Returns:
      a0 = 0 on success
      a0 = 1 if one term overflows u256
      a0 = 2 if the running sum overflows u256

    The output is zeroed before accumulation, so count=0 produces zero. -/
def b3CoinbaseFeeCreditSumFunction : String :=
  "b3_coinbase_fee_credit_sum:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                    # priority fee array cursor\n" ++
  "  mv s1, a1                    # receipt increment array cursor\n" ++
  "  mv s2, a2                    # tx count\n" ++
  "  mv s3, a3                    # out credit ptr\n" ++
  "  mv t0, s3; li t1, 4          # zero output accumulator\n" ++
  ".Lb3cfs_zero_out:\n" ++
  "  beqz t1, .Lb3cfs_zero_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lb3cfs_zero_out\n" ++
  ".Lb3cfs_zero_done:\n" ++
  "  li s4, 0                     # tx index\n" ++
  ".Lb3cfs_loop:\n" ++
  "  beq s4, s2, .Lb3cfs_ok\n" ++
  "  mv a0, s0\n" ++
  "  ld a1, 0(s1)\n" ++
  "  la a2, b3cfs_term\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lb3cfs_mul_overflow\n" ++
  "  mv a0, s3\n" ++
  "  la a1, b3cfs_term\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lb3cfs_sum_overflow\n" ++
  "  addi s0, s0, 32\n" ++
  "  addi s1, s1, 8\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lb3cfs_loop\n" ++
  ".Lb3cfs_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lb3cfs_return\n" ++
  ".Lb3cfs_mul_overflow:\n" ++
  "  li a0, 1\n" ++
  "  j .Lb3cfs_return\n" ++
  ".Lb3cfs_sum_overflow:\n" ++
  "  li a0, 2\n" ++
  ".Lb3cfs_return:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); addi sp, sp, 64\n" ++
  "  ret"

def b3CoinbaseFeeCreditSumData : String :=
  ".balign 32\n" ++
  "b3cfs_term:\n  .zero 32\n"

/-- `zisk_b3_coinbase_fee_credit_sum`: known-answer probe.
    Three transaction terms are 2*21000, 3*100, and 0*999, so the aggregate
    coinbase credit is 42300 (0xa53c). A second count=0 call checks that the
    helper returns success and clears the output accumulator. -/
def ziskB3CoinbaseFeeCreditSumPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, b3cfs_prios\n" ++
  "  li t1, 12\n" ++
  ".Lb3cfs_probe_zero_prios:\n" ++
  "  beqz t1, .Lb3cfs_probe_prios_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lb3cfs_probe_zero_prios\n" ++
  ".Lb3cfs_probe_prios_done:\n" ++
  "  la t0, b3cfs_prios\n" ++
  "  li t1, 2; sb t1, 31(t0)\n" ++
  "  li t1, 3; sb t1, 63(t0)\n" ++
  "  la t0, b3cfs_receipts\n" ++
  "  li t1, 21000; sd t1, 0(t0)\n" ++
  "  li t1, 100; sd t1, 8(t0)\n" ++
  "  li t1, 999; sd t1, 16(t0)\n" ++
  "  la a0, b3cfs_prios\n" ++
  "  la a1, b3cfs_receipts\n" ++
  "  li a2, 3\n" ++
  "  la a3, b3cfs_out\n" ++
  "  jal ra, b3_coinbase_fee_credit_sum\n" ++
  "  sd a0, 0(s0)\n" ++
  "  la t0, b3cfs_out\n" ++
  "  lbu t1, 31(t0); sd t1, 8(s0)\n" ++
  "  lbu t1, 30(t0); sd t1, 16(s0)\n" ++
  "  lbu t1, 0(t0); sd t1, 24(s0)\n" ++
  "  la t0, b3cfs_zero_out\n" ++
  "  li t1, -1\n" ++
  "  sd t1, 0(t0); sd t1, 8(t0); sd t1, 16(t0); sd t1, 24(t0)\n" ++
  "  la a0, b3cfs_prios\n" ++
  "  la a1, b3cfs_receipts\n" ++
  "  li a2, 0\n" ++
  "  la a3, b3cfs_zero_out\n" ++
  "  jal ra, b3_coinbase_fee_credit_sum\n" ++
  "  sd a0, 32(s0)\n" ++
  "  la t0, b3cfs_zero_out\n" ++
  "  lbu t1, 31(t0); sd t1, 40(s0)\n" ++
  "  j .Lb3cfs_done\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  b3CoinbaseFeeCreditSumFunction ++ "\n" ++
  ".Lb3cfs_done:"

def ziskB3CoinbaseFeeCreditSumDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "b3cfs_prios:\n  .zero 96\n" ++
  "b3cfs_out:\n  .zero 32\n" ++
  "b3cfs_zero_out:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "b3cfs_receipts:\n  .zero 24\n" ++
  "u256m_acc:\n  .zero 40\n" ++
  b3CoinbaseFeeCreditSumData


end EvmAsm.Codegen
