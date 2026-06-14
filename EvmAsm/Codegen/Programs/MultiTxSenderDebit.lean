/-
  EvmAsm.Codegen.Programs.MultiTxSenderDebit

  Focused helper for the bmvmx.5.5.2.2 B2 cumulative-balance chain.
  It derives the actual sender debit for one multi-tx context row from the
  dispatcher-settled runtime gas tuple, without using max upfront cost.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## multi_tx_actual_sender_debit

    Calling convention:
      a0 = multi_tx_nth_context record ptr
           +40 gas_limit u64
           +96 value u256 BE
      a1 = settled gas_left u64
           This is the value returned by `dispatch_tx_runtime_code` after
           `dispatcher_tx_gas_settle`, so EIP-8037 state-gas reservoir effects
           have already been folded into the gas-left value consumed here.
      a2 = settled refund_counter u64
      a3 = calldata_floor_gas_cost u64
      a4 = effective_gas_price ptr, u256 BE
      a5 = output ptr

    Output layout:
      +0  status from `tx_gas_result_increments`
      +8  receipt gas increment
      +16 actual sender debit, u256 BE

    Effect:
      debit = receipt_inc * effective_gas_price + tx.value

    This is the per-row arithmetic substrate for the later running per-sender
    balance table. It deliberately models actual post-exec cost, not upfront
    `gas_limit * max_fee_per_gas`.
-/
def multiTxActualSenderDebitFunction : String :=
  "multi_tx_actual_sender_debit:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                    # ctx\n" ++
  "  mv s1, a4                    # effective_gas_price ptr\n" ++
  "  mv s2, a5                    # output ptr\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2); sd zero, 16(s2); sd zero, 24(s2); sd zero, 32(s2); sd zero, 40(s2)\n" ++
  "  ld a0, 40(s0)                # tx.gas_limit\n" ++
  "  jal ra, tx_gas_result_increments\n" ++
  "  sd a0, 0(s2)                 # status\n" ++
  "  sd a2, 8(s2)                 # receipt_inc\n" ++
  "  bnez a0, .Lmtxsd_ret\n" ++
  "  mv s3, a2                    # receipt_inc\n" ++
  "  mv a0, s1; mv a1, s3; la a2, mtxsd_gascost\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  la a0, mtxsd_gascost; addi a1, s0, 96; addi a2, s2, 16\n" ++
  "  jal ra, u256_add_be\n" ++
  ".Lmtxsd_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 48\n" ++
  "  ret"

/- Probe input after zisk's 8-byte length prefix:
      +8   gas_limit u64
      +16  settled gas_left u64
      +24  refund_counter u64
      +32  calldata_floor u64
      +40  effective_gas_price u256 BE
      +72  value u256 BE

   Output is the helper's 48-byte output structure at 0xa0010000. -/
def ziskMultiTxActualSenderDebitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  la s1, mtxsd_ctx\n" ++
  "  ld t0, 8(s0); sd t0, 40(s1)      # gas_limit\n" ++
  "  addi t1, s0, 72; addi t2, s1, 96; li t3, 4\n" ++
  ".Lmtxsd_probe_value:\n" ++
  "  beqz t3, .Lmtxsd_probe_value_done\n" ++
  "  ld t4, 0(t1); sd t4, 0(t2); addi t1, t1, 8; addi t2, t2, 8; addi t3, t3, -1; j .Lmtxsd_probe_value\n" ++
  ".Lmtxsd_probe_value_done:\n" ++
  "  mv a0, s1\n" ++
  "  ld a1, 16(s0)                    # settled gas_left\n" ++
  "  ld a2, 24(s0)                    # refund_counter\n" ++
  "  ld a3, 32(s0)                    # calldata_floor\n" ++
  "  addi a4, s0, 40                  # effective_gas_price\n" ++
  "  li a5, 0xa0010000\n" ++
  "  jal ra, multi_tx_actual_sender_debit\n" ++
  "  j .Lmtxsd_probe_done\n" ++
  txGasResultIncrementsFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  multiTxActualSenderDebitFunction ++ "\n" ++
  ".Lmtxsd_probe_done:"

def ziskMultiTxActualSenderDebitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mtxsd_ctx:\n  .zero 192\n" ++
  ".balign 32\n" ++
  "mtxsd_gascost:\n  .zero 32\n" ++
  "u256m_acc:\n  .zero 40\n"

def ziskMultiTxActualSenderDebitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMultiTxActualSenderDebitPrologue
  dataAsm     := ziskMultiTxActualSenderDebitDataSection
}

end EvmAsm.Codegen
