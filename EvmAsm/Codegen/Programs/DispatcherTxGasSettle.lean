/-
  EvmAsm.Codegen.Programs.DispatcherTxGasSettle

  Focused probe for `dispatcher_tx_gas_settle`, the EIP-8037 post-dispatch fold
  consumed by block-verdict gas-result code. The helper turns the dispatcher's
  live gas cells into the effective `gas_left` and refund counter used by the
  Amsterdam transaction settlement formula:

    tx_gas_used_before_refund = tx.gas - gas_left - state_gas_left

  by returning `gas_left + state_gas_left` on success, restoring
  `state_gas_used` into `state_gas_left` on errors, discarding refunds on errors,
  and burning remaining regular gas on exceptional halts.
-/

import EvmAsm.Codegen.Dispatch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## multi_tx_sequential_gas_settle_step

    Isolated per-transaction settlement substrate for the sequential path.
    The caller supplies the live regular/state-gas counters, refund counter,
    halt kind, and state-gas accounting cells; the helper stages those values
    into the existing dispatcher settlement ABI and returns the settled
    effective gas-left, refund, and success bit at the output pointer.

    This is deliberately emitted as an unwired callable.  The sequential
    verdict path still takes its existing bail edge until the later whitelist,
    log-window, and request-tail increments make the accept path complete.
-/
def multiTxSequentialGasSettleStepFunction : String :=
  "multi_tx_sequential_gas_settle_step:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6\n" ++
  "  la t0, evm_env; sd s1, 568(t0)\n" ++
  "  la t0, evm_state_gas_left; sd s2, 0(t0)\n" ++
  "  la t0, evm_refund_acc; sd s3, 0(t0)\n" ++
  "  la t0, evm_state_gas_used; sd s4, 0(t0)\n" ++
  "  la t0, evm_state_gas_spilled; sd s5, 0(t0)\n" ++
  "  li t0, 0xa0010000; sd s6, 32(t0)\n" ++
  "  jal ra, dispatcher_tx_gas_settle\n" ++
  "  sd a0, 0(s0); sd a1, 8(s0); sd a2, 16(s0)\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 64\n" ++
  "  ret"

/-- Input u64s at `INPUT_ADDR + 8`:
      +0  halt_kind
      +8  env.gas_left
      +16 evm_state_gas_left
      +24 evm_refund_acc
      +32 evm_state_gas_used
      +40 evm_state_gas_spilled

    Output u64s at `OUTPUT_ADDR`:
      +0  effective gas_left
      +8  effective refund_counter
      +16 tx success bit. -/
def ziskDispatcherTxGasSettlePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li s1, 0x40000008\n" ++
  "  ld a6, 0(s1)        # halt_kind\n" ++
  "  ld a1, 8(s1)        # env.gas_left\n" ++
  "  ld a2, 16(s1)       # state_gas_left\n" ++
  "  ld a3, 24(s1)       # refund\n" ++
  "  ld a4, 32(s1)       # state_gas_used\n" ++
  "  ld a5, 40(s1)       # state_gas_spilled\n" ++
  "  mv a0, s0\n" ++
  "  jal ra, multi_tx_sequential_gas_settle_step\n" ++
  "  j .Ldtgs_probe_done\n" ++
  multiTxSequentialGasSettleStepFunction ++ "\n" ++
  dispatcherTxGasSettleFunction ++ "\n" ++
  ".Ldtgs_probe_done:"

def ziskDispatcherTxGasSettleDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_env:\n  .zero 640\n" ++
  ".balign 8\n" ++
  "evm_state_gas_left:\n  .zero 8\n" ++
  "evm_state_gas_used:\n  .zero 8\n" ++
  "evm_state_gas_spilled:\n  .zero 8\n" ++
  "evm_refund_acc:\n  .zero 8\n"

def ziskDispatcherTxGasSettleProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskDispatcherTxGasSettlePrologue
  dataAsm     := ziskDispatcherTxGasSettleDataSection
}

end EvmAsm.Codegen
