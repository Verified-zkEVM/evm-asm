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
import EvmAsm.Codegen.Programs.EvmBasic

namespace EvmAsm.Codegen

open EvmAsm.Rv64

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
  "  ld t0, 0(s1); sd t0, 32(s0)       # halt_kind for dispatcher_tx_gas_settle\n" ++
  "  la t1, evm_env; ld t0, 8(s1); sd t0, 568(t1)\n" ++
  "  la t1, evm_state_gas_left; ld t0, 16(s1); sd t0, 0(t1)\n" ++
  "  la t1, evm_refund_acc; ld t0, 24(s1); sd t0, 0(t1)\n" ++
  "  la t1, evm_state_gas_used; ld t0, 32(s1); sd t0, 0(t1)\n" ++
  "  la t1, evm_state_gas_spilled; ld t0, 40(s1); sd t0, 0(t1)\n" ++
  "  jal ra, dispatcher_tx_gas_settle\n" ++
  "  sd a0, 0(s0)\n" ++
  "  sd a1, 8(s0)\n" ++
  "  sd a2, 16(s0)\n" ++
  "  j .Ldtgs_probe_done\n" ++
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
