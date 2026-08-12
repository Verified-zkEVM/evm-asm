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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

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
def multiTxSequentialGasSettleStep_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .AUIPC .x5 (laHi GuestAddrs.evm_env 2147483712),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_env 2147483712),
    .SD .x5 .x9 (568 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.evm_state_gas_left 2147483724),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_state_gas_left 2147483724),
    .SD .x5 .x18 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.evm_refund_acc 2147483736),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_refund_acc 2147483736),
    .SD .x5 .x19 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.evm_state_gas_used 2147483748),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_state_gas_used 2147483748),
    .SD .x5 .x20 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.evm_state_gas_spilled 2147483760),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_state_gas_spilled 2147483760),
    .SD .x5 .x21 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.rdg_halt_kind 2147483772),
    .ADDI .x5 .x5 (laLo GuestAddrs.rdg_halt_kind 2147483772),
    .SD .x5 .x22 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.dispatcher_tx_gas_settle 2147483784),
    .SD .x8 .x10 (0 : BitVec 12),
    .SD .x8 .x11 (8 : BitVec 12),
    .SD .x8 .x12 (16 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `multiTxSequentialGasSettleStep_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def multiTxSequentialGasSettleStep_relocs : RelocTable :=
  [ (16, .la .x5 "evm_env"),
    (19, .la .x5 "evm_state_gas_left"),
    (22, .la .x5 "evm_refund_acc"),
    (25, .la .x5 "evm_state_gas_used"),
    (28, .la .x5 "evm_state_gas_spilled"),
    (31, .la .x5 "rdg_halt_kind"),
    (34, .jal .x1 "dispatcher_tx_gas_settle") ]

def multiTxSequentialGasSettleStepFunction : String :=
  "multi_tx_sequential_gas_settle_step:\n" ++ emitProgramR multiTxSequentialGasSettleStep_prog multiTxSequentialGasSettleStep_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `multiTxSequentialGasSettleStep_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem multiTxSequentialGasSettleStepFunction_eq_prog :
    multiTxSequentialGasSettleStepFunction = "multi_tx_sequential_gas_settle_step:\n" ++ emitProgramR multiTxSequentialGasSettleStep_prog multiTxSequentialGasSettleStep_relocs := rfl

#guard multiTxSequentialGasSettleStepFunction.startsWith "multi_tx_sequential_gas_settle_step:\n"
#guard multiTxSequentialGasSettleStep_prog.length = 48
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
  "evm_refund_acc:\n  .zero 8\n" ++
  "rdg_halt_kind:\n  .zero 8\n"

def ziskDispatcherTxGasSettleProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskDispatcherTxGasSettlePrologue
  dataAsm     := ziskDispatcherTxGasSettleDataSection
}

end EvmAsm.Codegen
