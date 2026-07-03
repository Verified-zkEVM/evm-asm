/-
  EvmAsm.Codegen.Programs.DispatcherExecStateGas

  nxio8 / fhsxz.2.4.2.57.11.6.5.2.1 substrate half: persist each transaction's
  EXECUTED state gas (the `evm_state_gas_used` global, EIP-8037) into a per-tx
  strided array so the verdict's EIP-7778 2D inclusion gate can use the
  EXECUTION-derived state budget instead of the (too-lenient) intrinsic-only one.

  WHY (the latent false-accept this unblocks). execution-specs fork.py computes,
  per tx:
      tx_state_gas = intrinsic.state + tx_output.state_gas_used - tx_output.state_refund
      block_output.block_state_gas_used += tx_state_gas                 (fork.py:1194-1202)
  and the per-tx inclusion check (fork.py:584-598) is
      state_gas_available = block_gas_limit - block_output.block_state_gas_used
      reject if  tx.gas - intrinsic.regular > state_gas_available.
  The guest persists only the INTRINSIC term per tx (`bvgr_tx_state_gas`,
  g8zeq.1.4.3); `block_state_gas_used` is therefore under-counted by the EXECUTED
  term `tx_output.state_gas_used`, so `state_gas_available` is OVER-stated and the
  gate is too lenient -> a residual FALSE-ACCEPT (no honest EEST fixture exercises
  it). The executed term is the dispatcher's runtime output, hence c2's
  execution-substrate lane.

  Where the executed value is live. The per-tx dispatch reset (Dispatch.lean,
  "the callable dispatcher is invoked once per tx") zeroes `evm_state_gas_used`
  at the start of each tx; the SSTORE/state-growth charges accumulate into it
  during the tx (Storage.lean). So immediately AFTER a tx's
  `dispatch_tx_runtime_code` / `dispatcher_tx_gas_settle`, the global holds THIS
  tx's `tx_output.state_gas_used` (raw, pre the spec's on-error `= 0` rule —
  `dispatcher_tx_gas_settle` folds `state_gas_left += state_gas_used` on error but
  does not zero the global). This helper persists that RAW value; the spec's
  error rule (fork.py:1122-1124), the `+ intrinsic.state` term, and the
  `- state_refund` term are composed by the verdict gate's accumulator (c1's
  lane), which already holds the per-tx success status (`bv_tx_status_arr`) and
  the intrinsic array.

  This slice provides the capture HELPER + a probe ONLY. The wiring — one
  `dispatcher_capture_exec_state_gas` call per dispatch site (with that tx's
  index), the `bvgr_tx_exec_state_gas` definition in BlockVerdictDataSection, and
  the 2D state check in `eip7778_remaining_block_gas_check` — is c1's follow-up
  (coordinated via /tmp/to_c1.txt; c1 owns the verdict gate + dispatch loop).
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## dispatcher_capture_exec_state_gas

    Persist the current executed state gas into the per-tx executed-state-gas
    array at a caller-supplied transaction index.

    Calling convention:
      a0 (input)  : transaction index i (0 <= i < bvMtxArenaTxCap, the bvgr_* array capacity)
      ra (input)  : return
      (output)    : bvgr_tx_exec_state_gas[i] := evm_state_gas_used  (raw u64)
    Clobbers t0, t1, t2 only (no saved regs, no stack frame, no loop — a
    bounded, branch-free block with the post-condition
    `mem[bvgr_tx_exec_state_gas + 8*i] = evm_state_gas_used`).

    The 8-byte stride keeps every store 8-aligned (the array is `.balign 8`),
    honouring the project's no-misaligned-access rule. -/
def dispatcherCaptureExecStateGas_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.evm_state_gas_used (GuestAddrs.dispatcher_capture_exec_state_gas + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_state_gas_used (GuestAddrs.dispatcher_capture_exec_state_gas + 0)),
    .LD .x5 .x5 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bvgr_tx_exec_state_gas (GuestAddrs.dispatcher_capture_exec_state_gas + 12)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bvgr_tx_exec_state_gas (GuestAddrs.dispatcher_capture_exec_state_gas + 12)),
    .SLLI .x7 .x10 (3 : BitVec 6),
    .ADD .x6 .x6 .x7,
    .SD .x6 .x5 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def dispatcherCaptureExecStateGasFunction : String :=
  "dispatcher_capture_exec_state_gas:\n" ++ emitProgram dispatcherCaptureExecStateGas_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `dispatcherCaptureExecStateGas_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem dispatcherCaptureExecStateGasFunction_eq_prog :
    dispatcherCaptureExecStateGasFunction = "dispatcher_capture_exec_state_gas:\n" ++ emitProgram dispatcherCaptureExecStateGas_prog := rfl

#guard dispatcherCaptureExecStateGasFunction.startsWith "dispatcher_capture_exec_state_gas:\n"
#guard dispatcherCaptureExecStateGas_prog.length = 9
/-- The per-tx executed-state-gas array definition (`bvMtxArenaTxCap` entries,
    matching `bvgr_tx_state_gas`). c1 adds this identical line next to
    `bvgr_tx_state_gas` in `BlockVerdictDataSection.lean` so the verdict program
    links it; this copy is for the standalone probe. -/
def dispatcherExecStateGasArrayDef : String :=
  "bvgr_tx_exec_state_gas:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n"

/-- `zisk_capture_exec_state_gas`: focused probe for
    `dispatcher_capture_exec_state_gas`.

    Drives three captures at distinct indices (0, 17, 1023 = last) with distinct
    `evm_state_gas_used` values, then reads the array back to assert: the value
    landed, the 8-byte stride is correct, and an untouched entry stays 0.

    Output layout at 0xa0010000:
      +0  bvgr_tx_exec_state_gas[0]    (expect 0x1111)
      +8  bvgr_tx_exec_state_gas[17]   (expect 0x2222)
      +16 bvgr_tx_exec_state_gas[1023] (expect 0x3333)
      +24 bvgr_tx_exec_state_gas[1]    (expect 0 — untouched) -/
def ziskCaptureExecStateGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, evm_state_gas_used; li t1, 0x1111; sd t1, 0(t0)\n" ++
  "  li a0, 0; jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  la t0, evm_state_gas_used; li t1, 0x2222; sd t1, 0(t0)\n" ++
  "  li a0, 17; jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  la t0, evm_state_gas_used; li t1, 0x3333; sd t1, 0(t0)\n" ++
  "  li a0, 1023; jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, bvgr_tx_exec_state_gas\n" ++
  "  ld t2, 0(t1);     sd t2, 0(t0)     # [0]    expect 0x1111\n" ++
  "  ld t2, 136(t1);   sd t2, 8(t0)     # [17]   expect 0x2222\n" ++
  "  li t3, 8184; add t3, t1, t3; ld t2, 0(t3); sd t2, 16(t0)  # [1023] expect 0x3333\n" ++
  "  ld t2, 8(t1);     sd t2, 24(t0)    # [1]    untouched, expect 0\n" ++
  "  j .Lcesg_pdone\n" ++
  dispatcherCaptureExecStateGasFunction ++ "\n" ++
  ".Lcesg_pdone:"

def ziskCaptureExecStateGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_state_gas_used:\n  .zero 8\n" ++
  dispatcherExecStateGasArrayDef ++
  ".balign 8\n" ++
  "dcesg_pad:\n  .zero 16\n"

def ziskCaptureExecStateGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCaptureExecStateGasPrologue
  dataAsm     := ziskCaptureExecStateGasDataSection
}

end EvmAsm.Codegen
