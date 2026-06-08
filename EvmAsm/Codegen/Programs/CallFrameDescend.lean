/-
  EvmAsm.Codegen.Programs.CallFrameDescend

  `call_frame_enter` — the child-frame entry primitive for the CALL/CREATE
  descent (bead fhsxz.2.4.2.61.6.5). It composes the merged layout primitives
  `frame_base` (#8516) and `frame_depth_*` (#8517) into the register rebase +
  child-memory zero-init a CALL/STATICCALL descent performs once the
  depth/balance/static gate passes. The env setup, gas forwarding, calldata
  aliasing, and the dispatch re-entry / return are the remaining descent steps
  (still in NoopChildFrame, .61.6); this isolates the register/memory core so it
  is unit-verified (probe `zisk_call_descend`) BEFORE it is wired into the
  verdict-critical dispatcher path.

  Layout offsets from `CallFrameLayout` (docs/call-frame-memory-layout.md §4):
  `frameMemOff = 0`, `frameStackTopOff = 0x18200`, `frameEnvOff = 0x28400`,
  `FRAME_STRIDE = 0x29000`. Per the non-uniform layout, this helper is for
  child depth `d >= 1` (frame[0] keeps the existing `evm_memory`/stack/env).

  HARD soundness requirement (docs §1, §5): the child slot aliases the
  replay-dirtied BAL union, so the child's 64 KiB EVM memory is NOT zero — it
  must be zeroed on every descent (EVM fresh-zero-per-frame semantics; also the
  runtime relies on EVM memory reading as zero for `evm_mload` beyond MSIZE and
  the `.data` calldata-zero assumption).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.CallFrameBase
import EvmAsm.Codegen.Programs.CallFrameSwitch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `call_frame_enter(a0 = child depth d >= 1)`: rebase the per-frame registers
    onto child `frame[d]` and zero-init its EVM memory. Returns
    `a0 = child memBase` (x13 = `frame_base(d) + frameMemOff`),
    `a1 = child stack top` (x12 = `frame_base(d) + frameStackTopOff`),
    `a2 = child env base` (x20 = `frame_base(d) + frameEnvOff`).
    The caller saves the parent's pc/codebase via `frame_save_regs` before
    calling and re-points x13/x12/x20 from the returns. Clobbers t0/t1. -/
def callFrameEnterFunction : String :=
  "call_frame_enter:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  jal ra, frame_base                 # a0 = call_frame_arena + (d-1)*0x29000\n" ++
  "  mv s0, a0                          # s0 = child slot base (frameMemOff = 0)\n" ++
  -- Zero-init the child's 64 KiB EVM memory [base, base + 0x10000).
  "  mv t0, s0\n" ++
  "  li t1, 0x10000\n" ++
  ".Lcfe_zero:\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -8\n" ++
  "  bnez t1, .Lcfe_zero\n" ++
  -- Child register bases.
  "  mv a0, s0                          # x13 = base + frameMemOff (0)\n" ++
  "  li t0, 0x18200\n" ++
  "  add a1, s0, t0                     # x12 = base + frameStackTopOff\n" ++
  "  li t0, 0x28400\n" ++
  "  add a2, s0, t0                     # x20 = base + frameEnvOff\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_call_descend`: unit-probe for `call_frame_enter` over a local
    `call_frame_arena` stub. Pushes depth 0->1, pre-dirties the child slot,
    enters the frame, and checks the rebased register bases + the memory
    zero-init.
    Output:
      +0  depth after push from 0            (expect 1)
      +8  child x13 (= frame_base(1))         (expect call_frame_arena)
      +16 child x12                           (= base + 0x18200)
      +24 child x20                           (= base + 0x28400)
      +32 child mem[0] after zero-init        (expect 0, was pre-dirtied)
      +40 x12 - x13                           (expect 0x18200)
      +48 x20 - x13                           (expect 0x28400)
      +56 x13 - call_frame_arena              (expect 0 — depth 1 slot) -/
def ziskCallDescendPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  jal ra, frame_depth_push\n" ++          -- depth 0 -> 1, a0 = 1
  "  sd a0, 0(s0)\n" ++
  -- Pre-dirty the child slot's first word so the zero-init is observable.
  "  li a0, 1; jal ra, frame_base\n" ++
  "  li t0, 0x1234567; sd t0, 0(a0)\n" ++
  -- Enter the child frame at depth 1.
  "  li a0, 1; jal ra, call_frame_enter\n" ++
  "  sd a0, 8(s0)\n" ++
  "  sd a1, 16(s0)\n" ++
  "  sd a2, 24(s0)\n" ++
  "  ld t0, 0(a0); sd t0, 32(s0)\n" ++
  "  sub t1, a1, a0; sd t1, 40(s0)\n" ++
  "  sub t1, a2, a0; sd t1, 48(s0)\n" ++
  "  la t0, call_frame_arena; sub t1, a0, t0; sd t1, 56(s0)\n" ++
  "  j .Lcd_done\n" ++
  frameBaseFunction ++ "\n" ++
  frameDepthPushFunction ++ "\n" ++
  callFrameEnterFunction ++ "\n" ++
  ".Lcd_done:"

/-- Local stubs so the probe links standalone (the real `call_frame_arena`
    lives in the guest's `BlockVerdictDataSection`; `evm_call_depth` in the
    embedded helper data). The arena stub holds one frame slot. -/
def ziskCallDescendDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero " ++ toString (0x29000 : Nat) ++ "\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n"

def ziskCallDescendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCallDescendPrologue
  dataAsm     := ziskCallDescendDataSection
}

end EvmAsm.Codegen
