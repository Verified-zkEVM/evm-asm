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

/-- `call_frame_set_call_env(a0 = child env base, a1 = parent env base,
    a2 = to-word ptr, a3 = value-word ptr, a4 = is_static)`: set the child
    frame's per-frame env call-context for CALL/STATICCALL (DELEGATECALL/CALLCODE
    caller/value rules are .61.7). Writes the three 32-byte words:
      child.ADDRESS  (env+0)  = `to`            (the call target / current_target)
      child.CALLER   (env+64) = parent.ADDRESS  (msg.sender = the calling frame)
      child.CALLVALUE (env+96) = is_static ? 0 : `value`
    Offsets per the per-frame env layout (docs §3; ADDRESS@0 / CALLER@64 read by
    EvmLogHandlers, CALLVALUE@96). Clobbers t0. -/
def callFrameSetCallEnvFunction : String :=
  "call_frame_set_call_env:\n" ++
  -- ADDRESS = to (4 limbs)
  "  ld t0, 0(a2); sd t0, 0(a0)\n" ++
  "  ld t0, 8(a2); sd t0, 8(a0)\n" ++
  "  ld t0, 16(a2); sd t0, 16(a0)\n" ++
  "  ld t0, 24(a2); sd t0, 24(a0)\n" ++
  -- CALLER = parent.ADDRESS (parent env+0 -> child env+64)
  "  ld t0, 0(a1); sd t0, 64(a0)\n" ++
  "  ld t0, 8(a1); sd t0, 72(a0)\n" ++
  "  ld t0, 16(a1); sd t0, 80(a0)\n" ++
  "  ld t0, 24(a1); sd t0, 88(a0)\n" ++
  -- CALLVALUE = is_static ? 0 : value
  "  bnez a4, .Lcfsce_static\n" ++
  "  ld t0, 0(a3); sd t0, 96(a0)\n" ++
  "  ld t0, 8(a3); sd t0, 104(a0)\n" ++
  "  ld t0, 16(a3); sd t0, 112(a0)\n" ++
  "  ld t0, 24(a3); sd t0, 120(a0)\n" ++
  "  ret\n" ++
  ".Lcfsce_static:\n" ++
  "  sd zero, 96(a0); sd zero, 104(a0); sd zero, 112(a0); sd zero, 120(a0)\n" ++
  "  ret"

/-- `call_frame_set_calldata(a0 = child env base, a1 = parent mem base,
    a2 = argsOff, a3 = argsLen)`: alias the child's calldata view into the
    parent frame's memory — `callDataPtr@416 = parent_mem + argsOff`,
    `callDataLen@424 = argsLen`. No copy: the parent frame slot persists
    (strictly shallower index) while the child runs, so CALLDATALOAD/COPY read
    directly from it. Clobbers t0. -/
def callFrameSetCalldataFunction : String :=
  "call_frame_set_calldata:\n" ++
  "  add t0, a1, a2\n" ++
  "  sd t0, 416(a0)\n" ++
  "  sd a3, 424(a0)\n" ++
  "  ret"

/-- `call_frame_forward_gas(a0 = gas_left, a1 = requested, a2 = value_nonzero)`:
    EIP-150 message-call gas forwarding (`vm/gas.py:419,424,64,415`). Returns
    `a0 = min(requested, gas_left - gas_left/64) + (value_nonzero ? 2300 : 0)`.
    `gas_left` is the caller's gas AFTER the memory-expansion + access cost is
    charged; the all-but-1/64 cap leaves the caller 1/64; the `CALL_STIPEND`
    (2300) is added to the callee for value-bearing CALL/CALLCODE and is NOT
    charged to the caller (a gift). Clobbers t0/t1. -/
def callFrameForwardGasFunction : String :=
  "call_frame_forward_gas:\n" ++
  "  srli t0, a0, 6\n" ++                 -- gas_left / 64
  "  sub t1, a0, t0\n" ++                 -- max_message_call_gas = gas_left - gas_left/64
  "  bltu a1, t1, .Lcffg_min\n" ++        -- requested < max -> use requested
  "  j .Lcffg_stipend\n" ++               -- else keep max in t1
  ".Lcffg_min:\n" ++
  "  mv t1, a1\n" ++
  ".Lcffg_stipend:\n" ++
  "  beqz a2, .Lcffg_done\n" ++
  "  li t0, 2300\n" ++                    -- CALL_STIPEND (> addi imm range)
  "  add t1, t1, t0\n" ++
  ".Lcffg_done:\n" ++
  "  mv a0, t1\n" ++
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
  -- Env setup test: child env = call_frame_arena + frameEnvOff (0x28400) for depth 1.
  "  la a0, call_frame_arena; li t0, 0x28400; add a0, a0, t0\n" ++
  "  la a1, cfd_parent_env\n" ++
  "  la a2, cfd_to_word\n" ++
  "  la a3, cfd_value_word\n" ++
  "  li a4, 0\n" ++                          -- CALL (not static)
  "  jal ra, call_frame_set_call_env\n" ++
  "  ld t0, 0(a0); sd t0, 64(s0)\n" ++       -- child ADDRESS limb0 (expect 0xaaaaaaaa = to)
  "  ld t0, 64(a0); sd t0, 72(s0)\n" ++      -- child CALLER limb0 (expect 0xbbbbbbbb = parent ADDRESS)
  "  ld t0, 96(a0); sd t0, 80(s0)\n" ++      -- child CALLVALUE limb0 (expect 0xcccccccc = value)
  "  la a0, call_frame_arena; li t0, 0x28400; add a0, a0, t0\n" ++
  "  la a1, cfd_parent_env; la a2, cfd_to_word; la a3, cfd_value_word; li a4, 1\n" ++  -- STATICCALL
  "  jal ra, call_frame_set_call_env\n" ++
  "  ld t0, 96(a0); sd t0, 88(s0)\n" ++      -- child CALLVALUE limb0 (expect 0 = static)
  -- Calldata alias test: child callDataPtr@416 = parent_mem + argsOff, len@424.
  "  la a0, call_frame_arena; li t0, 0x28400; add a0, a0, t0\n" ++
  "  la a1, call_frame_arena; li a2, 0x40; li a3, 0x20\n" ++
  "  jal ra, call_frame_set_calldata\n" ++
  "  ld t0, 416(a0); la t1, call_frame_arena; sub t0, t0, t1; sd t0, 96(s0)\n" ++  -- expect 0x40
  "  ld t0, 424(a0); sd t0, 104(s0)\n" ++                                          -- expect 0x20
  -- Gas forward test (EIP-150 63/64 + stipend).
  "  li a0, 6400; li a1, 100000; li a2, 0; jal ra, call_frame_forward_gas; sd a0, 112(s0)\n" ++  -- 6300
  "  li a0, 6400; li a1, 1000; li a2, 1; jal ra, call_frame_forward_gas; sd a0, 120(s0)\n" ++    -- 3300
  "  li a0, 64; li a1, 100; li a2, 0; jal ra, call_frame_forward_gas; sd a0, 128(s0)\n" ++       -- 63
  "  j .Lcd_done\n" ++
  frameBaseFunction ++ "\n" ++
  frameDepthPushFunction ++ "\n" ++
  callFrameEnterFunction ++ "\n" ++
  callFrameSetCallEnvFunction ++ "\n" ++
  callFrameSetCalldataFunction ++ "\n" ++
  callFrameForwardGasFunction ++ "\n" ++
  ".Lcd_done:"

/-- Local stubs so the probe links standalone (the real `call_frame_arena`
    lives in the guest's `BlockVerdictDataSection`; `evm_call_depth` in the
    embedded helper data). The arena stub holds one frame slot. -/
def ziskCallDescendDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero " ++ toString (0x29000 : Nat) ++ "\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "cfd_parent_env:\n  .quad 0xbbbbbbbb, 0, 0, 0\n" ++   -- parent ADDRESS@0
  "cfd_to_word:\n  .quad 0xaaaaaaaa, 0, 0, 0\n" ++       -- call target
  "cfd_value_word:\n  .quad 0xcccccccc, 0, 0, 0\n"       -- call value

def ziskCallDescendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCallDescendPrologue
  dataAsm     := ziskCallDescendDataSection
}

end EvmAsm.Codegen
