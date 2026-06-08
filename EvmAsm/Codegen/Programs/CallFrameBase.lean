/-
  EvmAsm.Codegen.Programs.CallFrameBase

  `frame_base(depth)` — the call-frame addressing primitive (bead
  fhsxz.2.4.2.61.4). Per the non-uniform layout (docs/call-frame-memory-layout.md
  §1, §4): frame[0] is the existing single-frame dispatcher state (NOT in the
  arena), and frames 1..1024 live in the overlay union at
  `call_frame_arena + (depth-1) * FRAME_STRIDE`. This helper returns that base
  for `depth >= 1`; the CALL/CREATE descent (.61.6+) uses it to set the child
  register bases (x13=base+frameMemOff, x12=base+frameStackTopOff,
  x20=base+frameEnvOff) on a depth bump.

  `FRAME_STRIDE = 0x29000` (CallFrameLayout.frameStride). The arena symbol
  `call_frame_arena` aliases `basr_values` in the guest (#8513); this module's
  probe links a local stub to test the offset arithmetic in isolation.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## frame_base

    a0 = depth (>= 1). Returns a0 = `call_frame_arena + (depth-1) * 0x29000`.
    (depth 0 is NOT handled here — it uses the existing evm_memory/stack/env
    labels directly; see the layout doc §1.) Clobbers t0/t1. -/
def frameBaseFunction : String :=
  "frame_base:\n" ++
  "  addi t0, a0, -1                 # depth-1\n" ++
  "  li t1, 0x29000                  # FRAME_STRIDE\n" ++
  "  mul t0, t0, t1                  # (depth-1)*FRAME_STRIDE\n" ++
  "  la t1, call_frame_arena\n" ++
  "  add a0, t1, t0\n" ++
  "  ret"

/-- `zisk_frame_base`: probe over a local `call_frame_arena` stub. Verifies the
    offsets `frame_base(d) - call_frame_arena` for d = 1, 2, 1024 are
    `0`, `0x29000`, `1023*0x29000` respectively (the layout arithmetic). -/
def ziskFrameBasePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la s1, call_frame_arena\n" ++
  -- frame_base(1) - arena -> expect 0
  "  li a0, 1; jal ra, frame_base; sub a0, a0, s1; sd a0, 0(s0)\n" ++
  -- frame_base(2) - arena -> expect 0x29000
  "  li a0, 2; jal ra, frame_base; sub a0, a0, s1; sd a0, 8(s0)\n" ++
  -- frame_base(1024) - arena -> expect 1023*0x29000 = 0xa3d7000
  "  li a0, 1024; jal ra, frame_base; sub a0, a0, s1; sd a0, 16(s0)\n" ++
  "  j .Lfb_done\n" ++
  frameBaseFunction ++ "\n" ++
  ".Lfb_done:"

/-- Local stub for the arena symbol so the probe links standalone (the real
    `call_frame_arena` lives in the guest's BlockVerdictDataSection). -/
def ziskFrameBaseDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero 64\n"

def ziskFrameBaseProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskFrameBasePrologue
  dataAsm     := ziskFrameBaseDataSection
}

end EvmAsm.Codegen
