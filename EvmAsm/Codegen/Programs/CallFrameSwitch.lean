/-
  EvmAsm.Codegen.Programs.CallFrameSwitch

  Call-frame switching state (bead fhsxz.2.4.2.61.5): the `evm_call_depth`
  counter and the per-depth saved-register area used by CALL/CREATE descent and
  RETURN/REVERT return.

  DESIGN NOTE (refines docs §4): the per-depth saved PC (x10) / code-base (x21)
  do NOT live inside the union frame slots. Under the non-uniform layout
  `frame[0]` is the existing dispatcher state (NOT in the arena), so an in-slot
  save area cannot hold depth-0's saved registers. Instead this module uses a
  SEPARATE small uniform `frame_save_area` indexed by depth (1025 entries × 16 B
  = pc, codebase), in ordinary `.data` (~16 KiB, cheap). This handles every depth
  0..1024 uniformly and keeps the big memory/stack arenas on the overlay union.

  On a CALL/CREATE descent (depth d → d+1) the handler calls `frame_save_regs(d,
  pc, codebase)` then bumps `evm_call_depth`; on return it decrements and calls
  `frame_load_regs(d)`. The register-base recompute (x12/x13/x20) uses
  `frame_base` (.61.4) for d ≥ 1, or the existing labels for d = 0.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `frame_save_regs(a0=depth, a1=pc, a2=codebase)`: store the saved PC and
    code-base for `depth` into `frame_save_area + depth*16`. Clobbers t0/t1. -/
def frameSaveRegsFunction : String :=
  "frame_save_regs:\n" ++
  "  la t0, frame_save_area\n" ++
  "  slli t1, a0, 4                 # depth*16\n" ++
  "  add t0, t0, t1\n" ++
  "  sd a1, 0(t0)                   # saved pc\n" ++
  "  sd a2, 8(t0)                   # saved codebase\n" ++
  "  ret"

/-- `frame_load_regs(a0=depth)`: load the saved (pc, codebase) for `depth` into
    (a0, a1). Clobbers t0/t1. -/
def frameLoadRegsFunction : String :=
  "frame_load_regs:\n" ++
  "  la t0, frame_save_area\n" ++
  "  slli t1, a0, 4\n" ++
  "  add t0, t0, t1\n" ++
  "  ld a0, 0(t0)                   # saved pc\n" ++
  "  ld a1, 8(t0)                   # saved codebase\n" ++
  "  ret"

/-- `frame_depth_push`: increment `evm_call_depth`, return new depth in a0. -/
def frameDepthPushFunction : String :=
  "frame_depth_push:\n" ++
  "  la t0, evm_call_depth\n" ++
  "  ld a0, 0(t0)\n" ++
  "  addi a0, a0, 1\n" ++
  "  sd a0, 0(t0)\n" ++
  "  ret"

/-- `frame_depth_pop`: decrement `evm_call_depth`, return new depth in a0. -/
def frameDepthPopFunction : String :=
  "frame_depth_pop:\n" ++
  "  la t0, evm_call_depth\n" ++
  "  ld a0, 0(t0)\n" ++
  "  addi a0, a0, -1\n" ++
  "  sd a0, 0(t0)\n" ++
  "  ret"

/-- `zisk_frame_switch`: round-trips the depth counter + per-depth save area.
    Output:
      +0  depth after push from 0           (expect 1)
      +8  depth after second push           (expect 2)
      +16 depth after pop                   (expect 1)
      +24 frame_load_regs(0).pc             (expect 0x111)
      +32 frame_load_regs(0).codebase       (expect 0x222)
      +40 frame_load_regs(1).pc             (expect 0x333)
      +48 frame_load_regs(1).codebase       (expect 0x444) -/
def ziskFrameSwitchPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- depth starts 0; push -> 1, push -> 2, pop -> 1
  "  jal ra, frame_depth_push; sd a0, 0(s0)\n" ++
  "  jal ra, frame_depth_push; sd a0, 8(s0)\n" ++
  "  jal ra, frame_depth_pop;  sd a0, 16(s0)\n" ++
  -- save (depth 0: pc=0x111, cb=0x222), (depth 1: pc=0x333, cb=0x444)
  "  li a0, 0; li a1, 0x111; li a2, 0x222; jal ra, frame_save_regs\n" ++
  "  li a0, 1; li a1, 0x333; li a2, 0x444; jal ra, frame_save_regs\n" ++
  -- load back and store to OUTPUT
  "  li a0, 0; jal ra, frame_load_regs; sd a0, 24(s0); sd a1, 32(s0)\n" ++
  "  li a0, 1; jal ra, frame_load_regs; sd a0, 40(s0); sd a1, 48(s0)\n" ++
  "  j .Lfsw_done\n" ++
  frameDepthPushFunction ++ "\n" ++
  frameDepthPopFunction ++ "\n" ++
  frameSaveRegsFunction ++ "\n" ++
  frameLoadRegsFunction ++ "\n" ++
  ".Lfsw_done:"

/-- Data: the depth counter + the uniform per-depth save area (1025 × 16 B). -/
def ziskFrameSwitchDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 16\n" ++
  "frame_save_area:\n  .zero 16400\n"  -- 1025 entries × 16 B (pc, codebase)

def ziskFrameSwitchProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskFrameSwitchPrologue
  dataAsm     := ziskFrameSwitchDataSection
}

end EvmAsm.Codegen
