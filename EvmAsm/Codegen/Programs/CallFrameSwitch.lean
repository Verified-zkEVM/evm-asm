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
  `frame_base` (.61.4) for any d ≥ 0; depth 0 has its own slot since the
  `depth-1` skew was removed, though the dispatcher still binds the globals for it.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `frame_save_regs(a0=depth, a1=pc, a2=codebase)`: store the saved PC and
    code-base for `depth` into `frame_save_area + depth*16`. Clobbers t0/t1. -/
def frameSaveRegs_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.frame_save_area (GuestAddrs.frame_save_regs + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.frame_save_area (GuestAddrs.frame_save_regs + 0)),
    .SLLI .x6 .x10 (4 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .SD .x5 .x11 (0 : BitVec 12),
    .SD .x5 .x12 (8 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `frameSaveRegs_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def frameSaveRegs_relocs : RelocTable :=
  [ (0, .la .x5 "frame_save_area") ]

def frameSaveRegsFunction : String :=
  "frame_save_regs:\n" ++ emitProgramR frameSaveRegs_prog frameSaveRegs_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `frameSaveRegs_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem frameSaveRegsFunction_eq_prog :
    frameSaveRegsFunction = "frame_save_regs:\n" ++ emitProgramR frameSaveRegs_prog frameSaveRegs_relocs := rfl

#guard frameSaveRegsFunction.startsWith "frame_save_regs:\n"
/-- `frame_load_regs(a0=depth)`: load the saved (pc, codebase) for `depth` into
    (a0, a1). Clobbers t0/t1. -/
def frameLoadRegs_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.frame_save_area (GuestAddrs.frame_load_regs + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.frame_save_area (GuestAddrs.frame_load_regs + 0)),
    .SLLI .x6 .x10 (4 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .LD .x10 .x5 (0 : BitVec 12),
    .LD .x11 .x5 (8 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `frameLoadRegs_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def frameLoadRegs_relocs : RelocTable :=
  [ (0, .la .x5 "frame_save_area") ]

def frameLoadRegsFunction : String :=
  "frame_load_regs:\n" ++ emitProgramR frameLoadRegs_prog frameLoadRegs_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `frameLoadRegs_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem frameLoadRegsFunction_eq_prog :
    frameLoadRegsFunction = "frame_load_regs:\n" ++ emitProgramR frameLoadRegs_prog frameLoadRegs_relocs := rfl

#guard frameLoadRegsFunction.startsWith "frame_load_regs:\n"
/-- `frame_depth_push`: increment `evm_call_depth`, return new depth in a0. -/
def frameDepthPush_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.evm_call_depth (GuestAddrs.frame_depth_push + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_call_depth (GuestAddrs.frame_depth_push + 0)),
    .LD .x10 .x5 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .SD .x5 .x10 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `frameDepthPush_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def frameDepthPush_relocs : RelocTable :=
  [ (0, .la .x5 "evm_call_depth") ]

def frameDepthPushFunction : String :=
  "frame_depth_push:\n" ++ emitProgramR frameDepthPush_prog frameDepthPush_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `frameDepthPush_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem frameDepthPushFunction_eq_prog :
    frameDepthPushFunction = "frame_depth_push:\n" ++ emitProgramR frameDepthPush_prog frameDepthPush_relocs := rfl

#guard frameDepthPushFunction.startsWith "frame_depth_push:\n"
/-- `frame_depth_pop`: decrement `evm_call_depth`, return new depth in a0. -/
def frameDepthPop_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.evm_call_depth (GuestAddrs.frame_depth_pop + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_call_depth (GuestAddrs.frame_depth_pop + 0)),
    .LD .x10 .x5 (0 : BitVec 12),
    .ADDI .x10 .x10 (-1 : BitVec 12),
    .SD .x5 .x10 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `frameDepthPop_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def frameDepthPop_relocs : RelocTable :=
  [ (0, .la .x5 "evm_call_depth") ]

def frameDepthPopFunction : String :=
  "frame_depth_pop:\n" ++ emitProgramR frameDepthPop_prog frameDepthPop_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `frameDepthPop_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem frameDepthPopFunction_eq_prog :
    frameDepthPopFunction = "frame_depth_pop:\n" ++ emitProgramR frameDepthPop_prog frameDepthPop_relocs := rfl

#guard frameDepthPopFunction.startsWith "frame_depth_pop:\n"
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


end EvmAsm.Codegen
