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
  `call_frame_arena` is a standalone pre-zeroed block in the guest (it aliased
  `basr_values` under the retired 1G layout, #8513); this module's probe links
  a local stub to test the offset arithmetic in isolation.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## frame_base

    a0 = depth (>= 1). Returns a0 = `call_frame_arena + (depth-1) * 0x29000`.
    (depth 0 is NOT handled here — it uses the existing evm_memory/stack/env
    labels directly; see the layout doc §1.) Clobbers t0/t1. -/
def frameBase_prog : Program :=
  [ .ADDI .x5 .x10 (-1 : BitVec 12),
    .LUI .x6 (41 : BitVec 20),
    .MUL .x5 .x5 .x6,
    .AUIPC .x6 (laHi GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 12)),
    .ADDI .x6 .x6 (laLo GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 12)),
    .ADD .x10 .x6 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `frameBase_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def frameBase_relocs : RelocTable :=
  [ (3, .la .x6 "call_frame_arena") ]

def frameBaseFunction : String :=
  "frame_base:\n" ++ emitProgramR frameBase_prog frameBase_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `frameBase_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem frameBaseFunction_eq_prog :
    frameBaseFunction = "frame_base:\n" ++ emitProgramR frameBase_prog frameBase_relocs := rfl

#guard frameBaseFunction.startsWith "frame_base:\n"
#guard frameBase_prog.length = 7
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
