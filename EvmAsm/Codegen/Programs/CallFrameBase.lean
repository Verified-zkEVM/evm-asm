/-
  EvmAsm.Codegen.Programs.CallFrameBase

  `frame_base(depth)` — the call-frame addressing primitive (bead
  fhsxz.2.4.2.61.4). Per the non-uniform layout (docs/call-frame-memory-layout.md
  §1, §4): frames 0..1024 live in the overlay union at
  `call_frame_arena + depth * FRAME_STRIDE`. This helper returns that base
  for `depth >= 0`; the CALL/CREATE descent (.61.6+) uses it to set the child
  register bases (x13=base+frameMemOff, x12=base+frameStackTopOff,
  x20=base+frameEnvOff) on a depth bump.

  `FRAME_STRIDE = 0x19000` (CallFrameLayout.frameStride). The arena symbol
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

    a0 = depth (>= 0). Returns a0 = `call_frame_arena + depth * 0x19000`.

    ⚠️ Depth 0 now indexes a slot of its own (GH #10938 preparation). The arena was
    ALREADY sized for it: `call_frame_arena_end - call_frame_arena = 0x6419000`, which is
    exactly `frameSlotCount * frameStride = 1025 * 0x19000`, while the previous `depth-1`
    skew used only indices 0..1023. So this is a pure re-indexing with **zero new
    allocation** — the spare slot was already paid for.

    ⚠️ This does NOT affect `call_frame_enter`'s `depth == 1` special case, which takes
    `evm_memory_pool` as the parent memory base. That case is about the POOL ORIGIN, not
    about slot addressing, and `frameMemBytes = 0` (`CallFrameLayout`) means a slot holds
    no memory sub-region at all — so a depth-0 slot cannot supply a memory base and the
    special case survives on its own reason. Adjacent, not coupled; do not remove it here.

    Clobbers t0/t1. -/
def frameBase_prog : Program :=
  [ .LUI .x6 (25 : BitVec 20),
    .MUL .x5 .x10 .x6,
    .AUIPC .x6 (laHi GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 8)),
    .ADDI .x6 .x6 (laLo GuestAddrs.call_frame_arena (GuestAddrs.frame_base + 8)),
    .ADD .x10 .x6 .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `frameBase_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def frameBase_relocs : RelocTable :=
  [ (2, .la .x6 "call_frame_arena") ]

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
#guard frameBase_prog.length = 6
/-- `zisk_frame_base`: probe over a local `call_frame_arena` stub. Verifies the
    offsets `frame_base(d) - call_frame_arena` for d = 0, 1, 1024 are
    `0`, `0x19000`, `1024*0x19000` respectively (the layout arithmetic).

    ⚠️ These expectations MOVED with the depth-0 re-indexing: they were `0`, `0x19000`,
    `1023*0x19000` for d = 1, 2, 1024 under the old `depth-1` skew.  **d = 0 is the new
    case and is the point of the change** — it must land at offset 0, i.e. the slot the
    arena was already sized for. -/
def ziskFrameBasePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la s1, call_frame_arena\n" ++
  -- frame_base(0) - arena -> expect 0   (the depth-0 slot; new with this change)
  "  li a0, 0; jal ra, frame_base; sub a0, a0, s1; sd a0, 0(s0)\n" ++
  -- frame_base(1) - arena -> expect 0x19000
  "  li a0, 1; jal ra, frame_base; sub a0, a0, s1; sd a0, 8(s0)\n" ++
  -- frame_base(1024) - arena -> expect 1024*0x19000 = 0x6400000 (the last slot)
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
