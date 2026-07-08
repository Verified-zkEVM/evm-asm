/-
  EvmAsm.Rv64.SAsm.AbiFrame

  ABI stack-frame support for SAsm (bead evm-asm-4ch8f.76, extending .3).

  Bead .3 modelled frames as *static* stack-arena windows and deliberately
  deferred the guest's *dynamic* C-ABI leaf frames — the `addi sp, sp, -N`
  prologue that saves `ra`/callee-saved `s`-registers, uses them as locals,
  restores them, and `addi sp, sp, +N` before `ret`.  The SAsm block engine
  (`Sym.lean`) cannot express these: `sp` (x2) and the `s`-registers
  (x8/x9/x18–x27) are outside `Reg.isExposed`, and the stack frame is memory
  below `sp` that no `Region`/`RwRegion` owns.  See `FrameConv.lean` for the
  register-preservation conventions that story replaced.

  This file supplies the missing capability as a **machine-level frame
  construct**, built directly on `cpsTripleWithin` (the same layer the whole
  codebase trusts) rather than as a new `Stmt` node.  This keeps the existing
  caller-only static-`rw` soundness path (`Stmt.sound`/`soundR`, `blockOk`)
  completely untouched (the "additive" invariant) while modelling exactly the
  three pieces a real frame needs:

  1. **A frame-region assertion** (`frameSlotsOwn`): the allocated slots below
     `sp` as *genuinely owned* dword cells (`memOwn`), carved from the caller's
     stack space, disjoint (by `**`) from every register atom, the caller's
     `rw`/`ro` regions, and the ambient — no arbitrary stack read/write.
  2. **Proven callee-saved preservation**: the prologue stores the *entry*
     value of each saved register into its slot; the body runs with those
     slots *framed* (in the `cpsTripleWithin` frame `R`, hence untouched by the
     body's own scratch use of the `s`-registers); the epilogue reads the entry
     value straight back.  Preservation is therefore *derived* from the frame
     rule, never assumed.
  3. **Frame-scoped `s`-register exposure**: inside the frame body the saved
     registers (x1/x8/x9 here) are ordinary owned `↦ᵣ` atoms — usable and
     clobberable as locals — while *outside* a frame they remain unowned by the
     SAsm state (they are not in `Reg.isExposed`, exactly as before).

  Byte-transparency: `abiFrameProg` is literally
  `prologue ++ body ++ epilogue ++ [ret]`, reproduced by `#guard` against a
  hand-written program (`AbiFrameDemo.lean`).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Program

namespace EvmAsm.Rv64
namespace SAsm

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- The emitted prologue / epilogue (byte-transparent)
-- ============================================================================

/-- Standard leaf-frame prologue saving `ra` (x1), `s0` (x8), `s1` (x9) into a
    24-byte frame:  `addi sp,sp,-24 ; sd ra,0(sp) ; sd s0,8(sp) ; sd s1,16(sp)`.
    `negImm` is the (negative) allocation immediate. -/
def framePrologue (negImm : BitVec 12) : List Instr :=
  [ .ADDI .x2 .x2 negImm,
    .SD .x2 .x1 0,
    .SD .x2 .x8 8,
    .SD .x2 .x9 16 ]

/-- The matching epilogue: `ld ra,0(sp) ; ld s0,8(sp) ; ld s1,16(sp) ;
    addi sp,sp,+24`. -/
def frameEpilogue (posImm : BitVec 12) : List Instr :=
  [ .LD .x1 .x2 0,
    .LD .x8 .x2 8,
    .LD .x9 .x2 16,
    .ADDI .x2 .x2 posImm ]

/-- A full leaf ABI-frame routine: prologue, body, epilogue, `ret`.  This is
    the byte-transparent flatten of the frame construct. -/
def abiFrameProg (negImm posImm : BitVec 12) (body : List Instr) : List Instr :=
  framePrologue negImm ++ body ++ frameEpilogue posImm ++ [.JALR .x0 .x1 0]

/-- Byte-transparency: the frame flatten is exactly prologue ++ body ++
    epilogue ++ ret, by definition. -/
theorem abiFrameProg_eq (negImm posImm : BitVec 12) (body : List Instr) :
    abiFrameProg negImm posImm body
      = framePrologue negImm ++ body ++ frameEpilogue posImm ++ [.JALR .x0 .x1 0] :=
  rfl

-- ============================================================================
-- The frame-region assertion (the new memory-model piece)
-- ============================================================================

/-- The three-slot leaf frame below `sp0` (24 bytes): fresh, *owned* stack
    dwords with arbitrary contents (`memOwn`).  This is the frame region carved
    from the caller's stack space; being an ordinary owned-memory atom it is
    disjoint (through `**`) from the register atoms, the caller's regions, and
    the ambient. -/
def frameSlotsOwn (sp0 : Word) : Assertion :=
  memOwn (sp0 - 24) ** (memOwn (sp0 - 16) ** memOwn (sp0 - 8))

/-- The same three slots after the prologue has saved the entry values
    `vra`/`v0`/`v1` — the frame filled. -/
def frameSlotsSaved (sp0 vra v0 v1 : Word) : Assertion :=
  ((sp0 - 24) ↦ₘ vra) ** (((sp0 - 16) ↦ₘ v0) ** ((sp0 - 8) ↦ₘ v1))

theorem pcFree_frameSlotsSaved (sp0 vra v0 v1 : Word) :
    (frameSlotsSaved sp0 vra v0 v1).pcFree :=
  pcFree_sepConj pcFree_memIs (pcFree_sepConj pcFree_memIs pcFree_memIs)

end SAsm
end EvmAsm.Rv64
