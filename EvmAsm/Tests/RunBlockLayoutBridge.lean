import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Program
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Codegen.GuestLayoutInstance

namespace EvmAsm.Tests.RunBlockLayoutBridge

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

def layoutLi_prog_of (_ : GuestLayout) : Program := by
  exact (show List Instr from [ Instr.LI .x5 (0 : Word) ])
def layoutLi_prog : Program := layoutLi_prog_of guestLayout

example (base v : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base layoutLi_prog)
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ 0) := by
  have h := li_spec_gen_within .x5 v (0 : Word) base (by nofun)
  runBlock h

/-! ## #12294: a `_prog` defined as a LITERAL instruction list

  The case above routes through `layoutLi_prog_of guestLayout`, which is what
  made `runBlock` work for it. A `_prog` whose body is a concrete list directly —
  the shape most hand-written and `asm_to_program`-emitted routines have — used to
  take a different path: `CodeReq.ofProg` was delta-unfolded ITSELF, the
  code-membership step could no longer see the singleton chain, and because those
  side goals go through `runTacticSilent` the tactic returned "successfully" while
  leaving metavariables. The only symptom appeared later as
  `don't know how to synthesize placeholder` at every PRECEDING `have`.

  These two examples pin that the literal-list shape now works. Note the contrast
  with the `opaqueProgram` example further down, which SHOULD still fail: an
  `opaque` program genuinely cannot be reduced, so the placeholder error is the
  honest outcome there and stays pinned by `#guard_msgs`. -/

def literalLi_prog : Program := [ Instr.LI .x5 (0 : Word) ]

example (base v : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base literalLi_prog)
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ 0) := by
  have h := li_spec_gen_within .x5 v (0 : Word) base (by nofun)
  runBlock h

/-- A two-instruction literal-list program, so the fix is exercised on a chain
    rather than a single `singleton` that might succeed by accident. -/
def literalTwo_prog : Program :=
  [ Instr.LI .x5 (0 : Word), Instr.LI .x6 (1 : Word) ]

example (base v w : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base literalTwo_prog)
      ((.x5 ↦ᵣ v) ** (.x6 ↦ᵣ w)) ((.x5 ↦ᵣ 0) ** (.x6 ↦ᵣ 1)) := by
  have h1 := li_spec_gen_within .x5 v (0 : Word) base (by nofun)
  have h2 := li_spec_gen_within .x6 w (1 : Word) (base + 4) (by nofun)
  runBlock h1 h2

opaque opaqueProgram : Program := by
  exact (show List Instr from [ Instr.LI .x5 (0 : Word) ])

/--
error: don't know how to synthesize placeholder
context:
base v : Word
h : cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base (Instr.LI Reg.x5 0)) (Reg.x5 ↦ᵣ v) (Reg.x5 ↦ᵣ 0)
⊢ cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base opaqueProgram) (Reg.x5 ↦ᵣ v) (Reg.x5 ↦ᵣ 0)
-/
#guard_msgs in
example (base v : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base opaqueProgram)
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ 0) := by
  have h := li_spec_gen_within .x5 v (0 : Word) base (by nofun)
  runBlock h

def tooDeep4_prog_of (_ : GuestLayout) : Program := by
  exact (show List Instr from [ Instr.LI .x5 (0 : Word) ])
def tooDeep3_prog_of (L : GuestLayout) : Program := tooDeep4_prog_of L
def tooDeep2_prog_of (L : GuestLayout) : Program := tooDeep3_prog_of L
def tooDeep1_prog_of (L : GuestLayout) : Program := tooDeep2_prog_of L
def tooDeep0_prog_of (L : GuestLayout) : Program := tooDeep1_prog_of L

/--
error: runBlock: layout CodeReq.ofProg normalization exhausted 4 steps at EvmAsm.Tests.RunBlockLayoutBridge.tooDeep4_prog_of; add an explicit bridge theorem or increase the tactic fuel deliberately.
-/
#guard_msgs in
example (base v : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base (tooDeep0_prog_of guestLayout))
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ 0) := by
  have h := li_spec_gen_within .x5 v (0 : Word) base (by nofun)
  runBlock h

end EvmAsm.Tests.RunBlockLayoutBridge
