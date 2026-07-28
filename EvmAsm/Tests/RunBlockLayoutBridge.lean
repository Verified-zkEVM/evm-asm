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
