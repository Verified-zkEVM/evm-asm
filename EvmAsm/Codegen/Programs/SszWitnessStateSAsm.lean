/-
  EvmAsm.Codegen.Programs.SszWitnessStateSAsm

  Verified SAsm port for `sws_u32le`.
-/

import EvmAsm.Codegen.Programs.SszWitnessState
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SszWitnessStateSAsm

open SgLoadU32leSAsm

/-- Verified port of `sws_u32le`: `a0 := leU32 (bytes at a0) 0`. -/
def swsU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "swsU32le"
  region := ⟨p, bs⟩
  pre := fun rf _ _ => rf.get .x10 = p ∧ 4 ≤ bs.length
  post := fun rf _ _ => rf.get .x10 = leU32 bs 0
  body := sgLoadU32leBody

theorem swsU32le_byte_tie :
    (swsU32leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = swsU32le_prog := rfl

#guard ((swsU32leFn 0 []).body.flatten 0).length = 11

theorem swsU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (swsU32leFn p bs).Spec base := by
  simpa [swsU32leFn, sgLoadU32leFn] using sgLoadU32leFn_spec p bs hwf base

end SszWitnessStateSAsm

end EvmAsm.Codegen
