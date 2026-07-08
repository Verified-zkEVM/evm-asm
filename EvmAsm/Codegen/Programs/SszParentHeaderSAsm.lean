/-
  EvmAsm.Codegen.Programs.SszParentHeaderSAsm

  Verified SAsm port for `eph_u32le`.
-/

import EvmAsm.Codegen.Programs.SszParentHeader
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SszParentHeaderSAsm

open SgLoadU32leSAsm

/-- Verified port of `eph_u32le`: `a0 := leU32 (bytes at a0) 0`. -/
def ephU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "ephU32le"
  region := ⟨p, bs⟩
  pre := fun rf _ _ => rf.get .x10 = p ∧ 4 ≤ bs.length
  post := fun rf _ _ => rf.get .x10 = leU32 bs 0
  body := sgLoadU32leBody

theorem ephU32le_byte_tie :
    (ephU32leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = ephU32le_prog := rfl

#guard ((ephU32leFn 0 []).body.flatten 0).length = 11

theorem ephU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (ephU32leFn p bs).Spec base := by
  simpa [ephU32leFn, sgLoadU32leFn] using sgLoadU32leFn_spec p bs hwf base

end SszParentHeaderSAsm

end EvmAsm.Codegen
