/-
  EvmAsm.Codegen.Programs.BlockAccessListHashSAsm

  Verified SAsm port for `bah_u32le`.
-/

import EvmAsm.Codegen.Programs.BlockAccessListHash
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace BlockAccessListHashSAsm

open SgLoadU32leSAsm

/-- Verified port of `bah_u32le`: `a0 := leU32 (bytes at a0) 0`. -/
def bahU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "bahU32le"
  region := ⟨p, bs⟩
  pre := fun rf _ _ => rf.get .x10 = p ∧ 4 ≤ bs.length
  post := fun rf _ _ => rf.get .x10 = leU32 bs 0
  body := sgLoadU32leBody

theorem bahU32le_byte_tie :
    (bahU32leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = bahU32le_prog := rfl

#guard ((bahU32leFn 0 []).body.flatten 0).length = 11

theorem bahU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (bahU32leFn p bs).Spec base := by
  simpa [bahU32leFn, sgLoadU32leFn] using sgLoadU32leFn_spec p bs hwf base

end BlockAccessListHashSAsm

end EvmAsm.Codegen
