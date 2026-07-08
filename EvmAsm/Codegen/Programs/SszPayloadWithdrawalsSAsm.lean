/-
  EvmAsm.Codegen.Programs.SszPayloadWithdrawalsSAsm

  Verified SAsm port for `spw_u32le`.
-/

import EvmAsm.Codegen.Programs.SszPayloadWithdrawals
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SszPayloadWithdrawalsSAsm

open SgLoadU32leSAsm

/-- Verified port of `spw_u32le`: `a0 := leU32 (bytes at a0) 0`. -/
def spwU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "spwU32le"
  region := ⟨p, bs⟩
  pre := fun rf _ _ => rf.get .x10 = p ∧ 4 ≤ bs.length
  post := fun rf _ _ => rf.get .x10 = leU32 bs 0
  body := sgLoadU32leBody

theorem spwU32le_byte_tie :
    (spwU32leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = spwU32le_prog := rfl

#guard ((spwU32leFn 0 []).body.flatten 0).length = 11

theorem spwU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (spwU32leFn p bs).Spec base := by
  simpa [spwU32leFn, sgLoadU32leFn] using sgLoadU32leFn_spec p bs hwf base

end SszPayloadWithdrawalsSAsm

end EvmAsm.Codegen
