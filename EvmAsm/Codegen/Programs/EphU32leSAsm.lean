/-
  EvmAsm.Codegen.Programs.EphU32leSAsm

  Verified SAsm port of the byte-wise `eph_u32le` SSZ leaf helper.  Its
  instruction sequence is the same four-LBU little-endian loader used by
  `sg_load_u32le`/`spw_u32le`; the generic proof is reused, while this module
  pins the helper's own emitted Program by a separate byte tie.
-/

import EvmAsm.Codegen.Programs.SszParentHeader
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace EphU32leSAsm

def ephU32leFn (p : Word) (bs : List (BitVec 8)) : Fn where
  name := "ephU32le"
  region := ⟨p, bs⟩
  pre := fun rf _ _ => rf.get .x10 = p ∧ 4 ≤ bs.length
  post := fun rf _ _ => rf.get .x10 = SgLoadU32leSAsm.leU32 bs 0
  body := SgLoadU32leSAsm.sgLoadU32leBody

theorem ephU32le_byte_tie :
    (ephU32leFn 0 []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = ephU32le_prog := by
  rfl

#guard ((ephU32leFn 0 []).body.flatten 0).length = 11

theorem ephU32leFn_spec (p : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk p bs).wf) (base : Word) :
    (ephU32leFn p bs).Spec base := by
  simpa [ephU32leFn, SgLoadU32leSAsm.sgLoadU32leFn] using
    SgLoadU32leSAsm.sgLoadU32leFn_spec p bs hwf base


end EphU32leSAsm
end EvmAsm.Codegen
