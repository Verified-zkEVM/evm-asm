/-
  EvmAsm.Evm64.SMod.Compose.ModCallExactCallableV5

  v5 SMOD wrapper: lift the M2 x9-owned mod callable spec
  (`evm_mod_callable_v5_stack_spec_within_x9owned`) onto the `smodCodeV5` code
  surface, framed by an arbitrary PC-free `F`.  Mirror of the SDIV
  `evm_div_callable_v5_x9owned_framed_spec_in_sdivCodeV5`.  Step 1 of the SMOD
  `.proven` flip over `evm_mod_callable_v5`.
-/

import EvmAsm.Evm64.SMod.Compose.CodeHandlesV5
import EvmAsm.Evm64.DivMod.Compose.ModCallableV5Assembly

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- v5 SMOD wrapper: M2's x9-owned mod callable spec framed by `F` and lifted
    onto `smodCodeV5` (the embedded `evm_mod_callable_v5` at `wrapperEndOff`).
    x9 is already owned in the post and the `sp+3936` scratch cell rides through. -/
theorem evm_mod_callable_v5_x9owned_framed_spec_in_smodCodeV5
    {F : Assertion} [Assertion.PCFree F]
    (sp base x9In raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (smodCodeV5 base)
      ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem)) ** F)
      ((EvmAsm.Evm64.modStackDispatchPostCallableX9Owned sp a b raVal **
        memOwn (sp + signExtend12 3936)) ** F) := by
  exact cpsTripleWithin_extend_code
    (hmono := evm_mod_callable_code_v5_sub_smodCodeV5 (base := base))
    (cpsTripleWithin_frameR F (by pcFree)
      (EvmAsm.Evm64.evm_mod_callable_v5_stack_spec_within_x9owned
        sp (base + wrapperEndOff) a b x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign))

end EvmAsm.Evm64.SMod.Compose
