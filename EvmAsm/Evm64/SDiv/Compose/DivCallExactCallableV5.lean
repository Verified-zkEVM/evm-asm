/-
  EvmAsm.Evm64.SDiv.Compose.DivCallExactCallableV5

  v5 SDIV wrapper: lift the M2 x9-owned callable spec
  (`evm_div_callable_v5_stack_spec_within_x9owned`) onto the `sdivCodeV5` code
  surface, framed by an arbitrary PC-free `F`.  Mirror of the v4
  `evm_div_callable_v4_preserving_x1_x9out_exact_pre_divCode_body_framed_spec_in_sdivCodeV4`,
  but the post carries `regOwn .x9` (already shed by M2) plus the `sp+3936`
  div128-scratch cell (`memOwn`) instead of an exact `(.x9 ↦ x9Out)`.

  Step 1 of the SDIV `.proven` flip over `evm_div_callable_v5`.
-/

import EvmAsm.Evm64.SDiv.Compose.CodeHandlesV5
import EvmAsm.Evm64.DivMod.Compose.DivCallableV5Assembly

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- v5 SDIV wrapper: M2's x9-owned callable spec framed by `F` and lifted onto
    `sdivCodeV5` (the embedded `evm_div_callable_v5` at `wrapperEndOff`).  x9 is
    already owned in the post and the `sp+3936` scratch cell rides through. -/
theorem evm_div_callable_v5_x9owned_framed_spec_in_sdivCodeV5
    {F : Assertion} [Assertion.PCFree F]
    (sp base x9In raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : (((base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) +
        signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + wrapperEndOff) + EvmAsm.Evm64.div128CallRetOff) :
    cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV5 base)
      ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem)) ** F)
      ((EvmAsm.Evm64.divStackDispatchPostCallableX9Owned sp a b raVal **
        memOwn (sp + signExtend12 3936)) ** F) := by
  exact cpsTripleWithin_extend_code
    (hmono := evm_div_callable_code_v5_sub_sdivCodeV5 (base := base))
    (cpsTripleWithin_frameR F (by pcFree)
      (EvmAsm.Evm64.evm_div_callable_v5_stack_spec_within_x9owned
        sp (base + wrapperEndOff) a b x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign))

end EvmAsm.Evm64.SDiv.Compose
