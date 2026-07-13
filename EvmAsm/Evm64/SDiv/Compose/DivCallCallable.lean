/-
  EvmAsm.Evm64.SDiv.Compose.DivCallCallable

  Embedding helpers for the appended unsigned `evm_div_callable` body inside
  the full SDIV code region.
-/

import EvmAsm.Evm64.DivMod.CallableV1Legacy
import EvmAsm.Evm64.DivMod.CallableV4Div
import EvmAsm.Evm64.SDiv.Compose.Base
import EvmAsm.Evm64.SDiv.Compose.SDivViewChainC

namespace EvmAsm.Evm64.SDiv.Compose

theorem evm_div_callable_code_v4_sub_sdivCodeV4 {base : Word} :
    ∀ a i,
      (EvmAsm.Evm64.evm_div_callable_code_v4 (base + wrapperEndOff)) a = some i →
      (sdivCodeV4 base) a = some i := by
  intro a i h
  have hOfProg :
      (EvmAsm.Rv64.CodeReq.ofProg
        (base + wrapperEndOff) EvmAsm.Evm64.evm_div_callable_v4) a =
        some i := by
    rw [← EvmAsm.Evm64.evm_div_callable_code_v4_eq_ofProg (base + wrapperEndOff)]
    exact h
  exact sdivCodeV4_divCallable_sub (base := base) a i
    (by
      simpa [divCallableCodeV4] using hOfProg)

theorem evm_div_callable_preserving_x1_spec_in_sdivCodeV4
    (sp base raVal : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : EvmAsm.Evm64.DivStackSpecCase (base + wrapperEndOff) a b)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) := by
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code
    (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base))
    (EvmAsm.Evm64.evm_div_callable_v4_spec_from_noNop_preserving_x1
      sp (base + wrapperEndOff) raVal a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)

end EvmAsm.Evm64.SDiv.Compose
