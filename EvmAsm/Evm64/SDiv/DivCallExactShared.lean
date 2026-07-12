/- Shared declaration home for the exact SDIV callable, return, and zero-divisor handoff chain. -/

import EvmAsm.Evm64.SDiv.DivCallHandoffChainShared
import EvmAsm.Evm64.DivMod.CallableV1Legacy
import EvmAsm.Evm64.DivMod.CallableV4Div
import EvmAsm.Evm64.SDiv.Compose.DivCallFramedCallable
import EvmAsm.Evm64.SDiv.DivCallHandoffChainShared
import EvmAsm.Evm64.SDiv.Compose.DispatchStackViews
import EvmAsm.Evm64.SDiv.Compose.BzeroCallablePost
import EvmAsm.Evm64.SDiv.Compose.DispatchReadyPost
import EvmAsm.Evm64.DivMod.CallableBzeroV4

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

/-- v4 variant of the preserving-`x1` unsigned-DIV callable wrapper whose
    no-NOP body proof already has the exact caller return address in the
    dispatch precondition. -/
theorem evm_div_callable_v4_preserving_x1_exact_pre_spec_in_sdivCodeV4
    (sp base x9Val raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hStackCallDiv :=
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := EvmAsm.Evm64.sharedDivModCodeNoNop_v4_sub_div_callable_code_v4)
      hStack
  have hStackCall :=
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base))
      hStackCallDiv
  have hRetDiv :=
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := EvmAsm.Evm64.evm_div_callable_code_v4_ret_sub
        (base := base + wrapperEndOff))
      (EvmAsm.Evm64.ret_spec_within' ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff) raVal)
  have hRet :=
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base))
      hRetDiv
  have hRetFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameL
      (EvmAsm.Evm64.divStackDispatchPostCallable sp a b)
      (EvmAsm.Evm64.divStackDispatchPostCallable_pcFree sp a b)
      hRet
  exact EvmAsm.Rv64.cpsTripleWithin_seq_same_cr hStackCall hRetFramed

/-- v4 variant of
    `evm_div_callable_preserving_x1_x9_exact_pre_spec_in_sdivCode`. -/
theorem evm_div_callable_v4_preserving_x1_x9_exact_pre_spec_in_sdivCodeV4
    (sp base x9Val raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Val))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base))
      (EvmAsm.Evm64.evm_div_callable_v4_spec_from_noNop_preserving_x1_x9
        sp (base + wrapperEndOff) x9Val raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)

/-- v4 embedded DIV callable wrapper with the named exact caller-frame post. -/
theorem evm_div_callable_v4_exact_frame_spec_in_sdivCodeV4
    (sp base x9Val raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallableExactFrame sp a b raVal x9Val)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (EvmAsm.Evm64.divStackDispatchPostCallableExactFrame sp a b raVal x9Val) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base))
      (EvmAsm.Evm64.evm_div_callable_v4_spec_from_noNop_exact_frame
        sp (base + wrapperEndOff) x9Val raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)

/-- v4 branch-certificate specialization of
    `evm_div_callable_preserving_x1_exact_pre_spec_in_sdivCode`.

    The dispatcher precondition uses the exact return value described by
    `DivStackSpecCase.returnX1`, while the CLZ/shift register comes from the
    branch certificate's `x2` selector. -/
theorem evm_div_callable_v4_preserving_branch_return_x1_spec_in_sdivCodeV4
    (sp base : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : EvmAsm.Evm64.DivStackSpecCase (base + wrapperEndOff) a b)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp a b
          branch.returnX1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b **
          (.x1 ↦ᵣ branch.returnX1))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (branch.returnX1 &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPre sp a b
        branch.returnX1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b **
        (.x1 ↦ᵣ branch.returnX1)) := by
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code
    (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base))
    (EvmAsm.Evm64.evm_div_callable_v4_spec_from_noNop_branch_return_x1
      sp (base + wrapperEndOff) a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)

/-- Framed variant of
    `evm_div_callable_v4_preserving_branch_return_x1_spec_in_sdivCodeV4`. -/
theorem evm_div_callable_v4_preserving_branch_return_x1_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (sp base : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : EvmAsm.Evm64.DivStackSpecCase (base + wrapperEndOff) a b)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPre sp a b
          branch.returnX1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b **
          (.x1 ↦ᵣ branch.returnX1))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (branch.returnX1 &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPre sp a b
        branch.returnX1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b **
        (.x1 ↦ᵣ branch.returnX1)) ** F) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_v4_preserving_branch_return_x1_spec_in_sdivCodeV4
        sp base a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)

/-- v4 framed variant of
    `evm_div_callable_v4_preserving_x1_exact_pre_spec_in_sdivCodeV4`. -/
theorem evm_div_callable_v4_preserving_x1_exact_pre_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (sp base x9Val raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) ** F) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_v4_preserving_x1_exact_pre_spec_in_sdivCodeV4
        sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)

/-- v4 framed variant of
    `evm_div_callable_v4_preserving_x1_x9_exact_pre_spec_in_sdivCodeV4`. -/
theorem evm_div_callable_v4_preserving_x1_x9_exact_pre_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (sp base x9Val raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Val))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) ** F) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_v4_preserving_x1_x9_exact_pre_spec_in_sdivCodeV4
        sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)

/-- Framed v4 embedded DIV callable wrapper with the named exact caller-frame
    post. -/
theorem evm_div_callable_v4_exact_frame_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (sp base x9Val raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallableExactFrame sp a b raVal x9Val)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (EvmAsm.Evm64.divStackDispatchPostCallableExactFrame sp a b raVal x9Val ** F) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_v4_exact_frame_spec_in_sdivCodeV4
        sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)

/-- v4 SDIV wrapper for exact-pre unsigned-DIV body proofs that already carry
    an explicit PC-free frame through the no-NOP body. -/
theorem evm_div_callable_v4_preserving_x1_x9_exact_pre_body_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (sp base x9Val raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Val)) ** F)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) ** F) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base))
      (EvmAsm.Evm64.evm_div_callable_v4_spec_from_noNop_preserving_x1_x9_body_framed
        sp (base + wrapperEndOff) x9Val raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)

/-- v4 SDIV wrapper for exact-pre unsigned-DIV body proofs that already carry
    an explicit PC-free frame and return a possibly different exact x9 value. -/
theorem evm_div_callable_v4_preserving_x1_x9out_exact_pre_body_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (sp base x9In x9Out raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
          x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Out)) ** F)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Out)) ** F) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base))
      (EvmAsm.Evm64.evm_div_callable_v4_spec_from_noNop_preserving_x1_x9out_body_framed
        sp (base + wrapperEndOff) x9In x9Out raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)

/-- v4 SDIV wrapper for full `divCode_noNop_v4` body proofs that already
    carry an explicit PC-free frame and return a possibly different exact x9. -/
theorem evm_div_callable_v4_preserving_x1_x9out_exact_pre_divCode_body_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (sp base x9In x9Out raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
          x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Out)) ** F)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Out)) ** F) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base))
      (EvmAsm.Evm64.evm_div_callable_v4_spec_from_divCode_noNop_preserving_x1_x9out_body_framed
        sp (base + wrapperEndOff) x9In x9Out raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)

/-- v4 embedded DIV callable wrapper for full `divCode_noNop_v4` body proofs
    that transform an explicit frame. -/
theorem evm_div_callable_v4_preserving_x1_x9out_exact_pre_divCode_body_frame_transform_spec_in_sdivCodeV4
    {FPre FPost : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree FPost]
    (sp base x9In x9Out raVal : Word) (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
          x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Out)) ** FPost)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (raVal &&& ~~~1) (sdivCodeV4 base)
      (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp a b
        x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
      (((EvmAsm.Evm64.divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Out)) ** FPost) := by
  exact
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base))
      (EvmAsm.Evm64.evm_div_callable_v4_spec_from_divCode_noNop_preserving_x1_x9out_body_frame_transform
        sp (base + wrapperEndOff) x9In x9Out raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack)


/-- v4 generic exact-`x1` callable handoff from the SDIV dispatch-ready bundle.
    The branch-specific obligation is the `sharedDivModCodeNoNop_v4` proof
    `hStack`, whose precondition already carries SDIV's exact return address
    in `x1`. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSign := sdivAbsSign divisorTop
  let divisorMask := sdivAbsMask divisorTop
  let divisorSum0 := sdivAbsSum0 divisorLimb0 divisorTop
  let divisorCarry0 := sdivAbsCarry0 divisorLimb0 divisorTop
  let divisorSum1 := sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop
  let divisorCarry1 := sdivAbsCarry1 divisorLimb0 divisorLimb1 divisorTop
  let divisorSum2 := sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry2 := sdivAbsCarry2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSum3 := sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 := sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let resultSign := sdivDivCallResultSign dividendTop divisorTop
  let signFrameNoX9 : EvmAsm.Rv64.Assertion :=
    (.x8 ↦ᵣ resultSign) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))
  have hCallableFramed :=
    evm_div_callable_v4_preserving_x1_exact_pre_framed_spec_in_sdivCodeV4
      (F := signFrameNoX9)
      sp base divisorSign ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by
        dsimp [dividendAbsWord, divisorAbsWord, divisorSum3, divisorMask,
          divisorCarry3] at hStack ⊢
        exact hStack)
  have hCallableExit :
      EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          signFrameNoX9)
        ((EvmAsm.Evm64.divStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          signFrameNoX9) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact hCallableFramed
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3, signFrameNoX9] at hp ⊢
    exact hp) (fun h hp => by
    rw [saveRaDivCallCallablePostNoX9_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign,
      signFrameNoX9, sdivDivCallResultSign, sdivAbsSign] at hp ⊢
    exact hp) hCallableExit

/-- v4 exact callable handoff for already-framed unsigned-DIV body proofs that
    return an exact `x9` value and carry an explicit PC-free frame. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 x9Out : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ x9Out)) ** F)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ x9Out)) ** F)) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSign := sdivAbsSign divisorTop
  let divisorMask := sdivAbsMask divisorTop
  let divisorSum0 := sdivAbsSum0 divisorLimb0 divisorTop
  let divisorCarry0 := sdivAbsCarry0 divisorLimb0 divisorTop
  let divisorSum1 := sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop
  let divisorCarry1 := sdivAbsCarry1 divisorLimb0 divisorLimb1 divisorTop
  let divisorSum2 := sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry2 := sdivAbsCarry2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSum3 := sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 := sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let resultSign := sdivDivCallResultSign dividendTop divisorTop
  let signFrameNoX9 : EvmAsm.Rv64.Assertion :=
    (.x8 ↦ᵣ resultSign) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))
  have hCallableFramed :=
    evm_div_callable_v4_preserving_x1_x9out_exact_pre_body_framed_spec_in_sdivCodeV4
      (F := signFrameNoX9 ** F)
      sp base divisorSign x9Out ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by
        dsimp [dividendAbsWord, divisorAbsWord, divisorSum3, divisorMask,
          divisorCarry3] at hStack ⊢
        exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
          xperm_hyp hp) (fun h hp => by
          xperm_hyp hp)
          (EvmAsm.Rv64.cpsTripleWithin_frameR signFrameNoX9 (by
            dsimp [signFrameNoX9]
            pcFree) hStack))
  have hCallableExit :
      EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask
          divisorCarry3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** signFrameNoX9) ** F)
        ((((EvmAsm.Evm64.divStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) ** signFrameNoX9) **
          (.x9 ↦ᵣ x9Out)) ** F) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
      xperm_hyp hp) (fun h hp => by
      xperm_hyp hp) hCallableFramed
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3, signFrameNoX9] at hp ⊢
    exact hp) (fun h hp => by
    rw [saveRaDivCallCallablePostNoX9_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign,
      signFrameNoX9, sdivDivCallResultSign, sdivAbsSign] at hp ⊢
    exact hp) hCallableExit

/-- v4 exact callable handoff for already-framed full `divCode_noNop_v4`
    unsigned-DIV body proofs that return an exact `x9` value. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 x9Out : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ x9Out)) ** F)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ x9Out)) ** F)) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSign := sdivAbsSign divisorTop
  let divisorMask := sdivAbsMask divisorTop
  let divisorSum0 := sdivAbsSum0 divisorLimb0 divisorTop
  let divisorCarry0 := sdivAbsCarry0 divisorLimb0 divisorTop
  let divisorSum1 := sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop
  let divisorCarry1 := sdivAbsCarry1 divisorLimb0 divisorLimb1 divisorTop
  let divisorSum2 := sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry2 := sdivAbsCarry2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSum3 := sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 := sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let resultSign := sdivDivCallResultSign dividendTop divisorTop
  let signFrameNoX9 : EvmAsm.Rv64.Assertion :=
    (.x8 ↦ᵣ resultSign) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))
  have hCallableFramed :=
    evm_div_callable_v4_preserving_x1_x9out_exact_pre_divCode_body_framed_spec_in_sdivCodeV4
      (F := signFrameNoX9 ** F)
      sp base divisorSign x9Out ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by
        dsimp [dividendAbsWord, divisorAbsWord, divisorSum3, divisorMask,
          divisorCarry3] at hStack ⊢
        exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
          xperm_hyp hp) (fun h hp => by
          xperm_hyp hp)
          (EvmAsm.Rv64.cpsTripleWithin_frameR signFrameNoX9 (by
            dsimp [signFrameNoX9]
            pcFree) hStack))
  have hCallableExit :
      EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask
          divisorCarry3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** signFrameNoX9) ** F)
        ((((EvmAsm.Evm64.divStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) ** signFrameNoX9) **
          (.x9 ↦ᵣ x9Out)) ** F) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
      xperm_hyp hp) (fun h hp => by
      xperm_hyp hp) hCallableFramed
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3, signFrameNoX9] at hp ⊢
    exact hp) (fun h hp => by
    rw [saveRaDivCallCallablePostNoX9_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign,
      signFrameNoX9, sdivDivCallResultSign, sdivAbsSign] at hp ⊢
    exact hp) hCallableExit

/-- v4 exact callable handoff for full `divCode_noNop_v4` unsigned-DIV body
    proofs that transform an explicit frame and return an exact `x9` value. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_frame_transform_spec_in_sdivCodeV4
    {FPre FPost : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree FPost]
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 x9Out : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ x9Out)) ** FPost)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** FPre)
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ x9Out)) ** FPost)) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSign := sdivAbsSign divisorTop
  let divisorMask := sdivAbsMask divisorTop
  let divisorSum0 := sdivAbsSum0 divisorLimb0 divisorTop
  let divisorCarry0 := sdivAbsCarry0 divisorLimb0 divisorTop
  let divisorSum1 := sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop
  let divisorCarry1 := sdivAbsCarry1 divisorLimb0 divisorLimb1 divisorTop
  let divisorSum2 := sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry2 := sdivAbsCarry2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSum3 := sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 := sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let resultSign := sdivDivCallResultSign dividendTop divisorTop
  let signFrameNoX9 : EvmAsm.Rv64.Assertion :=
    (.x8 ↦ᵣ resultSign) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))
  have hCallableFramed :=
    evm_div_callable_v4_preserving_x1_x9out_exact_pre_divCode_body_frame_transform_spec_in_sdivCodeV4
      (FPre := signFrameNoX9 ** FPre) (FPost := signFrameNoX9 ** FPost)
      sp base divisorSign x9Out ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by
        dsimp [dividendAbsWord, divisorAbsWord, divisorSum3, divisorMask,
          divisorCarry3] at hStack ⊢
        exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
          xperm_hyp hp) (fun h hp => by
          xperm_hyp hp)
          (EvmAsm.Rv64.cpsTripleWithin_frameR signFrameNoX9 (by
            dsimp [signFrameNoX9]
            pcFree) hStack))
  have hCallableExit :
      EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        ((EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask
          divisorCarry3 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** signFrameNoX9) ** FPre)
        ((((EvmAsm.Evm64.divStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) ** signFrameNoX9) **
          (.x9 ↦ᵣ x9Out)) ** FPost) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
      xperm_hyp hp) (fun h hp => by
      xperm_hyp hp) hCallableFramed
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3, signFrameNoX9] at hp ⊢
    exact hp) (fun h hp => by
    rw [saveRaDivCallCallablePostNoX9_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign,
      signFrameNoX9, sdivDivCallResultSign, sdivAbsSign] at hp ⊢
    exact hp) hCallableExit

/-- v4 exact callable handoff for full `divCode_noNop_v4` body proofs whose
    precondition has the N1-style zero `x9` value. This specializes the generic
    SDIV handoff to the branch where the saved divisor sign is zero. -/
theorem saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_zeroX9_framed_spec_in_sdivCodeV4
    {F : EvmAsm.Rv64.Assertion} [EvmAsm.Rv64.Assertion.PCFree F]
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 x9Out : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hdivisorSign :
      sdivAbsSign divisorTop = EvmAsm.Rv64.signExtend12 (4 : BitVec 12) - (4 : Word))
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.divCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (EvmAsm.Rv64.signExtend12 (4 : BitVec 12) - (4 : Word))
          ((base + divCallOff) + 4)
          v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
        (((EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ x9Out)) ** F)) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((saveRaDivCallCallablePostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
        (.x9 ↦ᵣ x9Out)) ** F)) := by
  apply saveRaDivCallDispatchReadyPost_exact_callable_x9out_divCode_framed_spec_in_sdivCodeV4
    (F := F) vRa sp base dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
    divisorLimb0 divisorLimb1 divisorLimb2 divisorTop v2 v5 v6 x9Out
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 hbase
  rwa [hdivisorSign]


/-- v4 exact SDIV path through result-sign-fix and the saved-RA return,
    specialized from the sidecar exact callable handoff. -/
theorem saveRa_signs_abs_signXor_then_divCall_exact_then_return_normalized_named_post_from_handoff_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallCallableReturnPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  have hExit :
      (((vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) +
        EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) =
        (vRa &&& ~~~(1 : Word)) := by
    rw [EvmAsm.Rv64.signExtend12_0]
    simp [BitVec.add_zero]
  rw [← hExit]
  exact
    saveRa_signs_abs_signXor_then_divCall_then_return_of_callable_post_noX9_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base
      (saveRaDivCallDispatchReadyPost_exact_callable_spec_in_sdivCodeV4
        vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 hbase hStack)

/-- v4 tail-framed exact SDIV path through result-sign-fix and the saved-RA
    return. This is the caller-stack companion of the limb-level exact
    handoff: the untouched stack tail is carried from `sp+64` through the
    callable and return sequence. -/
theorem saveRa_signs_abs_signXor_then_divCall_exact_then_return_stack_tail_from_handoff_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallCallableReturnPostNoX9 vRa sp base
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) **
       evmStackIs (sp + 64) rest) := by
  let scratchFrame : EvmAsm.Rv64.Assertion :=
    ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
     EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratchUn0)
  have hBase :=
    saveRa_signs_abs_signXor_then_divCall_exact_then_return_normalized_named_post_from_handoff_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3)
      (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3)
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack
  have hFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameR
      (evmStackIs (sp + 64) rest) pcFree_evmStackIs hBase
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
      have h_old :
          ((saveRaSignsAbsSignXorThenDivCallPre
              vRa vSavedOld sp sDividendOld sDivisorOld
              dividendMaskOld dividendValueOld dividendCarryOld
              (dividend.getLimbN 0) (dividend.getLimbN 1)
              (dividend.getLimbN 2) (dividend.getLimbN 3)
              (divisor.getLimbN 0) (divisor.getLimbN 1)
              (divisor.getLimbN 2) (divisor.getLimbN 3) **
            evmStackIs (sp + 64) rest) ** scratchFrame) h := by
        rw [saveRaSignsAbsSignXorThenDivCallPre_stack_pair_rest]
        dsimp [scratchFrame]
        exact hp
      dsimp [scratchFrame] at h_old
      xperm_hyp h_old) (fun _ hp => hp) hFramed

/-- v4 exact SDIV path through result-sign-fix and the saved-RA return, with
    the result slot folded as a single sign-fixed EVM word. -/
theorem saveRa_signs_abs_signXor_then_divCall_exact_then_return_sign_fixed_word_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsSign divisorTop) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (sdivAbsMask divisorTop)
          (sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallCallableReturnSignFixedWordPostNoX9 vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [saveRaDivCallCallableReturnPostNoX9_evmWordIs] at hp
      exact hp)
    (saveRa_signs_abs_signXor_then_divCall_exact_then_return_normalized_named_post_from_handoff_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)


/-- v4 version of the named zero-divisor callable handoff from the SDIV
    dispatch-ready bundle to the zero-divisor callable post. -/
theorem saveRaDivCallDispatchReadyPost_bzero_callable_spec_in_sdivCodeV4
    (vRa sp base
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
      (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaDivCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  let dividendAbsWord :=
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
  let divisorAbsWord :=
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSign := sdivAbsSign divisorTop
  let divisorMask := sdivAbsMask divisorTop
  let divisorSum0 := sdivAbsSum0 divisorLimb0 divisorTop
  let divisorCarry0 := sdivAbsCarry0 divisorLimb0 divisorTop
  let divisorSum1 := sdivAbsSum1 divisorLimb0 divisorLimb1 divisorTop
  let divisorCarry1 := sdivAbsCarry1 divisorLimb0 divisorLimb1 divisorTop
  let divisorSum2 := sdivAbsSum2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry2 := sdivAbsCarry2 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorSum3 := sdivAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let divisorCarry3 := sdivAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
  let resultSign := sdivDivCallResultSign dividendTop divisorTop
  let signFrameNoX9 : EvmAsm.Rv64.Assertion :=
    ((.x8 ↦ᵣ resultSign) **
      (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))
  have hCallableRaw :=
    EvmAsm.Evm64.evm_div_callable_bzero_v4_concrete_preserving_x1_spec
      sp (base + wrapperEndOff) divisorSign ((base + divCallOff) + 4)
      dividendAbsWord divisorAbsWord v2 v5 v6 divisorSum3 divisorMask divisorCarry3
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (by simpa [divisorAbsWord] using hbz)
  have hCallableCode :=
    EvmAsm.Rv64.cpsTripleWithin_extend_code
      (hmono := evm_div_callable_code_v4_sub_sdivCodeV4 (base := base)) hCallableRaw
  have hCallableFramed :=
    EvmAsm.Rv64.cpsTripleWithin_frameR signFrameNoX9 (by
      dsimp [signFrameNoX9]
      pcFree) hCallableCode
  have hCallableExit :
      EvmAsm.Rv64.cpsTripleWithin (EvmAsm.Evm64.unifiedDivBound + 1)
        (base + wrapperEndOff) (base + resultSignFixOff) (sdivCodeV4 base)
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
          signFrameNoX9)
        (EvmAsm.Evm64.divConcretePostNoX1Frame sp dividendAbsWord divisorAbsWord
          divisorSign ((base + divCallOff) + 4) v2 v6 divisorSum3 divisorCarry3
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** signFrameNoX9) := by
    rw [← divCall_return_andn_one_eq_resultSignFixOff base hbase]
    exact hCallableFramed
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun h hp => by
    rw [saveRaDivCallDispatchReadyPost_unfold] at hp
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, divisorMask, divisorSum0,
      divisorCarry0, divisorSum1, divisorCarry1, divisorSum2, divisorCarry2,
      divisorSum3, divisorCarry3, resultSign, saveRaDivCallSignFrame,
      sdivDivCallResultSign, sdivAbsSign, sdivAbsMask, sdivAbsSum0, sdivAbsCarry0,
      sdivAbsSum1, sdivAbsCarry1, sdivAbsSum2, sdivAbsCarry2, sdivAbsSum3,
      sdivAbsCarry3] at hp ⊢
    dsimp [signFrameNoX9] at hp ⊢
    exact hp) (fun h hp => by
    have hPublic :
        ((((EvmAsm.Evm64.divStackDispatchPostCallable sp dividendAbsWord divisorAbsWord **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
          (.x9 ↦ᵣ divisorSign)) ** signFrameNoX9) h) := by
      refine EvmAsm.Rv64.sepConj_mono ?_ ?_ h hp
      · intro hLeft hpLeft
        exact EvmAsm.Evm64.divConcretePostNoX1_weaken_callable_frame
          sp dividendAbsWord divisorAbsWord hLeft hpLeft
      · intro hRight hpRight
        exact hpRight
    rw [saveRaDivCallBzeroCallablePost_unfold]
    dsimp [dividendAbsWord, divisorAbsWord, divisorSign, resultSign, signFrameNoX9,
      saveRaDivCallSignFrame, sdivDivCallResultSign, sdivAbsSign] at hp hPublic ⊢
    xperm_hyp hPublic) hCallableExit


/-- v4 SDIV wrapper prefix followed by the zero-divisor unsigned-DIV callable,
    using the sidecar dispatch-ready handoff above. -/
theorem saveRa_signs_abs_signXor_then_divCall_bzero_callable_named_post_from_handoff_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    EvmAsm.Rv64.cpsTripleWithin (49 + (EvmAsm.Evm64.unifiedDivBound + 1))
      base (base + resultSignFixOff) (sdivCodeV4 base)
      (saveRaSignsAbsSignXorThenDivCallPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  exact
    saveRa_signs_abs_signXor_then_divCall_then_exact_callable_spec_in_sdivCodeV4
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0
      base (base + resultSignFixOff)
      (saveRaDivCallDispatchReadyPost_bzero_callable_spec_in_sdivCodeV4
        vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 hbase hbz)

end EvmAsm.Evm64.SDiv.Compose
