/-
  EvmAsm.Evm64.SDiv.Compose.DivCallExactCallable

  Exact-`x1` unsigned-DIV callable wrappers used by the SDIV div-call
  postcondition sidecar proofs.
-/

import EvmAsm.Evm64.SDiv.DivCallHandoffShared
import EvmAsm.Evm64.DivMod.CallableV1Legacy
import EvmAsm.Evm64.DivMod.CallableV4Div

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

end EvmAsm.Evm64.SDiv.Compose
