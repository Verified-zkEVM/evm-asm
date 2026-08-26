/-
  EvmAsm.Evm64.DivMod.CallableBzeroV4

  Split v4 zero-divisor callable wrappers for DIV.
-/

module

public import EvmAsm.Evm64.DivMod.CallableV4Div

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v4 zero-divisor DIV callable wrapper in the concrete post shape used by
    SDIV branch handoffs before weakening to the public callable postcondition. -/
theorem evm_div_callable_bzero_v4_concrete_preserving_x1_spec
    (sp base x9Val raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  exact
    evm_div_callable_v4_spec_from_noNop_concrete_preserving_x1_x9
      sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (evm_div_bzero_stack_spec_within_dispatch_noNop_v4_concrete_callable_uni
        sp base a b x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz)

/-- v4 zero-divisor DIV callable wrapper that preserves exact `x1` for return
    and exact `x9` as caller-framed state. -/
theorem evm_div_callable_bzero_v4_preserving_x1_spec (sp base x9Val raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (divConcretePostNoX1_weaken_callable_frame sp a b)
    (evm_div_callable_bzero_v4_concrete_preserving_x1_spec
      sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz)

/-- Framed variant of `evm_div_callable_bzero_v4_preserving_x1_spec`. -/
theorem evm_div_callable_bzero_v4_preserving_x1_framed_spec
    {F : Assertion} [Assertion.PCFree F] (sp base x9Val raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      (((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_bzero_v4_preserving_x1_spec
        sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz)

/-- v4 zero-divisor DIV callable wrapper with exact `x1` and no `x9` frame. -/
theorem evm_div_callable_bzero_v4_preserving_x1_noX9_spec (sp base raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  exact
    evm_div_callable_v4_spec_from_noNop_preserving_x1_noX9
      sp base raVal a b v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (evm_div_bzero_stack_spec_within_dispatch_noNop_v4_callable_x1_uni
        sp base a b raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz)

end EvmAsm.Evm64
