/-
  EvmAsm.Evm64.DivMod.Spec.BzeroV4ExactFrame

  Branch-certificate-free v4 exact-frame zero-divisor DIV wrappers.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v4 zero-divisor branch of the no-NOP DIV dispatcher exposed through the
    named exact-frame callable postcondition. -/
theorem evm_div_stack_spec_bzero_noNop_v4_preNoX1_callableExactFrame
    (sp base : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostCallableExactFrame sp a b raVal x9Val) := by
  rw [divStackDispatchPostCallableExactFrame_unfold]
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (divConcretePostNoX1_weaken_callable_frame
      sp a b (x9Val := x9Val) (raVal := raVal) (v2 := v2)
      (v6 := v6) (v7 := v7) (v11 := v11)
      (q0 := q0) (q1 := q1) (q2 := q2) (q3 := q3)
      (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
      (u4 := u4) (u5 := u5) (u6 := u6) (u7 := u7)
      (shiftMem := shiftMem) (nMem := nMem) (jMem := jMem)
      (retMem := retMem) (dMem := dMem) (dloMem := dloMem)
      (scratch_un0 := scratch_un0))
    (evm_div_bzero_stack_spec_within_dispatch_noNop_v4_concrete_callable_uni
      sp base a b x9Val raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz)

end EvmAsm.Evm64
