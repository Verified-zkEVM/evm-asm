/-
  EvmAsm.Evm64.DivMod.Spec.BzeroPublicPost

  Per-lane unconditional bzero wrapper at the public dispatch-post surface.

  Composes:
    • `evm_div_stack_spec_bzero_noNop_v4_preNoX1_callableExactFrame`
      (callable-frame post from b = 0).
    • `divStackDispatchPostCallableExactFrame_weaken`
      (callable-frame → public dispatch-post).

  Yields a clean per-lane theorem `evm_div_stack_spec_bzero_dispatchPost`
  with only `b = 0` as a public hypothesis and the public
  `divStackDispatchPost` as postcondition.  This is the bzero component
  of the final 5-way `DivisorLimbCase` assembly at bead 7.1.7.2.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.BzeroV4ExactFrame
public import EvmAsm.Evm64.DivMod.Spec.StackPostBridge

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bzero lane wrapper at the public dispatch-post surface. -/
theorem evm_div_stack_spec_bzero_dispatchPost
    (sp base : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff)
      (sharedDivModCodeNoNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) :=
  cpsTripleWithin_weaken
    (fun _ hp => hp)
    (divStackDispatchPostCallableExactFrame_weaken sp a b raVal x9Val)
    (evm_div_stack_spec_bzero_noNop_v4_preNoX1_callableExactFrame
      sp base a b x9Val raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz)

end EvmAsm.Evm64
