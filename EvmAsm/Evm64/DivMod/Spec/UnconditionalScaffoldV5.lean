/-
  EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5

  v5 structural 5-way `DivisorLimbCase` assembly for the unconditional DIV
  stack-spec over `sharedDivModCodeNoNop_v5`.  Mirror of
  `evm_div_stack_spec_unconditional_of_lanes` (UnconditionalScaffold), but over
  the v5 code surface and taking the bzero case as an explicit hypothesis (so it
  does not depend on a v5-specific bzero lemma yet).  Once the five v5 lane
  wrappers (bzero/N1/N2/N3/N4) exist, this instantiates to the v5 unconditional
  stack-spec.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.DivisorCasesNamedElim
public import EvmAsm.Evm64.DivMod.Spec.Dispatcher
public import EvmAsm.Evm64.DivMod.Compose.V5Code

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 structural 5-way DivisorLimbCase assembly: given the bzero case and the
    four per-lane unconditional wrappers (each at the public dispatch-post surface
    over `sharedDivModCodeNoNop_v5`), produces the unconditional DIV stack-spec by
    case-splitting on the divisor's shape. -/
theorem evm_div_stack_spec_unconditional_of_lanes_v5
    (sp base : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (lane_bzero : b = 0 →
      cpsTripleWithin unifiedDivBound base (base + nopOff)
        (sharedDivModCodeNoNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b))
    (lane_n1 : N1ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff)
        (sharedDivModCodeNoNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b))
    (lane_n2 : N2ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff)
        (sharedDivModCodeNoNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b))
    (lane_n3 : N3ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff)
        (sharedDivModCodeNoNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b))
    (lane_n4 : N4ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff)
        (sharedDivModCodeNoNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff)
      (sharedDivModCodeNoNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  refine DivisorLimbCase.elim_named
    (P := fun b' => cpsTripleWithin unifiedDivBound base (base + nopOff)
      (sharedDivModCodeNoNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b'
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b'))
    b ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero => exact lane_bzero
  case n1 => exact lane_n1
  case n2 => exact lane_n2
  case n3 => exact lane_n3
  case n4 => exact lane_n4

end EvmAsm.Evm64
