/-
  EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5DivCallable

  Callable-ExactFrame twin of `evm_div_stack_spec_unconditional_of_lanes_v5_div`:
  the same `DivisorLimbCase.elim_named` five-way divisor dispatch over
  `divCode_noNop_v5`, but every lane (and the combined result) lands the CALLABLE
  exact-frame post `divStackDispatchPostCallableExactFrame sp a b raVal x9Out **
  memOwn (sp+3936)` (caller return address `x1 = raVal` kept concrete) instead of
  the ownership post `divStackDispatchPostV5`.  Combinator toward
  `evm_div_callable_v5`: feed the per-shape callable ExactFrame lanes
  (`evm_div_{bzero,n1,n2,n3,n4}_..._callableExactFrame...`) and get the
  full-divisor callable body triple, which the layer-1 adapter
  (`CallableV5Div`) turns into the callable spec over `evm_div_callable_code_v5`.

  The incoming `x9In` is a free parameter (the div body reads no preamble program's
  `.x9` — it is framed unread until `divK_loopSetup`'s `ADDI .x9 .x0 4` overwrites
  it), split from the body-clobbered `x9Out`.  This is what lets the caller
  (SDIV/SMOD) supply an arbitrary incoming `x9` (e.g. `sdivAbsSign …`) while the
  lanes still land the concrete post value.
-/

import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div
import EvmAsm.Evm64.DivMod.Spec.CallablePost

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Callable-ExactFrame v5 DIV unconditional spec from the five divisor-shape
    lanes, over `divCode_noNop_v5`, landing the callable exact-frame post
    (`x1 = raVal` concrete) plus the `sp+3936` div128-scratch cell.

    Uses SEPARATE `x9In` (incoming, framed unread by the div body) and `x9Out`
    (the body-clobbered final value): pre-x9 = post-x9 would be forced by a single
    slot, which the honest v5 lanes (pre-x9 incoming/dead, post-x9 =
    `signExtend12 4095` after `loopSetup`) can never satisfy.  This is the shape
    the scratch adapter
    (`evm_div_callable_v5_spec_from_noNop_exact_frame_scratch`) consumes.  The
    `DivisorLimbCase.elim_named` dispatch is agnostic to both x9 slots. -/
theorem evm_div_stack_spec_unconditional_of_lanes_v5_div_callableExact
    (sp base : Word) (a b : EvmWord)
    (x9In x9Out raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (lane_bzero : b = 0 →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableExactFrame sp a b raVal x9Out **
         memOwn (sp + signExtend12 3936)))
    (lane_n1 : N1ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableExactFrame sp a b raVal x9Out **
         memOwn (sp + signExtend12 3936)))
    (lane_n2 : N2ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableExactFrame sp a b raVal x9Out **
         memOwn (sp + signExtend12 3936)))
    (lane_n3 : N3ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableExactFrame sp a b raVal x9Out **
         memOwn (sp + signExtend12 3936)))
    (lane_n4 : N4ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableExactFrame sp a b raVal x9Out **
         memOwn (sp + signExtend12 3936))) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal x9Out **
       memOwn (sp + signExtend12 3936)) := by
  refine DivisorLimbCase.elim_named
    (P := fun b' => cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b' x9In raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b' raVal x9Out **
       memOwn (sp + signExtend12 3936)))
    b ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero => exact lane_bzero
  case n1 => exact lane_n1
  case n2 => exact lane_n2
  case n3 => exact lane_n3
  case n4 => exact lane_n4

end EvmAsm.Evm64
