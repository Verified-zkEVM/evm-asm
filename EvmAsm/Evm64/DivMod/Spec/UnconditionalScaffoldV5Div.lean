/-
  EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div

  The v5 DIV unconditional scaffold corrected for the actual v5 DIV code surface:
  over `divCode_noNop_v5` (which, unlike `sharedDivModCodeNoNop_v5`, contains the DIV
  epilogue block the DIV path executes), with the dispatch post carrying the extra
  `memOwn (sp+3936)` the v5 div128 loop owns (`divStackDispatchPostV5`) and the pre
  carrying the matching `sp+3936` scratch cell.  Same `DivisorLimbCase.elim_named`
  case-split as `evm_div_stack_spec_unconditional_of_lanes_v5`.  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5
public import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 DIV stack-dispatch post: the standard post plus the extra `sp+3936`
    div128-scratch cell the v5 loop owns. -/
def divStackDispatchPostV5 (sp : Word) (a b : EvmWord) : Assertion :=
  divStackDispatchPost sp a b ** memOwn (sp + signExtend12 3936)

/-- v5 DIV unconditional spec from the five divisor-shape lanes, over the actual
    DIV code surface `divCode_noNop_v5` with the v5 dispatch post. -/
theorem evm_div_stack_spec_unconditional_of_lanes_v5_div
    (sp base : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (lane_bzero : b = 0 →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostV5 sp a b))
    (lane_n1 : N1ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostV5 sp a b))
    (lane_n2 : N2ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostV5 sp a b))
    (lane_n3 : N3ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostV5 sp a b))
    (lane_n4 : N4ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostV5 sp a b)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  refine DivisorLimbCase.elim_named
    (P := fun b' => cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b' x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b'))
    b ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero => exact lane_bzero
  case n1 => exact lane_n1
  case n2 => exact lane_n2
  case n3 => exact lane_n3
  case n4 => exact lane_n4

end EvmAsm.Evm64
