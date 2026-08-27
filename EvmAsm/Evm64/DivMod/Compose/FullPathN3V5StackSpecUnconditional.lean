/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5StackSpecUnconditional

  The n=3 v5 DIV lane in the canonical shape-predicate (`N3ShapeIs`) form: the
  bead-`9.3.3` deliverable `evm_div_n3_stack_spec_unconditional`.  Repackages the
  complete n=3 lane `evm_div_n3_lane_v5` (#7565) — which takes the raw shape facts
  `b.getLimbN 3 = 0` and `b.getLimbN 2 ≠ 0` — under the named `N3ShapeIs` predicate,
  so it can be slotted directly into the 5-lane DIV scaffold's `lane_n3` hook
  (`UnconditionalScaffoldV5Div`).  n=3 analog of the n=2 `_complete` lane.
  Bead `evm-asm-wbc4i.9.3.3`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5Lane
public import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The complete v5 n=3 DIV lane, under the named `N3ShapeIs` predicate. -/
theorem evm_div_n3_stack_spec_unconditional (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hshape : N3ShapeIs b)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) :=
  evm_div_n3_lane_v5 sp base a b raVal v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hshape.2.1 hshape.2.2 halign

end EvmAsm.Evm64
