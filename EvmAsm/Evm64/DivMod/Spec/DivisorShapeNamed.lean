/-
  EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

  Named per-lane shape predicates `NkShapeIs (b : EvmWord) : Prop` for k=1..4.
  Pairs with `divisor_full_domain_shape` (PR #6973) and `nonzero_divisor_limb_shape`
  (PR #6972) by giving downstream code consistent names for the four shape
  cases.
-/

module

public import EvmAsm.Evm64.Stack

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- N1 shape predicate: `b` is nonzero and only its lowest limb is nonzero. -/
abbrev N1ShapeIs (b : EvmWord) : Prop :=
  b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 = 0 ∧ b.getLimbN 1 = 0 ∧ b.getLimbN 0 ≠ 0

/-- N2 shape predicate: `b` is nonzero with limbs 2 and 3 zero, limb 1 nonzero. -/
abbrev N2ShapeIs (b : EvmWord) : Prop :=
  b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 = 0 ∧ b.getLimbN 1 ≠ 0

/-- N3 shape predicate: `b` is nonzero with limb 3 zero, limb 2 nonzero. -/
abbrev N3ShapeIs (b : EvmWord) : Prop :=
  b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 ≠ 0

/-- N4 shape predicate: `b` is nonzero with the top limb nonzero. -/
abbrev N4ShapeIs (b : EvmWord) : Prop :=
  b ≠ 0 ∧ b.getLimbN 3 ≠ 0

end EvmAsm.Evm64
