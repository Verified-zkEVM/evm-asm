/-
  EvmAsm.Evm64.DivMod.Spec.DivisorShapeLimbProjections

  Per-limb projection lemmas extracting the individual `getLimbN` facts
  from each `NkShapeIs` predicate.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace N1ShapeIs

theorem b3_eq_zero {b : EvmWord} (h : N1ShapeIs b) : b.getLimbN 3 = 0 := h.2.1
theorem b2_eq_zero {b : EvmWord} (h : N1ShapeIs b) : b.getLimbN 2 = 0 := h.2.2.1
theorem b1_eq_zero {b : EvmWord} (h : N1ShapeIs b) : b.getLimbN 1 = 0 := h.2.2.2.1
theorem b0_ne_zero {b : EvmWord} (h : N1ShapeIs b) : b.getLimbN 0 ≠ 0 := h.2.2.2.2

end N1ShapeIs

namespace N2ShapeIs

theorem b3_eq_zero {b : EvmWord} (h : N2ShapeIs b) : b.getLimbN 3 = 0 := h.2.1
theorem b2_eq_zero {b : EvmWord} (h : N2ShapeIs b) : b.getLimbN 2 = 0 := h.2.2.1
theorem b1_ne_zero {b : EvmWord} (h : N2ShapeIs b) : b.getLimbN 1 ≠ 0 := h.2.2.2

end N2ShapeIs

namespace N3ShapeIs

theorem b3_eq_zero {b : EvmWord} (h : N3ShapeIs b) : b.getLimbN 3 = 0 := h.2.1
theorem b2_ne_zero {b : EvmWord} (h : N3ShapeIs b) : b.getLimbN 2 ≠ 0 := h.2.2

end N3ShapeIs

namespace N4ShapeIs

theorem b3_ne_zero {b : EvmWord} (h : N4ShapeIs b) : b.getLimbN 3 ≠ 0 := h.2

end N4ShapeIs

end EvmAsm.Evm64
