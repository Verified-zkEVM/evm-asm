/-
  EvmAsm.Evm64.DivMod.Spec.DivisorShapeToLimbCase

  Reverse projections from the named `NkShapeIs` predicates back to the
  inductive `DivisorLimbCase` form.
-/

import EvmAsm.Evm64.DivMod.Spec.UnifiedDivisorCases
import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

theorem N1ShapeIs.to_DivisorLimbCase {b : EvmWord} (h : N1ShapeIs b) :
    DivisorLimbCase b :=
  DivisorLimbCase.n1 h.1 ((EvmWord.ne_zero_iff_getLimbN_or).mp h.1)
    h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem N2ShapeIs.to_DivisorLimbCase {b : EvmWord} (h : N2ShapeIs b) :
    DivisorLimbCase b :=
  DivisorLimbCase.n2 h.1 ((EvmWord.ne_zero_iff_getLimbN_or).mp h.1)
    h.2.1 h.2.2.1 h.2.2.2

theorem N3ShapeIs.to_DivisorLimbCase {b : EvmWord} (h : N3ShapeIs b) :
    DivisorLimbCase b :=
  DivisorLimbCase.n3 h.1 ((EvmWord.ne_zero_iff_getLimbN_or).mp h.1)
    h.2.1 h.2.2

theorem N4ShapeIs.to_DivisorLimbCase {b : EvmWord} (h : N4ShapeIs b) :
    DivisorLimbCase b :=
  DivisorLimbCase.n4 h.1 ((EvmWord.ne_zero_iff_getLimbN_or).mp h.1)
    h.2

end EvmAsm.Evm64
