/-
  EvmAsm.Evm64.DivMod.Spec.N3V5NormVShapeFacts

  `fullDivN3NormV_shape_facts`: the normalized n=3 divisor shape facts bundle —
  the leading limb is `≥ 2^63` (msb set) and the top limb is `0` (`v3 = 0`),
  from `b3 = 0`, `b2 ≠ 0`, and `shift_nz`.  n3 mirror of
  `fullDivN2NormV_shape_facts`, packaging the existing
  `fullDivN3NormV_msb_of_b2_ne_zero` / `fullDivN3NormV_top_zero_of_shape_shift_nz`
  (DivN3NormVStructure).  Consumed by the n=3 carry-from-shape / from-shape
  assembly (bead 9.3.3.3).
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN3NormVStructure

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The normalized n=3 divisor `(fullDivN3NormV b0 b1 b2 b3)` has leading limb
    `≥ 2^63` and top limb `0`. -/
theorem fullDivN3NormV_shape_facts (b0 b1 b2 b3 : Word)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0) (hshift_nz : (clzResult b2).1 ≠ 0) :
    2 ^ 63 ≤ (fullDivN3NormV b0 b1 b2 b3).2.2.1.toNat ∧
    (fullDivN3NormV b0 b1 b2 b3).2.2.2 = 0 :=
  ⟨fullDivN3NormV_msb_of_b2_ne_zero b0 b1 b2 b3 hb2nz,
   fullDivN3NormV_top_zero_of_shape_shift_nz b0 b1 b2 b3 hb3z hshift_nz⟩

end EvmAsm.Evm64
