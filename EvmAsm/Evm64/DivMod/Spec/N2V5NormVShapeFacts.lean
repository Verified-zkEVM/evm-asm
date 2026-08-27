/-
  EvmAsm.Evm64.DivMod.Spec.N2V5NormVShapeFacts

  Bundled n=2 normalized-divisor shape facts: from the n=2 shape (`b2 = 0`,
  `b3 = 0`, `b1 ≠ 0`, `shift ≠ 0`), the normalized divisor `fullDivN2NormV` has
  its top limb MSB set (`≥ 2^63`) and its two high limbs zero (`v2 = v3 = 0`).
  These are the `hv1_norm`/`v2=0`/`v3=0` facts the per-digit carry discharges
  (#7454/#7455) and the validity telescope repeatedly consume when discharging
  `loopN2SelectedBorrowCarryV5` from shape at the lane level.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN2NormVStructure

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The three normalized-divisor facts for the n=2 lane, bundled. -/
theorem fullDivN2NormV_shape_facts (b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hb1nz : b1 ≠ 0) (hshift_nz : (clzResult b1).1 ≠ 0) :
    2 ^ 63 ≤ (fullDivN2NormV b0 b1 b2 b3).2.1.toNat ∧
    (fullDivN2NormV b0 b1 b2 b3).2.2.1 = 0 ∧
    (fullDivN2NormV b0 b1 b2 b3).2.2.2 = 0 :=
  ⟨fullDivN2NormV_msb_of_b1_ne_zero b0 b1 b2 b3 hb1nz,
   fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz,
   fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z⟩

end EvmAsm.Evm64
