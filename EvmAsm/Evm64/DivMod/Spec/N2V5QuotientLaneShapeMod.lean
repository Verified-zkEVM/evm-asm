/-
  EvmAsm.Evm64.DivMod.Spec.N2V5QuotientLaneShapeMod

  Lane-ready (`a b : EvmWord`) form of the n=2 v5 quotient-word correctness
  FROM SHAPE: `fullModN2RemainderWordV5 … = EvmWord.mod a b`, from the n=2 divisor
  shape (`b2=b3=0`, `b1≠0`, shift≠0) and the per-digit `bltu` path matches.
  Bridges the `fromLimbs`-form `fullModN2RemainderWordV5_eq_mod_of_shape` to the
  `a b` form via `EvmWord.fromLimbs_match_getLimbN_id`.  This is the shape-derived
  `hdivWord` the n=2 lane feeds to
  `fullDivN2UnifiedPostNoX1V5_to_divStackDispatchPostV5` (#7464) — the
  shape-counterpart of the `hmulsub`/`hge`-form `fullModN2RemainderWordV5_eq_mod_lane`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5ModRemainder
import EvmAsm.Evm64.DivMod.Spec.N2V5QuotientShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Lane form from shape: the assembled v5 n=2 quotient word equals `EvmWord.mod a b`. -/
theorem fullModN2RemainderWordV5_eq_mod_lane_of_shape
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true → BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc1 : bltu_1 = true → BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc0 : bltu_0 = true → BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    fullModN2RemainderWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b := by
  have hraw := fullModN2RemainderWordV5_eq_mod_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 bltu_0
    hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0
  subst a0; subst a1; subst a2; subst a3; subst b0; subst b1; subst b2; subst b3
  refine hraw.trans ?_
  congr 1
  · exact EvmWord.fromLimbs_match_getLimbN_id a
  · exact EvmWord.fromLimbs_match_getLimbN_id b

end EvmAsm.Evm64
