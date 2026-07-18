/-
  EvmAsm.Evm64.DivMod.Spec.N3V5QuotientLaneShapeMod

  Lane-ready (`a b : EvmWord`) form of the n=3 v5 MOD remainder-word correctness
  FROM SHAPE: `fullModN3RemainderWordV5 … = EvmWord.mod a b`, from the n=3 divisor
  shape (`b3=0`, `b2≠0`, shift≠0) and the per-digit `bltu` path matches.  Bridges
  the `fromLimbs`-form `fullModN3RemainderWordV5_eq_mod_of_shape` to the `a b` form
  via `EvmWord.fromLimbs_match_getLimbN_id`.  This is the shape-derived remainder
  correctness the n=3 lane feeds to its post-bridge.  n=3 analog of
  `fullModN2RemainderWordV5_eq_mod_lane_of_shape` (N2V5QuotientLaneShapeMod).
-/

import EvmAsm.Evm64.DivMod.Spec.N3V5RemainderShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Lane form from shape: the assembled v5 n=3 remainder word equals `EvmWord.mod a b`. -/
theorem fullModN3RemainderWordV5_eq_mod_lane_of_shape
    (bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    fullModN3RemainderWordV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b := by
  have hraw := fullModN3RemainderWordV5_eq_mod_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_1 bltu_0 hb3z hshift_nz hb2nz hc1 hm1 hc0 hm0
  subst a0; subst a1; subst a2; subst a3; subst b0; subst b1; subst b2; subst b3
  refine hraw.trans ?_
  congr 1
  · exact EvmWord.fromLimbs_match_getLimbN_id a
  · exact EvmWord.fromLimbs_match_getLimbN_id b

end EvmAsm.Evm64
