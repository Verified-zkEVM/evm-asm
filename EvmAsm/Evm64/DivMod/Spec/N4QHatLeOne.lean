/-
  EvmAsm.Evm64.DivMod.Spec.N4QHatLeOne

  Under `U4 = 0`, the n=4 call trial quotient is at most 1, hence overestimates the
  normalized-window quotient by at most 1 (the `+1` `hq_over` the n=4 v5 semantic
  `n4CallAddbackBeqSemanticHoldsV5_of_runtime_conditions_legacy` takes — tighter
  than the `+2` of #7574).

  `qHat = div128Quot_v5 U4 U3 B3' = (U4·2^64 + U3) / B3'` exactly (`#7218`,
  `divKTrialCallV5QHat_eq_floor`); with `U4 = 0` this is `U3 / B3'`, and since
  `U3 < 2^64 ≤ 2·B3'` (B3' ≥ 2^63 normalized), the floor is ≤ 1.  No div128 phase
  internals are needed — just the proven floor characterization + arithmetic.
  Bead `evm-asm-wbc4i.8.2.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeV5
import EvmAsm.Evm64.EvmWordArith.DivV5TrialOverestimate

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Under `U4 = 0`, the n=4 call trial quotient is at most 1. -/
theorem n4CallAddbackBeqQHatV5_le_one_of_u4_zero {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hu4 : (n4CallAddbackBeqU4 a b).toNat = 0) :
    (n4CallAddbackBeqQHatV5 a b).toNat ≤ 1 := by
  have hB3 : (n4CallAddbackBeqB3Prime b).toNat ≥ 2 ^ 63 :=
    n4CallAddbackBeqB3Prime_ge_pow63 hb3nz
  have hU3 : (n4CallAddbackBeqU3 a b).toNat < 2 ^ 64 := (n4CallAddbackBeqU3 a b).isLt
  rw [n4CallAddbackBeqQHatV5_eq_normalized, ← divKTrialCallV5QHat_eq_div128Quot_v5,
    divKTrialCallV5QHat_eq_floor _ _ _ hB3 (by omega), hu4, Nat.zero_mul, Nat.zero_add]
  apply Nat.lt_succ_iff.mp
  rw [Nat.div_lt_iff_lt_mul (by omega : 0 < (n4CallAddbackBeqB3Prime b).toNat)]
  omega

/-- Under `U4 = 0`, the n=4 call trial quotient overestimates the normalized-window
    quotient by at most 1 — the `+1` `hq_over` of the n=4 v5 semantic. -/
theorem n4CallAddbackBeqQHatV5_le_window_div_plus_one_of_u4_zero {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hu4 : (n4CallAddbackBeqU4 a b).toNat = 0) :
    (n4CallAddbackBeqQHatV5 a b).toNat ≤
      EvmWord.val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) /
      EvmWord.val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) + 1 := by
  have h := n4CallAddbackBeqQHatV5_le_one_of_u4_zero hb3nz hu4
  exact Nat.le_trans h (Nat.le_add_left 1 _)

end EvmAsm.Evm64
