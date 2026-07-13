/-
  EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindow

  The abstract Knuth Theorem A floor inequality (the "trial does not
  underestimate" direction) and its v5 n=2 per-digit specialization.

  `knuth_a_floor_window_le` is the position-independent core extracted from the
  n=4 `val256_ratio_le_u_total_div_b3_prime` (CallSkipLowerBoundV2): for a
  normalized window where the divisor's value is at least its top part times the
  place value (`Vtop·K ≤ V`) and the dividend splits as `U = Utop·K + Ulow` with
  `Ulow < K`, the full quotient `U/V` is at most the top-window quotient
  `Utop/Vtop`.

  `n2_window_val256_div_le_trial_v5` instantiates it at the n=2 limb positions
  (divisor `(v0,v1,0,0)`, window `(u0,u1,u2,0)`, trial on `u2,u1,v1`) and chains
  the v5 trial lower bound `div128Quot_v5_ge_q_true` to give the per-digit
  no-underestimate `val256 u / val256 v ≤ divKTrialCallV5QHat u2 u1 v1` — the
  `hq_ge` input of `iterWithDoubleAddback_remainder_lt_of_plus_two` for the v5
  n=2 lane.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainD
import EvmAsm.Evm64.EvmWordArith.DivV5TrialOverestimate
import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **Abstract Knuth-A floor inequality.** For a normalized window — divisor
    value at least its top part times the place value (`Vtop·K ≤ V`) and dividend
    `U = Utop·K + Ulow` with `Ulow < K` — the full quotient is at most the
    top-window quotient.  Position-independent core of
    `val256_ratio_le_u_total_div_b3_prime`. -/
theorem knuth_a_floor_window_le {U V Utop Ulow Vtop K : Nat}
    (hV : Vtop * K ≤ V) (hVtop : 0 < Vtop) (hK : 0 < K)
    (hU : U = Utop * K + Ulow) (hUlow : Ulow < K) :
    U / V ≤ Utop / Vtop := by
  have hpos : 0 < Vtop * K := Nat.mul_pos hVtop hK
  calc U / V ≤ U / (Vtop * K) := Nat.div_le_div_left hV hpos
    _ = (Utop * K + Ulow) / (Vtop * K) := by rw [hU]
    _ = Utop / Vtop := nat_trunc_div_add_lt Utop Vtop K Ulow hK hVtop hUlow

/-- **v5 n=2 per-digit no-underestimate.** The full window quotient is at most
    the v5 trial quotient (which divides the top two window limbs `u2,u1` by the
    divisor's top limb `v1`).  Needs normalization (`v1 ≥ 2^63`) and the call
    regime (`u2 < v1`).  This is the `hq_ge` ingredient for the n=2 per-digit
    remainder bound. -/
theorem n2_window_val256_div_le_trial_v5
    (v0 v1 u0 u1 u2 : Word)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    val256 u0 u1 u2 0 / val256 v0 v1 0 0 ≤
      (divKTrialCallV5QHat u2 u1 v1).toNat := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  have h0 : (0 : Word).toNat = 0 := rfl
  have hVtop : 0 < v1.toNat := by omega
  have hV : v1.toNat * 2^64 ≤ val256 v0 v1 0 0 := by
    simp only [EvmWord.val256, h0]; omega
  have hU : val256 u0 u1 u2 0 = (u2.toNat * 2^64 + u1.toNat) * 2^64 + u0.toNat := by
    simp only [EvmWord.val256, h0]; ring
  have hUlow : u0.toNat < 2^64 := u0.isLt
  have hknuth := knuth_a_floor_window_le hV hVtop (by positivity) hU hUlow
  have hge := div128Quot_v5_ge_q_true u2 u1 v1 hv1 hcall
  omega

/-- **v5 n=2 per-digit Knuth-A upper bound (`+2`).** The top-window quotient
    `(u2·2^64+u1)/v1` overshoots the full window quotient by at most 2.  Proved
    by reusing the n=4 `knuth_theorem_b_abstract` after scaling both window and
    divisor by `2^128` (which embeds the 2-limb divisor into the 4-limb top-digit
    frame; the scaling cancels in the quotient via `Nat.mul_div_mul_right`). -/
theorem n2_window_top_div_le_val256_div_plus_two
    (v0 v1 u0 u1 u2 : Word)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    (u2.toNat * 2^64 + u1.toNat) / v1.toNat ≤
      val256 u0 u1 u2 0 / val256 v0 v1 0 0 + 2 := by
  have h0 : (0 : Word).toNat = 0 := rfl
  have hvr : v0.toNat * 2^128 < 2^192 := by
    have h := v0.isLt
    calc v0.toNat * 2^128 < 2^64 * 2^128 :=
          Nat.mul_lt_mul_of_pos_right h (by positivity)
      _ = 2^192 := by rw [← pow_add]
  have hb := knuth_theorem_b_abstract
    (val256 u0 u1 u2 0 * 2^128) (val256 v0 v1 0 0 * 2^128)
    u2.toNat u1.toNat (u0.toNat * 2^128) v1.toNat (v0.toNat * 2^128)
    (by simp only [EvmWord.val256, h0]; ring)
    (by simp only [EvmWord.val256, h0]; ring)
    hvr hv1 hcall u1.isLt
  rwa [Nat.mul_div_mul_right _ _ (by positivity)] at hb

/-- **v5 n=2 per-digit overestimate (`hq_over`).** The v5 trial quotient is at
    most `val256 u / val256 v + 2` — the `hq_over` input of
    `iterWithDoubleAddback_remainder_lt_of_plus_two`.  Combines
    `divKTrialCallV5QHat_eq_floor` (the v5 trial is the exact top-window floor)
    with the Knuth-A upper bound above. -/
theorem n2_window_div_le_val256_div_plus_two_v5
    (v0 v1 u0 u1 u2 : Word)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    (divKTrialCallV5QHat u2 u1 v1).toNat ≤
      val256 u0 u1 u2 0 / val256 v0 v1 0 0 + 2 := by
  rw [divKTrialCallV5QHat_eq_floor u2 u1 v1 hv1 hcall]
  exact n2_window_top_div_le_val256_div_plus_two v0 v1 u0 u1 u2 hv1 hcall

end EvmAsm.Evm64
