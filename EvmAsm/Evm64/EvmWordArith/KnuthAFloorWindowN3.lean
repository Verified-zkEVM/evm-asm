/-
  EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindowN3

  The v5 n=3 per-digit trial bounds — the n=3 analogs of the n=2 lemmas in
  `KnuthAFloorWindow`.  For a 3-limb divisor `(v0,v1,v2,0)` (top limb `v2`,
  normalized `v2 ≥ 2^63`) and a 4-limb window `(u0,u1,u2,u3)` in the call regime
  (`u3 < v2`):

  - `n3_window_val256_div_le_trial_v5` (no-underestimate, `hq_ge`):
    `val256 u / val256 v ≤ divKTrialCallV5QHat u3 u2 v2`.
  - `n3_window_div_le_val256_div_plus_two_v5` (overestimate, `hq_over`):
    `divKTrialCallV5QHat u3 u2 v2 ≤ val256 u / val256 v + 2`.

  Both reuse the position-independent cores `knuth_a_floor_window_le` /
  `knuth_theorem_b_abstract`, instantiated at the n=3 place values
  (`K = 2^128`, divisor scaled by `2^64` to embed the 3-limb divisor into the
  4-limb top-digit frame), and the v5 trial floor lemmas
  (`div128Quot_v5_ge_q_true`, `divKTrialCallV5QHat_eq_floor`).  These are the
  `hq_ge`/`hq_over` inputs to `iterWithDoubleAddback`'s conservation/remainder
  bounds for the v5 n=3 lane.  Bead `evm-asm-wbc4i.9.3`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindow

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=3 per-digit no-underestimate.** The full 4-limb window quotient is at
    most the v5 trial quotient (top two window limbs `u3,u2` over the divisor's
    top limb `v2`).  `hq_ge` ingredient for the n=3 per-digit remainder bound. -/
theorem n3_window_val256_div_le_trial_v5
    (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hcall : u3.toNat < v2.toNat) :
    val256 u0 u1 u2 u3 / val256 v0 v1 v2 0 ≤
      (divKTrialCallV5QHat u3 u2 v2).toNat := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  have h0 : (0 : Word).toNat = 0 := rfl
  have hVtop : 0 < v2.toNat := by omega
  have hV : v2.toNat * 2 ^ 128 ≤ val256 v0 v1 v2 0 := by
    simp only [EvmWord.val256, h0]; omega
  have hU : val256 u0 u1 u2 u3 =
      (u3.toNat * 2 ^ 64 + u2.toNat) * 2 ^ 128 + (u0.toNat + u1.toNat * 2 ^ 64) := by
    simp only [EvmWord.val256]; ring
  have hUlow : u0.toNat + u1.toNat * 2 ^ 64 < 2 ^ 128 := by
    have := u0.isLt; have := u1.isLt; omega
  have hknuth := knuth_a_floor_window_le hV hVtop (by positivity) hU hUlow
  have hge := div128Quot_v5_ge_q_true u3 u2 v2 hv2 hcall
  omega

/-- **v5 n=3 per-digit Knuth-A upper bound (`+2`).** The top-window quotient
    `(u3·2^64+u2)/v2` overshoots the full 4-limb window quotient by at most 2.
    Reuses `knuth_theorem_b_abstract` after scaling both window and divisor by
    `2^64` (embedding the 3-limb divisor into the 4-limb top-digit frame). -/
theorem n3_window_top_div_le_val256_div_plus_two
    (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hcall : u3.toNat < v2.toNat) :
    (u3.toNat * 2 ^ 64 + u2.toNat) / v2.toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 0 + 2 := by
  have h0 : (0 : Word).toNat = 0 := rfl
  have hvr : val256 v0 v1 0 0 * 2 ^ 64 < 2 ^ 192 := by
    have := v0.isLt; have := v1.isLt; simp only [EvmWord.val256, h0]; omega
  have hb := knuth_theorem_b_abstract
    (val256 u0 u1 u2 u3 * 2 ^ 64) (val256 v0 v1 v2 0 * 2 ^ 64)
    u3.toNat u2.toNat (val256 u0 u1 0 0 * 2 ^ 64) v2.toNat (val256 v0 v1 0 0 * 2 ^ 64)
    (by simp only [EvmWord.val256, h0]; ring)
    (by simp only [EvmWord.val256, h0]; ring)
    hvr hv2 hcall u2.isLt
  rwa [Nat.mul_div_mul_right _ _ (by positivity)] at hb

/-- **v5 n=3 per-digit overestimate (`hq_over`).** The v5 trial quotient is at
    most `val256 u / val256 v + 2`.  Combines `divKTrialCallV5QHat_eq_floor`
    (the v5 trial is the exact top-window floor) with the Knuth-A upper bound. -/
theorem n3_window_div_le_val256_div_plus_two_v5
    (v0 v1 v2 u0 u1 u2 u3 : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hcall : u3.toNat < v2.toNat) :
    (divKTrialCallV5QHat u3 u2 v2).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 0 + 2 := by
  rw [divKTrialCallV5QHat_eq_floor u3 u2 v2 hv2 hcall]
  exact n3_window_top_div_le_val256_div_plus_two v0 v1 v2 u0 u1 u2 u3 hv2 hcall

end EvmAsm.Evm64
