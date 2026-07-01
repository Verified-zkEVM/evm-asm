/-
  EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipModWordLaneNative

  Native MOD counterpart of `n4_call_skip_mod_getLimbN_v5` (N4V5CallSkipModWordLane):
  the four limbs of `EvmWord.mod a b` equal the denormalized mulsub result, derived
  from ONLY the v5 skip-borrow `isSkipBorrowN4CallV5` (plus the n=4 shape / shift≠0)
  — NO v4 borrow, NO v4 semantic `n4CallSkipSemanticHoldsV4`, and NO v5↔v4 trial
  bridge.  The two overestimate bounds fed to
  `denorm_limbN_eq_mod_of_overestimate_getLimbN` are the SAME native v5 bounds the
  quotient word lane `n4_call_skip_div_mod_getLimbN_v5_native` (#7640) uses:
  * upper `divKTrialCallV5QHat_call_skip_mul_val256_b_le_val256_a` (#7638), from the
    v5 skip-borrow;
  * lower `divKTrialCallV5QHat_ge_val256_div` (#7637);
  and the carry bound `c3_le_u4_of_skip_borrow_call_v5` (also from the v5 borrow).
  The MOD companion to the native DIV word lane, for the native shift≠0 MOD lane.
-/

import EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipUpperBound
import EvmAsm.Evm64.DivMod.Spec.CallSkipOverestimateBridge
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5Native

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Native MOD limb facts for the n=4 call+skip path (v5): the four limbs of
    `EvmWord.mod a b` are the funnel-shift-down of the normalized mulsub result,
    derived from ONLY the v5 skip-borrow `isSkipBorrowN4CallV5` (no v4 facts). -/
theorem n4_call_skip_mod_getLimbN_v5_native (a b : EvmWord)
    (_hbnz : b ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hborrowV5 : isSkipBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1)
      (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := divKTrialCallV5QHat u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    (EvmWord.mod a b).getLimbN 0 = ((ms.1 >>> shift) ||| (ms.2.1 <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 1 = ((ms.2.1 >>> shift) ||| (ms.2.2.1 <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 2 = ((ms.2.2.1 >>> shift) ||| (ms.2.2.2.1 <<< antiShift)) ∧
    (EvmWord.mod a b).getLimbN 3 = (ms.2.2.2.1 >>> shift) := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms
  -- Shift bounds.
  have hclz_le := clzResult_fst_toNat_le (b.getLimbN 3)
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h
    apply hshift_nz
    apply BitVec.eq_of_toNat_eq
    rw [show (0 : Word).toNat = 0 from rfl]
    omega
  have hshift_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have hmod_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hanti_toNat_mod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat := by
    have h0se12 : signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1 =
        -((clzResult (b.getLimbN 3)).1) := by rw [signExtend12_0]; simp
    rw [h0se12, BitVec.toNat_neg]
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 2 ^ 64 := by
      have := ((clzResult (b.getLimbN 3)).1).isLt; omega
    omega
  -- b3 CLZ top bound.
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- Call-trial predicate from shift≠0.
  have hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz
  -- The two native v5 bounds (from the v5 skip-borrow) + the carry bound.
  have hT3 := divKTrialCallV5QHat_call_skip_mul_val256_b_le_val256_a
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hshift_nz hborrowV5
  have hsem := divKTrialCallV5QHat_ge_val256_div
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hb3nz hshift_nz hcall
  have hc3_le := c3_le_u4_of_skip_borrow_call_v5 hborrowV5
  change (divKTrialCallV5QHat _ _ _).toNat *
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) at hT3
  change val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      (divKTrialCallV5QHat _ _ _).toNat at hsem
  simp only [hmod_eq, hanti_toNat_mod] at hT3 hsem hc3_le
  -- Apply the per-limb overestimate bridge with `s = clz.1.toNat`, v5 qHat.
  have h_limbs := denorm_limbN_eq_mod_of_overestimate_getLimbN (a := a) (b := b)
    (qHat := divKTrialCallV5QHat
      ((a.getLimbN 3) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))
      (((a.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
       ((a.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat)))
      (((b.getLimbN 3) <<< (clzResult (b.getLimbN 3)).1.toNat) |||
       ((b.getLimbN 2) >>> (64 - (clzResult (b.getLimbN 3)).1.toNat))))
    hshift_pos hshift_lt_64 hb3_bound hT3 hsem hb3nz hc3_le
  simp only [shift, antiShift, b3', b2', b1', b0', u4, u3, u2, u1, u0, qHat, ms,
    hmod_eq, hanti_toNat_mod]
  exact h_limbs

end EvmAsm.Evm64
