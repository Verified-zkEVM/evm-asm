/-
  EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipModWordLane

  MOD counterpart of `n4_call_skip_div_mod_getLimbN_v5` (N4V5CallSkipWordLane):
  under the n=4 call+skip conditions, the four limbs of `EvmWord.mod a b` equal
  the denormalized (funnel-shift-down by the normalization shift) mulsub result
  `mulsubN4 qHat b'… u…`.  Discharges the four overestimate bounds of
  `denorm_limbN_eq_mod_of_overestimate_getLimbN` from the call-skip facts exactly
  as the (old-modCode) `output_slot_to_evmWordIs_mod_n4_call_skip_denorm` does:
  the T3 bound (`div128Quot_v4_call_skip_mul_val256_b_le_val256_a`, bridged to the
  v5 qHat via `hbridge`), the Knuth-A bound (`n4CallSkipSemanticHoldsV4`), the
  `hc3_n_le_u_top` carry bound (`c3_le_u4_of_skip_borrow_call_v5`), and the CLZ
  top bound (`clzResult_fst_top_bound`).  The one missing link for the n=4 MOD
  shiftNz `_of_conds` lane.
-/

import EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipWordLane
import EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipUpperBound
import EvmAsm.Evm64.DivMod.Spec.CallSkipOverestimateBridge
import EvmAsm.Evm64.EvmWordArith.Div128CallSkipCloseV4
import EvmAsm.Evm64.EvmWordArith.CLZLemmas

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- MOD limb facts for the n=4 call+skip path (v5), from the call-skip
    conditions.  The four limbs of `EvmWord.mod a b` are the funnel-shift-down of
    the normalized mulsub result by the normalization shift. -/
theorem n4_call_skip_mod_getLimbN_v5 (a b : EvmWord)
    (_hbnz : b ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hborrowV5 : isSkipBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1)
      (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3))
    (hsem : n4CallSkipSemanticHoldsV4 a b)
    (hbridge :
      divKTrialCallV5QHat
        ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
        (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
        (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))) =
      div128Quot_v4
        ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
        (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
        (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))) :
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
  -- T3 bound (v4) + hsem (Knuth-A) + c3 carry bound (v5).
  rw [isSkipBorrowN4CallV4Evm_def] at hborrow
  have hT3 := div128Quot_v4_call_skip_mul_val256_b_le_val256_a
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hshift_nz hborrow
  rw [n4CallSkipSemanticHoldsV4_def] at hsem
  have hc3_le := c3_le_u4_of_skip_borrow_call_v5 hborrowV5
  simp only [hmod_eq, hanti_toNat_mod] at hT3 hsem hc3_le hbridge
  -- Convert the T3 and Knuth-A bounds onto the v5 qHat via `hbridge`.
  rw [← hbridge] at hT3 hsem
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
