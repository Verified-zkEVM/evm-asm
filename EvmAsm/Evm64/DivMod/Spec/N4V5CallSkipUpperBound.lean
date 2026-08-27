/-
  EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipUpperBound

  The native v5 call-skip UPPER bound: under the v5 skip-borrow runtime check
  (`isSkipBorrowN4CallV5`, i.e. the v5 trial's outer mulsub does not borrow) and
  shift normalization, the v5 trial quotient `divKTrialCallV5QHat` does not
  overflow against the true divisor:
  `(divKTrialCallV5QHat u4 u3 b3').toNat * val256 b ≤ val256 a`.

  v5-native counterpart of `div128Quot_v4_call_skip_mul_val256_b_le_val256_a`
  (Div128CallSkipCloseV4): the no-overflow argument (mulsub Euclidean identity +
  `c3 ≤ u4` + normalization scaling) is qHat-agnostic, so it transfers verbatim;
  only the `c3 ≤ u4` extraction is reproved for the v5 borrow (which is directly
  `mulsubN4NoBorrow (divKTrialCallV5QHat …) …`, with no v4 trial bridge).

  Combined with the lower bound `divKTrialCallV5QHat_ge_val256_div` (#7637), this
  pins the v5 trial to the exact quotient `val256 a / val256 b` on the skip branch
  — the upper half of the v5-native call-skip word equality, discharging the
  shift≠0 call-skip semantic from the shape (around the v4 no-wrap blocker).
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopPreloopCallSkip
public import EvmAsm.Evm64.EvmWordArith.Div128CallSkipCloseV4

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256 val256_bound ult_iff)

/-- v5 analogue of `c3_le_u4_of_skip_borrow_call_v4`: the v5 skip-borrow check
    forces the outer mulsub carry `c3 ≤ u4`. -/
theorem c3_le_u4_of_skip_borrow_call_v5
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : isSkipBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let b2' := (b2 <<< shift) ||| (b1 >>> antiShift)
    let b1' := (b1 <<< shift) ||| (b0 >>> antiShift)
    let b0' := b0 <<< shift
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let u2 := (a2 <<< shift) ||| (a1 >>> antiShift)
    let u1 := (a1 <<< shift) ||| (a0 >>> antiShift)
    let u0 := a0 <<< shift
    let qHat := divKTrialCallV5QHat u4 u3 b3'
    (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat ≤ u4.toNat := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  unfold isSkipBorrowN4CallV5 at h
  simp only [] at h
  unfold mulsubN4NoBorrow at h
  simp only [] at h
  by_cases hlt : BitVec.ult u4 (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2
  · rw [if_pos hlt] at h
    exact absurd h (by decide)
  · rw [ult_iff] at hlt
    omega

/-- v5-native call-skip no-overflow bound. -/
theorem divKTrialCallV5QHat_call_skip_mul_val256_b_le_val256_a
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hskip : isSkipBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (divKTrialCallV5QHat u4 u3 b3').toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3 := by
  intro shift antiShift b3' u4 u3
  set b2' := (b2 <<< shift) ||| (b1 >>> antiShift)
  set b1' := (b1 <<< shift) ||| (b0 >>> antiShift)
  set b0' := b0 <<< shift
  set u2 := (a2 <<< shift) ||| (a1 >>> antiShift)
  set u1 := (a1 <<< shift) ||| (a0 >>> antiShift)
  set u0 := a0 <<< shift
  set qHat := divKTrialCallV5QHat u4 u3 b3'
  have h_c3_le := c3_le_u4_of_skip_borrow_call_v5 hskip
  have h_mulsub := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  have h_norm_u := u_val256_eq_scaled_with_overflow a0 a1 a2 a3 b3 hshift_nz
  have h_norm_v := b3_prime_val256_eq_scaled b0 b1 b2 b3 hshift_nz
  have h_un_bound : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2 ^ 256 :=
    val256_bound _ _ _ _
  have h_qHat_mul_v' : qHat.toNat * val256 b0' b1' b2' b3' ≤
      val256 a0 a1 a2 a3 * 2 ^ (clzResult b3).1.toNat := by
    have hb1 : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2 ^ 256 := h_un_bound
    have hb2 : qHat.toNat * val256 b0' b1' b2' b3' ≤
        val256 u0 u1 u2 u3 + ms.2.2.2.2.toNat * 2 ^ 256 := by omega
    have hb3 : val256 u0 u1 u2 u3 + ms.2.2.2.2.toNat * 2 ^ 256 ≤
        val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256 := by
      apply Nat.add_le_add_left
      exact Nat.mul_le_mul_right _ h_c3_le
    have hb4 : val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256 =
        val256 a0 a1 a2 a3 * 2 ^ (clzResult b3).1.toNat := h_norm_u
    omega
  rw [h_norm_v] at h_qHat_mul_v'
  have hpow_pos : 0 < (2 : Nat) ^ (clzResult b3).1.toNat := by positivity
  have h_mul_rearr : qHat.toNat * (val256 b0 b1 b2 b3 * 2 ^ (clzResult b3).1.toNat) =
      qHat.toNat * val256 b0 b1 b2 b3 * 2 ^ (clzResult b3).1.toNat := by ring
  rw [h_mul_rearr] at h_qHat_mul_v'
  exact Nat.le_of_mul_le_mul_right h_qHat_mul_v' hpow_pos

end EvmAsm.Evm64
