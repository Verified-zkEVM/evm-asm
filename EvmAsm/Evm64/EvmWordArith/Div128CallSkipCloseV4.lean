/-
  EvmAsm.Evm64.EvmWordArith.Div128CallSkipCloseV4

  v4 analogues of the call+skip arithmetic closure in `Div128CallSkipClose`.

  Provides the two Word-level facts that the upcoming v4 form of the n=4
  call+skip stack spec needs, both phrased over `div128Quot_v4` and the
  v4 borrow predicate `isSkipBorrowN4CallV4Ab`:

  * `c3_le_u4_of_skip_borrow_call_v4` — extracts `c3 ≤ u4` from the v4
    skip-borrow runtime check (mirror of `c3_le_u4_of_skip_borrow_call`).
  * `div128Quot_v4_call_skip_mul_val256_b_le_val256_a` — the no-overflow
    bound `qHat * val256(b) ≤ val256(a)` (mirror of
    `div128Quot_call_skip_mul_val256_b_le_val256_a`).

  Both are structural transfers of the v1 proofs: only the runtime borrow
  predicate (and therefore the qHat that goes into `mulsubN4_c3`) differs.
  The Knuth-arithmetic argument is qHat-agnostic.

  Unblocks bead `evm-asm-9iqmw.7.1.3.1` (DIV n=4 call+skip stack spec
  port to `divCode_v4`).
-/

module

public import EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose
public import EvmAsm.Evm64.DivMod.Compose.FullPathN4CallV4NoNop
public import EvmAsm.Evm64.DivMod.LoopBody.TrialCall

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- v4 analogue of `c3_le_u4_of_skip_borrow_call`: under the v4 skip-borrow
    runtime check, the outer-mulsub borrow limb `c3` is at most `u4`.

    The borrow predicate `isSkipBorrowN4CallV4Ab` is structurally the same
    `if-then-else` shape as the v1 predicate; only the qHat that goes into
    `mulsubN4_c3` is `div128Quot_v4` rather than `div128Quot`. The proof
    transfers verbatim. -/
theorem c3_le_u4_of_skip_borrow_call_v4
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : isSkipBorrowN4CallV4Ab a0 a1 a2 a3 b0 b1 b2 b3) :
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
    let qHat := div128Quot_v4 u4 u3 b3'
    (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat ≤ u4.toNat := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  -- `isSkipBorrowN4CallV4Ab` unfolds to `mulsubN4NoBorrow qHat_v4 …`, and
  -- `mulsubN4NoBorrow` is the same `(if ult uTop c3 then 1 else 0) = 0`
  -- shape as the v1 `isSkipBorrowN4Call`. Bridge the v4 trial-call qHat to
  -- `div128Quot_v4`, then case-split as in the v1 proof.
  unfold isSkipBorrowN4CallV4Ab at h
  simp only [] at h
  unfold loopBodyN4CallSkipJ0BorrowV4 at h
  rw [divKTrialCallV4QHat_eq_div128Quot_v4] at h
  unfold mulsubN4NoBorrow at h
  simp only [] at h
  by_cases hlt :
      BitVec.ult u4 (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2
  · rw [if_pos hlt] at h
    exact absurd h (by decide)
  · rw [ult_iff] at hlt
    omega

/-- v4 analogue of `div128Quot_call_skip_mul_val256_b_le_val256_a`: under
    the v4 skip-borrow runtime check and shift-normalization, the v4 trial
    quotient `div128Quot_v4` does not overflow when multiplied by the true
    divisor.

    Proof structure (transfers verbatim from the v1 form): combine the
    mulsubN4 Euclidean identity, the v4 outer-mulsub borrow bound
    `c3 ≤ u4`, and the normalization identities `val256(u) + u4 * 2^256 =
    val256(a) * 2^shift` and `val256(v') = val256(b) * 2^shift`. Cancel
    `2^shift > 0` since `val256(b) > 0` whenever `b3 ≠ 0`.

    Conclusion: `qHat.toNat * val256(b) ≤ val256(a)` (unscaled). -/
theorem div128Quot_v4_call_skip_mul_val256_b_le_val256_a
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hskip : isSkipBorrowN4CallV4Ab a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (div128Quot_v4 u4 u3 b3').toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3 := by
  intro shift antiShift b3' u4 u3
  set b2' := (b2 <<< shift) ||| (b1 >>> antiShift)
  set b1' := (b1 <<< shift) ||| (b0 >>> antiShift)
  set b0' := b0 <<< shift
  set u2 := (a2 <<< shift) ||| (a1 >>> antiShift)
  set u1 := (a1 <<< shift) ||| (a0 >>> antiShift)
  set u0 := a0 <<< shift
  set qHat := div128Quot_v4 u4 u3 b3'
  -- v4 outer-mulsub borrow bound.
  have h_c3_le := c3_le_u4_of_skip_borrow_call_v4 hskip
  -- mulsubN4 Euclidean identity is qHat-agnostic.
  have h_mulsub := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Normalization identities transfer unchanged.
  have h_norm_u := u_val256_eq_scaled_with_overflow a0 a1 a2 a3 b3 hshift_nz
  have h_norm_v := b3_prime_val256_eq_scaled b0 b1 b2 b3 hshift_nz
  have h_un_bound : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 :=
    val256_bound _ _ _ _
  have h_qHat_mul_v' : qHat.toNat * val256 b0' b1' b2' b3' ≤
      val256 a0 a1 a2 a3 * 2^(clzResult b3).1.toNat := by
    have : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 := h_un_bound
    have : qHat.toNat * val256 b0' b1' b2' b3' ≤
        val256 u0 u1 u2 u3 + ms.2.2.2.2.toNat * 2^256 := by omega
    have : val256 u0 u1 u2 u3 + ms.2.2.2.2.toNat * 2^256 ≤
        val256 u0 u1 u2 u3 + u4.toNat * 2^256 := by
      apply Nat.add_le_add_left
      exact Nat.mul_le_mul_right _ h_c3_le
    have : val256 u0 u1 u2 u3 + u4.toNat * 2^256 =
        val256 a0 a1 a2 a3 * 2^(clzResult b3).1.toNat := h_norm_u
    omega
  rw [h_norm_v] at h_qHat_mul_v'
  have hpow_pos : 0 < (2 : Nat)^(clzResult b3).1.toNat := by positivity
  have h_mul_rearr : qHat.toNat * (val256 b0 b1 b2 b3 * 2^(clzResult b3).1.toNat) =
      qHat.toNat * val256 b0 b1 b2 b3 * 2^(clzResult b3).1.toNat := by ring
  rw [h_mul_rearr] at h_qHat_mul_v'
  exact Nat.le_of_mul_le_mul_right h_qHat_mul_v' hpow_pos

/-- v4 analogue of `div128Quot_call_skip_le_val256_div`: under v4
    skip-borrow + shift normalization, the v4 trial quotient is bounded
    above by the true val256 quotient.

    Direct corollary of the no-overflow bound
    `div128Quot_v4_call_skip_mul_val256_b_le_val256_a` via `Nat.le_div_iff_mul_le`,
    using `val256_pos_of_or_ne_zero` to obtain `0 < val256(b)` from `b3 ≠ 0`. -/
theorem div128Quot_v4_call_skip_le_val256_div
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hskip : isSkipBorrowN4CallV4Ab a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (div128Quot_v4 u4 u3 b3').toNat ≤
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
  intro shift antiShift b3' u4 u3
  have h_bnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hv_pos : 0 < val256 b0 b1 b2 b3 := val256_pos_of_or_ne_zero h_bnz
  have h_mul := div128Quot_v4_call_skip_mul_val256_b_le_val256_a
    a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz hskip
  simp only [] at h_mul
  exact (Nat.le_div_iff_mul_le hv_pos).mpr h_mul

end EvmAsm.Evm64
