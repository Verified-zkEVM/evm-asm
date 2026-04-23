/-
  EvmAsm.Evm64.EvmWordArith.Div128Shift0

  Lemmas about `div128Quot 0 a3 b3` under shift=0 normalization
  (`b3 ≥ 2^63`). Under this regime, uHi=0 ⟹ un21 < 2^32 ⟹ Phase 2a
  doesn't correct ⟹ rhat2c < 2^32 ⟹ the Phase 2b false-positive
  (counterexample from #1138) CAN'T fire. So the algorithm is correct
  in this regime regardless of whether the Phase 2b guard is in place.

  Purpose: build the semantic bridge for
  `evm_div_n4_shift0_call_skip_stack_spec` (task #67 in
  `project_un21_lt_vTop_plan.md`) without depending on #1138 merging.

  Structure:
  1. Arithmetic bridge lemmas (fully proved).
  2. Phase 1 trivialization helpers under uHi=0 — scaffolded with sorrys,
     each is a small focused proof to fill in incrementally per
     `feedback_commit_sorry_intermediate` and `feedback_loop_attack_blockers`.
  3. The composite `div128Quot_shift0_ge_a3_div_b3` builds on (2).
  4. Final `div128Quot_shift0_eq_val256_div` combines everything.
-/

import EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

-- ============================================================================
-- Arithmetic bridge lemmas
-- ============================================================================

/-- Key identity: `(a3 >>> 32).toNat * 2^32 + ((a3 <<< 32) >>> 32).toNat = a3.toNat`.
    Expresses a 64-bit word as its top-32-bits * 2^32 + low-32-bits. -/
theorem word_hi32_lo32_decomp (a : Word) :
    (a >>> (32 : BitVec 6).toNat).toNat * 2^32 +
    ((a <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat = a.toNat := by
  have h32 : (32 : BitVec 6).toNat = 32 := by decide
  rw [h32]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h_shl : ((a <<< 32 : Word) >>> 32).toNat = a.toNat % 2^32 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have h_eq : (a.toNat * 2^32) % 2^64 = (a.toNat % 2^32) * 2^32 := by
      rw [show (2^64 : Nat) = 2^32 * 2^32 from by decide, Nat.mul_mod_mul_right]
    rw [h_eq]
    have h_pos : (2^32 : Nat) > 0 := by decide
    rw [Nat.mul_div_cancel _ h_pos]
  rw [h_shl]
  have := Nat.div_add_mod a.toNat (2^32)
  omega

/-- Under shift=0 (b3 ≥ 2^63), a3 < b3 implies val256(a) < val256(b). -/
theorem val256_lt_of_a3_lt_b3 (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (h : a3.toNat < b3.toNat) :
    val256 a0 a1 a2 a3 < val256 b0 b1 b2 b3 := by
  have h_low_bound : a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 < 2^192 := by
    have h0 := a0.isLt
    have h1 := a1.isLt
    have h2 := a2.isLt
    calc a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128
        ≤ (2^64 - 1) + (2^64 - 1) * 2^64 + (2^64 - 1) * 2^128 := by
          have h1' : a1.toNat * 2^64 ≤ (2^64 - 1) * 2^64 :=
            Nat.mul_le_mul_right _ (by omega)
          have h2' : a2.toNat * 2^128 ≤ (2^64 - 1) * 2^128 :=
            Nat.mul_le_mul_right _ (by omega)
          omega
      _ = 2^192 - 1 := by decide
      _ < 2^192 := by decide
  have h_b_ge : val256 b0 b1 b2 b3 ≥ b3.toNat * 2^192 := by
    show b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192 ≥ _
    omega
  have h_a_ub : val256 a0 a1 a2 a3 < (a3.toNat + 1) * 2^192 := by
    show a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192 < _
    have : (a3.toNat + 1) * 2^192 = a3.toNat * 2^192 + 2^192 := by ring
    omega
  have h_bound : (a3.toNat + 1) * 2^192 ≤ b3.toNat * 2^192 := by
    apply Nat.mul_le_mul_right
    omega
  omega

/-- Under shift=0 (b3 ≥ 2^63), the top-limb ratio `a3.toNat / b3.toNat`
    upper-bounds the full 256-bit ratio. -/
theorem a3_div_b3_ge_val256_div (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63)
    (hb : val256 b0 b1 b2 b3 > 0) :
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ a3.toNat / b3.toNat := by
  have hv_b_ge : val256 b0 b1 b2 b3 ≥ 2^255 := by
    show b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192 ≥ _
    have : b3.toNat * 2^192 ≥ 2^63 * 2^192 := Nat.mul_le_mul_right _ hb3_ge
    have : (2^63 : Nat) * 2^192 = 2^255 := by decide
    omega
  have hv_a_lt : val256 a0 a1 a2 a3 < 2^256 := val256_bound _ _ _ _
  have h_ratio_le : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hb]
    have : 2 * val256 b0 b1 b2 b3 ≥ 2^256 := by
      have : 2 * val256 b0 b1 b2 b3 ≥ 2 * 2^255 := Nat.mul_le_mul_left _ hv_b_ge
      have : 2 * 2^255 = (2^256 : Nat) := by decide
      omega
    omega
  rcases Nat.lt_or_ge (val256 a0 a1 a2 a3) (val256 b0 b1 b2 b3) with h | h
  · have h_eq : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 = 0 :=
      Nat.div_eq_of_lt h
    rw [h_eq]
    exact Nat.zero_le _
  · have h_ratio_eq : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 = 1 := by
      have h_ge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≥ 1 :=
        Nat.one_le_div_iff hb |>.mpr h
      omega
    rw [h_ratio_eq]
    have h_a3_ge : a3.toNat ≥ b3.toNat := by
      by_contra h_lt
      push Not at h_lt
      exact absurd h (Nat.not_le.mpr (val256_lt_of_a3_lt_b3 a0 a1 a2 a3 b0 b1 b2 b3 h_lt))
    have hb3_pos : 0 < b3.toNat := by omega
    exact (Nat.one_le_div_iff hb3_pos).mpr h_a3_ge

-- ============================================================================
-- Phase 1 trivialization under uHi=0 (each a focused ~5-15 line proof)
-- Each sub-lemma isolates one step of the `div128Quot 0 a3 b3` computation.
-- ============================================================================

/-- Under b3 ≥ 2^63 and uHi=0, Phase 1's q1 is zero. -/
theorem div128Quot_shift0_q1_eq_zero (dHi : Word) (hdHi_ne : dHi ≠ 0) :
    rv64_divu (0 : Word) dHi = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [rv64_divu_toNat _ _ hdHi_ne]
  show (0 : Word).toNat / dHi.toNat = (0 : Word).toNat
  simp

/-- Under uHi=0 + hdHi_ne, Phase 1's hi1 = 0. -/
theorem div128Quot_shift0_hi1_eq_zero (dHi : Word) (hdHi_ne : dHi ≠ 0) :
    (rv64_divu (0 : Word) dHi) >>> (32 : BitVec 6).toNat = 0 := by
  rw [div128Quot_shift0_q1_eq_zero dHi hdHi_ne]
  rfl

/-- Under uHi=0 + hdHi_ne, Phase 1's q1c = 0. -/
theorem div128Quot_shift0_q1c_eq_zero (dHi : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     if hi1 = 0 then q1 else q1 + signExtend12 4095) = 0 := by
  simp only []
  rw [div128Quot_shift0_hi1_eq_zero dHi hdHi_ne]
  rw [if_pos rfl]
  exact div128Quot_shift0_q1_eq_zero dHi hdHi_ne

/-- Under uHi=0 + hdHi_ne, Phase 1's rhat = 0 - q1*dHi = 0. -/
theorem div128Quot_shift0_rhat_eq_zero (dHi : Word) (hdHi_ne : dHi ≠ 0) :
    (0 : Word) - (rv64_divu (0 : Word) dHi) * dHi = 0 := by
  rw [div128Quot_shift0_q1_eq_zero dHi hdHi_ne]
  simp

-- ============================================================================
-- The main composite lemma — scaffolded with sorrys for Phase 1 tracing
-- and Phase 2b reasoning. Filled incrementally per feedback_commit_sorry_intermediate.
-- ============================================================================

/-- Under shift=0 (b3 ≥ 2^63) + b3 ≠ 0:
    `(div128Quot 0 a3 b3).toNat ≥ a3.toNat / b3.toNat`.

    Proof sketch (TODO: fill in sorrys):
    1. Apply `div128Quot_toNat_eq` to get qHat.toNat = (q1' % 2^32) * 2^32 + q0'.toNat.
    2. Show q1' = 0 under uHi=0 via Phase 1 trivialization.
    3. Apply KB-LB8 (`div128Quot_q0_prime_ge_q_true_0_of_un21_lt_pow63`) to get
       q0'.toNat ≥ (un21*2^32 + div_un0) / vTop.
    4. Show un21 = a3 >> 32 under uHi=0 (Phase 1 trivialization).
    5. Simplify: un21*2^32 + div_un0 = (a3>>32)*2^32 + (a3 mod 2^32) = a3.toNat
       (via `word_hi32_lo32_decomp`).
    6. Combine: qHat.toNat = q0'.toNat ≥ a3.toNat / b3.toNat. -/
theorem div128Quot_shift0_ge_a3_div_b3 (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63)
    (hb3_nz : b3 ≠ 0) :
    (div128Quot (0 : Word) a3 b3).toNat ≥ a3.toNat / b3.toNat := by
  -- TODO(#67): the full 5-step proof outlined above. Requires careful
  -- algorithm tracing through div128Quot's 15+ let bindings. Split into
  -- sub-lemmas in subsequent iterations.
  sorry

/-- Upper bound: under shift=0 (b3 ≥ 2^63), `div128Quot 0 a3 b3` is at most 1.

    Proof sketch:
    1. div128Quot_toNat_eq gives qHat.toNat = (q1' % 2^32)*2^32 + q0'.toNat.
    2. q1' = 0 under uHi=0 (Phase 1 trivialization).
    3. q0'.toNat ≤ 1 under uHi=0: q0 = un21/dHi ≤ 1 (un21 < 2^32, dHi ≥ 2^31),
       Phase 2a doesn't correct (hi2 = 0), q0c = q0 ≤ 1. Phase 2b either
       keeps q0c or decrements to q0c - 1 ≤ 0 ≤ 1. -/
theorem div128Quot_shift0_le_one (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63)
    (hb3_nz : b3 ≠ 0) :
    (div128Quot (0 : Word) a3 b3).toNat ≤ 1 := by
  -- TODO(#67): fill in via Phase 1 trivialization + Phase 2 bound.
  sorry

/-- If `div128Quot 0 a3 b3 = 0` under shift=0, then a3 < b3. -/
theorem div128Quot_shift0_eq_zero_implies_a3_lt_b3 (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63)
    (hb3_nz : b3 ≠ 0)
    (hqHat_zero : div128Quot (0 : Word) a3 b3 = 0) :
    a3.toNat < b3.toNat := by
  have h_ge := div128Quot_shift0_ge_a3_div_b3 a3 b3 hb3_ge hb3_nz
  have h_zero_toNat : (div128Quot (0 : Word) a3 b3).toNat = 0 := by
    rw [hqHat_zero]; rfl
  rw [h_zero_toNat] at h_ge
  have h_b3_pos : 0 < b3.toNat := by
    have : b3.toNat ≥ 2^63 := hb3_ge
    omega
  have h_div_zero : a3.toNat / b3.toNat = 0 := Nat.le_zero.mp h_ge
  exact (Nat.div_eq_zero_iff_lt h_b3_pos).mp h_div_zero

/-- **Shift=0 correctness (composite)**: under b3 ≥ 2^63 + b3 ≠ 0 +
    `div128Quot 0 a3 b3 = qHat`:
    `qHat.toNat ≥ val256(a)/val256(b)`.

    Direct composition of `div128Quot_shift0_ge_a3_div_b3` (algorithm lower
    bound) + `a3_div_b3_ge_val256_div` (arithmetic bridge).

    This is the overestimate (hge) that `div_correct_n4_no_shift` needs to
    conclude `qHat = EvmWord.div a b` limb-0 under skip-borrow. -/
theorem div128Quot_shift0_ge_val256_div (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63)
    (hb3_nz : b3 ≠ 0)
    (hb : val256 b0 b1 b2 b3 > 0) :
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot (0 : Word) a3 b3).toNat := by
  have h_algo := div128Quot_shift0_ge_a3_div_b3 a3 b3 hb3_ge hb3_nz
  have h_arith := a3_div_b3_ge_val256_div a0 a1 a2 a3 b0 b1 b2 b3 hb3_ge hb
  omega

end EvmAsm.Evm64
