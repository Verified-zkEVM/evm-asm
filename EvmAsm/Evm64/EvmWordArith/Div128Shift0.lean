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

/-- Under uHi=0 + hdHi_ne, Phase 1's qDlo = q1c * dLo = 0. -/
theorem div128Quot_shift0_qDlo_eq_zero (dHi dLo : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     q1c * dLo) = 0 := by
  simp only []
  rw [div128Quot_shift0_q1c_eq_zero dHi hdHi_ne]
  simp

/-- Under uHi=0 + hdHi_ne, Phase 1's rhatc = 0 (since rhat = 0 and hi1 = 0 so rhatc = rhat). -/
theorem div128Quot_shift0_rhatc_eq_zero (dHi : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     if hi1 = 0 then rhat else rhat + dHi) = 0 := by
  simp only []
  rw [div128Quot_shift0_hi1_eq_zero dHi hdHi_ne]
  rw [if_pos rfl]
  exact div128Quot_shift0_rhat_eq_zero dHi hdHi_ne

/-- Under uHi=0 + hdHi_ne, Phase 1's rhatUn1 = (rhatc << 32) ||| div_un1 = div_un1
    (since rhatc = 0). -/
theorem div128Quot_shift0_rhatUn1_eq_div_un1 (dHi div_un1 : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) = div_un1 := by
  simp only []
  rw [show (if (rv64_divu (0 : Word) dHi) >>> (32 : BitVec 6).toNat = 0 then
            (0 : Word) - (rv64_divu (0 : Word) dHi) * dHi
          else
            ((0 : Word) - (rv64_divu (0 : Word) dHi) * dHi) + dHi) = 0 from
    div128Quot_shift0_rhatc_eq_zero dHi hdHi_ne]
  simp

/-- Under uHi=0 + hdHi_ne, Phase 2a's guard `BitVec.ult rhatUn1 qDlo = false`
    since `qDlo = 0` and unsigned comparison `x < 0` is always false. -/
theorem div128Quot_shift0_ult_false (dHi dLo div_un1 : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     BitVec.ult rhatUn1 qDlo) = false := by
  simp only []
  -- Reduce to `BitVec.ult rhatUn1 0 = false`. qDlo = 0 via helper.
  have hqDlo : (if (rv64_divu (0 : Word) dHi) >>> (32 : BitVec 6).toNat = 0 then
               rv64_divu (0 : Word) dHi
             else
               rv64_divu (0 : Word) dHi + signExtend12 4095) * dLo = 0 :=
    div128Quot_shift0_qDlo_eq_zero dHi dLo hdHi_ne
  rw [hqDlo]
  -- Now goal: BitVec.ult rhatUn1 0 = false.
  -- Use ult_iff + Nat.not_lt_zero.
  rw [Bool.eq_false_iff]
  intro h
  rw [ult_iff] at h
  rw [show (0 : Word).toNat = 0 from rfl] at h
  exact Nat.not_lt_zero _ h

/-- Under uHi=0 + hdHi_ne, Phase 2a's q1' = q1c = 0. -/
theorem div128Quot_shift0_q1_prime_eq_zero (dHi dLo div_un1 : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c) = 0 := by
  simp only []
  have hult := div128Quot_shift0_ult_false dHi dLo div_un1 hdHi_ne
  simp only [] at hult
  rw [hult]
  simp only [Bool.false_eq_true, if_false]
  exact div128Quot_shift0_q1c_eq_zero dHi hdHi_ne

/-- Under uHi=0 + hdHi_ne, Phase 2a's rhat' = rhatc = 0. -/
theorem div128Quot_shift0_rhat_prime_eq_zero (dHi dLo div_un1 : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) = 0 := by
  simp only []
  have hult := div128Quot_shift0_ult_false dHi dLo div_un1 hdHi_ne
  simp only [] at hult
  rw [hult]
  simp only [Bool.false_eq_true, if_false]
  exact div128Quot_shift0_rhatc_eq_zero dHi hdHi_ne

/-- Under uHi=0 + hdHi_ne, Phase 2b's cu_rhat_un1 = (rhat' << 32) ||| div_un1 = div_un1. -/
theorem div128Quot_shift0_cu_rhat_un1_eq_div_un1 (dHi dLo div_un1 : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
     (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1) = div_un1 := by
  simp only []
  rw [show (let q1 := rv64_divu (0 : Word) dHi
            let rhat := (0 : Word) - q1 * dHi
            let hi1 := q1 >>> (32 : BitVec 6).toNat
            let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
            let rhatc := if hi1 = 0 then rhat else rhat + dHi
            let qDlo := q1c * dLo
            let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
            if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) = 0 from
    div128Quot_shift0_rhat_prime_eq_zero dHi dLo div_un1 hdHi_ne]
  simp

/-- Under uHi=0 + hdHi_ne, Phase 2b's cu_q1_dlo = q1' * dLo = 0 (since q1' = 0). -/
theorem div128Quot_shift0_cu_q1_dlo_eq_zero (dHi dLo div_un1 : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
     q1' * dLo) = 0 := by
  simp only []
  rw [show (let q1 := rv64_divu (0 : Word) dHi
            let rhat := (0 : Word) - q1 * dHi
            let hi1 := q1 >>> (32 : BitVec 6).toNat
            let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
            let rhatc := if hi1 = 0 then rhat else rhat + dHi
            let qDlo := q1c * dLo
            let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
            if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c) = 0 from
    div128Quot_shift0_q1_prime_eq_zero dHi dLo div_un1 hdHi_ne]
  simp

/-- Under uHi=0 + hdHi_ne, Phase 2b's un21 = cu_rhat_un1 - cu_q1_dlo = div_un1. -/
theorem div128Quot_shift0_un21_eq_div_un1 (dHi dLo div_un1 : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
     let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
     let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
     let cu_q1_dlo := q1' * dLo
     cu_rhat_un1 - cu_q1_dlo) = div_un1 := by
  simp only []
  rw [div128Quot_shift0_cu_rhat_un1_eq_div_un1 dHi dLo div_un1 hdHi_ne,
      div128Quot_shift0_cu_q1_dlo_eq_zero dHi dLo div_un1 hdHi_ne]
  simp

/-- Under uHi=0 + hdHi_ne, Phase 2b's q0 = rv64_divu un21 dHi = rv64_divu div_un1 dHi. -/
theorem div128Quot_shift0_q0_eq (dHi dLo div_un1 : Word) (hdHi_ne : dHi ≠ 0) :
    (let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
     let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
     let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
     let cu_q1_dlo := q1' * dLo
     let un21 := cu_rhat_un1 - cu_q1_dlo
     rv64_divu un21 dHi) = rv64_divu div_un1 dHi := by
  simp only []
  rw [div128Quot_shift0_un21_eq_div_un1 dHi dLo div_un1 hdHi_ne]

/-- Under div_un1 < 2^32 and dHi ≥ 2^31: `(rv64_divu div_un1 dHi).toNat ≤ 1`. -/
theorem rv64_divu_lo32_hi32_le_one (div_un1 dHi : Word)
    (hdiv_un1_lt : div_un1.toNat < 2^32) (hdHi_ge : dHi.toNat ≥ 2^31) :
    (rv64_divu div_un1 dHi).toNat ≤ 1 := by
  have hdHi_ne : dHi ≠ 0 := by
    intro h
    rw [h] at hdHi_ge
    simp at hdHi_ge
  rw [rv64_divu_toNat _ _ hdHi_ne]
  -- div_un1.toNat / dHi.toNat: div_un1 < 2^32, dHi ≥ 2^31, so quotient ≤ 1.
  -- Since (2^32 - 1) / 2^31 = 1, worst case is 1.
  have hq : div_un1.toNat / dHi.toNat ≤ div_un1.toNat / 2^31 :=
    Nat.div_le_div_left hdHi_ge (by positivity)
  have hub : div_un1.toNat / 2^31 ≤ 1 := by
    apply Nat.div_le_iff_le_mul (by decide : 0 < (2:Nat)^31) |>.mpr
    have : (1 : Nat) * 2^31 = 2^31 := by ring
    omega
  omega

/-- Structural bound: `((a << 32) >> 32).toNat < 2^32` (low 32 bits of a). -/
theorem lo32_toNat_lt_pow32 (a : Word) :
    ((a <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
  rw [show (32 : BitVec 6).toNat = 32 from by decide]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hpow : (2:Nat)^64 = 2^32 * 2^32 := by decide
  rw [hpow]
  have h1 : a.toNat * 2^32 % (2^32 * 2^32) = (a.toNat % 2^32) * 2^32 := by
    rw [Nat.mul_mod_mul_right]
  rw [h1]
  rw [Nat.mul_div_cancel _ (by positivity : 0 < (2:Nat)^32)]
  exact Nat.mod_lt _ (by positivity)

/-- Structural bound: `(a >>> 32).toNat < 2^32` (high 32 bits of a fit in 32 bits). -/
theorem hi32_toNat_lt_pow32 (a : Word) :
    (a >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
  rw [show (32 : BitVec 6).toNat = 32 from by decide]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h : a.toNat < 2^64 := a.isLt
  have hpow : (2:Nat)^64 = 2^32 * 2^32 := by decide
  have h1 : a.toNat / 2^32 < 2^32 := by
    rw [hpow] at h
    exact Nat.div_lt_iff_lt_mul (by positivity) |>.mpr h
  exact h1

-- TODO: composed q0_le_one (uses dHi_ne/dHi_ge at lines 429/421) will be
-- added after dHi_ne in the file layout.

-- ============================================================================
-- The main composite lemma — scaffolded with sorrys for Phase 1 tracing
-- and Phase 2b reasoning. Filled incrementally per feedback_commit_sorry_intermediate.
-- ============================================================================

-- `div128Quot_shift0_ge_a3_div_b3` is defined below (after dHi_ne et al).

/-- Under b3 ≥ 2^63, dHi = b3 >> 32 has toNat ≥ 2^31. -/
theorem div128Quot_shift0_dHi_ge (b3 : Word) (hb3_ge : b3.toNat ≥ 2^63) :
    (b3 >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
  rw [show (32 : BitVec 6).toNat = 32 from by decide]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h : (2^31 : Nat) * 2^32 = 2^63 := by decide
  exact Nat.le_div_iff_mul_le (by decide : 0 < (2:Nat)^32) |>.mpr (by omega)

/-- Under b3 ≥ 2^63, dHi = b3 >> 32 is nonzero. -/
theorem div128Quot_shift0_dHi_ne (b3 : Word) (hb3_ge : b3.toNat ≥ 2^63) :
    b3 >>> (32 : BitVec 6).toNat ≠ 0 := by
  intro h
  have h_ge := div128Quot_shift0_dHi_ge b3 hb3_ge
  have h_toNat : (b3 >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [h]; rfl
  omega

/-- Under uHi=0 + b3 ≥ 2^63: `q0.toNat ≤ 1` in the div128Quot shift=0 chain.
    Composes `div128Quot_shift0_q0_eq` + `rv64_divu_lo32_hi32_le_one` +
    `lo32_toNat_lt_pow32` + `div128Quot_shift0_dHi_ge` + `_dHi_ne`. -/
theorem div128Quot_shift0_q0_le_one (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63) :
    (let dHi := b3 >>> (32 : BitVec 6).toNat
     let dLo := (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
     let div_un1 := a3 >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
     let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
     let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
     let cu_q1_dlo := q1' * dLo
     let un21 := cu_rhat_un1 - cu_q1_dlo
     (rv64_divu un21 dHi).toNat) ≤ 1 := by
  simp only []
  rw [div128Quot_shift0_q0_eq (b3 >>> (32 : BitVec 6).toNat)
        ((b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
        (a3 >>> (32 : BitVec 6).toNat)
        (div128Quot_shift0_dHi_ne b3 hb3_ge)]
  exact rv64_divu_lo32_hi32_le_one _ _ (hi32_toNat_lt_pow32 a3)
    (div128Quot_shift0_dHi_ge b3 hb3_ge)

/-- Generic: if `x.toNat ≤ 1`, then `(x >>> 32).toNat = 0` (hi-32 bits are 0). -/
theorem hi32_eq_zero_of_toNat_le_one (x : Word) (hx : x.toNat ≤ 1) :
    (x >>> (32 : BitVec 6).toNat).toNat = 0 := by
  rw [show (32 : BitVec 6).toNat = 32 from by decide]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have : x.toNat < 2^32 := by
    have : (2 : Nat) ^ 32 > 1 := by decide
    omega
  exact Nat.div_eq_of_lt this

/-- Under uHi=0 + b3 ≥ 2^63: in the div128Quot shift=0 chain, `hi2 = q0 >>> 32 = 0`.
    Composes `div128Quot_shift0_q0_le_one` with `hi32_eq_zero_of_toNat_le_one`. -/
theorem div128Quot_shift0_hi2_eq_zero (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63) :
    (let dHi := b3 >>> (32 : BitVec 6).toNat
     let dLo := (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
     let div_un1 := a3 >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
     let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
     let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
     let cu_q1_dlo := q1' * dLo
     let un21 := cu_rhat_un1 - cu_q1_dlo
     let q0 := rv64_divu un21 dHi
     q0 >>> (32 : BitVec 6).toNat = 0) := by
  simp only []
  apply BitVec.eq_of_toNat_eq
  rw [show (0 : Word).toNat = 0 from rfl]
  exact hi32_eq_zero_of_toNat_le_one _ (div128Quot_shift0_q0_le_one a3 b3 hb3_ge)

/-- Generic: if `q0c.toNat ≤ 1`, then the Phase 2b output also has
    `div128Quot_phase2b_q0'.toNat ≤ 1`.

    The tricky sub-case is when `q0c = 0` and the decrement fires:
    `q0c + signExtend12 4095 = 0 + (2^64 - 1) = 2^64 - 1`, which is NOT ≤ 1.
    But when `q0c = 0`, `q0Dlo = 0 * dLo = 0`, and `BitVec.ult _ 0 = false`,
    so the decrement guard can't fire — ruling out this case. -/
theorem div128Quot_phase2b_q0'_toNat_le_one
    (q0c rhat2c dLo div_un0 : Word) (hq0c : q0c.toNat ≤ 1) :
    (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat ≤ 1 := by
  unfold div128Quot_phase2b_q0'
  simp only []
  split
  · -- rhat2cHi = 0
    split
    · -- BitVec.ult (rhat2c <<< 32 ||| div_un0) (q0c * dLo) = true
      rename_i h_ult
      by_cases hq0c_zero : q0c.toNat = 0
      · -- q0c.toNat = 0 ⟹ q0c = 0 ⟹ q0c * dLo = 0 ⟹ ult is false: contradiction
        have hq0c_eq : q0c = 0 := BitVec.eq_of_toNat_eq (by rw [hq0c_zero]; rfl)
        rw [hq0c_eq] at h_ult
        rw [ult_iff] at h_ult
        have h0 : ((0 : Word) * dLo).toNat = 0 := by simp
        omega
      · -- q0c.toNat = 1 ⟹ q0c + signExtend12 4095 = 0
        have hq0c_one : q0c.toNat = 1 := by omega
        rw [BitVec.toNat_add]
        have h_sext : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
        rw [hq0c_one, h_sext]
        have h_mod : (1 + (2^64 - 1)) % 2^64 = 0 := by decide
        rw [h_mod]
        omega
    · exact hq0c
  · exact hq0c

/-- Under uHi=0 + b3 ≥ 2^63: in the div128Quot shift=0 chain, Phase 2a correction
    doesn't fire: `q0c = q0`. Follows from `div128Quot_shift0_hi2_eq_zero`. -/
theorem div128Quot_shift0_q0c_eq_q0 (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63) :
    (let dHi := b3 >>> (32 : BitVec 6).toNat
     let dLo := (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
     let div_un1 := a3 >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
     let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
     let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
     let cu_q1_dlo := q1' * dLo
     let un21 := cu_rhat_un1 - cu_q1_dlo
     let q0 := rv64_divu un21 dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     (if hi2 = 0 then q0 else q0 + signExtend12 4095) = q0) := by
  simp only []
  rw [div128Quot_shift0_hi2_eq_zero a3 b3 hb3_ge]
  simp

/-- Under uHi=0 + b3 ≥ 2^63: in the div128Quot shift=0 chain, `q0c.toNat ≤ 1`.
    Composite of `q0_le_one` + `q0c_eq_q0` (Phase 2a doesn't correct ⟹ q0c = q0). -/
theorem div128Quot_shift0_q0c_toNat_le_one (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63) :
    (let dHi := b3 >>> (32 : BitVec 6).toNat
     let dLo := (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
     let div_un1 := a3 >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
     let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
     let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
     let cu_q1_dlo := q1' * dLo
     let un21 := cu_rhat_un1 - cu_q1_dlo
     let q0 := rv64_divu un21 dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     (if hi2 = 0 then q0 else q0 + signExtend12 4095).toNat ≤ 1) := by
  simp only []
  rw [div128Quot_shift0_q0c_eq_q0 a3 b3 hb3_ge]
  exact div128Quot_shift0_q0_le_one a3 b3 hb3_ge

/-- Under uHi=0 + b3 ≥ 2^63: in the div128Quot shift=0 chain, `q0'.toNat ≤ 1`.
    Applies generic `div128Quot_phase2b_q0'_toNat_le_one` to
    `div128Quot_shift0_q0c_toNat_le_one`. -/
theorem div128Quot_shift0_q0_prime_toNat_le_one (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63) :
    (let dHi := b3 >>> (32 : BitVec 6).toNat
     let dLo := (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
     let div_un1 := a3 >>> (32 : BitVec 6).toNat
     let div_un0 := (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu (0 : Word) dHi
     let rhat := (0 : Word) - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
     let rhatc := if hi1 = 0 then rhat else rhat + dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
     let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
     let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
     let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
     let cu_q1_dlo := q1' * dLo
     let un21 := cu_rhat_un1 - cu_q1_dlo
     let q0 := rv64_divu un21 dHi
     let rhat2 := un21 - q0 * dHi
     let hi2 := q0 >>> (32 : BitVec 6).toNat
     let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
     let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
     (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat ≤ 1) := by
  simp only []
  apply div128Quot_phase2b_q0'_toNat_le_one
  exact div128Quot_shift0_q0c_toNat_le_one a3 b3 hb3_ge

/-- Upper bound: under shift=0 (b3 ≥ 2^63), `div128Quot 0 a3 b3` is at most 1.

    Proof sketch:
    1. div128Quot_toNat_eq gives qHat.toNat = (q1' % 2^32)*2^32 + q0'.toNat.
    2. q1' = 0 under uHi=0 (Phase 1 trivialization).
    3. q0'.toNat ≤ 1 under uHi=0: q0 = un21/dHi ≤ 1 (un21 < 2^32, dHi ≥ 2^31),
       Phase 2a doesn't correct (hi2 = 0), q0c = q0 ≤ 1. Phase 2b either
       keeps q0c or decrements to q0c - 1 ≤ 0 ≤ 1. -/
theorem div128Quot_shift0_le_one (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63) :
    (div128Quot (0 : Word) a3 b3).toNat ≤ 1 := by
  have hdHi_ne := div128Quot_shift0_dHi_ne b3 hb3_ge
  have h_q0'_le_one := div128Quot_shift0_q0_prime_toNat_le_one a3 b3 hb3_ge
  have h_q1'_zero := div128Quot_shift0_q1_prime_eq_zero
    (b3 >>> (32 : BitVec 6).toNat)
    ((b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
    (a3 >>> (32 : BitVec 6).toNat) hdHi_ne
  unfold div128Quot
  dsimp only at h_q0'_le_one h_q1'_zero ⊢
  rw [h_q1'_zero] at h_q0'_le_one ⊢
  have h_zero_shift : ((0 : Word) <<< (32 : BitVec 6).toNat) = 0 := by decide
  rw [h_zero_shift]
  have h_zero_or : ∀ x : Word, (0 ||| x) = x := fun x => by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [h_zero_or]
  exact h_q0'_le_one

/-- **Lower bound (composite)**: under shift=0 (b3 ≥ 2^63) + b3 ≠ 0:
    `(div128Quot 0 a3 b3).toNat ≥ a3.toNat / b3.toNat`.

    Proof outline:
    1. Apply KB-LB8 specialized with `un21 := a3 >>> 32, uLo := a3`:
       gives q0'.toNat ≥ (un21*2^32 + div_un0) / (dHi*2^32 + dLo)
       which simplifies to `a3.toNat / b3.toNat` via `word_hi32_lo32_decomp`.
    2. Use `div128Quot_toNat_eq` + `q1'_eq_zero` to show
       `(div128Quot 0 a3 b3).toNat = q0'.toNat`.
    3. Combine. -/
theorem div128Quot_shift0_ge_a3_div_b3 (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63) :
    (div128Quot (0 : Word) a3 b3).toNat ≥ a3.toNat / b3.toNat := by
  -- Setup: standard arithmetic facts under shift=0.
  have hdHi_ne := div128Quot_shift0_dHi_ne b3 hb3_ge
  have hdHi_ge := div128Quot_shift0_dHi_ge b3 hb3_ge
  have hdHi_lt : (b3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := hi32_toNat_lt_pow32 b3
  have hdLo_lt : ((b3 <<< (32 : BitVec 6).toNat) >>>
                  (32 : BitVec 6).toNat).toNat < 2^32 := lo32_toNat_lt_pow32 b3
  have h_un21_lt : (a3 >>> (32 : BitVec 6).toNat : Word).toNat < 2^63 := by
    have := hi32_toNat_lt_pow32 a3
    have : (2 : Nat) ^ 63 > 2^32 := by decide
    omega
  have h_un21_lt_vTop : (a3 >>> (32 : BitVec 6).toNat : Word).toNat <
      (b3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    have h_b3_decomp := word_hi32_lo32_decomp b3
    have := hi32_toNat_lt_pow32 a3
    omega
  -- KB-LB8: q0'.toNat ≥ (a3>>>32 * 2^32 + (a3<<32)>>32) / (b3>>>32 * 2^32 + (b3<<32)>>32).
  have h_lb8 := div128Quot_q0_prime_ge_q_true_0_of_un21_lt_pow63
    (a3 >>> (32 : BitVec 6).toNat)
    (b3 >>> (32 : BitVec 6).toNat)
    ((b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
    a3 hdHi_ge hdHi_lt hdLo_lt h_un21_lt h_un21_lt_vTop
  -- Chain's un21 equals a3 >>> 32 under shift=0.
  have h_un21_eq := div128Quot_shift0_un21_eq_div_un1
    (b3 >>> (32 : BitVec 6).toNat)
    ((b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
    (a3 >>> (32 : BitVec 6).toNat) hdHi_ne
  -- Chain's q1' equals 0 under shift=0.
  have h_q1'_zero := div128Quot_shift0_q1_prime_eq_zero
    (b3 >>> (32 : BitVec 6).toNat)
    ((b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
    (a3 >>> (32 : BitVec 6).toNat) hdHi_ne
  -- Rewrite the KB-LB8 LHS via word_hi32_lo32_decomp to get a3.toNat / b3.toNat.
  have h_a3 := word_hi32_lo32_decomp a3
  have h_b3 := word_hi32_lo32_decomp b3
  dsimp only at h_lb8
  rw [h_a3, h_b3] at h_lb8
  -- Now h_lb8 : a3.toNat / b3.toNat ≤ (phase2b_q0' ...).toNat
  -- Unfold div128Quot and substitute q1' = 0 and un21 = a3 >>> 32 in goal.
  unfold div128Quot
  dsimp only at h_q1'_zero h_un21_eq h_lb8 ⊢
  rw [h_q1'_zero] at ⊢
  have h_zero_shift : ((0 : Word) <<< (32 : BitVec 6).toNat) = 0 := by decide
  rw [h_zero_shift]
  have h_zero_or : ∀ x : Word, (0 ||| x) = x := fun x => by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [h_zero_or]
  -- Now goal: (div128Quot's q0' with q1' := 0).toNat ≥ a3.toNat / b3.toNat
  -- The Q0' here should unify with h_lb8's q0' via chain's un21 = a3 >>> 32.
  rw [h_q1'_zero] at h_un21_eq
  rw [h_un21_eq]
  exact h_lb8

/-- If `div128Quot 0 a3 b3 = 0` under shift=0, then a3 < b3. -/
theorem div128Quot_shift0_eq_zero_implies_a3_lt_b3 (a3 b3 : Word)
    (hb3_ge : b3.toNat ≥ 2^63)
    (hqHat_zero : div128Quot (0 : Word) a3 b3 = 0) :
    a3.toNat < b3.toNat := by
  have h_ge := div128Quot_shift0_ge_a3_div_b3 a3 b3 hb3_ge
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
    (hb : val256 b0 b1 b2 b3 > 0) :
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot (0 : Word) a3 b3).toNat := by
  have h_algo := div128Quot_shift0_ge_a3_div_b3 a3 b3 hb3_ge
  have h_arith := a3_div_b3_ge_val256_div a0 a1 a2 a3 b0 b1 b2 b3 hb3_ge hb
  omega

end EvmAsm.Evm64
