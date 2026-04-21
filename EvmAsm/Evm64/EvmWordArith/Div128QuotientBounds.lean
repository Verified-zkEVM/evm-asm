/-
  EvmAsm.Evm64.EvmWordArith.Div128QuotientBounds

  Top-down quotient-bound analysis for the `div128Quot` algorithm,
  tightening `q1` and `q1'` bounds through Phase 1a and Phase 1b.

  Split from `KnuthTheoremB.lean` (issue #61) to keep that file under
  the 1500-line size cap as Piece B grows.  Subsequent Phase 2 analysis
  (KB-4..KB-6) may land here or in a dedicated file.

  Key lemmas (all prefixed `div128Quot_`):
  - `phase1a_quotient_bound` (KB-1): `q1c.toNat ∈ [uHi/dHi - 1, uHi/dHi]`.
  - `phase1b_quotient_bound` (KB-2): `q1'.toNat ∈ [uHi/dHi - 2, uHi/dHi]`.
  - `phase1b_no_underflow` (KB-3a): `q1'.toNat * dHi.toNat ≤ uHi.toNat`.
  - `q1_prime_lt_pow33` (KB-3b): `q1'.toNat < 2^33`.
  - `q1_le_pow32_plus_one` (KB-3c): `q1.toNat ≤ 2^32 + 1` under hcall.
  - `q1c_le_q1`, `q1_prime_le_q1c` (KB-3d): Phase 1a/1b monotonicity.
  - `q1_prime_le_pow32_plus_one` (KB-3e): `q1'.toNat ≤ 2^32 + 1` under hcall.
  - `q1_prime_dLo_no_wrap` (KB-3f): `q1' * dLo` no-wraparound under hcall.

  See `memory/project_knuth_theorem_b_plan.md` for the full roadmap.
-/

import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Piece B: Phase 1a quotient bound (KB-1)
-- ============================================================================

/-- **KB-1: Phase 1a quotient bound.** The post-correction quotient `q1c`
    is within 1 below the true 64/32 quotient `uHi / dHi`:

    ```
    uHi.toNat / dHi.toNat - 1 ≤ q1c.toNat ≤ uHi.toNat / dHi.toNat
    ```

    Derived from the Euclidean equation `q1c * dHi + rhatc = uHi` (given by
    `div128Quot_first_round_post`) plus `rhatc < 2 * dHi` (given by
    `div128Quot_rhatc_lt_2dHi`). Together they give
    `uHi / dHi ∈ {q1c, q1c + 1}`.

    First concrete lemma of the top-down Knuth-B Piece B attack. Subsequent
    lemmas KB-2..KB-6 tighten the bound through Phase 1b, Phase 2a/2b, and
    final assembly. See `memory/project_knuth_theorem_b_plan.md`. -/
theorem div128Quot_phase1a_quotient_bound (uHi dHi : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    q1c.toNat ≤ uHi.toNat / dHi.toNat ∧
    uHi.toNat / dHi.toNat ≤ q1c.toNat + 1 := by
  intro q1 rhat hi1 q1c rhatc
  -- These match our local let-chain by zeta, so omega below sees matching atoms.
  have h_eucl : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat :=
    div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  have h_rhatc_lt : rhatc.toNat < 2 * dHi.toNat :=
    div128Quot_rhatc_lt_2dHi uHi dHi hdHi_ne hdHi_lt
  have hdHi_pos : 0 < dHi.toNat :=
    Nat.pos_of_ne_zero (fun h => hdHi_ne (BitVec.eq_of_toNat_eq h))
  refine ⟨?_, ?_⟩
  · -- q1c.toNat ≤ uHi.toNat / dHi.toNat: from q1c * dHi ≤ uHi via Euclidean.
    exact (Nat.le_div_iff_mul_le hdHi_pos).mpr (by nlinarith)
  · -- uHi.toNat / dHi.toNat ≤ q1c.toNat + 1: from uHi < (q1c+2)*dHi.
    have h_lt : uHi.toNat < (q1c.toNat + 2) * dHi.toNat := by nlinarith
    have h_div_lt := (Nat.div_lt_iff_lt_mul hdHi_pos).mpr h_lt
    omega

/-- **KB-2: Phase 1b quotient bound.** After Phase 1b's multiplication-check
    correction, the corrected quotient `q1'` is within 2 below the true
    64/32 quotient `uHi / dHi`:

    ```
    uHi.toNat / dHi.toNat - 2 ≤ q1'.toNat ≤ uHi.toNat / dHi.toNat
    ```

    Composes KB-1 (`div128Quot_phase1a_quotient_bound`: q1c ∈ [uHi/dHi - 1,
    uHi/dHi]) with the Phase 1b decrement property:

    - Check doesn't fire → `q1' = q1c` (bound preserved).
    - Check fires → `q1' = q1c - 1` (both bounds shift down by 1, using
      `div128Quot_phase1b_check_implies_q1c_pos` for the "no underflow"
      justification).

    Second concrete lemma of the top-down Knuth-B Piece B attack. -/
theorem div128Quot_phase1b_quotient_bound (uHi dHi : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32)
    (dLo rhatUn1 : Word) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    q1'.toNat + 2 ≥ uHi.toNat / dHi.toNat ∧
    q1'.toNat ≤ uHi.toNat / dHi.toNat := by
  intro q1 hi1 q1c q1'
  -- Extract KB-1 bounds at the right types (matching our local let-chain).
  have h_kb1 := div128Quot_phase1a_quotient_bound uHi dHi hdHi_ne hdHi_lt
  have h_upper_q1c : q1c.toNat ≤ uHi.toNat / dHi.toNat := h_kb1.1
  have h_lower_q1c : uHi.toNat / dHi.toNat ≤ q1c.toNat + 1 := h_kb1.2
  by_cases h_check : BitVec.ult rhatUn1 (q1c * dLo)
  · have h_q1c_pos := div128Quot_phase1b_check_implies_q1c_pos q1c dLo rhatUn1 h_check
    have h_q1'_eq : q1'.toNat = q1c.toNat - 1 := by
      show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095 else q1c).toNat = _
      rw [if_pos h_check]
      have h_se_neg1 : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
      rw [BitVec.toNat_add, h_se_neg1]
      have h_q1c_lt : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
      rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_lt]
    exact ⟨by omega, by omega⟩
  · have h_q1'_eq : q1'.toNat = q1c.toNat := by
      show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095 else q1c).toNat = _
      rw [if_neg h_check]
    exact ⟨by omega, by omega⟩

/-- **KB-3a: Post-Phase-1b no-underflow bound.** The post-corrected
    quotient `q1'` times `dHi` doesn't exceed `uHi` at the Nat level:

    ```
    q1'.toNat * dHi.toNat ≤ uHi.toNat
    ```

    Direct consequence of the Phase 1b Euclidean equation
    `q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat` (from
    `div128Quot_phase1b_post`) and `rhat'.toNat ≥ 0`.

    Useful corollary for Phase 2 analysis: it justifies that
    `uHi - q1' * dHi` doesn't underflow at the Nat level (the subtraction
    is well-defined as a Nat subtraction). -/
theorem div128Quot_phase1b_no_underflow (uHi dHi : Word)
    (hdHi_lt : dHi.toNat < 2^32) (q1c rhatc dLo rhatUn1 : Word)
    (h_post : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat)
    (h_rhatc_lt : rhatc.toNat < 2 * dHi.toNat) :
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    q1'.toNat * dHi.toNat ≤ uHi.toNat := by
  intro q1' rhat'
  -- Extract Phase 1b Euclidean at the right types (matching our local lets).
  have h_eucl : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat :=
    div128Quot_phase1b_post uHi dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post h_rhatc_lt
  omega

/-- **KB-3b: Post-Phase-1b output bound on `q1'.toNat`.** After the
    multiplication-check correction, `q1'` is still bounded by `2^33`:

    ```
    q1'.toNat < 2^33
    ```

    - Check doesn't fire → `q1' = q1c < 2^33` (from `div128Quot_q1c_lt_pow33`).
    - Check fires → `q1' = q1c - 1 < q1c < 2^33`.

    Used in Phase 2 analysis to bound `q1' * dLo` (which feeds into the
    `un21` computation). Companion to `div128Quot_rhat_prime_lt_3dHi`
    (bound on `rhat'`). -/
theorem div128Quot_q1_prime_lt_pow33 (uHi dHi : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31) (dLo rhatUn1 : Word) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    q1'.toNat < 2^33 := by
  intro q1 hi1 q1c q1'
  have h_q1c_lt : q1c.toNat < 2^33 := div128Quot_q1c_lt_pow33 uHi dHi hdHi_ge
  by_cases h_check : BitVec.ult rhatUn1 (q1c * dLo)
  · have h_q1c_pos := div128Quot_phase1b_check_implies_q1c_pos q1c dLo rhatUn1 h_check
    have h_q1'_eq : q1'.toNat = q1c.toNat - 1 := by
      show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095 else q1c).toNat = _
      rw [if_pos h_check]
      have h_se_neg1 : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
      rw [BitVec.toNat_add, h_se_neg1]
      have h_q1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
      rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_lt_word]
    omega
  · have h_q1'_eq : q1'.toNat = q1c.toNat := by
      show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095 else q1c).toNat = _
      rw [if_neg h_check]
    omega

/-- **KB-3c: Tighter q1 bound under `uHi < vTop`.** With the call-trial
    precondition (normalized dividend strictly less than the divisor at
    the 64-bit level), the first-round trial quotient satisfies

    ```
    (rv64_divu uHi dHi).toNat ≤ 2^32 + 1
    ```

    Derived as follows.  `uHi < vTop = dHi * 2^32 + dLo < dHi * 2^32 + 2^32 =
    (dHi + 1) * 2^32`.  Hence `uHi / dHi ≤ (uHi) / dHi ≤ (dHi + 1) * 2^32 / dHi
    = 2^32 + 2^32 / dHi ≤ 2^32 + 2` (using `dHi ≥ 2^31`), i.e.
    `≤ 2^32 + 1` in integer arithmetic.

    Tightens the landed `div128Quot_q1_lt_pow33` (`< 2^33`) bound. This is
    a step toward Knuth's invariant `q̂ ≤ 2^32 - 1` which Phase 1a's
    `hi1` correction enforces. -/
theorem div128Quot_q1_le_pow32_plus_one (uHi dHi dLo : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    (rv64_divu uHi dHi).toNat ≤ 2^32 + 1 := by
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have hdHi_pos : 0 < dHi.toNat := by omega
  rw [rv64_divu_toNat uHi dHi hdHi_ne]
  -- From huHi_lt_vTop: uHi < dHi * 2^32 + 2^32.
  have h_uHi_lt : uHi.toNat < dHi.toNat * 2^32 + 2^32 := by omega
  -- Use Nat.div_lt_iff_lt_mul: uHi / dHi < k ↔ uHi < k * dHi.
  -- We want uHi / dHi ≤ 2^32 + 1, i.e. uHi / dHi < 2^32 + 2, i.e. uHi < (2^32 + 2) * dHi.
  suffices h : uHi.toNat / dHi.toNat < 2^32 + 2 by omega
  apply (Nat.div_lt_iff_lt_mul hdHi_pos).mpr
  -- Goal: uHi.toNat < (2^32 + 2) * dHi.toNat
  -- We have uHi.toNat < dHi.toNat * 2^32 + 2^32, and dHi.toNat ≥ 2^31, so
  -- 2 * dHi.toNat ≥ 2 * 2^31 = 2^32, hence 2^32 ≤ 2 * dHi.toNat.
  -- Thus uHi.toNat < dHi.toNat * 2^32 + 2^32 ≤ dHi.toNat * 2^32 + 2 * dHi.toNat = (2^32 + 2) * dHi.toNat.
  have h_expand : (2^32 + 2) * dHi.toNat = dHi.toNat * 2^32 + 2 * dHi.toNat := by ring
  omega

/-- **KB-3d1: Phase 1a monotonicity.** The post-correction quotient `q1c`
    is never larger than the pre-correction `q1`:

    ```
    q1c.toNat ≤ q1.toNat
    ```

    - No-correction branch (`hi1 = 0`): `q1c = q1`, equality.
    - Correction branch (`hi1 ≠ 0`): `q1c = q1 - 1 < q1` at Nat, using
      `hi1 ≠ 0 → q1 ≥ 2^32 ≥ 1`. -/
theorem div128Quot_q1c_le_q1 (uHi dHi : Word) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat ≤ q1.toNat := by
  intro q1 hi1 q1c
  by_cases h_hi1 : hi1 = 0
  · show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat ≤ _
    rw [if_pos h_hi1]
  · have hq1_ge : q1.toNat ≥ 2^32 := by
      by_contra h
      push_neg at h
      apply h_hi1
      apply BitVec.eq_of_toNat_eq
      have h32 : (32 : BitVec 6).toNat = 32 := by decide
      rw [BitVec.toNat_ushiftRight, h32, Nat.shiftRight_eq_div_pow]
      show q1.toNat / 2^32 = (0 : Word).toNat
      rw [Nat.div_eq_of_lt h]
      rfl
    show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat ≤ _
    rw [if_neg h_hi1]
    have h_se_neg1 : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
    rw [BitVec.toNat_add, h_se_neg1]
    have hq1_lt_word : q1.toNat - 1 < 2^64 := by have := q1.isLt; omega
    rw [show q1.toNat + (2^64 - 1) = (q1.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq1_lt_word]
    omega

/-- **KB-3d2: Phase 1b monotonicity.** The post-Phase-1b quotient `q1'`
    is never larger than the pre-Phase-1b `q1c`:

    ```
    q1'.toNat ≤ q1c.toNat
    ```

    - Check doesn't fire: `q1' = q1c`.
    - Check fires: `q1' = q1c - 1 < q1c` (using
      `div128Quot_phase1b_check_implies_q1c_pos` for the no-underflow). -/
theorem div128Quot_q1_prime_le_q1c (q1c dLo rhatUn1 : Word) :
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    q1'.toNat ≤ q1c.toNat := by
  intro q1'
  by_cases h_check : BitVec.ult rhatUn1 (q1c * dLo)
  · have h_q1c_pos := div128Quot_phase1b_check_implies_q1c_pos q1c dLo rhatUn1 h_check
    show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095 else q1c).toNat ≤ _
    rw [if_pos h_check]
    have h_se_neg1 : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
    rw [BitVec.toNat_add, h_se_neg1]
    have h_q1c_lt : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
    rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_lt]
    omega
  · show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095 else q1c).toNat ≤ _
    rw [if_neg h_check]

/-- **KB-3e: Tight post-Phase-1b bound on q1' under hcall.** Composes
    `div128Quot_q1_le_pow32_plus_one` (q1 ≤ 2^32 + 1 under hcall) with
    the Phase 1a/1b monotonicity lemmas to give:

    ```
    q1'.toNat ≤ 2^32 + 1
    ```

    under `uHi.toNat < dHi.toNat * 2^32 + dLo.toNat` (the call-trial
    precondition). Tightens `div128Quot_q1_prime_lt_pow33` (`< 2^33`)
    by roughly a factor of 2.

    Used in Phase 2 analysis: with q1' ≤ 2^32 + 1 and dLo < 2^32, the
    product q1' * dLo ≤ (2^32 + 1) * 2^32 ≈ 2^64, so we're at the edge
    of the 64-bit range but not overflowing by much. -/
theorem div128Quot_q1_prime_le_pow32_plus_one (uHi dHi dLo rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    q1'.toNat ≤ 2^32 + 1 := by
  intro q1 hi1 q1c q1'
  have h_q1_le : q1.toNat ≤ 2^32 + 1 :=
    div128Quot_q1_le_pow32_plus_one uHi dHi dLo hdHi_ge hdLo_lt huHi_lt_vTop
  have h_q1c_le_q1 : q1c.toNat ≤ q1.toNat := div128Quot_q1c_le_q1 uHi dHi
  have h_q1'_le_q1c : q1'.toNat ≤ q1c.toNat := div128Quot_q1_prime_le_q1c q1c dLo rhatUn1
  omega

/-- **KB-3f: No-wraparound for `q1' * dLo`.** Under the call-trial
    precondition, the Word-level product equals the Nat-level product:

    ```
    (q1' * dLo).toNat = q1'.toNat * dLo.toNat
    ```

    Proof: from KB-3e, `q1'.toNat ≤ 2^32 + 1`; `dLo.toNat < 2^32`.  Hence
    `q1'.toNat * dLo.toNat ≤ (2^32 + 1) * (2^32 - 1) = 2^64 - 1 < 2^64`.
    Word multiplication therefore doesn't wrap, and `BitVec.toNat_mul`
    gives the stated equality.

    This is the key no-wraparound fact for subsequent Phase 2 analysis
    (bounding `un21`, relating it to abstract dividend quantities). -/
theorem div128Quot_q1_prime_dLo_no_wrap (uHi dHi dLo rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    (q1' * dLo).toNat = q1'.toNat * dLo.toNat := by
  intro q1 hi1 q1c q1'
  have h_q1'_le : q1'.toNat ≤ 2^32 + 1 :=
    div128Quot_q1_prime_le_pow32_plus_one uHi dHi dLo rhatUn1
      hdHi_ge hdLo_lt huHi_lt_vTop
  -- q1'.toNat * dLo.toNat ≤ (2^32 + 1) * (2^32 - 1) = 2^64 - 1.
  have h_mul_lt : q1'.toNat * dLo.toNat < 2^64 := by
    have : q1'.toNat * dLo.toNat ≤ (2^32 + 1) * (2^32 - 1) := by
      have hdLo_le : dLo.toNat ≤ 2^32 - 1 := by omega
      exact Nat.mul_le_mul h_q1'_le hdLo_le
    have h_eq : (2^32 + 1) * (2^32 - 1) = 2^64 - 1 := by decide
    omega
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h_mul_lt]

/-- **KB-3g: Generalized halfword combine.** Without an upper bound on
    `a`, the shift-left-by-32 + OR construction still has a clean Nat
    formula, truncating `a` modulo `2^32`:

    ```
    (a <<< 32 ||| b).toNat = (a.toNat % 2^32) * 2^32 + b.toNat
    ```

    Generalizes `halfword_combine` (which requires `a.toNat < 2^32`) by
    dropping the upper bound on `a`.  Useful for the Phase 2 `cu_rhat_un1`
    construction, where `rhat'` may exceed `2^32` (current bound:
    `< 3 * dHi`), so the top bits of `rhat'` get truncated by the shift
    and we need a Nat formula that captures this. -/
theorem halfword_combine_mod (a b : Word) (hb : b.toNat < 2^32) :
    (a <<< 32 ||| b).toNat = (a.toNat % 2^32) * 2^32 + b.toNat := by
  -- The shifted `a <<< 32` has its low 32 bits zero, and `b` has its
  -- high 32 bits zero, so their bitwise AND is zero and OR = ADD.
  have h_disjoint : a <<< 32 &&& b = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
    by_cases hi : (i : Nat) < 32
    · simp [hi]
    · simp only [hi, decide_false, Bool.not_false, Bool.true_and]
      have hbi : b[i] = false := by
        simp only [BitVec.getElem_eq_testBit_toNat]
        apply Nat.testBit_lt_two_pow
        calc b.toNat < 2 ^ 32 := hb
          _ ≤ 2 ^ (i : Nat) := Nat.pow_le_pow_right (by omega) (by omega)
      simp [hbi]
  rw [(BitVec.add_eq_or_of_and_eq_zero (a <<< 32) b h_disjoint).symm,
      BitVec.toNat_add_of_and_eq_zero h_disjoint,
      BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  -- Goal: (a.toNat * 2^32) % 2^64 + b.toNat = (a.toNat % 2^32) * 2^32 + b.toNat
  -- Use (a.toNat * 2^32) % 2^64 = (a.toNat % 2^32) * 2^32.
  have h_mod : (a.toNat * 2^32) % 2^64 = (a.toNat % 2^32) * 2^32 := by
    rw [show (2^64 : Nat) = 2^32 * 2^32 from by decide,
        Nat.mul_mod_mul_right]
  rw [h_mod]

end EvmAsm.Evm64
