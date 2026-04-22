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

/-- **KB-3e': Tighter post-Phase-1a bound on q1c under hcall.** Phase 1a's
    `hi1` correction absorbs one overshoot beyond `2^32`:

    ```
    q1c.toNat ≤ 2^32
    ```

    - hi1 = 0 branch: `q1 < 2^32` (by definition of hi1), so q1c = q1 < 2^32.
    - hi1 ≠ 0 branch: `q1 ≥ 2^32`, combined with KB-3c `q1 ≤ 2^32 + 1`,
      gives `q1 ∈ {2^32, 2^32 + 1}`, so `q1c = q1 - 1 ∈ {2^32 - 1, 2^32}`.

    Tightens KB-3c (`q1 ≤ 2^32 + 1`) by one after Phase 1a. The
    post-Phase-1b analogue `div128Quot_q1_prime_le_pow32` follows by
    Phase 1b monotonicity (KB-3d2). -/
theorem div128Quot_q1c_le_pow32 (uHi dHi dLo : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat ≤ 2^32 := by
  intro q1 hi1 q1c
  have h_q1_le : q1.toNat ≤ 2^32 + 1 :=
    div128Quot_q1_le_pow32_plus_one uHi dHi dLo hdHi_ge hdLo_lt huHi_lt_vTop
  by_cases h_hi1 : hi1 = 0
  · -- hi1 = 0 ⟹ q1 < 2^32 ⟹ q1c = q1 < 2^32.
    have h32 : (32 : BitVec 6).toNat = 32 := by decide
    have h_hi1_toNat : hi1.toNat = 0 := by rw [h_hi1]; rfl
    have h_q1_div : q1.toNat / 2^32 = 0 := by
      have : hi1.toNat = q1.toNat / 2^32 := by
        rw [BitVec.toNat_ushiftRight, h32, Nat.shiftRight_eq_div_pow]
      omega
    have hq1_lt : q1.toNat < 2^32 := by
      have h_pos : (0 : Nat) < 2^32 := by decide
      exact Nat.lt_of_div_eq_zero h_pos h_q1_div
    show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat ≤ _
    rw [if_pos h_hi1]
    omega
  · -- hi1 ≠ 0 ⟹ q1 ≥ 2^32. KB-3c gives q1 ≤ 2^32 + 1, so q1c = q1 - 1 ≤ 2^32.
    have hq1_ge : q1.toNat ≥ 2^32 := by
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

/-- **KB-3e'': Tighter post-Phase-1b bound on q1' under hcall.** Composes
    KB-3e' (`div128Quot_q1c_le_pow32`) with Phase 1b monotonicity
    (KB-3d2) to give:

    ```
    q1'.toNat ≤ 2^32
    ```

    Strict tightening of KB-3e (`q1' ≤ 2^32 + 1`) by one. Brings us one
    step closer to Knuth's `q1' < 2^32` invariant (needed for clean
    `halfword_combine` on the final output, avoiding the `% 2^32` wrap
    in KB-6a). -/
theorem div128Quot_q1_prime_le_pow32 (uHi dHi dLo rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    q1'.toNat ≤ 2^32 := by
  intro q1 hi1 q1c q1'
  have h_q1c_le : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt huHi_lt_vTop
  have h_q1'_le_q1c : q1'.toNat ≤ q1c.toNat :=
    div128Quot_q1_prime_le_q1c q1c dLo rhatUn1
  omega

/-- **KB-3e''': Strict q1' bound `< 2^32` under hcall (Knuth tightening
    closed).** Closes the last gap in the Phase 1 tightening chain:

    ```
    q1'.toNat < 2^32
    ```

    Case analysis on `q1c.toNat`:
    - **q1c < 2^32**: Phase 1b monotonicity (KB-3d2) gives `q1' ≤ q1c < 2^32`.
    - **q1c = 2^32**: The Euclidean equation `q1c * dHi + rhatc = uHi` combined
      with `uHi < dHi * 2^32 + dLo` forces `rhatc < dLo < 2^32`. Then
      `rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat` (halfword_combine)
      and `(q1c * dLo).toNat = 2^32 * dLo.toNat` (no wrap). The Phase 1b
      check `rhatUn1 < q1c * dLo` fires (since
      `rhatc * 2^32 + div_un1 < dLo * 2^32 = q1c * dLo`), making
      `q1' = q1c - 1 = 2^32 - 1 < 2^32`.

    This is Knuth's multiplication-check correctness for Phase 1b at the
    Word level — the last piece needed to get `q1' < 2^32` so that
    `halfword_combine` (not just `halfword_combine_mod`) applies to the
    `cu_rhat_un1` construction.

    Precondition `hdHi_lt : dHi.toNat < 2^32` added (needed for
    `div128Quot_first_round_post`); automatically satisfied when
    `dHi = vTop >>> 32` (the algorithm's actual instantiation). -/
theorem div128Quot_q1_prime_lt_pow32 (uHi dHi dLo uLo : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    q1'.toNat < 2^32 := by
  intro q1 rhat hi1 q1c rhatc div_un1 rhatUn1 q1'
  have h_q1c_le : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt huHi_lt_vTop
  by_cases h_eq : q1c.toNat = 2^32
  · -- q1c = 2^32: Phase 1b check fires.
    have hdHi_ne : dHi ≠ 0 := by
      intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
    have h_post : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat :=
      div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
    have h_rhatc_lt_dLo : rhatc.toNat < dLo.toNat := by
      rw [h_eq] at h_post
      omega
    have h_rhatc_lt_pow32 : rhatc.toNat < 2^32 := by omega
    have h_div_un1_lt : div_un1.toNat < 2^32 := by
      show (uLo >>> (32 : BitVec 6).toNat).toNat < 2^32
      rw [BitVec.toNat_ushiftRight]
      have h32 : (32 : BitVec 6).toNat = 32 := by decide
      rw [h32, Nat.shiftRight_eq_div_pow]
      have h_ulo_isLt : uLo.toNat < 2^64 := uLo.isLt
      have h_eq : (2^64 : Nat) = 2^32 * 2^32 := by decide
      exact Nat.div_lt_of_lt_mul (by omega)
    -- rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat.
    have h_rhatUn1_eq : rhatUn1.toNat =
        rhatc.toNat * 2^32 + div_un1.toNat := by
      show ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat = _
      have h32 : (32 : BitVec 6).toNat = 32 := by decide
      rw [h32]
      exact EvmWord.halfword_combine rhatc div_un1 h_rhatc_lt_pow32 h_div_un1_lt
    -- (q1c * dLo).toNat = q1c.toNat * dLo.toNat (no wrap: 2^32 * dLo < 2^64).
    have h_qDlo_eq : (q1c * dLo).toNat = q1c.toNat * dLo.toNat := by
      rw [BitVec.toNat_mul]
      apply Nat.mod_eq_of_lt
      rw [h_eq]
      calc 2^32 * dLo.toNat < 2^32 * 2^32 := by
              apply Nat.mul_lt_mul_left (by decide : 0 < 2^32) |>.mpr hdLo_lt
        _ = 2^64 := by decide
    -- Phase 1b check fires.
    have h_ult : rhatUn1.toNat < (q1c * dLo).toNat := by
      rw [h_rhatUn1_eq, h_qDlo_eq, h_eq]
      calc rhatc.toNat * 2^32 + div_un1.toNat
          < rhatc.toNat * 2^32 + 2^32 := by omega
        _ = (rhatc.toNat + 1) * 2^32 := by ring
        _ ≤ dLo.toNat * 2^32 := Nat.mul_le_mul_right _ (by omega)
        _ = 2^32 * dLo.toNat := by ring
    have h_check : BitVec.ult rhatUn1 (q1c * dLo) := by
      show decide (rhatUn1.toNat < (q1c * dLo).toNat) = true
      exact decide_eq_true h_ult
    show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
          else q1c).toNat < 2^32
    rw [if_pos h_check]
    have h_se_neg1 : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
    rw [BitVec.toNat_add, h_se_neg1]
    have h_q1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
    rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_lt_word]
    omega
  · -- q1c < 2^32 case: q1' ≤ q1c < 2^32.
    have h_q1c_lt : q1c.toNat < 2^32 := by omega
    have h_q1'_le_q1c : q1'.toNat ≤ q1c.toNat :=
      div128Quot_q1_prime_le_q1c q1c dLo rhatUn1
    omega

/-- **KB-6b: Phase 2b strict q0' bound `< 2^32` under `un21 < vTop`.** The
    Phase 2 mirror of KB-3e''' (`div128Quot_q1_prime_lt_pow32`):

    ```
    q0'.toNat < 2^32
    ```

    under `un21.toNat < dHi.toNat * 2^32 + dLo.toNat` (the Phase 2
    analogue of hcall) + `dHi ≥ 2^31` + `dHi < 2^32` + `dLo < 2^32`.

    Case analysis on q0c (via `div128Quot_q1c_le_pow32` with `uHi := un21`):

    - **q0c < 2^32**: Phase 2b monotonicity (via `div128Quot_q1_prime_le_q1c`
      with `q1c := q0c`) gives `q0' ≤ q0c < 2^32`.
    - **q0c = 2^32**: The Phase 2a Euclidean `q0c * dHi + rhat2c = un21`
      combined with `un21 < dHi * 2^32 + dLo` forces `rhat2c < dLo < 2^32`.
      Then `rhat2Un0.toNat = rhat2c.toNat * 2^32 + div_un0.toNat`
      (halfword_combine) and `(q0c * dLo).toNat = 2^32 * dLo.toNat` (no
      wrap). The Phase 2b check fires, making `q0' = q0c - 1 = 2^32 - 1`.

    **Blocked in practice on `un21 < vTop`**: the Phase 2 precondition
    requires threading Phase 1's post-state through a Knuth invariant
    argument (q1' ≥ q_true ⇒ un21 = uHi·2^32 + div_un1 − q1'·vTop ≤ vTop).
    This is the remaining Phase-2 gap; once closed, KB-6b + KB-6a combine
    to give `div128Quot.toNat = q1'.toNat * 2^32 + q0'.toNat` without the
    `% 2^32` wrap. -/
theorem div128Quot_q0_prime_lt_pow32 (un21 dHi dLo uLo : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (hun21_lt_vTop : un21.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2Un0 (q0c * dLo) then q0c + signExtend12 4095
               else q0c
    q0'.toNat < 2^32 := by
  intro q0 rhat2 hi2 q0c rhat2c div_un0 rhat2Un0 q0'
  -- Reuse Phase 1 lemma with uHi := un21.
  have h_q0c_le : q0c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 un21 dHi dLo hdHi_ge hdLo_lt hun21_lt_vTop
  by_cases h_eq : q0c.toNat = 2^32
  · -- q0c = 2^32: Phase 2b check fires.
    have hdHi_ne : dHi ≠ 0 := by
      intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
    have h_post : q0c.toNat * dHi.toNat + rhat2c.toNat = un21.toNat :=
      div128Quot_first_round_post un21 dHi hdHi_ne hdHi_lt
    have h_rhat2c_lt_dLo : rhat2c.toNat < dLo.toNat := by
      rw [h_eq] at h_post
      omega
    have h_rhat2c_lt_pow32 : rhat2c.toNat < 2^32 := by omega
    have h_div_un0_lt : div_un0.toNat < 2^32 := by
      show ((uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
      rw [BitVec.toNat_ushiftRight]
      have h32 : (32 : BitVec 6).toNat = 32 := by decide
      rw [h32, Nat.shiftRight_eq_div_pow]
      have h_shl_isLt : (uLo <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
        (uLo <<< (32 : BitVec 6).toNat : Word).isLt
      have h_eq_64 : (2^64 : Nat) = 2^32 * 2^32 := by decide
      exact Nat.div_lt_of_lt_mul (by omega)
    -- rhat2Un0.toNat = rhat2c.toNat * 2^32 + div_un0.toNat.
    have h_rhat2Un0_eq : rhat2Un0.toNat =
        rhat2c.toNat * 2^32 + div_un0.toNat := by
      show ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0).toNat = _
      have h32 : (32 : BitVec 6).toNat = 32 := by decide
      rw [h32]
      exact EvmWord.halfword_combine rhat2c div_un0 h_rhat2c_lt_pow32 h_div_un0_lt
    -- (q0c * dLo).toNat = q0c.toNat * dLo.toNat (no wrap).
    have h_q0Dlo_eq : (q0c * dLo).toNat = q0c.toNat * dLo.toNat := by
      rw [BitVec.toNat_mul]
      apply Nat.mod_eq_of_lt
      rw [h_eq]
      calc 2^32 * dLo.toNat < 2^32 * 2^32 := by
              apply Nat.mul_lt_mul_left (by decide : 0 < 2^32) |>.mpr hdLo_lt
        _ = 2^64 := by decide
    have h_ult : rhat2Un0.toNat < (q0c * dLo).toNat := by
      rw [h_rhat2Un0_eq, h_q0Dlo_eq, h_eq]
      calc rhat2c.toNat * 2^32 + div_un0.toNat
          < rhat2c.toNat * 2^32 + 2^32 := by omega
        _ = (rhat2c.toNat + 1) * 2^32 := by ring
        _ ≤ dLo.toNat * 2^32 := Nat.mul_le_mul_right _ (by omega)
        _ = 2^32 * dLo.toNat := by ring
    have h_check : BitVec.ult rhat2Un0 (q0c * dLo) := by
      show decide (rhat2Un0.toNat < (q0c * dLo).toNat) = true
      exact decide_eq_true h_ult
    show (if BitVec.ult rhat2Un0 (q0c * dLo) then q0c + signExtend12 4095
          else q0c).toNat < 2^32
    rw [if_pos h_check]
    have h_se_neg1 : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
    rw [BitVec.toNat_add, h_se_neg1]
    have h_q0c_lt_word : q0c.toNat - 1 < 2^64 := by have := q0c.isLt; omega
    rw [show q0c.toNat + (2^64 - 1) = (q0c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt h_q0c_lt_word]
    omega
  · -- q0c < 2^32 case: q0' ≤ q0c < 2^32.
    have h_q0c_lt : q0c.toNat < 2^32 := by omega
    have h_q0'_le_q0c : q0'.toNat ≤ q0c.toNat :=
      div128Quot_q1_prime_le_q1c q0c dLo rhat2Un0
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

/-- Utility: right-shifting a 64-bit Word by 32 produces a value bounded
    by `2^32`. -/
theorem Word_ushiftRight_32_lt_pow32 (x : Word) :
    (x >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
  rw [BitVec.toNat_ushiftRight]
  have h32 : (32 : BitVec 6).toNat = 32 := by decide
  rw [h32, Nat.shiftRight_eq_div_pow]
  have : x.toNat < 2^64 := x.isLt
  have : x.toNat / 2^32 < 2^32 := by
    apply Nat.div_lt_of_lt_mul
    have : (2^32 : Nat) * 2^32 = 2^64 := by decide
    omega
  exact this

/-- **KB-3h: cu_rhat_un1.toNat formula.** For Phase 2's
    `cu_rhat_un1 := (rhat' <<< 32) ||| div_un1` where `div_un1 := uLo >>> 32`,
    the Nat representation is:

    ```
    cu_rhat_un1.toNat = (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat
    ```

    Direct application of `halfword_combine_mod` (KB-3g) with
    `div_un1 < 2^32` discharged via `Word_ushiftRight_32_lt_pow32`.

    Key step of the Phase 2 un21 identity.  Note that if `rhat' ≥ 2^32`
    (possible under the current `rhat' < 3 * dHi` bound), the formula
    truncates `rhat'` modulo `2^32` — Phase 2 "sees" only the low 32
    bits of rhat'. -/
theorem div128Quot_cu_rhat_un1_toNat (rhat' uLo : Word) :
    ((rhat' <<< (32 : BitVec 6).toNat) ||| (uLo >>> (32 : BitVec 6).toNat)).toNat =
    (rhat'.toNat % 2^32) * 2^32 + (uLo >>> (32 : BitVec 6).toNat).toNat := by
  have h32 : (32 : BitVec 6).toNat = 32 := by decide
  rw [h32]
  apply halfword_combine_mod
  rw [← h32]
  exact Word_ushiftRight_32_lt_pow32 uLo

/-- **KB-3i: un21.toNat Nat formula.** Composes KB-3f (q1' * dLo no-wrap
    under hcall) + KB-3h (cu_rhat_un1 formula) + `BitVec.toNat_sub` to
    give an explicit modular-arithmetic formula for `un21.toNat`:

    ```
    un21.toNat =
      ((rhat'.toNat % 2^32) * 2^32 + (uLo >>> 32).toNat + 2^64
         - q1'.toNat * dLo.toNat) % 2^64
    ```

    under the standard hcall preconditions (`dHi ≥ 2^31`, `dLo < 2^32`,
    `uHi < dHi * 2^32 + dLo`).

    The `% 2^64` captures potential BitVec wraparound when `cu_q1_dlo`
    exceeds `cu_rhat_un1` (which happens in the "correction" case of
    Phase 2).  Subsequent lemmas can case-split on the wraparound. -/
theorem div128Quot_un21_toNat (uHi dHi dLo uLo rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    un21.toNat = ((rhat'.toNat % 2^32) * 2^32 + div_un1.toNat + 2^64 -
                   q1'.toNat * dLo.toNat) % 2^64 := by
  intro q1 rhat hi1 q1c rhatc q1' rhat' div_un1 cu_rhat_un1 cu_q1_dlo un21
  have h_cu_rhat : cu_rhat_un1.toNat =
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat :=
    div128Quot_cu_rhat_un1_toNat rhat' uLo
  have h_cu_q1 : cu_q1_dlo.toNat = q1'.toNat * dLo.toNat :=
    div128Quot_q1_prime_dLo_no_wrap uHi dHi dLo rhatUn1
      hdHi_ge hdLo_lt huHi_lt_vTop
  show (cu_rhat_un1 - cu_q1_dlo).toNat = _
  rw [BitVec.toNat_sub, h_cu_rhat, h_cu_q1]
  -- Reassociation modulo 2^64.
  congr 1
  omega

/-- **KB-3j: un21.toNat case-split on wraparound.** Resolves the
    modular formula from KB-3i into two cases based on whether the
    BitVec subtraction wraps:

    Let `A := (rhat'.toNat % 2^32) * 2^32 + (uLo >>> 32).toNat`
    and `B := q1'.toNat * dLo.toNat`.

    - **No wrap** (`B ≤ A`): `un21.toNat = A - B`.
    - **Wrap** (`A < B`): `un21.toNat = A + 2^64 - B`.

    The "no wrap" case is Knuth's expected flow. The "wrap" case should
    never occur in Knuth's algorithm by the multiplication-check
    invariant (Phase 1b was designed to prevent it), but formalizing
    that takes substantial work, so this lemma exposes both branches
    and leaves the choice to downstream reasoning. -/
theorem div128Quot_un21_toNat_case (uHi dHi dLo uLo rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let A := (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat
    let B := q1'.toNat * dLo.toNat
    (B ≤ A → un21.toNat = A - B) ∧
    (A < B → un21.toNat = A + 2^64 - B) := by
  intro q1 rhat hi1 q1c rhatc q1' rhat' div_un1 cu_rhat_un1 cu_q1_dlo un21 A B
  have h_formula : un21.toNat = (A + 2^64 - B) % 2^64 :=
    div128Quot_un21_toNat uHi dHi dLo uLo rhatUn1
      hdHi_ge hdLo_lt huHi_lt_vTop
  have h_A_lt : A < 2^64 := by
    show (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat < 2^64
    have h_rhat_mod : rhat'.toNat % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
    have h_divun1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32 uLo
    nlinarith
  have h_B_lt : B < 2^64 := by
    show q1'.toNat * dLo.toNat < 2^64
    have h_cu : cu_q1_dlo.toNat = q1'.toNat * dLo.toNat :=
      div128Quot_q1_prime_dLo_no_wrap uHi dHi dLo rhatUn1
        hdHi_ge hdLo_lt huHi_lt_vTop
    have := cu_q1_dlo.isLt
    omega
  refine ⟨?_, ?_⟩
  · intro hBA
    rw [h_formula]
    show (A + 2^64 - B) % 2^64 = A - B
    rw [show A + 2^64 - B = (A - B) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : A - B < 2^64)]
  · intro hAB
    rw [h_formula]
    show (A + 2^64 - B) % 2^64 = A + 2^64 - B
    exact Nat.mod_eq_of_lt (by omega)

/-- **KB-3k: vTop decomposition.** The divisor `vTop` decomposes cleanly
    into its high and low 32-bit halves `dHi` and `dLo`:

    ```
    vTop.toNat = dHi.toNat * 2^32 + dLo.toNat
    ```

    where `dHi := vTop >>> 32` and `dLo := (vTop <<< 32) >>> 32`.

    Pure utility: holds unconditionally for any 64-bit `vTop`.  Used to
    connect Phase 2's formula (involving `dHi` and `dLo` separately) with
    abstract dividend quantities that use `vTop` directly. -/
theorem div128Quot_vTop_decomp (vTop : Word) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
  intro dHi dLo
  have h32 : (32 : BitVec 6).toNat = 32 := by decide
  have h_dHi : dHi.toNat = vTop.toNat / 2^32 := by
    show (vTop >>> (32 : BitVec 6).toNat).toNat = _
    rw [BitVec.toNat_ushiftRight, h32, Nat.shiftRight_eq_div_pow]
  have h_dLo : dLo.toNat = vTop.toNat % 2^32 := by
    show ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat = _
    rw [BitVec.toNat_ushiftRight, h32, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_shiftLeft]
    simp only [Nat.shiftLeft_eq]
    rw [show (2^64 : Nat) = 2^32 * 2^32 from by decide,
        Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by decide : (0:Nat) < 2^32)]
  rw [h_dHi, h_dLo]
  have := Nat.div_add_mod vTop.toNat (2^32)
  omega

/-- Utility: multiplying a Nat by `2^32` decomposes via Nat.div_add_mod. -/
theorem Nat_mul_pow32_split (x : Nat) :
    x * 2^32 = (x / 2^32) * 2^64 + (x % 2^32) * 2^32 := by
  have hdiv : x = (x / 2^32) * 2^32 + x % 2^32 := by
    have := Nat.div_add_mod x (2^32); linarith
  calc x * 2^32
      = ((x / 2^32) * 2^32 + x % 2^32) * 2^32 := by rw [← hdiv]
    _ = (x / 2^32) * (2^32 * 2^32) + (x % 2^32) * 2^32 := by ring
    _ = (x / 2^32) * 2^64 + (x % 2^32) * 2^32 := by
        rw [show (2^32 * 2^32 : Nat) = 2^64 from by decide]

/-- **KB-3l: un21 connects to the abstract dividend (no-wrap case).**
    Under call-trial preconditions, Phase 1b Euclidean, and no-wrap
    (B ≤ A in KB-3j's notation), plus the semantic ordering
    `q1' * vTop ≤ uHi * 2^32 + div_un1`:

    ```
    un21.toNat + (rhat'.toNat / 2^32) * 2^64 =
      uHi.toNat * 2^32 + (uLo >>> 32).toNat - q1'.toNat * vTop.toNat
    ```

    The `(rhat' / 2^32) * 2^64` correction captures the "lost high bits"
    of `rhat'` truncated by the shift in `cu_rhat_un1`. When `rhat' <
    2^32` (Knuth's tight invariant, currently unproven here), this
    correction is zero and `un21` equals the abstract dividend directly. -/
theorem div128Quot_un21_abstract_dividend
    (uHi dHi dLo uLo vTop rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat)
    (h_dHi_eq : dHi = vTop >>> (32 : BitVec 6).toNat)
    (h_dLo_eq : dLo = (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let A := (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat
    let B := q1'.toNat * dLo.toNat
    B ≤ A →
    q1'.toNat * vTop.toNat ≤ uHi.toNat * 2^32 + div_un1.toNat →
    un21.toNat + (rhat'.toNat / 2^32) * 2^64 =
      uHi.toNat * 2^32 + div_un1.toNat - q1'.toNat * vTop.toNat := by
  intro q1 rhat hi1 q1c rhatc q1' rhat' div_un1 cu_rhat_un1 cu_q1_dlo un21 A B
    hBA habs_ge
  have h_case := div128Quot_un21_toNat_case uHi dHi dLo uLo rhatUn1
    hdHi_ge hdLo_lt huHi_lt_vTop
  have h_un21 : un21.toNat = A - B := h_case.1 hBA
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have hdHi_lt : dHi.toNat < 2^32 := by
    rw [h_dHi_eq]; exact Word_ushiftRight_32_lt_pow32 vTop
  have h_post := div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  have h_rhatc_lt := div128Quot_rhatc_lt_2dHi uHi dHi hdHi_ne hdHi_lt
  have h_eucl : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat :=
    div128Quot_phase1b_post uHi dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post h_rhatc_lt
  have h_vtop := div128Quot_vTop_decomp vTop
  rw [← h_dHi_eq, ← h_dLo_eq] at h_vtop
  -- Sub-lemma 1: rhat' * 2^32 decomposes.
  have h_rhat_split : rhat'.toNat * 2^32 =
      (rhat'.toNat / 2^32) * 2^64 + (rhat'.toNat % 2^32) * 2^32 :=
    Nat_mul_pow32_split rhat'.toNat
  -- Sub-lemma 2: rhat' = uHi - q1' * dHi at Nat (from h_eucl).
  have h_rhat_eq : rhat'.toNat = uHi.toNat - q1'.toNat * dHi.toNat := by omega
  -- Sub-lemma 3: q1' * vTop expanded.
  have h_q1_vtop : q1'.toNat * vTop.toNat =
      q1'.toNat * dHi.toNat * 2^32 + q1'.toNat * dLo.toNat := by
    rw [h_vtop]; ring
  -- Sub-lemma 4: q1' * dHi * 2^32 ≤ uHi * 2^32.
  have h_le : q1'.toNat * dHi.toNat * 2^32 ≤ uHi.toNat * 2^32 := by
    apply Nat.mul_le_mul_right; omega
  -- Sub-lemma 5: rhat' * 2^32 = uHi * 2^32 - q1' * dHi * 2^32.
  have h_rhat_mul : rhat'.toNat * 2^32 =
      uHi.toNat * 2^32 - q1'.toNat * dHi.toNat * 2^32 := by
    rw [h_rhat_eq, Nat.sub_mul]
  -- Final assembly.
  show un21.toNat + (rhat'.toNat / 2^32) * 2^64 = _
  rw [h_un21]
  show (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat - q1'.toNat * dLo.toNat
    + (rhat'.toNat / 2^32) * 2^64 = _
  -- Key facts for omega:
  -- h_rhat_split: rhat' * 2^32 = (rhat'/2^32) * 2^64 + (rhat'%2^32) * 2^32.
  -- h_rhat_mul: rhat' * 2^32 = uHi * 2^32 - q1' * dHi * 2^32.
  -- h_q1_vtop: q1' * vTop = q1' * dHi * 2^32 + q1' * dLo.
  -- h_le: q1' * dHi * 2^32 ≤ uHi * 2^32.
  -- habs_ge: q1' * vTop ≤ uHi * 2^32 + div_un1.
  -- Goal: (rhat'%2^32) * 2^32 + div_un1 - q1' * dLo + (rhat'/2^32) * 2^64
  --     = uHi * 2^32 + div_un1 - q1' * vTop.
  -- Use hBA to unfold A, B.
  have h_BA_num : q1'.toNat * dLo.toNat ≤
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat := hBA
  omega

/-- **KB-3m: un21 additive identity (no-wrap case).** Reformulation of
    KB-3l using addition instead of subtraction, eliminating the need
    for the semantic ordering hypothesis `habs_ge`:

    ```
    un21.toNat + (rhat'.toNat / 2^32) * 2^64 + q1'.toNat * vTop.toNat =
      uHi.toNat * 2^32 + (uLo >>> 32).toNat
    ```

    Same underlying math as KB-3l, but Nat addition on both sides is
    well-defined without ordering constraints. Use this form downstream
    when you want to reason about the relation without discharging
    `habs_ge`. -/
theorem div128Quot_un21_additive_identity
    (uHi dHi dLo uLo vTop rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat)
    (h_dHi_eq : dHi = vTop >>> (32 : BitVec 6).toNat)
    (h_dLo_eq : dLo = (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let A := (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat
    let B := q1'.toNat * dLo.toNat
    B ≤ A →
    un21.toNat + (rhat'.toNat / 2^32) * 2^64 + q1'.toNat * vTop.toNat =
      uHi.toNat * 2^32 + div_un1.toNat := by
  intro q1 rhat hi1 q1c rhatc q1' rhat' div_un1 cu_rhat_un1 cu_q1_dlo un21 A B hBA
  have h_case := div128Quot_un21_toNat_case uHi dHi dLo uLo rhatUn1
    hdHi_ge hdLo_lt huHi_lt_vTop
  have h_un21 : un21.toNat = A - B := h_case.1 hBA
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have hdHi_lt : dHi.toNat < 2^32 := by
    rw [h_dHi_eq]; exact Word_ushiftRight_32_lt_pow32 vTop
  have h_post := div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  have h_rhatc_lt := div128Quot_rhatc_lt_2dHi uHi dHi hdHi_ne hdHi_lt
  have h_eucl : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat :=
    div128Quot_phase1b_post uHi dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post h_rhatc_lt
  have h_vtop := div128Quot_vTop_decomp vTop
  rw [← h_dHi_eq, ← h_dLo_eq] at h_vtop
  have h_rhat_split : rhat'.toNat * 2^32 =
      (rhat'.toNat / 2^32) * 2^64 + (rhat'.toNat % 2^32) * 2^32 :=
    Nat_mul_pow32_split rhat'.toNat
  have h_rhat_eq : rhat'.toNat = uHi.toNat - q1'.toNat * dHi.toNat := by omega
  have h_rhat_mul : rhat'.toNat * 2^32 =
      uHi.toNat * 2^32 - q1'.toNat * dHi.toNat * 2^32 := by
    rw [h_rhat_eq, Nat.sub_mul]
  have h_q1_vtop : q1'.toNat * vTop.toNat =
      q1'.toNat * dHi.toNat * 2^32 + q1'.toNat * dLo.toNat := by
    rw [h_vtop]; ring
  have h_le : q1'.toNat * dHi.toNat * 2^32 ≤ uHi.toNat * 2^32 := by
    apply Nat.mul_le_mul_right; omega
  show un21.toNat + (rhat'.toNat / 2^32) * 2^64 + q1'.toNat * vTop.toNat = _
  rw [h_un21]
  show (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat - q1'.toNat * dLo.toNat
    + (rhat'.toNat / 2^32) * 2^64 + q1'.toNat * vTop.toNat = _
  have h_BA_num : q1'.toNat * dLo.toNat ≤
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat := hBA
  rw [h_q1_vtop]
  omega

-- ============================================================================
-- Piece B: Phase 2a bounds via Phase 1a reuse (KB-4)
-- ============================================================================

/-- **KB-4a: Phase 2a Euclidean.** Direct instantiation of
    `div128Quot_first_round_post` with `uHi := un21`: the Phase 2a
    post-correction quotient `q0c` and remainder `rhat2c` satisfy the
    Euclidean equation against `un21`:

    ```
    q0c.toNat * dHi.toNat + rhat2c.toNat = un21.toNat
    ```

    Phase 1a lemmas are generic over the dividend — they take any Word
    as `uHi`.  This is the observation documented in the Knuth-B plan
    memo: Phase 2 bounds require no new code beyond thin instantiation
    wrappers. -/
theorem div128Quot_phase2a_euclidean (un21 dHi : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    q0c.toNat * dHi.toNat + rhat2c.toNat = un21.toNat :=
  div128Quot_first_round_post un21 dHi hdHi_ne hdHi_lt

/-- **KB-4b: Phase 2a remainder bound.** Instantiation of
    `div128Quot_rhatc_lt_2dHi`: `rhat2c < 2 * dHi`. -/
theorem div128Quot_phase2a_rhat2c_lt_2dHi (un21 dHi : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    rhat2c.toNat < 2 * dHi.toNat :=
  div128Quot_rhatc_lt_2dHi un21 dHi hdHi_ne hdHi_lt

/-- **KB-4c: Phase 2a quotient bound.** Instantiation of
    `div128Quot_q1c_lt_pow33`: `q0c < 2^33`. -/
theorem div128Quot_phase2a_q0c_lt_pow33 (un21 dHi : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31) :
    let q0 := rv64_divu un21 dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    q0c.toNat < 2^33 :=
  div128Quot_q1c_lt_pow33 un21 dHi hdHi_ge

-- ============================================================================
-- Piece B: Phase 2b bounds via Phase 1b reuse (KB-5)
-- ============================================================================

/-- **KB-5a: Phase 2b Euclidean.** Instantiation of
    `div128Quot_phase1b_post` with `uHi := un21`, `q1c := q0c`,
    `rhatc := rhat2c`: post-Phase-2b (Phase 2b's multiplication-check
    correction), the corrected quotient `q0'` and remainder `rhat2'`
    still satisfy the Euclidean equation against `un21`. -/
theorem div128Quot_phase2b_post (un21 dHi : Word)
    (hdHi_lt : dHi.toNat < 2^32) (q0c rhat2c dLo rhat2Un0 : Word)
    (h_post : q0c.toNat * dHi.toNat + rhat2c.toNat = un21.toNat)
    (h_rhat2c_lt : rhat2c.toNat < 2 * dHi.toNat) :
    let q0' := if BitVec.ult rhat2Un0 (q0c * dLo) then q0c + signExtend12 4095
               else q0c
    let rhat2' := if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c
    q0'.toNat * dHi.toNat + rhat2'.toNat = un21.toNat :=
  div128Quot_phase1b_post un21 dHi q0c rhat2c dLo rhat2Un0 hdHi_lt h_post h_rhat2c_lt

/-- **KB-5b: Phase 2b check implies q0c ≥ 1.** Instantiation of
    `div128Quot_phase1b_check_implies_q1c_pos`. -/
theorem div128Quot_phase2b_check_implies_q0c_pos (q0c dLo rhat2Un0 : Word)
    (h_check : BitVec.ult rhat2Un0 (q0c * dLo)) :
    q0c.toNat ≥ 1 :=
  div128Quot_phase1b_check_implies_q1c_pos q0c dLo rhat2Un0 h_check

/-- **KB-5c: Phase 2b quotient bound.** Instantiation of
    `div128Quot_phase1b_quotient_bound` with `uHi := un21`. -/
theorem div128Quot_phase2b_quotient_bound (un21 dHi : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32)
    (dLo rhat2Un0 : Word) :
    let q0 := rv64_divu un21 dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let q0' := if BitVec.ult rhat2Un0 (q0c * dLo) then q0c + signExtend12 4095
               else q0c
    q0'.toNat + 2 ≥ un21.toNat / dHi.toNat ∧
    q0'.toNat ≤ un21.toNat / dHi.toNat :=
  div128Quot_phase1b_quotient_bound un21 dHi hdHi_ne hdHi_lt dLo rhat2Un0

/-- **KB-5d: Phase 2b output bound.** Instantiation of
    `div128Quot_q1_prime_lt_pow33` with `uHi := un21`: `q0' < 2^33`. -/
theorem div128Quot_phase2b_q0_prime_lt_pow33 (un21 dHi : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31) (dLo rhat2Un0 : Word) :
    let q0 := rv64_divu un21 dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let q0' := if BitVec.ult rhat2Un0 (q0c * dLo) then q0c + signExtend12 4095
               else q0c
    q0'.toNat < 2^33 :=
  div128Quot_q1_prime_lt_pow33 un21 dHi hdHi_ge dLo rhat2Un0

/-- **KB-6a: div128Quot output Nat formula.** Unfolds `div128Quot` and
    applies `halfword_combine_mod` to yield the output's Nat value:

    ```
    (div128Quot uHi uLo vTop).toNat = (q1'.toNat % 2^32) * 2^32 + q0'.toNat
    ```

    when `q0'.toNat < 2^32`.

    The `% 2^32` on `q1'` captures the top bits truncated by the final
    `<<< 32` shift — Phase 1b's `q1'` may exceed `2^32` (current bound
    `≤ 2^32 + 1` under hcall from KB-3e), so those high bits are lost
    in the output assembly. That loss is benign because the Knuth-B
    quotient bound only cares about the value modulo `2^64`, and
    `q_true * vTop ≤ uHi * 2^64 + uLo < 2^64 * vTop` guarantees
    `q_true < 2^64`.

    First step of the final-assembly chain (KB-6). Uses only
    `halfword_combine_mod` (KB-3g) and no Phase 2 infrastructure, so
    lives on the main path of the call-trial bounds. -/
theorem div128Quot_toNat_eq (uHi uLo vTop : Word) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
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
    let q0Dlo := q0c * dLo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2Un0 q0Dlo then q0c + signExtend12 4095 else q0c
    q0'.toNat < 2^32 →
    (div128Quot uHi uLo vTop).toNat = (q1'.toNat % 2^32) * 2^32 + q0'.toNat := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0Dlo rhat2Un0 q0' hq0
  show ((q1' <<< (32 : BitVec 6).toNat) ||| q0').toNat =
    (q1'.toNat % 2^32) * 2^32 + q0'.toNat
  have h32 : (32 : BitVec 6).toNat = 32 := by decide
  rw [h32]
  exact halfword_combine_mod q1' q0' hq0

end EvmAsm.Evm64
