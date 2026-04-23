/-
  EvmAsm.Evm64.EvmWordArith.Div128QuotientBounds

  Top-down quotient-bound analysis for the `div128Quot` algorithm,
  tightening `q1` and `q1'` bounds through Phase 1a and Phase 1b.

  Split from `KnuthTheoremB.lean` (issue #61) to keep that file under
  the 1500-line size cap as Piece B grows.

  Phase 1 bounds (KB-1..KB-3e''') live here; the Phase 2 un21 machinery,
  Phase 2a/2b reuse, and final output assembly (KB-3f..KB-3m, KB-4,
  KB-5, KB-6a/6a-strict) were split off into `Div128FinalAssembly.lean`
  when this file crossed the 1500-line guardrail. The Knuth "Lemma A"
  lower-bound chain (KB-LB1..9 + KB-Compose) was split off into
  `Div128KnuthLower.lean` for the same reason.

  Key lemmas in this file (all prefixed `div128Quot_`):
  - `phase1a_quotient_bound` (KB-1): `q1c.toNat ∈ [uHi/dHi - 1, uHi/dHi]`.
  - `phase1b_quotient_bound` (KB-2): `q1'.toNat ∈ [uHi/dHi - 2, uHi/dHi]`.
  - `phase1b_no_underflow` (KB-3a): `q1'.toNat * dHi.toNat ≤ uHi.toNat`.
  - `q1_prime_lt_pow33` (KB-3b): `q1'.toNat < 2^33`.
  - `q1_le_pow32_plus_one` (KB-3c): `q1.toNat ≤ 2^32 + 1` under hcall.
  - `q1c_le_q1`, `q1_prime_le_q1c` (KB-3d): Phase 1a/1b monotonicity.
  - `q1_prime_le_pow32_plus_one` (KB-3e): `q1'.toNat ≤ 2^32 + 1`.
  - `q1c_le_pow32` (KB-3e'): `q1c.toNat ≤ 2^32`.
  - `q1_prime_le_pow32` (KB-3e''): `q1'.toNat ≤ 2^32`.
  - `q1_prime_lt_pow32` (KB-3e'''): `q1'.toNat < 2^32` strict (Knuth tightening).
  - `q0_prime_lt_pow32` (KB-6b): Phase 2b strict under `un21 < vTop`.

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
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat ≤ uHi.toNat / dHi.toNat ∧
    uHi.toNat / dHi.toNat ≤ q1c.toNat + 1 := by
  intro q1 hi1 q1c
  let rhat := uHi - q1 * dHi
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
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
    q1'.toNat * dHi.toNat ≤ uHi.toNat := by
  intro q1'
  let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
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
      push Not at h
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
      push Not at h
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
      have : uLo.toNat < 2^64 := uLo.isLt
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
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q0'.toNat < 2^32 := by
  intro q0 rhat2 hi2 q0c rhat2c div_un0 q0'
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
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
    -- Guard `rhat2cHi = 0` holds since rhat2c < 2^32.
    have h_rhat2c_hi_zero : rhat2c >>> (32 : BitVec 6).toNat = 0 := by
      have h32 : (32 : BitVec 6).toNat = 32 := by decide
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, h32, Nat.shiftRight_eq_div_pow]
      show rhat2c.toNat / 2^32 = 0
      exact Nat.div_eq_of_lt h_rhat2c_lt_pow32
    show (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat < 2^32
    unfold div128Quot_phase2b_q0'
    rw [if_pos h_rhat2c_hi_zero]
    rw [if_pos h_check]
    have h_se_neg1 : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
    rw [BitVec.toNat_add, h_se_neg1]
    have h_q0c_lt_word : q0c.toNat - 1 < 2^64 := by have := q0c.isLt; omega
    rw [show q0c.toNat + (2^64 - 1) = (q0c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt h_q0c_lt_word]
    omega
  · -- q0c < 2^32 case: q0' ≤ q0c < 2^32.
    have h_q0c_lt : q0c.toNat < 2^32 := by omega
    -- The helper's q0' is either the unguarded check result (≤ q0c) or q0c
    -- itself — both paths bound by q0c.
    have h_q0'_le_q0c : q0'.toNat ≤ q0c.toNat := by
      show (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat ≤ q0c.toNat
      unfold div128Quot_phase2b_q0'
      split
      · exact div128Quot_q1_prime_le_q1c q0c dLo rhat2Un0
      · exact Nat.le_refl _
    omega


end EvmAsm.Evm64
