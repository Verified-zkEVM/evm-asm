/-
  EvmAsm.Evm64.EvmWordArith.Div128KnuthLower

  Knuth's "Lemma A" Lower Bound chain for `div128Quot`: the digit-wise
  trial quotient never underestimates the true quotient of the abstract
  top-digits division. Split from `Div128QuotientBounds.lean` when that
  file crossed the 1500-line guardrail.

  Key lemmas (all prefixed `div128Quot_`):
  - `q1_ge_q_true_1` (KB-LB1): Phase 1 trial ≥ abstract Knuth first digit.
  - `q_true_1_lt_pow32` (KB-LB2): abstract first digit < 2^32 under hcall.
  - `q1c_ge_q_true_1` (KB-LB3): Phase 1a preserves lower bound.
  - `knuth_theorem_c_abstract` (KB-LB4): abstract-algebra form of Knuth
    Theorem C (mult check → overshoot).
  - `q1_lt_pow32_of_uHi_lt_pow63` (KB-LB6a): `uHi < 2^63` ⟹ `q1 < 2^32`.
  - `rhatc_lt_pow32_of_uHi_lt_pow63` (KB-LB6b): `uHi < 2^63` ⟹ `rhatc < 2^32`.
  - `q1_prime_ge_q_true_1_small_rhatc` (KB-LB5): Phase 1b preserves
    lower bound when `rhatc < 2^32`.
  - `q1_prime_ge_q_true_1_of_uHi_lt_pow63` (KB-LB7): unconditional Phase 1b
    lower bound under `uHi < 2^63` (composition of KB-LB5/6).
  - `q0_prime_ge_q_true_0_of_un21_lt_pow63` (KB-LB8): Phase 2 mirror of
    KB-LB7 via `uHi := un21, uLo := uLo <<< 32`.
  - `q0_prime_plus_2_ge_q_true_0_abstract` (KB-LB9): weak Phase 2 lower
    bound, unconditional (off by 2).

  See `memory/project_un21_lt_vTop_plan.md` for the full chain plan.
-/

import EvmAsm.Evm64.EvmWordArith.Div128QuotientBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv6_toNat_32)

/-- **KB-LB1: Knuth Phase 1 lower bound.** The raw Phase 1 trial
    `rv64_divu uHi dHi` never under-estimates the true first-digit
    quotient `(uHi.toNat * 2^32 + div_un1.toNat) / vTop.toNat`, where
    `vTop.toNat = dHi.toNat * 2^32 + dLo.toNat`:

    ```
    (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) ≤ (rv64_divu uHi dHi).toNat
    ```

    Direct application of `trial_quotient_ge_general` with Bk = 2^32.
    This is **Knuth's Lemma A** (the "easy" direction of Theorem B):
    the digit-wise top-parts ratio never underestimates the full ratio.

    First step toward proving `div128Quot ≥ q_true` (Knuth's full-quotient
    lower bound). To extend to `q1' ≥ true_digit_1`, one must show that
    Phase 1a/1b corrections only decrement when the trial overshoots
    (Knuth's multiplication-check correctness, ~100 lines). -/
theorem div128Quot_q1_ge_q_true_1
    (uHi dHi dLo div_un1 : Word)
    (hdHi_ne : dHi ≠ 0)
    (h_div_un1_lt : div_un1.toNat < 2^32) :
    (uHi.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat) ≤
    (rv64_divu uHi dHi).toNat := by
  rw [rv64_divu_toNat uHi dHi hdHi_ne]
  have hdHi_pos : 0 < dHi.toNat :=
    Nat.pos_of_ne_zero (fun h => hdHi_ne (BitVec.eq_of_toNat_eq h))
  exact EvmWord.trial_quotient_ge_general uHi.toNat div_un1.toNat
    dHi.toNat dLo.toNat (2^32) hdHi_pos h_div_un1_lt

/-- **KB-LB2: True first digit is bounded by 2^32 under hcall.** Under
    the call-trial precondition `uHi < vTop`, the abstract Knuth first
    digit `q_true_1 = (uHi * 2^32 + div_un1) / vTop` is strictly less
    than 2^32:

    ```
    (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) < 2^32
    ```

    Proof: `uHi < vTop ⇒ uHi * 2^32 + div_un1 < uHi * 2^32 + 2^32 =
    (uHi + 1) * 2^32 ≤ vTop * 2^32`. Hence the ratio is `< 2^32`.

    Used in KB-LB3 to bound the Phase 1a-correction branch: when
    `q1 ≥ 2^32`, the corrected `q1c = q1 - 1 ≥ 2^32 - 1 ≥ q_true_1`. -/
theorem div128Quot_q_true_1_lt_pow32
    (uHi dHi dLo div_un1 : Word)
    (h_div_un1_lt : div_un1.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    (uHi.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat) < 2^32 := by
  set vTop_nat := dHi.toNat * 2^32 + dLo.toNat
  have h_vTop_pos : 0 < vTop_nat :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) huHi_lt_vTop
  have h_num_lt : uHi.toNat * 2^32 + div_un1.toNat < vTop_nat * 2^32 := by
    calc uHi.toNat * 2^32 + div_un1.toNat
        < uHi.toNat * 2^32 + 2^32 := by omega
      _ = (uHi.toNat + 1) * 2^32 := by ring
      _ ≤ vTop_nat * 2^32 := by
          apply Nat.mul_le_mul_right
          omega
  have h_num_lt' : uHi.toNat * 2^32 + div_un1.toNat < 2^32 * vTop_nat := by
    linarith
  exact (Nat.div_lt_iff_lt_mul h_vTop_pos).mpr h_num_lt'

/-- **KB-LB3: Phase 1a preserves Knuth lower bound.** After Phase 1a's
    `hi1` correction, the corrected trial `q1c` is still ≥ the true
    first digit:

    ```
    (uHi * 2^32 + div_un1) / vTop ≤ q1c.toNat
    ```

    Case analysis on `hi1`:
    - `hi1 = 0` (q1 < 2^32): q1c = q1 ≥ q_true_1 by KB-LB1.
    - `hi1 ≠ 0` (q1 ≥ 2^32): q1c = q1 − 1 ≥ 2^32 − 1 ≥ q_true_1 via KB-LB2.

    Second step of the Knuth lower-bound chain toward `div128Quot ≥
    q_true`. Phase 1b's lower-bound preservation (when the check fires,
    q1' = q1c − 1 must still ≥ q_true_1) requires Knuth's multiplication-
    check correctness (~100 lines, future iteration). -/
theorem div128Quot_q1c_ge_q_true_1
    (uHi dHi dLo div_un1 : Word)
    (hdHi_ne : dHi ≠ 0)
    (h_div_un1_lt : div_un1.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    (uHi.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat) ≤
    q1c.toNat := by
  intro q1 hi1 q1c
  have h_q1_ge : (uHi.toNat * 2^32 + div_un1.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) ≤ q1.toNat :=
    div128Quot_q1_ge_q_true_1 uHi dHi dLo div_un1 hdHi_ne h_div_un1_lt
  have : (uHi.toNat * 2^32 + div_un1.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) < 2^32 :=
    div128Quot_q_true_1_lt_pow32 uHi dHi dLo div_un1 h_div_un1_lt huHi_lt_vTop
  by_cases h_hi1 : hi1 = 0
  · show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat ≥ _
    rw [if_pos h_hi1]
    exact h_q1_ge
  · -- hi1 ≠ 0 ⟹ q1 ≥ 2^32. q1c = q1 - 1 ≥ 2^32 - 1 ≥ q_true_1.
    have : q1.toNat ≥ 2^32 := by
      by_contra h
      push Not at h
      apply h_hi1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      show q1.toNat / 2^32 = (0 : Word).toNat
      rw [Nat.div_eq_of_lt h]
      rfl
    show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat ≥ _
    rw [if_neg h_hi1]
    rw [BitVec.toNat_add, signExtend12_4095_toNat]
    have hq1_lt_word : q1.toNat - 1 < 2^64 := by have := q1.isLt; omega
    rw [show q1.toNat + (2^64 - 1) = (q1.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq1_lt_word]
    omega

/-- **KB-LB4: Knuth Theorem C (abstract algebra form).** The
    multiplication-check inequality implies the trial overshoots the
    true first digit:

    ```
    rhatc * 2^32 + div_un1 < q1c * dLo
      → uHi * 2^32 + div_un1 < q1c * (dHi * 2^32 + dLo)
    ```

    Proof: use Phase 1a Euclidean (`q1c * dHi + rhatc = uHi`) to
    substitute `rhatc = uHi - q1c * dHi`, then rearrange. Pure Nat
    algebra on abstract (uHi, dHi, dLo, div_un1, rhatc, q1c). -/
theorem knuth_theorem_c_abstract
    (uHi dHi dLo div_un1 rhatc q1c : Word)
    (h_eucl : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat)
    (h_check : rhatc.toNat * 2^32 + div_un1.toNat < q1c.toNat * dLo.toNat) :
    uHi.toNat * 2^32 + div_un1.toNat <
    q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) := by
  -- Multiply Euclidean by 2^32: q1c * dHi * 2^32 + rhatc * 2^32 = uHi * 2^32.
  have : q1c.toNat * dHi.toNat * 2^32 + rhatc.toNat * 2^32 =
      uHi.toNat * 2^32 := by
    have := congr_arg (· * 2^32) h_eucl
    simp only [Nat.add_mul] at this
    exact this
  -- Distribute q1c * vTop:
  have h_expand : q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) =
      q1c.toNat * dHi.toNat * 2^32 + q1c.toNat * dLo.toNat := by ring
  rw [h_expand]
  linarith

/-- **KB-LB6a: Small uHi ⟹ Phase 1 trial < 2^32.** With `uHi.toNat < 2^63`
    and `dHi.toNat ≥ 2^31`, the raw Phase 1 trial `rv64_divu uHi dHi` is
    strictly less than `2^32`:

    ```
    (rv64_divu uHi dHi).toNat < 2^32
    ```

    Proof: `q1.toNat = uHi.toNat / dHi.toNat < 2^63 / 2^31 = 2^32`.

    Together with KB-LB6b, this eliminates the "Phase 1a correction branch"
    entirely, giving `rhatc < 2^32` — the precondition of KB-LB5. The
    hypothesis `uHi < 2^63` holds automatically for `uHi = a3 >>> (64 - shift)`
    under `hshift_nz` (shift > 0 means the right-shift discards ≥ 1 bit
    of a3). -/
theorem div128Quot_q1_lt_pow32_of_uHi_lt_pow63
    (uHi dHi : Word)
    (hdHi_ne : dHi ≠ 0)
    (h_uHi_lt : uHi.toNat < 2^63)
    (hdHi_ge : dHi.toNat ≥ 2^31) :
    (rv64_divu uHi dHi).toNat < 2^32 := by
  rw [rv64_divu_toNat uHi dHi hdHi_ne]
  have hdHi_pos : 0 < dHi.toNat :=
    Nat.pos_of_ne_zero (fun h => hdHi_ne (BitVec.eq_of_toNat_eq h))
  -- uHi / dHi ≤ uHi / 2^31 (since dHi ≥ 2^31).
  have : uHi.toNat / dHi.toNat ≤ uHi.toNat / 2^31 :=
    Nat.div_le_div_left hdHi_ge (by decide : 0 < 2^31)
  -- uHi / 2^31 < 2^63 / 2^31 = 2^32 (under uHi < 2^63).
  have h_pow : (2^63 : Nat) = 2^32 * 2^31 := by decide
  have : uHi.toNat / 2^31 < 2^32 := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- **KB-LB6b: Under uHi < 2^63, Phase 1a doesn't correct; rhatc < 2^32.**
    Composing KB-LB6a (q1 < 2^32) with the algorithm: when `q1 < 2^32`,
    `hi1 = q1 >>> 32 = 0`, so Phase 1a takes the no-correction branch.
    Then `rhatc = rhat = uHi mod dHi < dHi < 2^32`:

    ```
    rhatc.toNat < 2^32
    ```

    This is the precondition of KB-LB5 (Phase 1b preserves lower bound).
    Together, KB-LB5 + KB-LB6a/b give an **unconditional Phase 1b lower
    bound under `uHi < 2^63`**, automatically satisfied under `hshift_nz`. -/
theorem div128Quot_rhatc_lt_pow32_of_uHi_lt_pow63
    (uHi dHi : Word)
    (hdHi_ne : dHi ≠ 0)
    (h_uHi_lt : uHi.toNat < 2^63)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    rhatc.toNat < 2^32 := by
  intro q1 rhat hi1 rhatc
  have h_q1_lt : q1.toNat < 2^32 :=
    div128Quot_q1_lt_pow32_of_uHi_lt_pow63 uHi dHi hdHi_ne h_uHi_lt hdHi_ge
  have h_hi1 : hi1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    show (q1 >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt h_q1_lt]
    rfl
  -- rhat = uHi mod dHi < dHi.
  have hdHi_pos : 0 < dHi.toNat :=
    Nat.pos_of_ne_zero (fun h => hdHi_ne (BitVec.eq_of_toNat_eq h))
  have h_rhat_lt : rhat.toNat < dHi.toNat := by
    show (uHi - q1 * dHi).toNat < dHi.toNat
    have h_q1_eq : q1.toNat = uHi.toNat / dHi.toNat := rv64_divu_toNat uHi dHi hdHi_ne
    -- uHi - q1 * dHi at Word equals uHi - q1 * dHi at Nat (no wrap under q1 < 2^32, dHi < 2^32).
    -- Apply first_round_post: q1c * dHi + rhatc = uHi at Nat. Under h_hi1, q1c = q1, rhatc = rhat.
    have h_post : q1.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
      have h := div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
      -- h binds its own q1/hi1/q1c/rhat/rhatc lets (via intro). Reduce them.
      simp only [show (rv64_divu uHi dHi >>> (32 : BitVec 6).toNat) = 0 from h_hi1,
                 if_true] at h
      exact h
    rw [h_q1_eq] at h_post
    -- h_post: (uHi/dHi) * dHi + rhat = uHi. So rhat = uHi - (uHi/dHi)*dHi = uHi mod dHi.
    have h_div_mul_add : uHi.toNat / dHi.toNat * dHi.toNat + uHi.toNat % dHi.toNat = uHi.toNat := by
      have := Nat.div_add_mod uHi.toNat dHi.toNat
      linarith
    have h_rhat_eq : rhat.toNat = uHi.toNat % dHi.toNat := by omega
    rw [h_rhat_eq]
    exact Nat.mod_lt _ hdHi_pos
  show (if hi1 = 0 then rhat else rhat + dHi).toNat < 2^32
  rw [if_pos h_hi1]
  omega

/-- **KB-LB5: Phase 1b preserves lower bound (small-rhatc form).** When
    `rhatc.toNat < 2^32`, the Word-level Phase 1b check exactly matches
    Knuth Theorem C's abstract condition, so Phase 1b's correction
    preserves `q1' ≥ q_true_1`:

    ```
    (uHi * 2^32 + (uLo >>> 32).toNat) / (dHi * 2^32 + dLo) ≤ q1'.toNat
    ```

    Case analysis on Phase 1b check:
    - Doesn't fire: `q1' = q1c ≥ q_true_1` by KB-LB3.
    - Fires: Word `rhatUn1 < q1c * dLo` corresponds under `rhatc < 2^32`
      (no halfword truncation in rhatUn1) + `q1c * dLo` no-wrap (from
      KB-3e' `q1c ≤ 2^32`) to the abstract `rhatc * 2^32 + div_un1 <
      q1c * dLo`, which by KB-LB4 implies `q1c * vTop > uHi * 2^32 + div_un1`,
      hence `q_true_1 < q1c`, i.e., `q1' = q1c - 1 ≥ q_true_1`.

    The `rhatc < 2^32` hypothesis is automatically satisfied when
    `dHi < 2^31` (since `rhatc < 2 * dHi < 2^32`). For normalized
    `dHi ≥ 2^31`, the complement `rhatc ≥ 2^32` is possible and requires
    separate Word-truncation analysis. -/
theorem div128Quot_q1_prime_ge_q_true_1_small_rhatc
    (uHi dHi dLo uLo : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat)
    (h_rhatc_lt : (let q1 := rv64_divu uHi dHi
                   let rhat := uHi - q1 * dHi
                   let hi1 := q1 >>> (32 : BitVec 6).toNat
                   let rhatc := if hi1 = 0 then rhat else rhat + dHi
                   rhatc.toNat) < 2^32) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    (uHi.toNat * 2^32 + div_un1.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) ≤ q1'.toNat := by
  intro q1 rhat hi1 q1c rhatc div_un1 rhatUn1 q1'
  -- Derived preconditions.
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (uLo >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight]
    rw [bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : uLo.toNat < 2^64 := uLo.isLt
    have : (2^64 : Nat) = 2^32 * 2^32 := by decide
    exact Nat.div_lt_of_lt_mul (by omega)
  -- KB-LB3: q_true_1 ≤ q1c (instantiated at our div_un1 value).
  have h_q1c_ge : (uHi.toNat * 2^32 + div_un1.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) ≤ q1c.toNat :=
    div128Quot_q1c_ge_q_true_1 uHi dHi dLo div_un1
      hdHi_ne h_div_un1_lt huHi_lt_vTop
  -- q1c ≤ 2^32 via KB-3e'.
  have h_q1c_le : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt huHi_lt_vTop
  -- Phase 1a Euclidean.
  have h_post : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat :=
    div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  by_cases h_check : BitVec.ult rhatUn1 (q1c * dLo)
  · -- Check fires: q1' = q1c - 1. Need q_true_1 ≤ q1c - 1.
    -- Step 1: Word check ⟺ Nat check (rhatc * 2^32 + div_un1 < q1c * dLo).
    have h_rhatUn1_eq : rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat := by
      show ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat = _
      rw [bv6_toNat_32]
      exact EvmWord.halfword_combine rhatc div_un1 h_rhatc_lt h_div_un1_lt
    have h_qDlo_eq : (q1c * dLo).toNat = q1c.toNat * dLo.toNat := by
      rw [BitVec.toNat_mul]
      apply Nat.mod_eq_of_lt
      calc q1c.toNat * dLo.toNat
          ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1c_le
        _ < 2^32 * 2^32 := by
            apply Nat.mul_lt_mul_left (by decide : 0 < 2^32) |>.mpr hdLo_lt
        _ = 2^64 := by decide
    have h_check_nat : rhatc.toNat * 2^32 + div_un1.toNat <
        q1c.toNat * dLo.toNat := by
      have h_ult : rhatUn1.toNat < (q1c * dLo).toNat := by
        rwa [BitVec.ult_iff_lt] at h_check
      rw [h_rhatUn1_eq, h_qDlo_eq] at h_ult
      exact h_ult
    -- Step 2: Apply KB-LB4 to get abstract overshoot.
    have h_abstract : uHi.toNat * 2^32 + div_un1.toNat <
        q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) :=
      knuth_theorem_c_abstract uHi dHi dLo div_un1 rhatc q1c h_post h_check_nat
    -- Step 3: Divide by vTop to get q_true_1 < q1c.
    set vTop_nat := dHi.toNat * 2^32 + dLo.toNat
    have h_vTop_pos : 0 < vTop_nat := by
      have : dHi.toNat * 2^32 ≥ 2^31 * 2^32 := Nat.mul_le_mul_right _ hdHi_ge
      have h_pow : (2^31 : Nat) * 2^32 = 2^63 := by decide
      show 0 < vTop_nat
      simp [vTop_nat]; omega
    have : uHi.toNat * 2^32 + div_un1.toNat <
        q1c.toNat * vTop_nat := h_abstract
    have h_q_true_lt_q1c :
        (uHi.toNat * 2^32 + div_un1.toNat) / vTop_nat < q1c.toNat :=
      (Nat.div_lt_iff_lt_mul h_vTop_pos).mpr (by linarith)
    -- Step 4: q1'.toNat = q1c.toNat - 1.
    show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
          else q1c).toNat ≥ _
    rw [if_pos h_check]
    have : q1c.toNat ≥ 1 :=
      div128Quot_phase1b_check_implies_q1c_pos q1c dLo rhatUn1 h_check
    rw [BitVec.toNat_add, signExtend12_4095_toNat]
    have h_q1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
    rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_lt_word]
    omega
  · -- Check doesn't fire: q1' = q1c ≥ q_true_1.
    show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
          else q1c).toNat ≥ _
    rw [if_neg h_check]
    exact h_q1c_ge

/-- **KB-LB7: Phase 1b Knuth lower bound (unconditional under `uHi < 2^63`).**
    Combines KB-LB5 (Phase 1b preserves lower bound when rhatc < 2^32) with
    KB-LB6a/b (rhatc < 2^32 follows from `uHi < 2^63` + `dHi ≥ 2^31`):

    ```
    (uHi * 2^32 + div_un1) / vTop ≤ q1'.toNat
    ```

    The hypothesis `uHi.toNat < 2^63` is automatically satisfied when
    `uHi = a3 >>> (64 - shift)` under `hshift_nz` (since the right shift
    discards ≥ 1 bit of a3). Therefore in the algorithm's call-trial path,
    Phase 1b never undershoots the abstract first-digit true quotient —
    the `rhatc ≥ 2^32` corner I previously feared is unreachable. -/
theorem div128Quot_q1_prime_ge_q_true_1_of_uHi_lt_pow63
    (uHi dHi dLo uLo : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (h_uHi_lt : uHi.toNat < 2^63)
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
    (uHi.toNat * 2^32 + div_un1.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) ≤ q1'.toNat := by
  intro q1 rhat hi1 q1c rhatc div_un1 rhatUn1 q1'
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    div128Quot_rhatc_lt_pow32_of_uHi_lt_pow63 uHi dHi hdHi_ne h_uHi_lt hdHi_ge hdHi_lt
  exact div128Quot_q1_prime_ge_q_true_1_small_rhatc uHi dHi dLo uLo
    hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop h_rhatc_lt

/-- **KB-LB8: Phase 2 Knuth lower bound under `un21 < 2^63` (easy case).**
    Phase 2 mirror of KB-LB7, applying the same Phase-1 machinery with
    `uHi := un21` and `uLo := uLo <<< 32` so that
    `(uLo <<< 32) >>> 32 = uLo mod 2^32 = div_un0`. Conclusion:

    ```
    (un21 * 2^32 + div_un0) / vTop ≤ q0'.toNat
    ```

    The hypothesis `un21.toNat < 2^63` rules out Phase 2a's `hi2`
    correction (same argument as KB-LB7 for Phase 1). The complementary
    case `un21 ≥ 2^63` is genuinely harder — it triggers Phase 2a's
    correction and can reach `rhat2c ≥ 2^32`, where Phase 2b's Word
    check may false-positive. That case requires separate analysis;
    see `memory/project_un21_lt_vTop_plan.md`. -/
theorem div128Quot_q0_prime_ge_q_true_0_of_un21_lt_pow63
    (un21 dHi dLo uLo : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (h_un21_lt : un21.toNat < 2^63)
    (hun21_lt_vTop : un21.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    (un21.toNat * 2^32 + div_un0.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) ≤ q0'.toNat := by
  intro q0 rhat2 hi2 q0c rhat2c div_un0 q0'
  -- div_un0 < 2^32 (from `uLo << 32 >> 32`).
  have h_div_un0_lt : div_un0.toNat < 2^32 := by
    show ((uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight]
    rw [bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h_shl : (uLo <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (uLo <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  show (un21.toNat * 2^32 + div_un0.toNat) /
         (dHi.toNat * 2^32 + dLo.toNat) ≤
       (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat
  unfold div128Quot_phase2b_q0'
  split
  · -- Guard doesn't fire: helper yields unguarded check.
    exact div128Quot_q1_prime_ge_q_true_1_of_uHi_lt_pow63 un21 dHi dLo
      (uLo <<< (32 : BitVec 6).toNat)
      hdHi_ge hdHi_lt hdLo_lt h_un21_lt hun21_lt_vTop
  · -- Guard fires: helper = q0c. Use KB-LB3 at Phase 2 (uHi := un21).
    have hdHi_ne : dHi ≠ 0 := by
      intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
    exact div128Quot_q1c_ge_q_true_1 un21 dHi dLo div_un0 hdHi_ne
      h_div_un0_lt hun21_lt_vTop

/-- **KB-LB9: Weak Phase 2 lower bound, unconditional.** Phase 2's output
    `q0'` satisfies the abstract Knuth trial bound off by 2:

    ```
    q0' + 2 ≥ (un21 * 2^32 + div_un0) / vTop
    ```

    without any hypothesis on `un21`'s magnitude (only `dHi ≠ 0` and
    `dHi < 2^32`). Composes KB-2 (Phase 1b quotient bound, at Phase 2
    via uHi := un21) giving `q0' + 2 ≥ un21 / dHi`, with
    `trial_quotient_ge_general` giving `(un21*2^32 + div_un0)/vTop ≤
    un21/dHi`.

    Weaker than the exact bound (`q0' ≥ q_true_0`) — off by at most 2.
    Composed with KB-LB7 (Phase 1 tight lower), gives the "2-off"
    composed bound `qHat ≥ q_true - 2`. Useful when the exact lower
    bound isn't reachable (Phase 2 false-positive corner). -/
theorem div128Quot_q0_prime_plus_2_ge_q_true_0_abstract
    (un21 dHi dLo uLo : Word)
    (hdHi_ne : dHi ≠ 0)
    (hdHi_lt : dHi.toNat < 2^32) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q0'.toNat + 2 ≥ (un21.toNat * 2^32 + div_un0.toNat) /
                     (dHi.toNat * 2^32 + dLo.toNat) := by
  intro q0 rhat2 hi2 q0c rhat2c div_un0 q0'
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  -- Case-split on helper's guard: rhat2cHi = 0.
  -- Guard fires: q0' = q0c, and q0c + 2 ≥ un21/dHi via KB-1 (Phase 1a bound).
  -- Guard doesn't fire: q0' = phase1b's un-guarded q1' at Phase 2, which
  -- satisfies the bound via div128Quot_phase1b_quotient_bound.
  have : q0'.toNat + 2 ≥ un21.toNat / dHi.toNat := by
    show (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat + 2 ≥
      un21.toNat / dHi.toNat
    unfold div128Quot_phase2b_q0'
    split
    · -- Guard doesn't fire (rhat2cHi = 0): helper yields the un-guarded check.
      exact (div128Quot_phase1b_quotient_bound un21 dHi hdHi_ne hdHi_lt dLo
        rhat2Un0).1
    · -- Guard fires (rhat2cHi ≠ 0): helper yields q0c. Use KB-1 at Phase 2.
      have h_kb1 := div128Quot_phase1a_quotient_bound un21 dHi hdHi_ne hdHi_lt
      have : un21.toNat / dHi.toNat ≤ q0c.toNat + 1 := h_kb1.2
      omega
  -- div_un0 < 2^32.
  have h_div_un0_lt : div_un0.toNat < 2^32 := by
    show ((uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight]
    rw [bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h_shl : (uLo <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (uLo <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  -- trial_quotient_ge_general: (un21*2^32+div_un0)/vTop ≤ un21/dHi.
  have : (un21.toNat * 2^32 + div_un0.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) ≤ un21.toNat / dHi.toNat := by
    have hdHi_pos : 0 < dHi.toNat :=
      Nat.pos_of_ne_zero (fun h => hdHi_ne (BitVec.eq_of_toNat_eq h))
    exact EvmWord.trial_quotient_ge_general un21.toNat div_un0.toNat
      dHi.toNat dLo.toNat (2^32) hdHi_pos h_div_un0_lt
  omega

/-- **KB-Compose: Knuth 2-digit composition identity (pure Nat algebra).**
    Under the Phase 1b Euclidean, un21 identity, Phase 2b Euclidean, and
    the two no-wrap conditions, the composed quotient satisfies:

    ```
    (q1' * 2^32 + q0') * (dHi * 2^32 + dLo) ≤ uHi * 2^64 + div_un1 * 2^32 + div_un0
    ```

    Derivation: multiply the Phase-2b Euclidean (rewritten without Nat
    subtraction) by `2^32`, combine with Phase 1b Euclidean ×2^64, and
    expand via `ring`. The final inequality reduces to the Phase-2
    no-wrap hypothesis.

    Key step: combined with `div_un1 * 2^32 + div_un0 = uLo`, gives
    `qHat * vTop ≤ uHi * 2^64 + uLo`, i.e., `qHat ≤ abstract_trial`. -/
theorem knuth_compose_qHat_vTop_le_nat
    (q1' q0' rhat' rhat2' dHi dLo div_un1 div_un0 uHi : Nat)
    (h_ph1_eucl : q1' * dHi + rhat' = uHi)
    (h_ph1_no_wrap : q1' * dLo ≤ rhat' * 2^32 + div_un1)
    (h_un21_ph2 : q0' * dHi + rhat2' = rhat' * 2^32 + div_un1 - q1' * dLo)
    (h_ph2_no_wrap : q0' * dLo ≤ rhat2' * 2^32 + div_un0) :
    (q1' * 2^32 + q0') * (dHi * 2^32 + dLo) ≤
    uHi * 2^64 + div_un1 * 2^32 + div_un0 := by
  have h_un21_plus : q0' * dHi + rhat2' + q1' * dLo = rhat' * 2^32 + div_un1 := by
    omega
  have h_mul : q0' * dHi * 2^32 + rhat2' * 2^32 + q1' * dLo * 2^32 =
               rhat' * 2^64 + div_un1 * 2^32 := by
    have h := congr_arg (· * 2^32) h_un21_plus
    simp only at h
    have h_expand_lhs :
        (q0' * dHi + rhat2' + q1' * dLo) * 2^32 =
        q0' * dHi * 2^32 + rhat2' * 2^32 + q1' * dLo * 2^32 := by ring
    have h_expand_rhs :
        (rhat' * 2^32 + div_un1) * 2^32 = rhat' * 2^64 + div_un1 * 2^32 := by ring
    linarith
  have : uHi * 2^64 = q1' * dHi * 2^64 + rhat' * 2^64 := by
    have h_expand : (q1' * dHi + rhat') * 2^64 = q1' * dHi * 2^64 + rhat' * 2^64 := by
      ring
    have := congr_arg (· * 2^64) h_ph1_eucl
    simp only at this
    linarith
  have h_lhs : (q1' * 2^32 + q0') * (dHi * 2^32 + dLo) =
               q1' * dHi * 2^64 + q1' * dLo * 2^32 + q0' * dHi * 2^32 + q0' * dLo := by
    ring
  rw [h_lhs]
  linarith

/-- **KB-ComposeLower: composed weak lower bound on qHat (pure Nat).**
    Under Phase 1 tight (q1' = exact abstract Phase 1 digit, expressed
    as the Euclidean identity `q1' * vTop + un21 = uHi * 2^32 + uLo_hi`
    with `un21 < vTop`), and Phase 2 weak lower (KB-LB9-style
    `q0' + 2 ≥ (un21 * 2^32 + uLo_lo) / vTop`), the composed quotient
    satisfies:

    ```
    (q1' * 2^32 + q0') + 2 ≥ (uHi * 2^64 + uLo_hi * 2^32 + uLo_lo) / vTop
    ```

    This is the key composition showing that the algorithm is at most
    2 below the abstract 128/64 quotient, **given Phase 1 is tight**.
    The tight Phase 1 hypothesis is currently unproven (requires Knuth
    Theorem C Word-level); this lemma makes the remaining gap explicit. -/
theorem knuth_compose_weak_lower_nat
    (q1' q0' un21 uHi uLo_hi uLo_lo vTop : Nat)
    (hvTop_pos : 0 < vTop)
    (h_ph1_tight : q1' * vTop + un21 = uHi * 2^32 + uLo_hi)
    (h_ph2_weak : q0' + 2 ≥ (un21 * 2^32 + uLo_lo) / vTop) :
    (q1' * 2^32 + q0') + 2 ≥ (uHi * 2^64 + uLo_hi * 2^32 + uLo_lo) / vTop := by
  -- From Phase 1 tight: full dividend = q1' * vTop * 2^32 + un21 * 2^32 + uLo_lo.
  have h_full_eq : uHi * 2^64 + uLo_hi * 2^32 + uLo_lo =
      q1' * vTop * 2^32 + (un21 * 2^32 + uLo_lo) := by
    have h_mul : (q1' * vTop + un21) * 2^32 = (uHi * 2^32 + uLo_hi) * 2^32 := by
      rw [h_ph1_tight]
    have h_expand_lhs : (q1' * vTop + un21) * 2^32 =
        q1' * vTop * 2^32 + un21 * 2^32 := by ring
    have h_expand_rhs : (uHi * 2^32 + uLo_hi) * 2^32 =
        uHi * 2^64 + uLo_hi * 2^32 := by ring
    linarith
  rw [h_full_eq]
  -- Divide by vTop and use Nat.add_mul_div_right.
  have h_div_eq : (q1' * vTop * 2^32 + (un21 * 2^32 + uLo_lo)) / vTop =
      q1' * 2^32 + (un21 * 2^32 + uLo_lo) / vTop := by
    have h_rearrange : q1' * vTop * 2^32 + (un21 * 2^32 + uLo_lo) =
        (un21 * 2^32 + uLo_lo) + (q1' * 2^32) * vTop := by ring
    rw [h_rearrange, Nat.add_mul_div_right _ _ hvTop_pos]
    ring
  rw [h_div_eq]
  omega

/-- **KB-ComposeUpper: qHat ≤ abstract_trial_full (pure Nat).** Direct
    corollary of KB-Compose (`knuth_compose_qHat_vTop_le_nat`): dividing
    both sides of `qHat * vTop ≤ top128` by `vTop` gives:

    ```
    qHat ≤ (uHi * 2^64 + div_un1 * 2^32 + div_un0) / vTop
    ```

    i.e., `qHat ≤ abstract_trial_full`. Combined with skip-borrow-derived
    `qHat ≤ val256(a) / val256(b)` (future outer-mulsub lemma), gives the
    upper direction for call+skip DIV spec. -/
theorem knuth_compose_qHat_le_abstract_trial_nat
    (q1' q0' rhat' rhat2' dHi dLo div_un1 div_un0 uHi : Nat)
    (hvTop_pos : 0 < dHi * 2^32 + dLo)
    (h_ph1_eucl : q1' * dHi + rhat' = uHi)
    (h_ph1_no_wrap : q1' * dLo ≤ rhat' * 2^32 + div_un1)
    (h_un21_ph2 : q0' * dHi + rhat2' = rhat' * 2^32 + div_un1 - q1' * dLo)
    (h_ph2_no_wrap : q0' * dLo ≤ rhat2' * 2^32 + div_un0) :
    q1' * 2^32 + q0' ≤
    (uHi * 2^64 + div_un1 * 2^32 + div_un0) / (dHi * 2^32 + dLo) := by
  have h := knuth_compose_qHat_vTop_le_nat q1' q0' rhat' rhat2' dHi dLo
    div_un1 div_un0 uHi h_ph1_eucl h_ph1_no_wrap h_un21_ph2 h_ph2_no_wrap
  exact (Nat.le_div_iff_mul_le hvTop_pos).mpr h

-- ============================================================================
-- Case A lower bound: `uHi < dHi * 2^32` variant of the Phase 1/2 chain.
-- Extends KB-LB6..LB8's coverage (previously `uHi < 2^63`). Under `dHi ≥ 2^31`,
-- the new hypothesis `uHi < dHi * 2^32` is strictly weaker (covers more).
-- Useful for Phase 2 application where `un21` can exceed `2^63` but still
-- satisfies `un21 < dHi * 2^32` (the "easy half" of the post-`hshift_nz`
-- hard case).
-- ============================================================================

/-- **KB-LB6a': `uHi < dHi * 2^32 ⟹ q1 < 2^32`.** Case A variant of KB-LB6a
    with a hypothesis on `dHi * 2^32` instead of `2^63`. Strictly weaker
    under `dHi ≥ 2^31`. -/
theorem div128Quot_q1_lt_pow32_of_uHi_lt_dHi_mul_pow32
    (uHi dHi : Word)
    (hdHi_ne : dHi ≠ 0)
    (h_uHi_lt : uHi.toNat < dHi.toNat * 2^32) :
    (rv64_divu uHi dHi).toNat < 2^32 := by
  rw [rv64_divu_toNat uHi dHi hdHi_ne]
  exact Nat.div_lt_of_lt_mul h_uHi_lt

/-- **KB-LB6b': `rhatc < 2^32` under `uHi < dHi * 2^32`.** Case A analog of
    KB-LB6b; same proof structure but uses KB-LB6a' for `q1 < 2^32`. -/
theorem div128Quot_rhatc_lt_pow32_of_uHi_lt_dHi_mul_pow32
    (uHi dHi : Word)
    (hdHi_ne : dHi ≠ 0)
    (h_uHi_lt : uHi.toNat < dHi.toNat * 2^32)
    (hdHi_lt : dHi.toNat < 2^32) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    rhatc.toNat < 2^32 := by
  intro q1 rhat hi1 rhatc
  have h_q1_lt : q1.toNat < 2^32 :=
    div128Quot_q1_lt_pow32_of_uHi_lt_dHi_mul_pow32 uHi dHi hdHi_ne h_uHi_lt
  have h_hi1 : hi1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    show (q1 >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt h_q1_lt]
    rfl
  have hdHi_pos : 0 < dHi.toNat :=
    Nat.pos_of_ne_zero (fun h => hdHi_ne (BitVec.eq_of_toNat_eq h))
  have h_rhat_lt : rhat.toNat < dHi.toNat := by
    show (uHi - q1 * dHi).toNat < dHi.toNat
    have h_q1_eq : q1.toNat = uHi.toNat / dHi.toNat :=
      rv64_divu_toNat uHi dHi hdHi_ne
    have h_post : q1.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
      have h := div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
      simp only [show (rv64_divu uHi dHi >>> (32 : BitVec 6).toNat) = 0 from h_hi1,
                 if_true] at h
      exact h
    rw [h_q1_eq] at h_post
    have h_div_mul_add :
        uHi.toNat / dHi.toNat * dHi.toNat + uHi.toNat % dHi.toNat = uHi.toNat := by
      have := Nat.div_add_mod uHi.toNat dHi.toNat
      linarith
    have h_rhat_eq : rhat.toNat = uHi.toNat % dHi.toNat := by omega
    rw [h_rhat_eq]
    exact Nat.mod_lt _ hdHi_pos
  show (if hi1 = 0 then rhat else rhat + dHi).toNat < 2^32
  rw [if_pos h_hi1]
  omega

/-- **KB-LB7': Phase 1b Knuth lower bound under `uHi < dHi * 2^32`.** Case A
    variant of KB-LB7, composing KB-LB5 (Phase 1b preserves lower when
    rhatc < 2^32) with KB-LB6b'. Covers the case `dHi * 2^32 > 2^63`
    (possible when dHi > 2^31), extending KB-LB7's `uHi < 2^63`. -/
theorem div128Quot_q1_prime_ge_q_true_1_of_uHi_lt_dHi_mul_pow32
    (uHi dHi dLo uLo : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (h_uHi_lt : uHi.toNat < dHi.toNat * 2^32)
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
    (uHi.toNat * 2^32 + div_un1.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) ≤ q1'.toNat := by
  intro q1 rhat hi1 q1c rhatc div_un1 rhatUn1 q1'
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    div128Quot_rhatc_lt_pow32_of_uHi_lt_dHi_mul_pow32 uHi dHi hdHi_ne h_uHi_lt hdHi_lt
  exact div128Quot_q1_prime_ge_q_true_1_small_rhatc uHi dHi dLo uLo
    hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop h_rhatc_lt

/-- **KB-LB8': Phase 2 Knuth lower bound under `un21 < dHi * 2^32`.** Case A
    variant of KB-LB8. Covers un21 values in `[0, dHi * 2^32)`, strictly
    larger than KB-LB8's `[0, 2^63)` when `dHi > 2^31`. The remaining
    hard case `un21 ∈ [dHi * 2^32, vTop)` (Case B) still requires
    Phase 2b Word false-positive analysis. -/
theorem div128Quot_q0_prime_ge_q_true_0_of_un21_lt_dHi_mul_pow32
    (un21 dHi dLo uLo : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (h_un21_lt : un21.toNat < dHi.toNat * 2^32)
    (hun21_lt_vTop : un21.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    (un21.toNat * 2^32 + div_un0.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) ≤ q0'.toNat := by
  intro q0 rhat2 hi2 q0c rhat2c div_un0 q0'
  -- div_un0 < 2^32 (from `uLo << 32 >> 32`).
  have h_div_un0_lt : div_un0.toNat < 2^32 := by
    show ((uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight]
    rw [bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h_shl : (uLo <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (uLo <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  show (un21.toNat * 2^32 + div_un0.toNat) /
         (dHi.toNat * 2^32 + dLo.toNat) ≤
       (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat
  unfold div128Quot_phase2b_q0'
  split
  · -- Guard doesn't fire: helper yields unguarded check.
    exact div128Quot_q1_prime_ge_q_true_1_of_uHi_lt_dHi_mul_pow32 un21 dHi dLo
      (uLo <<< (32 : BitVec 6).toNat)
      hdHi_ge hdHi_lt hdLo_lt h_un21_lt hun21_lt_vTop
  · -- Guard fires: helper = q0c. Use KB-LB3 at Phase 2.
    have hdHi_ne : dHi ≠ 0 := by
      intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
    exact div128Quot_q1c_ge_q_true_1 un21 dHi dLo div_un0 hdHi_ne
      h_div_un0_lt hun21_lt_vTop


/-- **KB-LB10 (Knuth Theorem B, raw form): Phase 1 partial-quotient ≤
    true first digit + 2.** The raw RISC-V single-digit divide
    `q1 = uHi / dHi` overshoots the abstract Knuth first digit
    `q_true_1 = (uHi * 2^32 + div_un1) / vTop` by at most 2:

    ```
    (rv64_divu uHi dHi).toNat ≤
      (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) + 2
    ```

    This is **Knuth's Theorem B** specialized to our two-digit-by-one-digit
    setting. The proof is a contradiction-based Nat algebra argument:
    assume `q1 ≥ q_true_1 + 3`. The Phase-1 Euclidean
    `q1 * dHi ≤ uHi` and the floor inequality
    `(q_true_1 + 1) * vTop > uHi * 2^32 + div_un1`
    combine to force `(q_true_1 + 1) * dLo > 2 * dHi * 2^32`. Under
    `dHi ≥ 2^31`, the RHS is `≥ 2^64`, so `q_true_1 + 1 > 2^32` (since
    `dLo < 2^32`), contradicting `q_true_1 < 2^32` from KB-LB2.

    Used as input to KB-LB11 (Phase 1a-corrected `≤ q_true_1 + 2`) and
    eventually KB-LB12 (Phase 1b-corrected `≤ q_true_1 + 1`, Knuth
    Theorem C tight). The latter closes U3's hard case. -/
theorem div128Quot_q1_le_q_true_1_plus_two
    (uHi dHi dLo div_un1 : Word)
    (hdHi_ne : dHi ≠ 0)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (h_div_un1_lt : div_un1.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    (rv64_divu uHi dHi).toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 2 := by
  set vTop := dHi.toNat * 2^32 + dLo.toNat with h_vTop_def
  set q_true_1 := (uHi.toNat * 2^32 + div_un1.toNat) / vTop with h_q_true_1_def
  set q1 := (rv64_divu uHi dHi).toNat with h_q1_def
  -- Phase 1 Euclidean: q1 * dHi ≤ uHi.
  have h_q1_eucl : q1 * dHi.toNat ≤ uHi.toNat :=
    EvmWord.rv64_divu_mul_le uHi dHi hdHi_ne
  -- vTop > 0.
  have h_vTop_pos : 0 < vTop := by
    have h_dHi_pos : 0 < dHi.toNat := by omega
    have h_pow_pos : (0 : Nat) < 2^32 := by decide
    have h1 : 0 < dHi.toNat * 2^32 := Nat.mul_pos h_dHi_pos h_pow_pos
    show 0 < dHi.toNat * 2^32 + dLo.toNat
    exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
  -- q_true_1 < 2^32 (KB-LB2).
  have h_q_true_1_lt : q_true_1 < 2^32 := by
    show (uHi.toNat * 2^32 + div_un1.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) < 2^32
    exact div128Quot_q_true_1_lt_pow32 uHi dHi dLo div_un1
      h_div_un1_lt huHi_lt_vTop
  -- Floor: q_true_1 * vTop ≤ uHi*B + div_un1 < (q_true_1 + 1) * vTop.
  set r := (uHi.toNat * 2^32 + div_un1.toNat) % vTop with h_r_def
  have h_dvm : vTop * q_true_1 + r = uHi.toNat * 2^32 + div_un1.toNat :=
    Nat.div_add_mod (uHi.toNat * 2^32 + div_un1.toNat) vTop
  have h_mod_lt : r < vTop :=
    Nat.mod_lt (uHi.toNat * 2^32 + div_un1.toNat) h_vTop_pos
  have h_floor_lt : uHi.toNat * 2^32 + div_un1.toNat < (q_true_1 + 1) * vTop := by
    have h_eq : (q_true_1 + 1) * vTop = vTop * q_true_1 + vTop := by ring
    rw [h_eq]; omega
  -- By contradiction: assume q1 > q_true_1 + 2, i.e. q1 ≥ q_true_1 + 3.
  by_contra h_assume
  push Not at h_assume
  have h_q1_ge : q1 ≥ q_true_1 + 3 := by omega
  -- (q_true_1 + 3) * dHi * 2^32 ≤ q1 * dHi * 2^32 ≤ uHi * 2^32.
  have h_mul_low : (q_true_1 + 3) * dHi.toNat * 2^32 ≤ uHi.toNat * 2^32 := by
    have h1 : (q_true_1 + 3) * dHi.toNat ≤ q1 * dHi.toNat :=
      Nat.mul_le_mul_right _ h_q1_ge
    have h2 : q1 * dHi.toNat ≤ uHi.toNat := h_q1_eucl
    have h3 : (q_true_1 + 3) * dHi.toNat ≤ uHi.toNat := Nat.le_trans h1 h2
    exact Nat.mul_le_mul_right _ h3
  -- Expand floor inequality: (q_true_1 + 1) * dHi * 2^32 + (q_true_1 + 1) * dLo
  --                          > uHi * 2^32 + div_un1.
  have h_ceil_expand :
      (q_true_1 + 1) * dHi.toNat * 2^32 + (q_true_1 + 1) * dLo.toNat
        > uHi.toNat * 2^32 + div_un1.toNat := by
    have h_eq : (q_true_1 + 1) * vTop =
        (q_true_1 + 1) * dHi.toNat * 2^32 + (q_true_1 + 1) * dLo.toNat := by
      rw [h_vTop_def]; ring
    linarith
  -- Subtract h_mul_low from h_ceil_expand:
  --   (q_true_1 + 1) * dLo > 2 * dHi * 2^32 + div_un1.
  have h_dLo_lower :
      (q_true_1 + 1) * dLo.toNat > 2 * dHi.toNat * 2^32 + div_un1.toNat := by
    have h_split : (q_true_1 + 3) * dHi.toNat * 2^32 =
        (q_true_1 + 1) * dHi.toNat * 2^32 + 2 * dHi.toNat * 2^32 := by ring
    linarith
  -- Under dHi ≥ 2^31: 2 * dHi * 2^32 ≥ 2^64.
  have h_dHi_2_lower : 2 * dHi.toNat * 2^32 ≥ 2^64 := by
    have h1 : 2 * dHi.toNat ≥ 2^32 := by omega
    have h2 : 2 * dHi.toNat * 2^32 ≥ 2^32 * 2^32 := Nat.mul_le_mul_right _ h1
    have h3 : (2^32 * 2^32 : Nat) = 2^64 := by decide
    linarith
  -- So (q_true_1 + 1) * dLo > 2^64.
  have h_big : (q_true_1 + 1) * dLo.toNat > 2^64 := by linarith
  -- But dLo < 2^32, so (q_true_1 + 1) > 2^32 (otherwise product < 2^64).
  have h_qtrue_big : q_true_1 + 1 > 2^32 := by
    by_contra h
    push Not at h
    have h1 : (q_true_1 + 1) * dLo.toNat ≤ 2^32 * dLo.toNat :=
      Nat.mul_le_mul_right _ h
    have h2 : 2^32 * dLo.toNat < 2^32 * 2^32 :=
      Nat.mul_lt_mul_of_pos_left hdLo_lt (by decide)
    have h3 : (2^32 * 2^32 : Nat) = 2^64 := by decide
    linarith
  -- But q_true_1 < 2^32 contradicts q_true_1 ≥ 2^32.
  omega

/-- **KB-LB11: Phase 1a preserves the Knuth Theorem B upper bound.**
    After the `hi1` correction, the corrected trial `q1c` is still
    bounded by `q_true_1 + 2`:

    ```
    q1c.toNat ≤ (uHi * 2^32 + div_un1) / vTop + 2
    ```

    Case analysis on `hi1`:
    - `hi1 = 0` (q1 < 2^32): `q1c = q1`, KB-LB10 closes directly.
    - `hi1 ≠ 0` (q1 ≥ 2^32): `q1c = q1 - 1`. From KB-LB10
      `q1 ≤ q_true_1 + 2`, so `q1c = q1 - 1 ≤ q_true_1 + 1 ≤ q_true_1 + 2`.

    Phase 1a-corrected upper bound on the way to KB-LB12 (Phase 1b
    Knuth Theorem C tight bound, which is the missing piece for U3). -/
theorem div128Quot_q1c_le_q_true_1_plus_two
    (uHi dHi dLo div_un1 : Word)
    (hdHi_ne : dHi ≠ 0)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (h_div_un1_lt : div_un1.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 2 := by
  intro q1 hi1 q1c
  have h_q1_le : q1.toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 2 :=
    div128Quot_q1_le_q_true_1_plus_two uHi dHi dLo div_un1
      hdHi_ne hdHi_ge hdLo_lt h_div_un1_lt huHi_lt_vTop
  by_cases h_hi1 : hi1 = 0
  · -- q1c = q1.
    show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat ≤ _
    rw [if_pos h_hi1]
    exact h_q1_le
  · -- q1c = q1 - 1 (mod 2^64). Use q1 ≥ 2^32 from hi1 ≠ 0.
    have h_q1_ge_pow32 : q1.toNat ≥ 2^32 := by
      by_contra h
      push Not at h
      apply h_hi1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      show q1.toNat / 2^32 = (0 : Word).toNat
      rw [Nat.div_eq_of_lt h]; rfl
    show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat ≤ _
    rw [if_neg h_hi1]
    rw [BitVec.toNat_add, signExtend12_4095_toNat]
    have h_q1_lt : q1.toNat < 2^64 := q1.isLt
    have h_q1_sub_lt : q1.toNat - 1 < 2^64 := by omega
    rw [show q1.toNat + (2^64 - 1) = (q1.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt h_q1_sub_lt]
    omega

/-- **Strong Knuth Theorem C (abstract algebra form): trial overshoot
    forces the multiplication check.** Given the Phase 1a Euclidean
    `q1c * dHi + rhatc = uHi` and a 2-overshoot of the trial, the
    Knuth multiplication-check inequality holds:

    ```
    q1c ≥ q_true_1 + 2  →  rhatc * 2^32 + div_un1 < q1c * dLo
    ```

    This is the **contrapositive** form needed to close Phase 1b's
    upper bound: if the check doesn't fire (so `q1' = q1c`) but q1c
    were ≥ q_true_1 + 2, this lemma would force the check to fire,
    contradicting the assumption.

    Proof: from overshoot `q1c ≥ q_true_1 + 2`, we have
    `q1c * vTop ≥ (q_true_1 + 2) * vTop = (q_true_1 + 1) * vTop + vTop
                 > (uHi * 2^32 + div_un1) + vTop`.
    Use Phase 1a Euclidean to expand `q1c * vTop = uHi * 2^32 -
    rhatc * 2^32 + q1c * dLo`. Combining: `q1c * dLo > rhatc * 2^32 +
    div_un1 + vTop > rhatc * 2^32 + div_un1`. -/
theorem knuth_theorem_c_strong_abstract
    (uHi dHi dLo div_un1 rhatc q1c : Word)
    (h_eucl : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat)
    (h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat)
    (h_q1c_overshoot :
        q1c.toNat ≥ (uHi.toNat * 2^32 + div_un1.toNat) /
                      (dHi.toNat * 2^32 + dLo.toNat) + 2) :
    rhatc.toNat * 2^32 + div_un1.toNat < q1c.toNat * dLo.toNat := by
  set vTop := dHi.toNat * 2^32 + dLo.toNat with h_vTop_def
  set q_true_1 := (uHi.toNat * 2^32 + div_un1.toNat) / vTop with h_q_true_1_def
  -- Floor inequality: uHi * 2^32 + div_un1 < (q_true_1 + 1) * vTop.
  set r := (uHi.toNat * 2^32 + div_un1.toNat) % vTop with h_r_def
  have h_dvm : vTop * q_true_1 + r = uHi.toNat * 2^32 + div_un1.toNat :=
    Nat.div_add_mod _ _
  have h_mod_lt : r < vTop :=
    Nat.mod_lt _ h_vTop_pos
  have h_floor_lt : uHi.toNat * 2^32 + div_un1.toNat < (q_true_1 + 1) * vTop := by
    have h_eq : (q_true_1 + 1) * vTop = vTop * q_true_1 + vTop := by ring
    rw [h_eq]; omega
  -- q1c * vTop ≥ (q_true_1 + 2) * vTop (monotonicity of overshoot).
  have h_q1c_vTop_ge : q1c.toNat * vTop ≥ (q_true_1 + 2) * vTop :=
    Nat.mul_le_mul_right _ h_q1c_overshoot
  -- (q_true_1 + 2) * vTop = (q_true_1 + 1) * vTop + vTop.
  have h_chain : q1c.toNat * vTop > uHi.toNat * 2^32 + div_un1.toNat + vTop := by
    have h_split : (q_true_1 + 2) * vTop = (q_true_1 + 1) * vTop + vTop := by ring
    linarith
  -- Multiply Phase 1a Euclidean by 2^32:
  --   uHi * 2^32 = q1c * dHi * 2^32 + rhatc * 2^32.
  have h_eucl_mul :
      uHi.toNat * 2^32 = q1c.toNat * dHi.toNat * 2^32 + rhatc.toNat * 2^32 := by
    have hh : (q1c.toNat * dHi.toNat + rhatc.toNat) * 2^32 = uHi.toNat * 2^32 :=
      congr_arg (· * 2^32) h_eucl
    have : (q1c.toNat * dHi.toNat + rhatc.toNat) * 2^32 =
        q1c.toNat * dHi.toNat * 2^32 + rhatc.toNat * 2^32 := by ring
    linarith
  -- Expand q1c * vTop = q1c * dHi * 2^32 + q1c * dLo.
  have h_expand_vTop :
      q1c.toNat * vTop = q1c.toNat * dHi.toNat * 2^32 + q1c.toNat * dLo.toNat := by
    show q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) = _
    ring
  -- vTop ≥ 1 (positivity).
  have h_vTop_ge_1 : 1 ≤ vTop := h_vTop_pos
  -- Now linarith should combine h_chain, h_expand_vTop, h_eucl_mul, h_vTop_ge_1.
  linarith

/-- **Strong Knuth-C contrapositive (abstract algebra form):
    no-check ⟹ q1c ≤ q_true_1 + 1.** The contrapositive of
    `knuth_theorem_c_strong_abstract`: when the multiplication check
    inequality fails (i.e., `q1c * dLo ≤ rhatc * 2^32 + div_un1`),
    the Phase 1a-corrected trial is at most `q_true_1 + 1`:

    ```
    q1c * dLo ≤ rhatc * 2^32 + div_un1
      → q1c ≤ q_true_1 + 1
    ```

    This is the form ready to use in Phase 1b's "check doesn't fire"
    branch: q1' = q1c there, so q1' ≤ q_true_1 + 1 directly.

    Direct contrapositive of `knuth_theorem_c_strong_abstract`. -/
theorem knuth_theorem_c_strong_contrapositive
    (uHi dHi dLo div_un1 rhatc q1c : Word)
    (h_eucl : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat)
    (h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat)
    (h_no_check : q1c.toNat * dLo.toNat ≤ rhatc.toNat * 2^32 + div_un1.toNat) :
    q1c.toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 1 := by
  by_contra h
  push Not at h
  have h_overshoot : q1c.toNat ≥
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 2 := by omega
  have h_check :=
    knuth_theorem_c_strong_abstract uHi dHi dLo div_un1 rhatc q1c
      h_eucl h_vTop_pos h_overshoot
  omega

/-- **KB-LB12: Phase 1b Knuth Theorem C tight upper bound.** Under the
    `uHi < 2^63` regime (gives KB-LB6a/6b: q1 < 2^32, rhatc < 2^32), the
    post-Phase-1b corrected trial `q1'` overshoots `q_true_1` by at most 1:

    ```
    q1'.toNat ≤ (uHi * 2^32 + div_un1) /
                (dHi * 2^32 + dLo) + 1
    ```

    This is **Knuth Theorem C** in its tight Word-level form, restricted
    to our specific algorithmic setup.

    Proof: case analysis on Phase 1b's check.
    - **Check fires** (q1' = q1c - 1): KB-LB11 gives q1c ≤ q_true_1 + 2,
      so q1' = q1c - 1 ≤ q_true_1 + 1. ✓
    - **Check doesn't fire** (q1' = q1c): the negation of the BitVec.ult
      check unfolds via `halfword_combine` + Word non-wrap of `q1c * dLo`
      to the Nat-level no-check inequality
      `q1c * dLo ≤ rhatc * 2^32 + div_un1`. The strong Knuth-C
      contrapositive then gives `q1c ≤ q_true_1 + 1`. ✓

    Note: This bound is necessary but **not sufficient** to close U3's
    hard case (which requires `q1' ≤ q_true_1` exactly when check fires
    AND rhat' < 2^32). See U3's roadmap comment. -/
theorem div128Quot_q1_prime_le_q_true_1_plus_one
    (uHi dHi dLo uLo : Word)
    (hdHi_ne : dHi ≠ 0)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63) :
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    q1'.toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 1 := by
  intro div_un1 q1 rhat hi1 q1c rhatc rhatUn1 q1'
  -- KB-LB6a: q1 < 2^32 under uHi < 2^63.
  have h_q1_lt : q1.toNat < 2^32 :=
    div128Quot_q1_lt_pow32_of_uHi_lt_pow63 uHi dHi hdHi_ne huHi_lt_pow63 hdHi_ge
  -- hi1 = 0 from q1 < 2^32, so q1c = q1 and rhatc = rhat.
  have h_hi1 : hi1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    show (q1 >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt h_q1_lt]; rfl
  have h_q1c_eq_q1 : q1c = q1 := by
    show (if hi1 = 0 then q1 else q1 + signExtend12 4095) = q1
    rw [if_pos h_hi1]
  have h_rhatc_eq_rhat : rhatc = rhat := by
    show (if hi1 = 0 then rhat else rhat + dHi) = rhat
    rw [if_pos h_hi1]
  have h_q1c_lt : q1c.toNat < 2^32 := h_q1c_eq_q1 ▸ h_q1_lt
  -- KB-LB6b: rhatc < 2^32 under uHi < 2^63.
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    div128Quot_rhatc_lt_pow32_of_uHi_lt_pow63 uHi dHi hdHi_ne huHi_lt_pow63
      hdHi_ge hdHi_lt
  -- div_un1 < 2^32.
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (uLo >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : uLo.toNat < 2^64 := uLo.isLt
    have heq64 : (2^64 : Nat) = 2^32 * 2^32 := by decide
    omega
  -- (q1c * dLo).toNat = q1c.toNat * dLo.toNat (Word non-wrap).
  have h_qDlo_eq : (q1c * dLo).toNat = q1c.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    have h1 : q1c.toNat * dLo.toNat < 2^32 * 2^32 :=
      Nat.mul_lt_mul'' h_q1c_lt hdLo_lt
    have h2 : (2^32 * 2^32 : Nat) = 2^64 := by decide
    omega
  -- rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat.
  have h_rhatUn1_eq : rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat := by
    show ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat = _
    rw [bv6_toNat_32]
    exact EvmWord.halfword_combine rhatc div_un1 h_rhatc_lt h_div_un1_lt
  -- Phase 1a Euclidean: q1c * dHi + rhatc = uHi.
  have h_eucl : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat :=
    div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  -- vTop > 0.
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h_dHi_pos : 0 < dHi.toNat := by omega
    have h_pow_pos : (0 : Nat) < 2^32 := by decide
    have : 0 < dHi.toNat * 2^32 := Nat.mul_pos h_dHi_pos h_pow_pos
    exact Nat.lt_of_lt_of_le this (Nat.le_add_right _ _)
  -- KB-LB11 gives q1c ≤ q_true_1 + 2 (need it for both branches).
  have h_q1c_le_plus_two : q1c.toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 2 := by
    have := div128Quot_q1c_le_q_true_1_plus_two uHi dHi dLo div_un1
      hdHi_ne hdHi_ge hdLo_lt h_div_un1_lt huHi_lt_vTop
    -- this gives the same bound but for `if hi1 = 0 then q1 else q1 + ...`.
    -- which is q1c.
    exact this
  -- Case analysis on Phase 1b check.
  by_cases h_check : BitVec.ult rhatUn1 (q1c * dLo)
  · -- Check fires: q1' = q1c - 1.
    have h_q1c_pos := div128Quot_phase1b_check_implies_q1c_pos q1c dLo rhatUn1 h_check
    have h_q1' : q1'.toNat = q1c.toNat - 1 := by
      show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
            else q1c).toNat = _
      rw [if_pos h_check]
      rw [BitVec.toNat_add, signExtend12_4095_toNat]
      have h_q1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
      rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_lt_word]
    omega
  · -- Check doesn't fire: q1' = q1c. Use strong Knuth-C contrapositive.
    have h_q1' : q1'.toNat = q1c.toNat := by
      show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
            else q1c).toNat = _
      rw [if_neg h_check]
    -- ¬BitVec.ult ⟹ rhatUn1.toNat ≥ (q1c * dLo).toNat.
    have h_no_check_word : (q1c * dLo).toNat ≤ rhatUn1.toNat := by
      have := h_check
      rw [EvmWord.ult_iff] at this
      omega
    -- Bridge to Nat: q1c.toNat * dLo.toNat ≤ rhatc.toNat * 2^32 + div_un1.toNat.
    have h_no_check_nat :
        q1c.toNat * dLo.toNat ≤ rhatc.toNat * 2^32 + div_un1.toNat := by
      rw [← h_qDlo_eq, ← h_rhatUn1_eq]; exact h_no_check_word
    -- Apply strong Knuth-C contrapositive.
    have h_contra :=
      knuth_theorem_c_strong_contrapositive uHi dHi dLo div_un1 rhatc q1c
        h_eucl h_vTop_pos h_no_check_nat
    omega


end EvmAsm.Evm64
