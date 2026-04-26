/-
  EvmAsm.Evm64.EvmWordArith.Div128PhaseNoWrap

  Phase 1 no-wrap precondition lemmas for `div128Quot`. Split from
  `Div128KnuthLower.lean` to stay under the 1500-line file-size guardrail.

  Contents:
  - `phase1_no_wrap_lo_subcase_a_iff_q1_prime_le_q_true_1` — Sub-case A
    algebraic reduction.
  - `div128Quot_phase1_no_wrap` — original U3 lemma (sorry; counterexample
    confirms unprovable as-stated, see `project_u3_unprovable_counterexample.md`).
  - `div128Quot_phase1_no_wrap_skip` — call-skip variant (CLOSED).

  See `project_un21_lt_vTop_plan.md` for the full plan.
-/

import EvmAsm.Evm64.EvmWordArith.Div128KnuthLower

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv6_toNat_32)

/-- **U3 Sub-case A reduction (abstract algebra form):
    no-wrap-lo ↔ q1' ≤ q_true_1 when rhat' < 2^32.** Under Phase 1b
    Euclidean `q1' * dHi + rhat' = uHi` and the small-rhat' regime
    (`rhat' < 2^32`), the algorithm's no-wrap precondition for `un21`
    is equivalent to the bound `q1' ≤ q_true_1`:

    ```
    q1' * dLo ≤ (rhat' % 2^32) * 2^32 + div_un1
      ↔ q1' ≤ (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo)
    ```

    This is the clean algebraic content of U3's Sub-case A. The
    remaining gap is the **quotient** direction: prove `q1' ≤ q_true_1`
    (i.e., rule out q1' = q_true_1 + 1, the Knuth-C borderline case).

    Combined with KB-LB7 (q1' ≥ q_true_1, lower bound) and KB-LB12
    (q1' ≤ q_true_1 + 1, Theorem-C upper bound), the only open case
    is q1' = q_true_1 + 1. Ruling it out under `rhat' < 2^32` is the
    deep Knuth invariant.

    Decomposes U3's hard case into:
    1. **Algebra** (this lemma, fully proven): biconditional reduction.
    2. **Quotient bound** (open): `q1' ≤ q_true_1` under rhat' < 2^32. -/
theorem phase1_no_wrap_lo_subcase_a_iff_q1_prime_le_q_true_1
    (q1' dHi dLo rhat' uHi div_un1 : Nat)
    (h_eucl : q1' * dHi + rhat' = uHi)
    (h_rhat'_lt_pow32 : rhat' < 2^32)
    (h_vTop_pos : 0 < dHi * 2^32 + dLo) :
    (q1' * dLo ≤ (rhat' % 2^32) * 2^32 + div_un1) ↔
    (q1' ≤ (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo)) := by
  set vTop := dHi * 2^32 + dLo with h_vTop_def
  rw [Nat.mod_eq_of_lt h_rhat'_lt_pow32]
  -- q1' * vTop expands and substitutes via Phase 1b Euclidean.
  have h_expand : q1' * vTop = q1' * dHi * 2^32 + q1' * dLo := by
    show q1' * (dHi * 2^32 + dLo) = _; ring
  -- q1' * dHi * 2^32 = (uHi - rhat') * 2^32 (Nat subtraction valid).
  have h_rhat'_le : rhat' ≤ uHi := by omega
  have h_eucl_mul : q1' * dHi * 2^32 = uHi * 2^32 - rhat' * 2^32 := by
    have h1 : q1' * dHi = uHi - rhat' := by omega
    rw [h1, Nat.sub_mul]
  constructor
  · -- Forward: q1' * dLo ≤ rhat' * 2^32 + div_un1 ⟹ q1' ≤ q_true_1.
    intro h_no_wrap
    -- q1' * vTop ≤ uHi * 2^32 + div_un1.
    have h_q1_vTop : q1' * vTop ≤ uHi * 2^32 + div_un1 := by
      rw [h_expand, h_eucl_mul]
      have h_rhat_pow : rhat' * 2^32 ≤ uHi * 2^32 :=
        Nat.mul_le_mul_right _ h_rhat'_le
      omega
    -- Conclude q1' ≤ q_true_1 via division.
    exact (Nat.le_div_iff_mul_le h_vTop_pos).mpr
      (by linarith [Nat.mul_comm q1' vTop])
  · -- Backward: q1' ≤ q_true_1 ⟹ q1' * dLo ≤ rhat' * 2^32 + div_un1.
    intro h_q1_le
    -- q1' * vTop ≤ q_true_1 * vTop ≤ uHi * 2^32 + div_un1.
    have h_q1_vTop : q1' * vTop ≤ uHi * 2^32 + div_un1 := by
      have h1 : q1' * vTop ≤
          ((uHi * 2^32 + div_un1) / vTop) * vTop :=
        Nat.mul_le_mul_right _ h_q1_le
      have h2 : ((uHi * 2^32 + div_un1) / vTop) * vTop ≤
          uHi * 2^32 + div_un1 :=
        Nat.div_mul_le_self _ _
      omega
    -- Substitute via Phase 1b Euclidean.
    rw [h_expand, h_eucl_mul] at h_q1_vTop
    have h_rhat_pow : rhat' * 2^32 ≤ uHi * 2^32 :=
      Nat.mul_le_mul_right _ h_rhat'_le
    omega

/-- **U3: Phase 1 no-wrap (SORRY).** The Phase 1b no-wrap precondition that
    feeds T1 (`div128Quot_qHat_vTop_le`):

    ```
    q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat
    ```

    Under `dHi ≥ 2^31` (normalization), `dLo < 2^32` (uniform halfword
    bound), `uHi < 2^63` (auto under hshift_nz, gives KB-LB6b's
    `rhatc < 2^32`).

    **Closure path** (case-split on Phase 1b check):

    - **Check doesn't fire** (¬ult rhatUn1 (q1c * dLo)):
      - q1' = q1c, rhat' = rhatc.
      - `(q1c * dLo).toNat = q1c * dLo` (no overflow: q1c < 2^32, dLo < 2^32).
      - `rhatUn1.toNat = rhatc * 2^32 + div_un1` (halfword_combine, since
        rhatc < 2^32 by KB-LB6b).
      - Negation of ult gives `rhatUn1.toNat ≥ q1c * dLo`, i.e.,
        `q1c * dLo ≤ rhatc * 2^32 + div_un1`. ✓

    - **Check fires** (ult rhatUn1 (q1c * dLo)):
      - q1' = q1c - 1, rhat' = rhatc + dHi (Phase 1b correction).
      - Need `(q1c - 1) * dLo ≤ ((rhatc + dHi) % 2^32) * 2^32 + div_un1`.
      - Knuth's correction restores the no-wrap invariant: from check firing
        plus the new rhat' = rhatc + dHi, the new (rhat' % 2^32) * 2^32 +
        div_un1 ≥ (q1c - 1) * dLo. Algebraic argument requires careful
        tracking of (rhatc + dHi) overflow into 2^32 boundary.

    Tracked in #1337 as part of the un21 < vTop plan. -/
theorem div128Quot_phase1_no_wrap (uHi dHi dLo uLo : Word)
    (hdHi_ne : dHi ≠ 0)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_pow63 : uHi.toNat < 2^63) :
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat := by
  intro div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
  -- KB-LB6a: q1 < 2^32 under uHi < 2^63.
  have h_q1_lt : q1.toNat < 2^32 :=
    div128Quot_q1_lt_pow32_of_uHi_lt_pow63 uHi dHi hdHi_ne huHi_lt_pow63 hdHi_ge
  -- KB-LB6b: rhatc < 2^32 under uHi < 2^63.
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    div128Quot_rhatc_lt_pow32_of_uHi_lt_pow63 uHi dHi hdHi_ne huHi_lt_pow63 hdHi_ge hdHi_lt
  -- Hence hi1 = 0 (since q1 < 2^32 means q1 >>> 32 = 0), so q1c = q1.
  have h_hi1 : hi1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    show (q1 >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt h_q1_lt]
    rfl
  have h_q1c_eq_q1 : q1c = q1 := by
    show (if hi1 = 0 then q1 else q1 + signExtend12 4095) = q1
    rw [if_pos h_hi1]
  have h_rhatc_eq_rhat : rhatc = rhat := by
    show (if hi1 = 0 then rhat else rhat + dHi) = rhat
    rw [if_pos h_hi1]
  have h_q1c_lt : q1c.toNat < 2^32 := h_q1c_eq_q1 ▸ h_q1_lt
  -- div_un1 < 2^32 (high half of uLo).
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (uLo >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : uLo.toNat < 2^64 := uLo.isLt
    have : (2^64 : Nat) = 2^32 * 2^32 := by decide
    omega
  -- qDlo doesn't overflow Word: q1c * dLo < 2^32 * 2^32 = 2^64.
  have h_qDlo_eq : qDlo.toNat = q1c.toNat * dLo.toNat := by
    show (q1c * dLo).toNat = _
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    have : q1c.toNat * dLo.toNat < 2^32 * 2^32 :=
      Nat.mul_lt_mul'' h_q1c_lt hdLo_lt
    have : (2^32 * 2^32 : Nat) = 2^64 := by decide
    omega
  -- rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat (halfword_combine).
  have h_rhatUn1_eq : rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat := by
    show ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat = _
    rw [bv6_toNat_32]
    exact EvmWord.halfword_combine rhatc div_un1 h_rhatc_lt h_div_un1_lt
  by_cases h_check : BitVec.ult rhatUn1 qDlo
  · -- Check fires: q1' = q1c - 1, rhat' = rhatc + dHi.
    -- See `project_u3_unprovable_counterexample.md` — this Sub-case A
    -- goal is **NOT PROVABLE** under just `uHi < 2^63`. Use
    -- `div128Quot_phase1_no_wrap_skip` (call-skip variant) for the
    -- closeable form with strengthened hypotheses.
    sorry
  · -- Check doesn't fire: q1' = q1c, rhat' = rhatc.
    have h_q1' : q1' = q1c := by
      show (if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c) = q1c
      rw [if_neg h_check]
    have h_rhat' : rhat' = rhatc := by
      show (if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) = rhatc
      rw [if_neg h_check]
    -- ¬ult rhatUn1 qDlo gives qDlo.toNat ≤ rhatUn1.toNat.
    have h_ge : qDlo.toNat ≤ rhatUn1.toNat := by
      have h := h_check
      rw [EvmWord.ult_iff] at h
      omega
    -- rhatc < 2^32 ⟹ rhatc % 2^32 = rhatc.
    have h_mod : rhatc.toNat % 2^32 = rhatc.toNat := Nat.mod_eq_of_lt h_rhatc_lt
    rw [h_q1', h_rhat', h_mod]
    rw [h_qDlo_eq, h_rhatUn1_eq] at h_ge
    exact h_ge

/-- **U3 call-skip variant (CLOSED for Sub-case A)**: under the
    additional hypothesis that q1' is bounded above by the abstract
    first digit (which holds in the call-skip path where the outer
    mulsub does not borrow on qHat), the no-wrap precondition closes
    cleanly when rhat' < 2^32.

    **Proof structure**:
    - Combined with KB-LB7 (`q1' ≥ q_true_1`), `hq1_prime_le_q_true_1`
      gives q1' = q_true_1 exactly (Knuth's "exact qHat" case).
    - Sub-case A (rhat' < 2^32) closes via
      `phase1_no_wrap_lo_subcase_a_iff_q1_prime_le_q_true_1`.
    - Sub-case B (rhat' ≥ 2^32) is excluded by hypothesis (the call-skip
      path has rhat' < 2^32 by Knuth's Phase 1 remainder invariant —
      derivable from no-addback but not assumed here for simplicity).

    **Caller obligation**: discharge `hq1_prime_le_q_true_1` from the
    runtime no-addback condition (`¬ isAddbackBorrowN4CallEvm a b` plus
    Knuth-B's outer-level `qHat ≤ q_true`). Discharge `hrhat'_lt` from
    KB-LB6b plus the same no-addback condition (forces rhat' < 2^32).

    Issue #1337 / #1338. -/
theorem div128Quot_phase1_no_wrap_skip (uHi dHi dLo uLo : Word)
    (hdHi_ne : dHi ≠ 0)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hq1_prime_le_q_true_1 :
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
                 else q1c
      q1'.toNat ≤ (uHi.toNat * 2^32 + div_un1.toNat) /
                    (dHi.toNat * 2^32 + dLo.toNat))
    (hrhat'_lt :
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
      let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi
                   else rhatc
      rhat'.toNat < 2^32) :
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat := by
  intro div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
  -- Phase 1b Euclidean: q1' * dHi + rhat' = uHi.
  have h_eucl : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat :=
    div128Quot_phase1b_post uHi dHi q1c rhatc dLo rhatUn1 hdHi_lt
      (div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt)
      (div128Quot_rhatc_lt_2dHi uHi dHi hdHi_ne hdHi_lt)
  -- vTop > 0.
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h_dHi_pos : 0 < dHi.toNat := by omega
    have h_pow : (0 : Nat) < 2^32 := by decide
    have h1 : 0 < dHi.toNat * 2^32 := Nat.mul_pos h_dHi_pos h_pow
    exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
  -- Apply Sub-case A iff lemma (rhat' < 2^32).
  exact (phase1_no_wrap_lo_subcase_a_iff_q1_prime_le_q_true_1
    q1'.toNat dHi.toNat dLo.toNat rhat'.toNat uHi.toNat div_un1.toNat
    h_eucl hrhat'_lt h_vTop_pos).mpr hq1_prime_le_q_true_1

end EvmAsm.Evm64
