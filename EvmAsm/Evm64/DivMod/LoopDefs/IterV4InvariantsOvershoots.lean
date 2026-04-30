/-
  EvmAsm.Evm64.DivMod.LoopDefs.IterV4InvariantsOvershoots

  Phase-1 overshoot dispatcher and `_phase1_perfect` for `div128Quot_v4`.
  Extracted from `IterV4Invariants.lean` for the file-size guardrail
  (issue #1419, slice 2/3).

  Contains:
    * `div128Quot_v4_phase1_overshoot_0_sub`
    * `div128Quot_v4_phase1_overshoot_1_rhatc_lt_pow32_sub`
    * `div128Quot_v4_phase1_overshoot_1_sub`
    * `div128Quot_v4_phase1_overshoot_2_rhatc_lt_pow32_sub`
    * `div128Quot_v4_phase1_overshoot_2_sub`
    * `div128Quot_v4_phase1_perfect`

  No semantic change: theorems and statements are identical to those
  previously in `IterV4Invariants.lean`.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.IterV4InvariantsHelpers

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Phase-1 overshoot 0 case (v4).** Under `q1c.toNat = q_true`,
    Phase-1b's 1st and 2nd D3 corrections are both no-ops, so
    `q1'' = q1c = q_true`. -/
theorem div128Quot_v4_phase1_overshoot_0_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat)) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Both `phase2b_q0'` calls are no-ops: the BLTU on (rhatc, q1c*dLo)
  -- doesn't fire because q1c = q_true (Knuth-A bound saturates). Apply
  -- the inner-BLTU-fails helper to discharge both.
  have h_q1c_le : q1c.toNat ≤ (uHi.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) := by
    rw [h_q1c_eq_q_true]
  have h_no_bltu := div128Quot_v4_phase1_inner_bltu_fails_when_q1c_le_q_true
    uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q1c_le
  -- 1st correction: q1' = q1c.
  have h_q1'_eq : q1' = q1c :=
    div128Quot_phase2b_q0'_eq_self_of_no_bltu q1c rhatc dLo div_un1 h_no_bltu
  -- rhat' = rhatc: the outer rhatc-update's inner if has the same
  -- ¬ BLTU as h_no_bltu, so the if-then else branch returns rhatc.
  have h_rhat'_eq : rhat' = rhatc := by
    show (if rhatc >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                            (q1c * dLo)
             then rhatc + dHi else rhatc)
          else rhatc) = rhatc
    by_cases h_guard : rhatc >>> (32 : BitVec 6).toNat = 0
    · rw [if_pos h_guard]
      have h_inner : ¬ BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                                   (q1c * dLo) :=
        fun hb => h_no_bltu ⟨h_guard, hb⟩
      rw [if_neg h_inner]
    · rw [if_neg h_guard]
  -- 2nd correction: q1'' = phase2b_q0' q1' rhat' dLo div_un1
  --   = phase2b_q0' q1c rhatc dLo div_un1 = q1c (no-op via the same helper).
  show (div128Quot_phase2b_q0' q1' rhat' dLo div_un1).toNat = _
  rw [h_q1'_eq, h_rhat'_eq,
      div128Quot_phase2b_q0'_eq_self_of_no_bltu q1c rhatc dLo div_un1 h_no_bltu]
  exact h_q1c_eq_q_true


/-- **Phase-1 overshoot 1 case (v4) — rhatc < 2^32 sub-case.** Under
    `q1c.toNat = q_true + 1` AND `rhatc < 2^32` (guard passes), the 1st
    BLTU fires (decrements q1' to q_true), the 2nd doesn't fire (q1' is
    exact). Result: q1''.toNat = q_true. -/
theorem div128Quot_v4_phase1_overshoot_1_rhatc_lt_pow32_sub
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_1 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 1)
    (h_rhatc_lt :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      rhatc.toNat < 2^32) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Unfold the let-prefixed hypotheses to plain Nat propositions.
  have h_rhatc_lt' : rhatc.toNat < 2^32 := h_rhatc_lt
  -- Set q_true_phase1 alias to bridge let-form mismatches between
  -- the hypothesis (computed via lets) and goal (using local lets).
  set q_true_phase1 := (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) with h_q_true_def
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
  -- Phase-1a Euclidean for q1c/rhatc.
  obtain ⟨h_q1c_dHi_le, h_rhatc_eq⟩ :=
    div128Quot_v4_phase1_rhatc_bridge uHi vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  -- q1c.toNat ≤ 2^32.
  have h_q1c_lt_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt h_uHi_lt_decomp
  -- Convert hypothesis to q_true_phase1 form.
  have h_q1c_eq_q_true_plus_1' : q1c.toNat = q_true_phase1 + 1 :=
    h_q1c_eq_q_true_plus_1
  -- 1st BLTU fires.
  have h_overshoot : q1c.toNat ≥ q_true_phase1 + 1 := by linarith
  have h_bltu_fires := div128Quot_v4_phase1_inner_bltu_fires_when_q1c_overshoots
    uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_overshoot h_rhatc_lt
  -- Outer guard passes.
  have h_guard : rhatc >>> (32 : BitVec 6).toNat = 0 :=
    div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32 rhatc h_rhatc_lt
  -- q1' = q1c + signExtend12 4095 (Word).
  have h_q1'_word : q1' = q1c + signExtend12 4095 := by
    show div128Quot_phase2b_q0' q1c rhatc dLo div_un1 = _
    unfold div128Quot_phase2b_q0'
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- q1c.toNat ≥ 1.
  have h_q1c_pos : q1c.toNat ≥ 1 := by linarith
  -- q1'.toNat = q1c.toNat - 1.
  have h_q1'_toNat : q1'.toNat = q1c.toNat - 1 := by
    rw [h_q1'_word, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
    rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq1c_lt_word]
  -- rhat' = rhatc + dHi (Word).
  have h_rhat'_word : rhat' = rhatc + dHi := by
    show (if rhatc >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                            (q1c * dLo)
             then rhatc + dHi else rhatc)
          else rhatc) = rhatc + dHi
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- rhat'.toNat = rhatc.toNat + dHi.toNat (no overflow).
  have h_rhat'_toNat : rhat'.toNat = rhatc.toNat + dHi.toNat := by
    rw [h_rhat'_word, BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    -- rhatc < 2^32 (h_rhatc_lt') + dHi < 2^32 (hdHi_lt) → sum < 2^33 < 2^64.
    have h_sum_lt : rhatc.toNat + dHi.toNat < 2^32 + 2^32 := by linarith
    linarith [show (2:Nat)^32 + 2^32 < 2^64 from by decide]
  -- New Phase-1a Eucl via the proven helper.
  obtain ⟨h_q1c_minus_one_dHi_le, h_rhatc_plus_dHi_eq⟩ :=
    div128Quot_v4_phase1_post_correction_eucl_arith
      uHi.toNat q1c.toNat dHi.toNat rhatc.toNat
      h_q1c_pos h_q1c_dHi_le h_rhatc_eq
  -- Translate to q1', rhat'.
  have h_q1'_dHi_le : q1'.toNat * dHi.toNat ≤ uHi.toNat := by
    rw [h_q1'_toNat]; exact h_q1c_minus_one_dHi_le
  have h_rhat'_eq : rhat'.toNat = uHi.toNat - q1'.toNat * dHi.toNat := by
    rw [h_q1'_toNat, h_rhat'_toNat]; exact h_rhatc_plus_dHi_eq
  -- q1'.toNat = q_true_phase1 (q1' = q_true exactly).
  have h_q1'_eq_q_true : q1'.toNat = q_true_phase1 := by
    have h1 : q1'.toNat = q1c.toNat - 1 := h_q1'_toNat
    have h2 : q1c.toNat = q_true_phase1 + 1 := h_q1c_eq_q_true_plus_1'
    omega
  have h_q1'_le_q_true : q1'.toNat ≤ (uHi.toNat * 2^32 + div_un1.toNat) /
                                      (dHi.toNat * 2^32 + dLo.toNat) := by
    rw [h_q1'_eq_q_true, h_q_true_def]
  -- q1'.toNat ≤ 2^32.
  have h_q1'_lt_pow32 : q1'.toNat ≤ 2^32 := by linarith
  -- 2nd BLTU doesn't fire (apply generic helper).
  have h_no_bltu := div128Quot_v4_phase1_inner_bltu_fails_generic
    uHi q1' rhat' dHi dLo div_un1
    hdLo_lt h_div_un1_lt h_q1'_dHi_le h_rhat'_eq h_q1'_lt_pow32 h_q1'_le_q_true
  -- 2nd correction: q1'' = q1' (no-op).
  show (div128Quot_phase2b_q0' q1' rhat' dLo div_un1).toNat = _
  rw [div128Quot_phase2b_q0'_eq_self_of_no_bltu q1' rhat' dLo div_un1 h_no_bltu]
  rw [h_q1'_eq_q_true, h_q_true_def]


/-- **Phase-1 overshoot 1 case (v4).** Under `q1c.toNat = q_true + 1`,
    the 1st D3 correction decrements to q_true, the 2nd is a no-op.

    Proof structure (case-split on the rhatc guard):

    - **Guard passes (rhatc < 2^32):**
      1st BLTU fires (via `_phase1_bltu_fires_arith` proven above):
      `rhatc * 2^32 + div_un1 < q1c * dLo` from
      `q1c * vTop > uHi*2^32 + div_un1` (Knuth strict, since q1c > q_true).
      So q1' = q1c - 1 = q_true. rhat' = rhatc + dHi.
      2nd BLTU doesn't fire (q1' is exact, applies
      `_phase1_inner_bltu_fails_when_q1c_le_q_true` to q1' / rhat').
      Thus q1'' = q1' = q_true.

    - **Guard fails (rhatc ≥ 2^32):** PROVABLY UNREACHABLE under
      shift-norm + uHi < vTop + overshoot ≥ 1. Closes via the
      `_phase1_no_overshoot_when_rhatc_ge_pow32` sub-lemma below.

      Algebraic argument (verified empirically on 438+ inputs):
      - rhatc ≥ 2^32 + hi1 ≠ 0 ⟹ rhat ≥ 2^32 - dHi.
      - Plugging into the floor inequality
        `(2^32 - 1) * vTop ≤ uHi*2^32 + div_un1` (Knuth-A applied to
        q1c = q_true + 1) gives a contradiction:
        `(dLo - dHi - r) * 2^32 ≤ div_un1 + dLo` would require
        `(2^32 - dLo) * 2^32 ≤ div_un1 + dLo`, but with dLo < 2^32 the
        LHS is positive ≥ 2^32 and RHS < 2^33, only marginally
        consistent — and after careful arithmetic, the strict
        inequality forces `dLo > 2^32 - O(1)` while `r ≥ 2^32 - dHi`
        forces dHi to dominate. The two constraints together force
        `2^64 < dLo * (2^32 - 1)`, which is impossible for
        `dLo < 2^32`.

      Net result: this case is vacuous; v4's algorithm is correct
      under runtime preconditions. -/
theorem div128Quot_v4_phase1_overshoot_1_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_1 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 1) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Case split on the rhatc guard.
  by_cases h_rhatc_lt : rhatc.toNat < 2^32
  · -- rhatc < 2^32: 1st BLTU fires, q1' = q_true; 2nd doesn't fire.
    -- Delegated to the focused helper below.
    exact div128Quot_v4_phase1_overshoot_1_rhatc_lt_pow32_sub
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q1c_eq_q_true_plus_1 h_rhatc_lt
  · -- rhatc ≥ 2^32: vacuous via `_no_overshoot_when_rhatc_ge_pow32`
    --   (contradicts the overshoot-1 hypothesis).
    push Not at h_rhatc_lt
    exfalso
    have h_no_overshoot := div128Quot_v4_phase1_no_overshoot_when_rhatc_ge_pow32
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_rhatc_lt
    -- h_no_overshoot: q1c.toNat ≤ q_true_phase1.
    -- h_q1c_eq_q_true_plus_1: q1c.toNat = q_true_phase1 + 1.
    omega


/-- **Phase-1 overshoot 2 case (v4) — rhatc < 2^32 sub-case.** Under
    `q1c.toNat = q_true + 2` AND `rhatc < 2^32` (guard passes), the 1st
    BLTU fires (q1' = q_true + 1), then the 2nd BLTU ALSO fires
    (q1'' = q_true). The crucial v4 case where Knuth's full
    2-correction loop is required. -/
theorem div128Quot_v4_phase1_overshoot_2_rhatc_lt_pow32_sub
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_2 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 2)
    (h_rhatc_lt :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let rhat := uHi - q1 * dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let rhatc := if hi1 = 0 then rhat else rhat + dHi
      rhatc.toNat < 2^32) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Unfold let-prefixed hypotheses.
  have h_rhatc_lt' : rhatc.toNat < 2^32 := h_rhatc_lt
  -- Set q_true_phase1 alias to bridge let-form mismatches.
  set q_true_phase1 := (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) with h_q_true_def
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
  -- Phase-1a Euclidean for q1c/rhatc.
  obtain ⟨h_q1c_dHi_le, h_rhatc_eq⟩ :=
    div128Quot_v4_phase1_rhatc_bridge uHi vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  -- q1c.toNat ≤ 2^32.
  have h_q1c_lt_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt h_uHi_lt_decomp
  -- Convert hypothesis to q_true_phase1 form.
  have h_q1c_eq_q_true_plus_2' : q1c.toNat = q_true_phase1 + 2 :=
    h_q1c_eq_q_true_plus_2
  -- 1st BLTU fires.
  have h_overshoot_1st : q1c.toNat ≥ q_true_phase1 + 1 := by linarith
  have h_overshoot_1st' : q1c.toNat ≥ (uHi.toNat * 2^32 + div_un1.toNat) /
                                       (dHi.toNat * 2^32 + dLo.toNat) + 1 :=
    h_overshoot_1st
  have h_bltu_fires := div128Quot_v4_phase1_inner_bltu_fires_when_q1c_overshoots
    uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_overshoot_1st' h_rhatc_lt
  -- Outer guard passes.
  have h_guard : rhatc >>> (32 : BitVec 6).toNat = 0 :=
    div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32 rhatc h_rhatc_lt'
  -- q1' = q1c + signExtend12 4095 (Word).
  have h_q1'_word : q1' = q1c + signExtend12 4095 := by
    show div128Quot_phase2b_q0' q1c rhatc dLo div_un1 = _
    unfold div128Quot_phase2b_q0'
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- q1c.toNat ≥ 2 (since q1c = q_true + 2).
  have h_q1c_ge_2 : q1c.toNat ≥ 2 := by linarith
  have h_q1c_pos : q1c.toNat ≥ 1 := by linarith
  -- q1'.toNat = q1c.toNat - 1.
  have h_q1'_toNat : q1'.toNat = q1c.toNat - 1 := by
    rw [h_q1'_word, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
    rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq1c_lt_word]
  -- rhat' = rhatc + dHi (Word).
  have h_rhat'_word : rhat' = rhatc + dHi := by
    show (if rhatc >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                            (q1c * dLo)
             then rhatc + dHi else rhatc)
          else rhatc) = rhatc + dHi
    simp only [h_guard, if_true]
    rw [if_pos h_bltu_fires]
  -- rhat'.toNat = rhatc.toNat + dHi.toNat (no overflow).
  have h_rhat'_toNat : rhat'.toNat = rhatc.toNat + dHi.toNat := by
    rw [h_rhat'_word, BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    have h_sum_lt : rhatc.toNat + dHi.toNat < 2^32 + 2^32 := by linarith
    linarith [show (2:Nat)^32 + 2^32 < 2^64 from by decide]
  -- New Phase-1a Eucl via the proven helper.
  obtain ⟨h_q1c_minus_one_dHi_le, h_rhatc_plus_dHi_eq⟩ :=
    div128Quot_v4_phase1_post_correction_eucl_arith
      uHi.toNat q1c.toNat dHi.toNat rhatc.toNat
      h_q1c_pos h_q1c_dHi_le h_rhatc_eq
  -- Translate to q1', rhat'.
  have h_q1'_dHi_le : q1'.toNat * dHi.toNat ≤ uHi.toNat := by
    rw [h_q1'_toNat]; exact h_q1c_minus_one_dHi_le
  have h_rhat'_eq : rhat'.toNat = uHi.toNat - q1'.toNat * dHi.toNat := by
    rw [h_q1'_toNat, h_rhat'_toNat]; exact h_rhatc_plus_dHi_eq
  -- q1'.toNat = q_true_phase1 + 1 (still overshoots by 1).
  have h_q1'_eq : q1'.toNat = q_true_phase1 + 1 := by
    have h1 : q1'.toNat = q1c.toNat - 1 := h_q1'_toNat
    have h2 : q1c.toNat = q_true_phase1 + 2 := h_q1c_eq_q_true_plus_2'
    omega
  -- q1'.toNat ≤ 2^32.
  have h_q1'_lt_pow32 : q1'.toNat ≤ 2^32 := by linarith
  -- rhat'.toNat < 2^32: derive via the no_overshoot_generic helper.
  --   If rhat' ≥ 2^32, then q1' ≤ q_true_phase1, but q1' = q_true + 1.
  --   Contradiction.
  have h_rhat'_lt : rhat'.toNat < 2^32 := by
    by_contra h
    push Not at h
    have h_no_over := div128Quot_v4_phase1_no_overshoot_when_rhat_ge_pow32_generic
      uHi q1' rhat' dHi dLo div_un1
      hdHi_ge hdLo_lt h_q1'_dHi_le h_rhat'_eq h_q1'_lt_pow32 h
    -- h_no_over : q1'.toNat ≤ q_true_phase1. But h_q1'_eq : q1'.toNat = q_true + 1.
    omega
  -- 2nd BLTU fires (apply fires_generic for q1', rhat').
  have h_q1'_overshoot : q1'.toNat ≥ (uHi.toNat * 2^32 + div_un1.toNat) /
                                      (dHi.toNat * 2^32 + dLo.toNat) + 1 := by
    rw [h_q1'_eq]
  have h_bltu_fires_2 :=
    div128Quot_v4_phase1_inner_bltu_fires_generic
      uHi q1' rhat' dHi dLo div_un1
      hdHi_ge hdLo_lt h_div_un1_lt h_q1'_dHi_le h_rhat'_eq
      h_rhat'_lt h_q1'_lt_pow32 h_q1'_overshoot
  -- Outer guard passes for the 2nd correction (rhat' < 2^32).
  have h_guard_2 : rhat' >>> (32 : BitVec 6).toNat = 0 :=
    div128Quot_v4_word_ushiftRight_32_zero_of_lt_pow32 rhat' h_rhat'_lt
  -- q1'' = q1' + signExtend12 4095 = q1' - 1 (Word).
  have h_q1''_word : q1'' = q1' + signExtend12 4095 := by
    show div128Quot_phase2b_q0' q1' rhat' dLo div_un1 = _
    unfold div128Quot_phase2b_q0'
    simp only [h_guard_2, if_true]
    rw [if_pos h_bltu_fires_2]
  -- q1''.toNat = q1'.toNat - 1.
  have h_q1''_toNat : q1''.toNat = q1'.toNat - 1 := by
    rw [h_q1''_word, BitVec.toNat_add, signExtend12_4095_toNat]
    have hq1'_lt_word : q1'.toNat - 1 < 2^64 := by have := q1'.isLt; omega
    have h_q1'_pos : q1'.toNat ≥ 1 := by linarith
    rw [show q1'.toNat + (2^64 - 1) = (q1'.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq1'_lt_word]
  -- Conclude q1''.toNat = q_true_phase1.
  have h_q1''_eq : q1''.toNat = q_true_phase1 := by
    have h1 : q1''.toNat = q1'.toNat - 1 := h_q1''_toNat
    have h2 : q1'.toNat = q_true_phase1 + 1 := h_q1'_eq
    omega
  rw [h_q1''_eq, h_q_true_def]


/-- **Phase-1 overshoot 2 case (v4).** Under `q1c.toNat = q_true + 2`,
    the 1st D3 correction decrements to q_true + 1, the 2nd to q_true. -/
theorem div128Quot_v4_phase1_overshoot_2_sub (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_q1c_eq_q_true_plus_2 :
      let dHi := vTop >>> (32 : BitVec 6).toNat
      let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
      let div_un1 := uLo >>> (32 : BitVec 6).toNat
      let q1 := rv64_divu uHi dHi
      let hi1 := q1 >>> (32 : BitVec 6).toNat
      let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
      q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                  (dHi.toNat * 2^32 + dLo.toNat) + 2) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Same dispatcher as `_phase1_overshoot_1_sub`: case-split on rhatc guard.
  by_cases h_rhatc_lt : rhatc.toNat < 2^32
  · -- rhatc < 2^32: 1st BLTU fires, q1' = q_true + 1; 2nd BLTU also fires,
    -- q1'' = q_true. Delegated to focused helper below.
    exact div128Quot_v4_phase1_overshoot_2_rhatc_lt_pow32_sub
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_q1c_eq_q_true_plus_2 h_rhatc_lt
  · -- rhatc ≥ 2^32: vacuous via `_no_overshoot_when_rhatc_ge_pow32`
    --   (contradicts the overshoot-2 hypothesis even more strongly).
    --   Actually under hi1 ≠ 0 (which forces rhatc ≥ 2^32 to be possible),
    --   q1c ≤ q_true + 1 (Knuth-B with hi1 ≠ 0), so overshoot-2 is
    --   already impossible at the Knuth-range level. The dispatcher
    --   bound suffices.
    push Not at h_rhatc_lt
    exfalso
    have h_no_overshoot := div128Quot_v4_phase1_no_overshoot_when_rhatc_ge_pow32
      uHi uLo vTop h_vTop_ge_pow63 h_uHi_lt_vTop h_rhatc_lt
    omega


/-- **Phase-1b 2-correction perfection (v4).** After v4's symmetric
    Phase-1b 2-correction loop, `q1''` equals the abstract Phase-1
    quotient `q*_phase1 = ⌊(uHi * 2^32 + div_un1) / vTop_high32⌋` where
    `vTop_high32 = dHi * 2^32 + dLo = vTop.toNat`.

    Mirrors Knuth's classical Algorithm D guarantee that the 2-iteration
    D3 loop always terminates with the exact trial digit.

    Dispatcher: case-splits on overshoot k = q1c.toNat - q_true ∈ {0, 1, 2}
    via `_phase1c_in_knuth_range`, then routes to the appropriate
    `_phase1_overshoot_k_sub`. -/
theorem div128Quot_v4_phase1_perfect (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                 (dHi.toNat * 2^32 + dLo.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1''
  -- Knuth range gives q_true ≤ q1c.toNat ≤ q_true + 2.
  have h_range := div128Quot_v4_phase1c_in_knuth_range uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_lower, h_upper⟩ := h_range
  -- linarith handles let-bindings more gracefully than omega: it matches
  -- on syntactic form and lets `change`/definitional reduction unify the
  -- q_true unfoldings between h_range and the goal.
  rcases Nat.lt_or_ge q1c.toNat
      ((uHi.toNat * 2^32 + div_un1.toNat) /
       (dHi.toNat * 2^32 + dLo.toNat) + 1) with h1 | h1
  · -- q1c.toNat = q_true (overshoot 0).
    have h_eq : q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                            (dHi.toNat * 2^32 + dLo.toNat) := by linarith
    exact div128Quot_v4_phase1_overshoot_0_sub uHi uLo vTop
      h_vTop_ge_pow63 h_uHi_lt_vTop h_eq
  · rcases Nat.lt_or_ge q1c.toNat
        ((uHi.toNat * 2^32 + div_un1.toNat) /
         (dHi.toNat * 2^32 + dLo.toNat) + 2) with h2 | h2
    · -- q1c.toNat = q_true + 1 (overshoot 1).
      have h_eq : q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) + 1 := by linarith
      exact div128Quot_v4_phase1_overshoot_1_sub uHi uLo vTop
        h_vTop_ge_pow63 h_uHi_lt_vTop h_eq
    · -- q1c.toNat = q_true + 2 (overshoot 2).
      have h_eq : q1c.toNat = (uHi.toNat * 2^32 + div_un1.toNat) /
                              (dHi.toNat * 2^32 + dLo.toNat) + 2 := by linarith
      exact div128Quot_v4_phase1_overshoot_2_sub uHi uLo vTop
        h_vTop_ge_pow63 h_uHi_lt_vTop h_eq

end EvmAsm.Evm64
