/-
  EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback

  Inversion of `addbackN4_second_carry_one`: derive the trial-quotient
  overestimate bound (`q ≤ ⌊u/v⌋ + 2`) from the second-addback carry = 1.

  This unblocks the double-addback correctness path: the runtime
  `isAddbackCarry2NzN4Max` check gives the algorithm a carry2 ≠ 0 witness
  (combined with `carry2 < 2` to pin it to 1); from carry2 = 1 this file
  proves the overestimate bound, which then feeds
  `mulsub_double_addback_val256_combined` to get the Euclidean equation
  `val256(u) = (q - 2) * val256(v) + val256(ab')`.

  Foundation for `n4_max_double_addback_correct` (Phase A of the n=4
  max+addback stack spec roadmap, Issue #61).
-/

import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_toNat_1)

/-- Local copy of `EvmWord.fromLimbs_match_getLimbN_id` with the match
    expression elaborated in this file's context, so that the auxiliary
    `match` function identity matches the one produced for our new lemmas'
    `fromLimbs fun i => match i with ...` patterns. Needed because
    `rewrite` requires syntactic identity of the match-auxiliary function,
    and Lean generates these per-file. -/
private theorem fromLimbs_match_getLimbN_id_local (v : EvmWord) :
    (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with
      | 0 => v.getLimbN 0
      | 1 => v.getLimbN 1
      | 2 => v.getLimbN 2
      | 3 => v.getLimbN 3) = v := EvmWord.fromLimbs_match_getLimbN_id v

/-- Inversion: if the second-addback carry is 1 (double-addback path), the
    trial quotient `q` overestimates `⌊val256(u)/val256(v)⌋` by at most 2.
    Converse to `addbackN4_second_carry_one` — that theorem assumes
    `hq_over` and proves `carry2 = 1`; this one uses `carry2 = 1` to
    conclude `hq_over`. -/
theorem hq_over_from_second_carry_one (q : Word) {v0 v1 v2 v3 u0 u1 u2 u3 : Word}
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hc3_one : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hcarry_zero : (addbackN4_carry
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
      v0 v1 v2 v3) = 0)
    (hcarry2_one :
      let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
      (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3).toNat = 1) :
    q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2 := by
  simp only [] at hcarry2_one
  -- From c3 = 1: val256(u) + 2^256 = val256(un) + q * val256(v)
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hmulsub
  rw [show (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = (1 : Word) from hc3_one] at hmulsub
  rw [word_toNat_1] at hmulsub
  -- First addback: val256(un) + val256(v) = val256(ab1) + 0 * 2^256 = val256(ab1)
  set ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
  have hab1 := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
  simp only [] at hab1
  have hc1_val : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3).toNat = 0 := by
    rw [hcarry_zero]; decide
  rw [hc1_val] at hab1
  -- Second addback: val256(ab1) + val256(v) = val256(ab') + 1 * 2^256
  set ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
  have hab' := addbackN4_val256_eq ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3
  simp only [] at hab'
  rw [hcarry2_one] at hab'
  -- Bounds
  have hv_pos : 0 < val256 v0 v1 v2 v3 := val256_pos_of_or_ne_zero hbnz
  have hab'_bound := val256_bound
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.2.1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.2.2.1
  -- From hab' + hab'_bound: val256(ab1) + val256(v) ≥ 2^256 + 1 > 2^256
  -- Combined with hab1 (val256(un) + val256(v) = val256(ab1)):
  --   val256(un) + 2 * val256(v) ≥ 2^256 + 1
  -- From hmulsub: val256(un) = val256(u) + 2^256 - q * val256(v)
  --   val256(u) + 2^256 - q * val256(v) + 2 * val256(v) ≥ 2^256 + 1
  --   val256(u) + (2 - q) * val256(v) ≥ 1  (signed arithmetic)
  --   val256(u) ≥ (q - 2) * val256(v)  (Nat subtraction handles q < 2 trivially)
  -- Hence u/v ≥ q - 2, i.e., q ≤ u/v + 2.
  have hq_v_le_plus : q.toNat * val256 v0 v1 v2 v3 ≤
      val256 u0 u1 u2 u3 + 2 * val256 v0 v1 v2 v3 := by nlinarith
  -- (q - 2) * v ≤ u
  have hqm2_le : (q.toNat - 2) * val256 v0 v1 v2 v3 ≤ val256 u0 u1 u2 u3 := by
    rcases Nat.lt_or_ge q.toNat 2 with hq_lt | hq_ge
    · -- q < 2: q - 2 = 0, trivial
      have : q.toNat - 2 = 0 := by omega
      rw [this]; simp
    · -- q ≥ 2
      have hq_split : q.toNat * val256 v0 v1 v2 v3 =
          (q.toNat - 2) * val256 v0 v1 v2 v3 + 2 * val256 v0 v1 v2 v3 := by
        have : q.toNat = (q.toNat - 2) + 2 := by omega
        nlinarith
      linarith
  -- u/v ≥ q - 2
  have hdiv_ge : val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 ≥ q.toNat - 2 := by
    exact Nat.le_div_iff_mul_le hv_pos |>.mpr (by linarith [Nat.mul_comm (q.toNat - 2) (val256 v0 v1 v2 v3)])
  omega

-- ============================================================================
-- Double-addback correctness: n=4 max trial, c3=1, carry1=0, carry2=1
-- ============================================================================

/-- Double-addback path (c3 = 1, carry1 = 0, carry2 = 1, max trial) at n=4:
    the corrected quotient `qHat - 2 = signExtend12 4095 * 3 = 2^64 - 3`
    equals ⌊val256(a)/val256(b)⌋, and the second-addback remainder equals
    `val256(a) mod val256(b)`.

    Parallels `n4_max_addback_correct` (single-addback case); proof threads
    `hq_over_from_second_carry_one` + `mulsub_double_addback_val256_combined`
    + `val256_euclidean_to_div_mod`. -/
theorem n4_max_double_addback_correct {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hb3nz : b3 ≠ 0)
    (hc3_one : (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 1)
    (hcarry1_zero : addbackN4_carry
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
      b0 b1 b2 b3 = 0)
    (hcarry2_one :
      let ms := mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2) b0 b1 b2 b3
      (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0 b1 b2 b3).toNat = 1) :
    let ms := mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2) b0 b1 b2 b3
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0 b1 b2 b3
    let qHat'' : Word := signExtend12 (4095 : BitVec 12) +
      signExtend12 (4095 : BitVec 12) + signExtend12 (4095 : BitVec 12)
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    let q := fromLimbs fun i : Fin 4 =>
      match i with | 0 => qHat'' | 1 => (0 : Word) | 2 => (0 : Word) | 3 => (0 : Word)
    let r := fromLimbs fun i : Fin 4 =>
      match i with | 0 => ab'.1 | 1 => ab'.2.1 | 2 => ab'.2.2.1 | 3 => ab'.2.2.2.1
    q = EvmWord.div a b ∧ r = EvmWord.mod a b := by
  intro ms ab ab' qHat'' a b q r
  have hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  -- Bridge: for any uTop, addbackN4's low-4 outputs are the same. So both
  -- the algorithm's `ab` (u4_new = 0 - c3) and lemma's ab (u4_new = 0) share
  -- low-4 limbs, and the second-addback low-4 outputs also match.
  have h_ab_indep := addbackN4_fst4_u4_indep ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    ((0 : Word) - ms.2.2.2.2) 0 b0 b1 b2 b3
  obtain ⟨hab_eq1, hab_eq21, hab_eq221, hab_eq2221⟩ := h_ab_indep
  -- Abbreviate lemma's ab (with u4_new = 0): write it as `ab0` shorthand.
  -- ab0.{1, 2.1, 2.2.1, 2.2.2.1} = ab.{…} by hab_eq{1,21,221,2221}.
  -- Convert algorithm carry2 = 1 to the lemma's form via hab_eq*.
  have hcarry2_lem : (addbackN4_carry
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
      b0 b1 b2 b3).toNat = 1 := by
    have := hcarry2_one
    simp only [] at this
    rw [← hab_eq1, ← hab_eq21, ← hab_eq221, ← hab_eq2221]
    exact this
  -- Derive hq_over from carry2 = 1.
  have hq_over := hq_over_from_second_carry_one (signExtend12 4095)
    hbnz hc3_one hcarry1_zero hcarry2_lem
  -- qHat ≥ 2: trivial.
  have hq_hat_toNat : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2 ^ 64 - 1 := by decide
  have hq_ge_2 : (signExtend12 (4095 : BitVec 12) : Word).toNat ≥ 2 := by
    rw [hq_hat_toNat]; decide
  -- Apply combined Euclidean lemma: val256(a) = (q-2)*val256(b) + val256(ab'_lem).
  have hcombined := mulsub_double_addback_val256_combined
    (signExtend12 4095) hbnz hq_over hc3_one hcarry1_zero hq_ge_2
  simp only [] at hcombined
  -- Bridge from lemma's ab' to algorithm's ab': both second addbacks compute
  -- from the same low-4 ab limbs (low 4 are uTop-independent), and second
  -- addback's low-4 outputs are themselves uTop-independent. So their
  -- low-4 val256s match.
  have h_ab'_alg_indep := addbackN4_fst4_u4_indep ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
    ab.2.2.2.2 0 b0 b1 b2 b3
  obtain ⟨hab'_1, hab'_21, hab'_221, hab'_2221⟩ := h_ab'_alg_indep
  -- Low-4 of algorithm's ab' = low-4 of lemma's ab' (via hab_eq* substitution).
  have hab'_eq1 : ab'.1 = (addbackN4
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
      0 b0 b1 b2 b3).1 := by
    rw [show ab' = _ from rfl, hab'_1, hab_eq1, hab_eq21, hab_eq221, hab_eq2221]
  have hab'_eq21 : ab'.2.1 = (addbackN4
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
      0 b0 b1 b2 b3).2.1 := by
    rw [show ab' = _ from rfl, hab'_21, hab_eq1, hab_eq21, hab_eq221, hab_eq2221]
  have hab'_eq221 : ab'.2.2.1 = (addbackN4
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
      0 b0 b1 b2 b3).2.2.1 := by
    rw [show ab' = _ from rfl, hab'_221, hab_eq1, hab_eq21, hab_eq221, hab_eq2221]
  have hab'_eq2221 : ab'.2.2.2.1 = (addbackN4
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
      0 b0 b1 b2 b3).2.2.2.1 := by
    rw [show ab' = _ from rfl, hab'_2221, hab_eq1, hab_eq21, hab_eq221, hab_eq2221]
  -- Rewrite the combined equation to algorithm's ab'.
  rw [← hab'_eq1, ← hab'_eq21, ← hab'_eq221, ← hab'_eq2221] at hcombined
  -- Derive val256(ab') < val256(v) via the second-addback equation on lemma's form.
  have hab'_bound_lem : val256
      (addbackN4 (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
        0 b0 b1 b2 b3).1
      (addbackN4 (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
        0 b0 b1 b2 b3).2.1
      (addbackN4 (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
        0 b0 b1 b2 b3).2.2.1
      (addbackN4 (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
        0 b0 b1 b2 b3).2.2.2.1
      < val256 b0 b1 b2 b3 := by
    have hab'_eq := addbackN4_val256_eq
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
      0 b0 b1 b2 b3
    simp only [] at hab'_eq
    rw [hcarry2_lem] at hab'_eq
    have := val256_bound
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0 b1 b2 b3).2.2.2.1
    linarith
  -- Transport the bound to algorithm's ab'.
  have hab'_bound : val256 ab'.1 ab'.2.1 ab'.2.2.1 ab'.2.2.2.1 < val256 b0 b1 b2 b3 := by
    rw [hab'_eq1, hab'_eq21, hab'_eq221, hab'_eq2221]; exact hab'_bound_lem
  -- Rewrite the Euclidean equation in val256_euclidean_to_div_mod's expected form.
  have hq_hat''_toNat : qHat''.toNat = (signExtend12 (4095 : BitVec 12) : Word).toNat - 2 := by
    simp only [qHat'']; decide
  have hq_val : val256 qHat'' 0 0 0 = qHat''.toNat := val256_zero_upper_3
  have heuclid : val256 a0 a1 a2 a3 =
      val256 qHat'' 0 0 0 * val256 b0 b1 b2 b3 +
      val256 ab'.1 ab'.2.1 ab'.2.2.1 ab'.2.2.2.1 := by
    rw [hq_val, hq_hat''_toNat]; exact hcombined
  exact val256_euclidean_to_div_mod hbnz heuclid hab'_bound

-- ============================================================================
-- Per-limb and EvmWord-level bridges for the double-addback case
-- ============================================================================

/-- n=4 max+double-addback path: per-limb quotient/remainder equalities.
    Direct consumer-facing form of `n4_max_double_addback_correct` —
    parallels `n4_max_addback_div_mod_limbs`. The corrected quotient is
    `qHat'' = 3 * signExtend12 4095 = 2^64 - 3` in the low limb. -/
theorem n4_max_double_addback_div_mod_limbs (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hc3_one : (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 1)
    (hcarry1_zero : addbackN4_carry
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
      b0 b1 b2 b3 = 0)
    (hcarry2_one :
      let ms := mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2) b0 b1 b2 b3
      (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0 b1 b2 b3).toNat = 1) :
    let ms := mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2) b0 b1 b2 b3
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0 b1 b2 b3
    let qHat'' : Word := signExtend12 (4095 : BitVec 12) +
      signExtend12 (4095 : BitVec 12) + signExtend12 (4095 : BitVec 12)
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    (EvmWord.div a b).getLimbN 0 = qHat'' ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 ∧
    (EvmWord.mod a b).getLimbN 0 = ab'.1 ∧
    (EvmWord.mod a b).getLimbN 1 = ab'.2.1 ∧
    (EvmWord.mod a b).getLimbN 2 = ab'.2.2.1 ∧
    (EvmWord.mod a b).getLimbN 3 = ab'.2.2.2.1 := by
  intro ms ab ab' qHat'' a b
  have ⟨hq, hr⟩ := n4_max_double_addback_correct hb3nz hc3_one hcarry1_zero hcarry2_one
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hq]; exact getLimbN_fromLimbs_0
  · rw [← hq]; exact getLimbN_fromLimbs_1
  · rw [← hq]; exact getLimbN_fromLimbs_2
  · rw [← hq]; exact getLimbN_fromLimbs_3
  · rw [← hr]; exact getLimbN_fromLimbs_0
  · rw [← hr]; exact getLimbN_fromLimbs_1
  · rw [← hr]; exact getLimbN_fromLimbs_2
  · rw [← hr]; exact getLimbN_fromLimbs_3

/-- n=4 max+double-addback path, EvmWord-level statement. Consumer form for
    stack specs: takes `a b : EvmWord`, works off `getLimbN`. Parallels
    `n4_max_addback_div_mod_getLimbN`. -/
theorem n4_max_double_addback_div_mod_getLimbN (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hc3_one : (mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 1)
    (hcarry1_zero : addbackN4_carry
      (mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).1
      (mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.1
      (mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.1
      (mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.1
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = 0)
    (hcarry2_one :
      let ms := mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).toNat = 1) :
    let ms := mulsubN4 (signExtend12 4095)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    let qHat'' : Word := signExtend12 (4095 : BitVec 12) +
      signExtend12 (4095 : BitVec 12) + signExtend12 (4095 : BitVec 12)
    (EvmWord.div a b).getLimbN 0 = qHat'' ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 ∧
    (EvmWord.mod a b).getLimbN 0 = ab'.1 ∧
    (EvmWord.mod a b).getLimbN 1 = ab'.2.1 ∧
    (EvmWord.mod a b).getLimbN 2 = ab'.2.2.1 ∧
    (EvmWord.mod a b).getLimbN 3 = ab'.2.2.2.1 := by
  have hraw := n4_max_double_addback_div_mod_limbs
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hc3_one hcarry1_zero hcarry2_one
  rw [fromLimbs_match_getLimbN_id_local a, fromLimbs_match_getLimbN_id_local b] at hraw
  exact hraw

end EvmAsm.Evm64
