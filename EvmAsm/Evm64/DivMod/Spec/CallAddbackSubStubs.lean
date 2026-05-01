-- file-size-exception NOT required: this sibling file lives below cap.
/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackSubStubs

  Trailing leaf cluster extracted from Spec/CallAddback.lean (lines 2643-3312
  pre-split) to bring CallAddback.lean toward the 1500-line cap (issue #1078,
  parent slice evm-asm-ry8, sub-slice evm-asm-hhow). No proof changes.

  Contents:
  - Sub-stubs:
      * qHat_eq_div_plus_one_of_single_addback
      * qHat_eq_div_plus_two_of_double_addback
      * algCallAddbackBeq_addback_combined_euclidean_carry2
      * algCallAddbackBeq_mulsub_euclidean
      * algCallAddbackBeq_amod_pow_s_lt_pow256
      * algCallAddbackBeq_mulsub_euclidean_double

  These are leaf theorems: no other declaration in CallAddback.lean
  references them, so a single-file extraction is import-cycle-free.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddback

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)
open EvmAsm.Rv64.Tactics

/-- **Sub-stub (single-addback): qHat.toNat = a/b + 1.** Under
    `n4CallAddbackBeqSemanticHolds` and the single-addback condition (i.e.
    first-addback carry ≠ 0, equivalent to `q_out = qHat - 1`), the trial
    quotient overestimates by exactly 1. Direct corollary of hsem (which
    pins q_out.toNat = a/b) plus q_out = qHat - 1 in this branch.

    Once filled, this sub-lemma + `mulsubN4_c3_le_one` give c3 ≤ 1 in the
    single-addback branch, which is the missing piece for the addback-BEQ
    MOD adapter's single-addback closure. -/
theorem qHat_eq_div_plus_one_of_single_addback (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
                 let antiShift :=
                   (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
                 let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
                 let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
                 let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
                 let b0' := (b.getLimbN 0) <<< shift
                 let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
                 let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
                 let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
                 let u0 := (a.getLimbN 0) <<< shift
                 let u4 := (a.getLimbN 3) >>> antiShift
                 let qHat := div128Quot u4 u3 b3'
                 let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
                 addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    (div128Quot u4 u3 b3').toNat = a.toNat / b.toNat + 1 := by
  intro shift antiShift b3' u3 u4
  rw [n4CallAddbackBeqSemanticHolds_def] at hsem
  -- Unfold the if in hsem using hcarry_nz.
  simp only [if_neg hcarry_nz] at hsem
  -- val256(a_limbs) = a.toNat, val256(b_limbs) = b.toNat.
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_val, hb_val] at hsem
  -- hsem : (qHat + signExtend12 4095).toNat = a.toNat / b.toNat
  -- Rewrite the LHS via BitVec.toNat_add + signExtend12_4095_toNat.
  rw [BitVec.toNat_add, signExtend12_4095_toNat] at hsem
  -- hsem : (qHat.toNat + (2^64 - 1)) % 2^64 = a.toNat / b.toNat
  set qHat := div128Quot u4 u3 b3' with hqHat_def
  have h_div_lt : a.toNat / b.toNat < 2^64 := by
    have := a.isLt; have := b.isLt
    -- Dividing by anything ≥ 1 keeps result < 2^256. But we need < 2^64.
    -- Use that hsem already pins (qHat + (-1)).toNat (which is < 2^64) = a/b.
    -- Since LHS < 2^64 (it's a Word toNat after addition), a/b < 2^64.
    have h_lhs_lt : ((qHat.toNat + (2^64 - 1)) % 2^64) < 2^64 := Nat.mod_lt _ (by decide)
    omega
  have hqHat_pos : qHat.toNat ≥ 1 := by
    -- From hborrow: c3 ≠ 0 (specifically u4 < c3 ≥ 1).
    -- Contrapositive of `c3_un_zero_of_qHat_mul_le`: c3 ≠ 0 → qHat * b > a.
    -- If qHat = 0, then 0 * b = 0 ≤ a, contradicting qHat * b > a.
    by_contra hqHat_zero
    push Not at hqHat_zero
    -- hqHat_zero : qHat.toNat < 1, i.e., qHat.toNat = 0.
    have hqHat_eq_zero : qHat.toNat = 0 := by omega
    -- Then qHat * b = 0 ≤ a, so c3 = 0 by `c3_un_zero_of_qHat_mul_le`.
    have h_mul_le : qHat.toNat *
        val256 ((b.getLimbN 0) <<< shift)
              (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> (64 - shift)))
              (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> (64 - shift)))
              (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> (64 - shift)))
        ≤ val256 ((a.getLimbN 0) <<< shift)
              (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> (64 - shift)))
              (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> (64 - shift)))
              (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> (64 - shift))) := by
      rw [hqHat_eq_zero, Nat.zero_mul]; exact Nat.zero_le _
    have h_c3_zero := c3_un_zero_of_qHat_mul_le h_mul_le
    -- But hborrow gives u4 < c3, hence c3 ≥ 1 ≠ 0.
    rw [isAddbackBorrowN4CallEvm_def] at hborrow
    have h_u4_lt_c3 := EvmWord.u_top_lt_c3_of_addback_borrow_call
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        hborrow
    -- shift in `_call` form uses the un-modded clzResult; reconcile via rfl/match.
    -- The c3 in h_c3_zero matches the c3 in h_u4_lt_c3 (same shift mod 64).
    simp only [] at h_u4_lt_c3
    -- Goal: False. From h_c3_zero (c3 = 0) and h_u4_lt_c3 (u4 < c3.toNat),
    -- we have u4 < 0, contradiction.
    have h_c3_toNat_zero : (mulsubN4 qHat
        ((b.getLimbN 0) <<< shift)
        (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> (64 - shift)))
        (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> (64 - shift)))
        (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> (64 - shift)))
        ((a.getLimbN 0) <<< shift)
        (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> (64 - shift)))
        (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> (64 - shift)))
        (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> (64 - shift)))).2.2.2.2.toNat = 0 := by
      rw [h_c3_zero]; rfl
    -- Bridge: convert h_u4_lt_c3's Word form to match h_c3_toNat_zero's Nat form.
    -- Use `antiShift_toNat_mod_eq` to rewrite `(signExtend12 0 - clz).toNat % 64`
    -- to `64 - clz.toNat`. Then `(64 - clz.toNat) = (64 - shift)` via
    -- `shift = clz.toNat % 64 = clz.toNat` when clz.toNat ≤ 63.
    have h_clz_le : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
      clzResult_fst_toNat_le _
    have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
      rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
      · exfalso; apply hshift_nz
        exact BitVec.eq_of_toNat_eq (by simp [h0])
      · exact h0
    have h_anti_eq : (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
        = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
      antiShift_toNat_mod_eq h_clz_pos h_clz_le
    have h_shift_eq : shift = (clzResult (b.getLimbN 3)).1.toNat := by
      show (clzResult (b.getLimbN 3)).1.toNat % 64 = (clzResult (b.getLimbN 3)).1.toNat
      omega
    -- Now h_u4_lt_c3 has antiShift in Word form, but h_anti_eq + h_shift_eq give
    -- it equals our local `64 - shift`. After rewriting, the mulsubN4 invocations
    -- in h_u4_lt_c3 and h_c3_toNat_zero have identical arguments, contradiction.
    rw [h_anti_eq] at h_u4_lt_c3
    rw [show (clzResult (b.getLimbN 3)).1.toNat % 64 = (clzResult (b.getLimbN 3)).1.toNat
        from by omega] at h_u4_lt_c3
    -- Unfold qHat/u4/u3/b3'/shift/antiShift in h_c3_toNat_zero to match h_u4_lt_c3's
    -- fully-inlined form, then omega closes via c3 = 0 ∧ u4.toNat < c3.toNat.
    have h_anti_unfold : antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat := h_anti_eq
    rw [hqHat_def,
        show u4 = a.getLimbN 3 >>> antiShift from rfl,
        show u3 = a.getLimbN 3 <<< shift ||| a.getLimbN 2 >>> antiShift from rfl,
        show b3' = b.getLimbN 3 <<< shift ||| b.getLimbN 2 >>> antiShift from rfl,
        h_shift_eq, h_anti_unfold] at h_c3_toNat_zero
    omega
  -- (qHat.toNat + 2^64 - 1) % 2^64 = qHat.toNat - 1 when qHat ≥ 1.
  have h_qHat_lt : qHat.toNat < 2^64 := qHat.isLt
  have : (qHat.toNat + (2^64 - 1)) % 2^64 = qHat.toNat - 1 := by
    rw [show qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 from by omega]
    rw [Nat.add_mod_right]
    apply Nat.mod_eq_of_lt; omega
  rw [this] at hsem
  -- hsem : qHat.toNat - 1 = a.toNat / b.toNat
  omega

/-- **B.1 (#1338, NOT Knuth-B blocked):** qHat.toNat = a/b + 2
    in double-addback case.

    Mirror of `qHat_eq_div_plus_one_of_single_addback` for the
    double-addback branch (`algCallAddbackBeqCarry a b = 0`).

    **REFINED ANALYSIS (2026-04-26):** This lemma does NOT actually need
    Knuth-B (#1337). The lower bound qHat ≥ a/b + 2 is **derivable
    directly** from hborrow + hcarry_zero via mulsub algebra:

    1. From hborrow: u4 < c3 (so c3 - u4 ≥ 1).
    2. From mulsub Euclidean (instantiated):
       val256(ms) + qHat * b * 2^s = a * 2^s + (c3 - u4) * 2^256.
    3. carry₁ = 0 means val256(ms) + b * 2^s < 2^256 (no overflow in
       first addback). Substituting (2):
       a * 2^s + (c3 - u4) * 2^256 - (qHat - 1) * b * 2^s < 2^256.
    4. With c3 - u4 ≥ 1: (qHat - 1) * b * 2^s > a * 2^s, hence
       (qHat - 1) * b > a, hence qHat - 1 > a/b, hence qHat ≥ a/b + 2.

    **Proof structure**: composes B.1a (qHat ≥ 2, CLOSED above) with
    Word arithmetic on hsem (this proof, ~50 LOC, fully closed).

    Issue #1338 Phase B.1. -/
theorem qHat_eq_div_plus_two_of_double_addback (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    (div128Quot u4 u3 b3').toNat = a.toNat / b.toNat + 2 := by
  intro shift antiShift b3' u3 u4
  -- B.1a (algorithm-side): qHat ≥ 2.
  have hqHat_ge_two : (div128Quot u4 u3 b3').toNat ≥ 2 :=
    qHat_ge_two_of_double_addback a b hshift_nz hborrow hcarry2_nz hcarry_zero
  -- Bridge hcarry_zero to the parent's let-chain form via algCallAddbackBeqCarry_unfold.
  rw [algCallAddbackBeqCarry_unfold] at hcarry_zero
  -- Unfold hsem with the carry-equals-0 case.
  rw [n4CallAddbackBeqSemanticHolds_def] at hsem
  simp only [if_pos hcarry_zero] at hsem
  -- val256(a_limbs) = a.toNat, val256(b_limbs) = b.toNat.
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  rw [ha_val, hb_val] at hsem
  -- hsem: (qHat + signExtend12 4095 + signExtend12 4095).toNat = a/b.
  set qHat := div128Quot u4 u3 b3' with hqHat_def
  rw [BitVec.toNat_add, BitVec.toNat_add, signExtend12_4095_toNat] at hsem
  have h_inner_eq : (qHat.toNat + (2^64 - 1)) % 2^64 = qHat.toNat - 1 := by
    have h_qHat_lt : qHat.toNat < 2^64 := qHat.isLt
    rw [show qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 from by omega]
    rw [Nat.add_mod_right]
    apply Nat.mod_eq_of_lt; omega
  rw [h_inner_eq] at hsem
  have h_outer_eq : ((qHat.toNat - 1) + (2^64 - 1)) % 2^64 = qHat.toNat - 2 := by
    rw [show (qHat.toNat - 1) + (2^64 - 1) = (qHat.toNat - 2) + 2^64 from by omega]
    rw [Nat.add_mod_right]
    apply Nat.mod_eq_of_lt
    have := qHat.isLt; omega
  rw [h_outer_eq] at hsem
  omega

/-- **B.5 building block STUB: combined two-addback Euclidean** (#1338).

    Mirror of `algCallAddbackBeq_addback_euclidean_carry_one` for the
    **double-addback** path. Combines:
    - First addback (carry₁ = 0): val256(ab) = val256(ms) + val256(b_norm).
    - Second addback (carry₂ = 1, from `isAddbackCarry2NzN4CallEvm`):
      val256(ab') + 2^256 = val256(ab) + val256(b_norm).

    Combined: `AbPrimeVal + 2^256 = MsLowVal + 2 · (val256(b_limbs) · 2^s)`.

    **Proof sketch** (~120 LOC, mirrors single-addback's structure):
    - Setup clz bounds.
    - Unfold AbPrimeVal and MsLowVal.
    - Apply `addbackN4_val256_eq` to first addback; use `addbackN4_top_eq`
      to get the 5th-limb input for second addback.
    - Apply `addbackN4_val256_eq` to second addback (low4 of first addback's
      output + b_norm).
    - Use carry₁ = 0 (hcarry_zero) and carry₂ = 1 (from hcarry2_nz +
      `addbackN4_carry_le_one`).
    - Combine: val256(ab') + 2^256 = val256(ms) + 2 · val256(b_norm).
    - Apply `val256_normalize` for b_norm.

    Independent of Knuth-B (#1337). The complexity is mostly notational
    (let-chains aligning across two addback applications). -/
theorem algCallAddbackBeq_addback_combined_euclidean_carry2
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqAbPrimeVal a b + 2 ^ 256 =
      algCallAddbackBeqMsLowVal a b +
        2 * (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) := by
  -- Setup clz bounds.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz; exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- Unfold both irreducibles.
  rw [algCallAddbackBeqAbPrimeVal_unfold, algCallAddbackBeqMsLowVal_unfold]
  simp only []
  -- Define local let-chain.
  set shift := (clzResult (b.getLimbN 3)).1.toNat % 64 with hshift_def
  set antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 with hanti_def
  set b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set u4 := (a.getLimbN 3) >>> antiShift
  set qHat := div128Quot u4 u3 b3'
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  set c3 := ms.2.2.2.2
  set u4_new := u4 - c3
  set ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3' with hab_eq
  set abPrime := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3'
                  with habPrime_eq
  -- First addback Euclidean.
  have h_ab_eq := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3'
  simp only [] at h_ab_eq
  -- carry₁ = 0 from hcarry_zero.
  rw [algCallAddbackBeqCarry_unfold] at hcarry_zero
  simp only [] at hcarry_zero
  have h_carry1_zero :
      (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 0 := by
    rw [hcarry_zero]; rfl
  rw [h_carry1_zero] at h_ab_eq
  -- Second addback Euclidean.
  have h_abPrime_eq := addbackN4_val256_eq ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2
                                            b0' b1' b2' b3'
  simp only [] at h_abPrime_eq
  -- carry₂ = 1 from hcarry2_nz applied to carry₁ = 0.
  rw [isAddbackCarry2NzN4CallEvm_def] at hcarry2_nz
  unfold isAddbackCarry2NzN4CallAb isAddbackCarry2NzN4Call isAddbackCarry2Nz at hcarry2_nz
  simp only [] at hcarry2_nz
  have h_carry2_nz_local := hcarry2_nz hcarry_zero
  have h_carry2_le := addbackN4_carry_le_one ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0' b1' b2' b3'
  have h_carry2_one :
      (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0' b1' b2' b3').toNat = 1 := by
    have h_pos : (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
                                    b0' b1' b2' b3').toNat ≠ 0 := by
      intro h_zero
      apply h_carry2_nz_local
      apply BitVec.eq_of_toNat_eq
      rw [h_zero]; rfl
    omega
  rw [h_carry2_one] at h_abPrime_eq
  -- val256(b_norm) = val256(b_limbs) * 2^shift.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- Bridge the goal's inline addbackN4 forms via rfl (mirror of mulsub Euclidean).
  have h_ab_low : val256
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3').1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3').2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3').2.2.1
      (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0' b1' b2' b3').2.2.2.1
      = val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 := rfl
  have h_abPrime_low : val256
      (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').1
      (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.1
      (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.1
      (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0' b1' b2' b3').2.2.2.1
      = val256 abPrime.1 abPrime.2.1 abPrime.2.2.1 abPrime.2.2.2.1 := rfl
  rw [h_ab_low] at h_ab_eq
  rw [h_abPrime_low] at h_abPrime_eq
  rw [h_norm_b] at h_ab_eq h_abPrime_eq
  -- Goal uses val256(b.getLimbN 0)... * 2^shift directly; hypotheses now match.
  omega

/-- **Mulsub Euclidean for the call+addback BEQ algorithm** (CLOSED).

    The val256-level mulsub Euclidean identity at normalized inputs,
    composed with `qHat = a/b + 1` (single-addback) and the normalization
    identities for `u_norm` and `b_norm`. In the irreducible-bundle form:

      (algCallAddbackBeqMsC3 a b).toNat * 2^256 +
        (val256(a_limbs) * 2^s - (algCallAddbackBeqU4 a b).toNat * 2^256) =
      algCallAddbackBeqMsLowVal a b +
        (val256(a_limbs) / val256(b_limbs) + 1) * (val256(b_limbs) * 2^s)

    Useful as the `h_mulsub` precondition of
    `post1_val_eq_amod_pow_s_pure_nat` when closing the wrapper. -/
theorem algCallAddbackBeq_mulsub_euclidean
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    (algCallAddbackBeqMsC3 a b).toNat * 2 ^ 256 +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) -
        (algCallAddbackBeqU4 a b).toNat * 2 ^ 256) =
    algCallAddbackBeqMsLowVal a b +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 1) *
      (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) := by
  -- Setup: clz bounds.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- Bridge val256(a_limbs) = a.toNat and similar for b.
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  -- qHat = a/b + 1 from the closed sub-stub.
  rw [algCallAddbackBeqCarry_unfold] at hcarry_nz
  have h_qHat_eq : (div128Quot ((a.getLimbN 3) >>>
      ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
      (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
        ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64)))
      (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
        ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64)))).toNat =
      a.toNat / b.toNat + 1 :=
    qHat_eq_div_plus_one_of_single_addback a b hshift_nz hborrow hsem hcarry_nz
  -- Unfold the irreducibles.
  rw [show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl,
      show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl,
      algCallAddbackBeqMsLowVal_unfold]
  simp only []
  -- Set up the let-chain.
  set shift := (clzResult (b.getLimbN 3)).1.toNat % 64 with hshift_def
  set antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 with hanti_def
  set b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift) with hb3_eq
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift) with hu3_eq
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set u4 := (a.getLimbN 3) >>> antiShift with hu4_eq
  set qHat := div128Quot u4 u3 b3' with hqHat_eq
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Mulsub Euclidean at val256 level.
  have h_mulsub_eq := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub_eq
  -- val256(b_norm) = val256(b) * 2^s.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- val256(u_norm low4) + u4 * 2^256 = val256(a) * 2^s.
  have h_norm_u : val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ shift := by
    show val256 ((a.getLimbN 0) <<< shift)
                (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift))
                (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift))
                (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)) +
            ((a.getLimbN 3) >>> antiShift).toNat * 2 ^ 256 = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize_general h_clz_pos h_clz_lt_64
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  -- Express h_qHat_eq in terms of the let-chain qHat.
  have h_qHat : qHat.toNat = a.toNat / b.toNat + 1 := h_qHat_eq
  -- Combine. Substitute into h_mulsub_eq using h_norm_b, h_qHat, h_norm_u.
  rw [h_norm_b] at h_mulsub_eq
  rw [h_qHat] at h_mulsub_eq
  rw [ha_val, hb_val]
  have h_u_eq : val256 u0 u1 u2 u3 = a.toNat * 2 ^ shift - u4.toNat * 2 ^ 256 := by
    have h := h_norm_u; rw [ha_val] at h; omega
  rw [h_u_eq] at h_mulsub_eq
  rw [hb_val] at h_mulsub_eq
  -- Bridge the goal's inline `mulsubN4 ...` forms to `ms.{...}` via rfl.
  have h_ms_top : (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
      = ms.2.2.2.2.toNat := rfl
  have h_ms_low : val256
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.1
      = val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := rfl
  rw [h_ms_top, h_ms_low]
  omega

/-- **Bound: `a%b * 2^s < 2^256` in the call+addback BEQ shape** (CLOSED).

    Wraps `EvmWord.val256_mod_mul_pow_lt_pow256_of_b3_bound` taking
    `b3 ≠ 0` (rather than `b ≠ 0`) and giving the `% 64`-shifted exponent
    form used by the algorithm scaffold. Useful as the `h_amod_pow_lt`
    precondition of `post1_val_eq_amod_pow_s_pure_nat` when closing
    `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback`. -/
theorem algCallAddbackBeq_amod_pow_s_lt_pow256
    (a b : EvmWord) (hb3nz : b.getLimbN 3 ≠ 0) :
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) < 2 ^ 256 := by
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hvb_pos : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    EvmWord.val256_pos_of_or_ne_zero hbnz
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  rw [h_s_eq]
  exact EvmWord.val256_mod_mul_pow_lt_pow256_of_b3_bound
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (by omega) hvb_pos hb3_bound

/-- **B.5 building block STUB: mulsub Euclidean for double-addback** (#1338).

    Mirror of `algCallAddbackBeq_mulsub_euclidean` for the double-addback path.
    The val256-level mulsub identity at normalized inputs, with the qHat factor
    being `val256(a)/val256(b) + 2` (per B.1 `qHat_eq_div_plus_two_of_double_addback`):

      c3_n · 2^256 + (val256(a)·2^s − u4·2^256) =
        algCallAddbackBeqMsLowVal a b + (val256(a)/val256(b) + 2) · (val256(b)·2^s)

    **Proof sketch** (~155 LOC, mirrors single-addback's structure):
    - Setup clz bounds (same as single-addback).
    - Bridge val256(a_limbs) = a.toNat, val256(b_limbs) = b.toNat.
    - Apply `mulsubN4_val256_eq` for the val256-level identity.
    - Substitute qHat via B.1 (`qHat_eq_div_plus_two_of_double_addback`).
    - val256_normalize for u_norm and b_norm.

    **Dependencies**: B.1 (CLOSED, `qHat_eq_div_plus_two_of_double_addback`).
    Mirror of single-addback's `algCallAddbackBeq_mulsub_euclidean`.
    Issue #1338 Phase B.5. -/
theorem algCallAddbackBeq_mulsub_euclidean_double
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    (algCallAddbackBeqMsC3 a b).toNat * 2 ^ 256 +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) -
        (algCallAddbackBeqU4 a b).toNat * 2 ^ 256) =
    algCallAddbackBeqMsLowVal a b +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2) *
      (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) := by
  -- Setup: clz bounds.
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by omega
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  -- Bridge val256(a_limbs) = a.toNat and similar for b.
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  -- qHat = a/b + 2 from B.1 (closed mod B.1a).
  have h_qHat_eq : (div128Quot ((a.getLimbN 3) >>>
      ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
      (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
        ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64)))
      (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
        ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult (b.getLimbN 3)).1).toNat % 64)))).toNat =
      a.toNat / b.toNat + 2 :=
    qHat_eq_div_plus_two_of_double_addback a b hshift_nz hborrow hcarry2_nz
      hsem hcarry_zero
  -- Unfold the irreducibles.
  rw [show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl,
      show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl,
      algCallAddbackBeqMsLowVal_unfold]
  simp only []
  -- Set up the let-chain.
  set shift := (clzResult (b.getLimbN 3)).1.toNat % 64 with hshift_def
  set antiShift :=
    (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 with hanti_def
  set b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift) with hb3_eq
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift) with hu3_eq
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set u4 := (a.getLimbN 3) >>> antiShift with hu4_eq
  set qHat := div128Quot u4 u3 b3' with hqHat_eq
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Mulsub Euclidean at val256 level.
  have h_mulsub_eq := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub_eq
  -- val256(b_norm) = val256(b) * 2^s.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ shift := by
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- val256(u_norm low4) + u4 * 2^256 = val256(a) * 2^s.
  have h_norm_u : val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ shift := by
    show val256 ((a.getLimbN 0) <<< shift)
                (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift))
                (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift))
                (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)) +
            ((a.getLimbN 3) >>> antiShift).toNat * 2 ^ 256 = _
    rw [show shift = (clzResult (b.getLimbN 3)).1.toNat from h_s_eq,
        show antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat from h_anti_eq]
    exact EvmWord.val256_normalize_general h_clz_pos h_clz_lt_64
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  -- Express h_qHat_eq in terms of the let-chain qHat.
  have h_qHat : qHat.toNat = a.toNat / b.toNat + 2 := h_qHat_eq
  -- Combine. Substitute into h_mulsub_eq using h_norm_b, h_qHat, h_norm_u.
  rw [h_norm_b] at h_mulsub_eq
  rw [h_qHat] at h_mulsub_eq
  rw [ha_val, hb_val]
  have h_u_eq : val256 u0 u1 u2 u3 = a.toNat * 2 ^ shift - u4.toNat * 2 ^ 256 := by
    have h := h_norm_u; rw [ha_val] at h; omega
  rw [h_u_eq] at h_mulsub_eq
  rw [hb_val] at h_mulsub_eq
  -- Bridge the goal's inline `mulsubN4 ...` forms to `ms.{...}` via rfl.
  have h_ms_top : (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
      = ms.2.2.2.2.toNat := rfl
  have h_ms_low : val256
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.1
      (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.1
      = val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := rfl
  rw [h_ms_top, h_ms_low]
  omega

end EvmAsm.Evm64
