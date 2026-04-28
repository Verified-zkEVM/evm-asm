/-
  EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgEuclideans

  Word-level Euclidean identities and qHat lower-bound theorems for the
  call+addback BEQ algorithm. Self-contained block — uses only AlgDefs
  primitives, no parent-only `n4CallAddbackBeqSemanticHolds` predicates.

  Contents:
  - `algCallAddbackBeq_addback_euclidean_carry_one` — single-addback
    val256 identity.
  - `algCallAddbackBeq_addback_euclidean_carry_zero_v2` — double-addback
    val256 identity (carry₁ = 0 form).
  - `algCallAddbackBeqMsLowVal_plus_b_norm_lt_pow256` — bound on
    addback's RHS sum.
  - `algCallAddbackBeq_mulsub_eucl_irreducible_form` — mulsub step's
    val256 identity wrapped via the @[irreducible] bundles.
  - `algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat` —
    `u4 < c3` from the runtime borrow precondition.
  - `qHat_ge_two_abstract` and `qHat_ge_two_of_double_addback` —
    qHat ≥ 2 in the double-addback regime (CLOSED, not Knuth-B blocked).

  Theorems that DEPEND on the parent's `n4CallAddbackBeqSemanticHolds`
  predicate (such as `qHat_eq_div_plus_two_of_double_addback`,
  `algCallAddbackBeq_addback_combined_euclidean_carry2`,
  `algCallAddbackBeq_mulsub_euclidean*`) remain in
  `SpecCallAddbackBeq.lean`.

  Extracted from `SpecCallAddbackBeq.lean` (2026-04-28) to ease the
  file-size guardrail. Issue #1338 / #61.
-/

import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.AlgDefs

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- **Addback Euclidean (carry = 1) for the call+addback BEQ algorithm** (CLOSED).

    In the single-addback branch (`algCallAddbackBeqCarry a b ≠ 0`),
    the val256 of the post1 limbs satisfies:

      `algCallAddbackBeqPost1Val a b + 2^256 =
         algCallAddbackBeqMsLowVal a b + val256(b_limbs) * 2^s`

    where s = clz % 64. Combines `addbackN4_val256_eq` (carry-form) with
    `addbackN4_carry_le_one` to pin carry.toNat = 1, plus `val256_normalize`
    to fold the normalized b into `val256(b) * 2^s`.

    Useful as the `h_addback` precondition of
    `post1_val_eq_amod_pow_s_pure_nat` when closing the wrapper. -/
theorem algCallAddbackBeq_addback_euclidean_carry_one
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqPost1Val a b + 2 ^ 256 =
      algCallAddbackBeqMsLowVal a b +
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
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
  -- Unfold both irreducibles.
  rw [algCallAddbackBeqPost1Val_unfold, algCallAddbackBeqMsLowVal_unfold]
  simp only []
  -- Define ms in let-chain form.
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
  -- Addback Euclidean at val256 level.
  have h_addback_eq := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  simp only [] at h_addback_eq
  -- carry.toNat = 1: from hcarry_nz (≠ 0) + addbackN4_carry_le_one (≤ 1).
  have h_carry_le := addbackN4_carry_le_one ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  rw [algCallAddbackBeqCarry_unfold] at hcarry_nz
  simp only [] at hcarry_nz
  have h_carry_eq_one :
      (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 1 := by
    have h_pos : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat ≠ 0 := by
      intro h_zero
      apply hcarry_nz
      apply BitVec.eq_of_toNat_eq
      rw [h_zero]; rfl
    omega
  rw [h_carry_eq_one] at h_addback_eq
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
  -- Combine.
  rw [h_norm_b] at h_addback_eq
  omega

/-- **Variant attempt**: prove carry_zero Euclidean WITHOUT the `simp
    [Nat.zero_mul, Nat.add_zero]` pre-pass. Maybe leaving `0 * 2^256`
    in the equation lets omega's certificate match the carry_one
    pattern (which has a `+ 1 * 2^256` term). -/
theorem algCallAddbackBeq_addback_euclidean_carry_zero_v2
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqPost1Val a b + 0 * 2 ^ 256 =
      algCallAddbackBeqMsLowVal a b +
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
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
  rw [algCallAddbackBeqPost1Val_unfold, algCallAddbackBeqMsLowVal_unfold]
  simp only []
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
  have h_addback_eq := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  simp only [] at h_addback_eq
  rw [algCallAddbackBeqCarry_unfold] at hcarry_zero
  simp only [] at hcarry_zero
  have h_carry_eq_zero :
      (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 0 := by
    rw [hcarry_zero]; rfl
  rw [h_carry_eq_zero] at h_addback_eq
  -- DELIBERATELY skip `simp [Nat.zero_mul, Nat.add_zero]`. Goal LHS now has
  -- `+ 0 * 2^256` to match the carry_one pattern's `+ 1 * 2^256`.
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
  rw [h_norm_b] at h_addback_eq
  omega

/-- **MsLowVal + val256(b_norm) * 2^s no-overflow** (CLOSED, derived via v2).

    `algCallAddbackBeqMsLowVal a b + val256(b_limbs) * 2^s < 2^256`

    when `algCallAddbackBeqCarry a b = 0` (double-addback's first
    addback has no overflow). This is the `h_no_overflow` precondition
    of `qHat_ge_two_abstract` for B.1a's call-addback-side closure.

    Derives via:
    - `algCallAddbackBeq_addback_euclidean_carry_zero_v2`: Post1Val + 0*2^256
      = MsLowVal + val256(b_limbs) * 2^s.
    - `algCallAddbackBeqPost1Val_lt_pow256`: Post1Val < 2^256.
    - `linarith` to combine (avoiding `omega`'s deterministic-timeout
      issue when chained through `algCallAddbackBeq_addback_euclidean_carry_zero_v2`). -/
theorem algCallAddbackBeqMsLowVal_plus_b_norm_lt_pow256
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqMsLowVal a b +
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) < 2 ^ 256 := by
  have h_eq := algCallAddbackBeq_addback_euclidean_carry_zero_v2 a b hshift_nz hcarry_zero
  have h_lt := algCallAddbackBeqPost1Val_lt_pow256 a b
  linarith

/-- **Mulsub Euclidean — raw form (no qHat substitution)** (CLOSED).

    The val256-level mulsub identity at the algorithm's normalized inputs,
    expressed directly in terms of the irreducibles `algCallAddbackBeqMsC3`
    and `algCallAddbackBeqMsLowVal` AND the algorithm's actual qHat
    (no substitution with `a/b + 1` or `a/b + 2`):

      `(MsC3 a b).toNat * 2^256 + val256(a) * 2^s
         = MsLowVal a b + qHat.toNat * (val256(b) * 2^s)
                        + (algCallAddbackBeqU4 a b).toNat * 2^256`

    Notation: `qHat := div128Quot u4 u3 b3'` (the algorithm's actual
    qHat in the let-chain).

    This is the **`h_mulsub` precondition for `qHat_ge_two_abstract`**
    in B.1a. Independent of B.1 (no qHat = a/b + 2 substitution),
    so usable in B.1a's proof. -/
theorem algCallAddbackBeq_mulsub_eucl_irreducible_form
    (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let qHat := div128Quot u4 u3 b3'
    (algCallAddbackBeqMsC3 a b).toNat * 2 ^ 256 +
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) =
    algCallAddbackBeqMsLowVal a b +
      qHat.toNat *
        (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) +
      (algCallAddbackBeqU4 a b).toNat * 2 ^ 256 := by
  intro shift antiShift b3' u3 u4 qHat
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
  rw [show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl,
      show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl,
      algCallAddbackBeqMsLowVal_unfold]
  simp only []
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Mulsub Euclidean.
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
  rw [h_norm_b] at h_mulsub_eq
  linarith

/-- **Bound: `algCallAddbackBeqU4 < algCallAddbackBeqMsC3`** (CLOSED).

    Wraps `EvmWord.u_top_lt_c3_of_addback_borrow_call` in the irreducible-
    bundle form, taking just `hborrow : isAddbackBorrowN4CallEvm a b`.
    Useful as the `h_u4_lt_c3` precondition of
    `post1_val_eq_amod_pow_s_pure_nat` when closing the wrapper. -/
theorem algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat
    (a b : EvmWord) (hborrow : isAddbackBorrowN4CallEvm a b) :
    (algCallAddbackBeqU4 a b).toNat < (algCallAddbackBeqMsC3 a b).toNat := by
  rw [show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl,
      show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl]
  rw [isAddbackBorrowN4CallEvm_def] at hborrow
  exact EvmWord.u_top_lt_c3_of_addback_borrow_call
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hborrow

/-- **Abstract Nat-level sub-lemma for B.1a**: under mulsub Euclidean +
    first-addback no-overflow + c3 ≥ 1, `qHat ≥ 2`.

    Pure Nat algebra. Used to factor B.1a's proof, avoiding the kernel
    deep-recursion that arises when `rfl`-bridging through deeply-nested
    `mulsubN4` let-chains.

    Hypotheses encode:
    - h_mulsub: `c3 · 2^256 + u_norm = ms + qHat · b_norm` (mulsubN4_val256_eq).
    - h_no_overflow: `ms + b_norm < 2^256` (first-addback Euclidean with carry₁ = 0
      directly gives this — `val256(ab) = ms + b_norm` and `val256(ab) < 2^256`).
    - h_c3_pos: `c3 ≥ 1` (from hborrow's u4 < c3).

    **Key simplification** (vs. earlier 6-arg version): folding the addback
    Euclidean + val256 bound into a single `h_no_overflow` parameter eliminates
    the explicit `ab` parameter, so callers don't need to supply the deep
    `addbackN4 (mulsubN4 ...) ...` expression — sidesteps the kernel
    deep-recursion at instantiation.

    Issue #1338 Phase B.1a. -/
theorem qHat_ge_two_abstract
    (qHat ms u_norm b_norm c3 : Nat)
    (h_mulsub : c3 * 2^256 + u_norm = ms + qHat * b_norm)
    (h_no_overflow : ms + b_norm < 2^256)
    (h_c3_pos : c3 ≥ 1) :
    qHat ≥ 2 := by
  by_contra h_lt
  push Not at h_lt
  have h_case : qHat = 0 ∨ qHat = 1 := by omega
  rcases h_case with h_qHat_zero | h_qHat_one
  · rw [h_qHat_zero] at h_mulsub
    simp only [Nat.zero_mul, Nat.add_zero] at h_mulsub
    omega
  · rw [h_qHat_one] at h_mulsub
    simp only [Nat.one_mul] at h_mulsub
    omega

/-- **B.1a (sub-lemma, sorry — pending bridges):** `qHat ≥ 2` under
    double-addback hypotheses.

    Moved here (from before line 2244) to use the
    `algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat` wrapper
    directly instead of the inline `EvmWord.u_top_lt_c3_of_addback_borrow_call`
    + antiShift dance. Eliminates the previous forward-reference issue.

    **Proof outline** (still pending closure due to set/rfl bridges):
    - by_contra h_lt: qHat.toNat < 2.
    - From hborrow + wrapper: u4 < c3 (Word level via irreducibles).
    - interval_cases qHat.toNat:
      - qHat = 0: c3_un_zero_of_qHat_mul_le gives c3 = 0. Contradiction
        with c3 > u4 ≥ 0.
      - qHat = 1: mulsub gives val256(u_norm) + c3*2^256 = val256(ms) +
        val256(b_norm). hcarry_zero with first-addback Euclidean gives
        val256(ms) + val256(b_norm) < 2^256. Combined with c3 ≥ 1:
        val256(u_norm) + 2^256 < 2^256 = contradiction.

    **Pending technicalities** for next iteration:
    - Bridge `(algCallAddbackBeqU4 a b).toNat = u4.toNat` via the
      irreducible's unfold (1-line `show`/`rfl`).
    - Handle `interval_cases qHat.toNat` substitution (use case
      hypothesis directly instead of `rfl`).
    - `set ms := ...` to align `c3_un_zero_of_qHat_mul_le`'s output.

    Estimated remaining: ~80 LOC. Issue #1338 Phase B.1a. -/
theorem qHat_ge_two_of_double_addback (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (_hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    (div128Quot u4 u3 b3').toNat ≥ 2 := by
  -- **4th attempt with `algCallAddbackBeqMsLowVal` / `algCallAddbackBeqMsC3`
  -- irreducibles still hits kernel deep-recursion (101 sec build)**.
  -- Per pirapira PR review (#1339 line 3543): "Use irreducible definitions".
  --
  -- The existing irreducibles work as opaque Nats at the abstract-lemma
  -- application level. The kernel-recursion happens at proof-CHECKING time:
  -- when verifying the `apply` step, Lean reduces the proof obligations
  -- (e.g., the `addbackN4 (mulsubN4 ...) ...` inside `h_addback`'s proof),
  -- which still triggers the deep let-chain reduction.
  --
  -- **Recommended path forward** (next iteration): add a NEW irreducible
  -- `algCallAddbackBeqAbLowValDouble a b : Nat` for the val256 of the
  -- first-addback's low 4 outputs in the double-addback path. Then
  -- `h_no_overflow` becomes:
  --   `algCallAddbackBeqMsLowVal a b + val256(b_norm)
  --     = algCallAddbackBeqAbLowValDouble a b   (carry = 0 case)
  --     ∧ algCallAddbackBeqAbLowValDouble a b < 2^256` (val256 bound)
  --   ⟹ `algCallAddbackBeqMsLowVal a b + val256(b_norm) < 2^256`.
  -- Both are statements about irreducibles only, no deep let-chain in proof.
  --
  intro shift antiShift b3' u3 u4
  -- Apply qHat_ge_two_abstract with irreducibles + closed preconditions.
  -- Note: u_norm = val256(a) * 2^s - u4 * 2^256 (Nat sub via h_u4_le).
  apply qHat_ge_two_abstract
    (div128Quot u4 u3 b3').toNat
    (algCallAddbackBeqMsLowVal a b)
    (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) -
      (algCallAddbackBeqU4 a b).toNat * 2 ^ 256)
    (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64))
    (algCallAddbackBeqMsC3 a b).toNat
  · -- h_mulsub: c3 * 2^256 + u_norm = ms + qHat * b_norm.
    have h_eucl := algCallAddbackBeq_mulsub_eucl_irreducible_form a b hshift_nz
    simp only [] at h_eucl
    have h_u4_le := algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s a b hshift_nz
    -- Bridge the let-fvars `u4 u3 b3'` (in the goal) to the explicit forms
    -- in h_eucl. Both are defeq via zeta but omega can't see lets.
    have h_qHat_eq : (div128Quot u4 u3 b3').toNat =
        (div128Quot ((a.getLimbN 3) >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
           ((a.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
           ((b.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat
                % 64)))).toNat := rfl
    rw [h_qHat_eq]
    -- Substitute val256(a)*2^s = u_norm + u4*2^256 (Nat sub bridge via h_u4_le).
    have h_a_eq :
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
            2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) =
        (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) -
          (algCallAddbackBeqU4 a b).toNat * 2 ^ 256) +
          (algCallAddbackBeqU4 a b).toNat * 2 ^ 256 := by omega
    rw [h_a_eq] at h_eucl
    omega
  · -- h_no_overflow: ms + b_norm < 2^256.
    exact algCallAddbackBeqMsLowVal_plus_b_norm_lt_pow256 a b hshift_nz hcarry_zero
  · -- h_c3_pos: c3 ≥ 1, from u4 < c3 (hborrow).
    have h := algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat a b hborrow
    have := (algCallAddbackBeqU4 a b).isLt; omega

end EvmAsm.Evm64
