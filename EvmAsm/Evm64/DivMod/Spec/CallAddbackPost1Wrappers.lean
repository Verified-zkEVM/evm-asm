/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackPost1Wrappers

  Single-addback `post1` Word-level wrappers extracted from
  `Spec/CallAddback.lean` to keep that file under the per-file size cap
  (#1078 / beads slice evm-asm-ry8). Pure relocation — no proof changes.

  Contents:
  - `c3_n_eq_u4_plus_one_of_single_addback` — sub-stub closing
    `c3_n = u4 + 1` under single-addback.
  - `algCallAddbackBeqMsC3_eq_u4_plus_one_of_single_addback` —
    irreducible-bundle wrapper.
  - `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback` —
    irreducible-bundle wrapper for the post1-val identity.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddback

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)
open EvmAsm.Rv64.Tactics

/-- **Sub-stub: c3_n = u4 + 1 in single-addback** (CLOSED).

    The key algebraic identity for the call-addback BEQ MOD adapter, mirroring
    `u_top_eq_c3_n_of_overestimate` (call-skip case where c3_n = u4).

    Under hsem + hcarry_nz (single-addback) + hborrow (giving u4 < c3_n):
    - From `qHat_eq_div_plus_one_of_single_addback`: qHat = val256(a)/val256(b) + 1.
    - Mulsub Euclidean: c3_n*2^256 = val256(ms_n) + qHat*val256(b_norm) - val256(u_norm).
    - val256(u_norm) = val256(a)*2^s - u4*2^256, val256(b_norm) = val256(b)*2^s.
    - Algebra: c3_n*2^256 = val256(ms_n) + (val256(b) - val256(a)%val256(b))*2^s + u4*2^256.

    The bound `0 ≤ val256(post1_low4) < 2^256` (from val256 being a 4-limb val)
    combined with the addback Euclidean (carry = 1) forces c3_n - 1 - u4 = 0,
    i.e., c3_n = u4 + 1.

    Combined with hborrow's c3_n ≥ u4 + 1, this pins c3_n exactly.

    **Caveat for callers**: this sub-stub uses `% 64` form for shift/antiShift
    (matching `n4CallAddbackBeqSemanticHolds_def`). Direct application from a
    parent context that uses `set s := clz.1.toNat` (no `% 64`) hits a
    200k-heartbeat elaboration timeout. Callers should align their let-chain
    binding form to use `% 64`, or inline the proof body. -/
theorem c3_n_eq_u4_plus_one_of_single_addback (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
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
    ms.2.2.2.2.toNat = u4.toNat + 1 := by
  intro shift antiShift b3' b2' b1' b0' u3 u2 u1 u0 u4 qHat ms
  -- Concrete proof: apply the closed pure-Nat sub-stub
  -- `c3_eq_u4_plus_one_from_mulsub_addback_bounds` after deriving its 6
  -- preconditions:
  -- - h_mulsub: from `mulsubN4_val256_eq` at normalized limbs +
  --   `qHat_eq_div_plus_one_of_single_addback` (hsem is in scope).
  -- - h_addback: from `addbackN4_val256_eq` at normalized limbs (carry = 1
  --   from hcarry_nz).
  -- - h_u4_le: u4*2^256 ≤ val256(a)*2^s. Follows from u4 = a3 >>> antiShift
  --   (top-s bits of a3) plus val256(a) ≥ a3 * 2^192.
  -- - h_post1_lt: val256(post1_low4) < 2^256 (always, val256 of 4 limbs).
  -- - h_amod_pow_lt: val256(a) % val256(b) * 2^s < 2^256. Follows from
  --   val256(a) % val256(b) < val256(b) ≤ 2^256 / 2^s ⟹ a%b * 2^s < 2^256.
  --   This is the val256_mod_mul_pow bound, available as
  --   `val256_mod_mul_pow_lt_pow256_of_b3_bound`.
  -- - h_u4_lt_c3: directly from hborrow via `u_top_lt_c3_of_addback_borrow_call`.
  -- TODO: each precondition is a small focused derivation (~5-15 lines).
  -- Save folded forms for sub-stub applications, before unfolding.
  have hsem_orig := hsem
  have hborrow_orig := hborrow
  -- Step 1: h_u4_lt_c3 from hborrow.
  rw [isAddbackBorrowN4CallEvm_def] at hborrow
  have h_u4_lt_c3 := EvmWord.u_top_lt_c3_of_addback_borrow_call
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hborrow
  -- Step 2: h_post1_lt — val256(post1_low4) < 2^256 (val256 of any 4-limb is bounded).
  let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  have h_post1_lt : val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1 < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  -- Step 3: h_amod_pow_lt — val256(a) % val256(b) * 2^s < 2^256.
  have h_clz_le : (clzResult (b.getLimbN 3)).1.toNat ≤ 64 := by
    have := clzResult_fst_toNat_le (b.getLimbN 3); omega
  have hbnz_or : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hvb_pos : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    EvmWord.val256_pos_of_or_ne_zero hbnz_or
  have hb3_bound : (b.getLimbN 3).toNat <
      2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat) :=
    clzResult_fst_top_bound (b.getLimbN 3)
  have h_amod_pow_lt :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ (clzResult (b.getLimbN 3)).1.toNat < 2 ^ 256 :=
    EvmWord.val256_mod_mul_pow_lt_pow256_of_b3_bound
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      h_clz_le hvb_pos hb3_bound
  -- Step 4: h_u4_le — u4 * 2^256 ≤ val256(a) * 2^s.
  -- u4 = a3 >>> antiShift = a3 / 2^(64-s), so u4 * 2^(64-s) ≤ a3.
  -- val256(a) ≥ a3 * 2^192. Hence u4 * 2^256 = u4 * 2^(64-s) * 2^(192+s)
  --   ≤ a3 * 2^(192+s) ≤ val256(a) * 2^s.
  have h_a3_val_ge :
      (a.getLimbN 3).toNat * 2^192 ≤
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := by
    unfold val256; nlinarith [(a.getLimbN 0).isLt, (a.getLimbN 1).isLt, (a.getLimbN 2).isLt]
  have h_u4_toNat : u4.toNat =
      (a.getLimbN 3).toNat / 2 ^ ((signExtend12 (0 : BitVec 12) -
        (clzResult (b.getLimbN 3)).1).toNat % 64) := by
    show ((a.getLimbN 3) >>> antiShift).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  -- antiShift = 64 - s, derived via antiShift_toNat_mod_eq (needs 1 ≤ s ≤ 63).
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_anti_eq : (signExtend12 (0 : BitVec 12) -
      (clzResult (b.getLimbN 3)).1).toNat % 64 = 64 - (clzResult (b.getLimbN 3)).1.toNat :=
    antiShift_toNat_mod_eq h_clz_pos h_clz_le_63
  have h_s_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have h_u4_le : u4.toNat * 2^256 ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    rw [h_s_eq]
    -- u4 * 2^antiShift ≤ a3 (Nat.div_mul_le_self).
    have h_u4_mul : u4.toNat * 2 ^ (64 - (clzResult (b.getLimbN 3)).1.toNat)
        ≤ (a.getLimbN 3).toNat := by
      rw [h_u4_toNat, h_anti_eq]
      exact Nat.div_mul_le_self _ _
    -- Multiply both sides by 2^(192 + s) and use the val256 ≥ a3*2^192 bound.
    set s := (clzResult (b.getLimbN 3)).1.toNat
    have h_pow_split : (2 : Nat)^256 = 2^(64 - s) * (2^192 * 2^s) := by
      rw [show (2 : Nat)^192 * 2^s = 2^(192 + s) from by rw [pow_add],
          show (2 : Nat)^(64 - s) * 2^(192 + s) = 2^((64 - s) + (192 + s)) from
            (pow_add 2 (64-s) (192+s)).symm,
          show (64 - s) + (192 + s) = 256 from by omega]
    rw [h_pow_split]
    -- Goal: u4 * (2^(64-s) * (2^192 * 2^s)) ≤ val256(a) * 2^s.
    calc u4.toNat * (2 ^ (64 - s) * (2 ^ 192 * 2 ^ s))
        = (u4.toNat * 2 ^ (64 - s)) * (2 ^ 192 * 2 ^ s) := by ring
      _ ≤ (a.getLimbN 3).toNat * (2 ^ 192 * 2 ^ s) :=
          Nat.mul_le_mul_right _ h_u4_mul
      _ = (a.getLimbN 3).toNat * 2 ^ 192 * 2 ^ s := by ring
      _ ≤ val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) * 2 ^ s :=
          Nat.mul_le_mul_right _ h_a3_val_ge
  -- Step 5a: addback Euclidean (val256-level, with carry term) — direct application.
  have h_addback_eq := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  simp only [] at h_addback_eq
  -- Step 5b: carry.toNat = 1 from hcarry_nz + addbackN4_carry_le_one.
  have h_carry_le := addbackN4_carry_le_one ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  have h_carry_eq_one : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 1 := by
    -- carry is a Word that's ≠ 0 (hcarry_nz) and ≤ 1 (h_carry_le); so carry.toNat = 1.
    have h_pos : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat ≠ 0 := by
      intro h_zero
      apply hcarry_nz
      change addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' = (0 : Word)
      apply BitVec.eq_of_toNat_eq
      rw [h_zero]; rfl
    omega
  -- Step 5c: val256(b_norm) = val256(b) * 2^s via val256_normalize.
  have h_norm_b : val256 b0' b1' b2' b3' =
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    -- Unfold b0'..b3' and antiShift to bring the `(64 - s)` form into scope.
    show val256 ((b.getLimbN 0) <<< shift)
                (((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift))
                (((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift))
                (((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)) = _
    have h_anti_unfold : antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat := h_anti_eq
    have h_shift_unfold : shift = (clzResult (b.getLimbN 3)).1.toNat := h_s_eq
    rw [h_anti_unfold, h_shift_unfold, h_s_eq]
    have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by
      have := h_clz_le_63; omega
    exact EvmWord.val256_normalize h_clz_pos h_clz_lt_64
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_bound
  -- Step 5d: combine h_addback_eq + h_carry_eq_one + h_norm_b → h_addback.
  have h_addback : val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1 + 2^256 =
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
          2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    show val256 (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').1
                (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.1
                (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.1
                (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.2.1 + 2^256 = _
    rw [← h_norm_b]
    have h := h_addback_eq
    rw [h_carry_eq_one] at h
    omega
  -- Step 6: h_qHat_eq — qHat.toNat = a/b + 1 from the closed sub-stub.
  have h_qHat_eq : qHat.toNat = a.toNat / b.toNat + 1 :=
    qHat_eq_div_plus_one_of_single_addback a b hshift_nz hborrow_orig hsem_orig hcarry_nz
  -- Step 7: h_mulsub_eq — mulsub Euclidean at val256 level.
  have h_mulsub_eq := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub_eq
  -- Step 8: h_norm_u — val256(u_norm_low4) + u4*2^256 = val256(a)*2^s.
  have h_norm_u : val256 u0 u1 u2 u3 + u4.toNat * 2^256 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    show val256 ((a.getLimbN 0) <<< shift)
                (((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift))
                (((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift))
                (((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)) +
            ((a.getLimbN 3) >>> antiShift).toNat * 2^256 = _
    have h_anti_unfold : antiShift = 64 - (clzResult (b.getLimbN 3)).1.toNat := h_anti_eq
    have h_shift_unfold : shift = (clzResult (b.getLimbN 3)).1.toNat := h_s_eq
    rw [h_anti_unfold, h_shift_unfold, h_s_eq]
    have h_clz_lt_64 : (clzResult (b.getLimbN 3)).1.toNat < 64 := by
      have := h_clz_le_63; omega
    exact EvmWord.val256_normalize_general h_clz_pos h_clz_lt_64
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  -- Step 9: combine h_mulsub_eq + h_norm_u + h_norm_b + h_qHat_eq → h_mulsub.
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
  -- Step 9: h_mulsub composition.
  -- h_norm_b'  : val256(b0'..b3') = b.toNat * 2^s.
  -- h_norm_u'  : val256(u0..u3) + u4*2^256 = a.toNat * 2^s.
  have h_norm_b' : val256 b0' b1' b2' b3' = b.toNat *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    rw [h_norm_b, hb_val]
  have h_norm_u' : val256 u0 u1 u2 u3 + u4.toNat * 2^256 = a.toNat *
      2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
    have h := h_norm_u
    rw [ha_val] at h
    exact h
  -- ms_eq: ms.2.2.2.2 = (inline mulsubN4 ...).2.2.2.2 (defeq via set ms).
  have h_ms_eq : ms.2.2.2.2 = (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2 := rfl
  have h_ms_lo_eq : (val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 :)
      = val256 (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).1
               (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.1
               (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.1
               (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.1 := rfl
  have h_mulsub : ms.2.2.2.2.toNat * 2^256 +
      (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) - u4.toNat * 2^256) =
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
        (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 1) *
          (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
            2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64)) := by
    rw [ha_val, hb_val, h_ms_eq, h_ms_lo_eq]
    have h := h_mulsub_eq
    rw [h_qHat_eq, h_norm_b'] at h
    have h_u_val : val256 u0 u1 u2 u3 =
        a.toNat * 2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) - u4.toNat * 2^256 := by
      have h2 := h_norm_u'
      omega
    rw [h_u_val] at h
    omega
  -- Align h_amod_pow_lt's `2^s` form (no `% 64`) with the Nat lemma's expected form.
  have h_amod_pow_lt' :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) < 2 ^ 256 := by
    rw [h_s_eq]; exact h_amod_pow_lt
  -- Final composition: apply the closed Nat lemma with all 6 preconditions.
  show ms.2.2.2.2.toNat = u4.toNat + 1
  exact c3_eq_u4_plus_one_from_mulsub_addback_bounds
    (val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1)
    (val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1)
    (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3))
    (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    ((clzResult (b.getLimbN 3)).1.toNat % 64) u4.toNat ms.2.2.2.2.toNat
    h_mulsub h_addback h_u4_le h_post1_lt h_amod_pow_lt' h_u4_lt_c3

/-- **Wrapper: c3 = u4 + 1 in single-addback (irreducible-form).**

    Wraps `c3_n_eq_u4_plus_one_of_single_addback` to take its hypothesis
    in irreducible-bundle form (`algCallAddbackBeqCarry a b ≠ 0`), avoiding
    the deep let-chain elaboration cost at the call site. The conclusion
    is also stated in irreducible form for symmetry.

    Internally unfolds the irreducible defs and applies the closed sub-stub.
    Caller should provide hb3nz, hshift_nz, hborrow, hsem, and the
    irreducible-form hcarry_nz. -/
theorem algCallAddbackBeqMsC3_eq_u4_plus_one_of_single_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    (algCallAddbackBeqMsC3 a b).toNat = (algCallAddbackBeqU4 a b).toNat + 1 := by
  -- Unfold the irreducible defs to get the let-chain forms.
  show _ = _
  rw [show (algCallAddbackBeqMsC3 a b).toNat = _ from by
        unfold algCallAddbackBeqMsC3; rfl,
      show (algCallAddbackBeqU4 a b).toNat = _ from by
        unfold algCallAddbackBeqU4; rfl]
  rw [algCallAddbackBeqCarry_unfold] at hcarry_nz
  exact c3_n_eq_u4_plus_one_of_single_addback a b hb3nz hshift_nz hborrow hsem hcarry_nz


/-- **Wrapper: post1Val = a%b * 2^s in single-addback (irreducible-form)** (CLOSED).

    Given the algorithm's invariants in single-addback (carry ≠ 0), the val256
    of the first-addback post1 limbs at normalized inputs equals
    `val256(a) % val256(b) * 2^s` — i.e., the un-truncated form of the
    Knuth-style remainder.

    Stated in irreducible-bundle form (`algCallAddbackBeqPost1Val a b` =
    val256-of-post1; `algCallAddbackBeqCarry a b ≠ 0` = single-addback)
    so the call site doesn't pay the deep let-chain elaboration cost.

    Composes the 6 closed Word-level preconditions through
    `post1_val_eq_amod_pow_s_pure_nat`:
    - `algCallAddbackBeqPost1Val_lt_pow256`                    (h_post1_lt)
    - `algCallAddbackBeq_amod_pow_s_lt_pow256`                 (h_amod_pow_lt)
    - `algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat` (h_u4_lt_c3)
    - `algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s`     (h_u4_le)
    - `algCallAddbackBeq_addback_euclidean_carry_one`          (h_addback)
    - `algCallAddbackBeq_mulsub_euclidean`                     (h_mulsub) -/
theorem algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    algCallAddbackBeqPost1Val a b =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
  exact post1_val_eq_amod_pow_s_pure_nat
    (algCallAddbackBeqPost1Val a b)
    (algCallAddbackBeqMsLowVal a b)
    (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3))
    (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    ((clzResult (b.getLimbN 3)).1.toNat % 64)
    (algCallAddbackBeqU4 a b).toNat
    (algCallAddbackBeqMsC3 a b).toNat
    (algCallAddbackBeq_mulsub_euclidean a b hshift_nz hborrow hsem hcarry_nz)
    (algCallAddbackBeq_addback_euclidean_carry_one a b hshift_nz hcarry_nz)
    (algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s a b hshift_nz)
    (algCallAddbackBeqPost1Val_lt_pow256 a b)
    (algCallAddbackBeq_amod_pow_s_lt_pow256 a b hb3nz)
    (algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat a b hborrow)

end EvmAsm.Evm64
