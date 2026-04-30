/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackMod

  EVM-stack-level MOD spec on the call+addback BEQ sub-path plus its
  per-limb mod equation lemmas, the parent val256 form for single-addback
  post1, and the n=4 shift_nz dispatcher specs (DIV + MOD).

  Extracted from `Spec/CallAddback.lean` to keep that file under the
  per-file size cap (#1078 / beads slice evm-asm-ry8). All declarations
  here are downstream consumers of the bulk of `Spec/CallAddback.lean`,
  so the extraction is unidirectional: this file imports CallAddback,
  not the other way around.

  Contents:
  - `parent_post1Val_eq_amod_pow_s_of_single_addback`
  - `mod_n4_call_addback_beq_single_addback_post1_limbs_close`
  - `mod_n4_call_addback_beq_double_addback_abPrime_limbs_close`
  - `output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm`
  - `evm_mod_n4_call_addback_beq_stack_spec_within`
  - `evm_div_n4_call_stack_spec`
  - `evm_mod_n4_call_stack_spec_within`
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddback

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)
open EvmAsm.Rv64.Tactics

/-- **Unified parent-form: post1Val = a%b * 2^s in single-addback** (CLOSED).

    Drop-in replacement for the parent adapter's single-addback branch:
    takes the parent's local `(64-s)`-form `addbackN4_carry … ≠ 0`
    hypothesis directly, and returns the val256 equation in the parent's
    `(64-s)`-form too. Internally chains the carry/post1Val bridges with
    the closed wrapper. -/
theorem parent_post1Val_eq_amod_pow_s_of_single_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz :
      let s := (clzResult (b.getLimbN 3)).1.toNat % 64
      let b0' := (b.getLimbN 0) <<< s
      let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
      let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
      let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
      let u0 := (a.getLimbN 0) <<< s
      let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
      let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
      let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
      let u4 := (a.getLimbN 3) >>> (64 - s)
      let qHat := div128Quot u4 u3 b3'
      let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
      addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0) :
    let s := (clzResult (b.getLimbN 3)).1.toNat % 64
    let b0' := (b.getLimbN 0) <<< s
    let b1' := ((b.getLimbN 1) <<< s) ||| ((b.getLimbN 0) >>> (64 - s))
    let b2' := ((b.getLimbN 2) <<< s) ||| ((b.getLimbN 1) >>> (64 - s))
    let b3' := ((b.getLimbN 3) <<< s) ||| ((b.getLimbN 2) >>> (64 - s))
    let u0 := (a.getLimbN 0) <<< s
    let u1 := ((a.getLimbN 1) <<< s) ||| ((a.getLimbN 0) >>> (64 - s))
    let u2 := ((a.getLimbN 2) <<< s) ||| ((a.getLimbN 1) >>> (64 - s))
    let u3 := ((a.getLimbN 3) <<< s) ||| ((a.getLimbN 2) >>> (64 - s))
    let u4 := (a.getLimbN 3) >>> (64 - s)
    let qHat := div128Quot u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let post1 := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
    val256 post1.1 post1.2.1 post1.2.2.1 post1.2.2.2.1 =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ s := by
  intro s b0' b1' b2' b3' u0 u1 u2 u3 u4 qHat ms post1
  -- Bridge hcarry_nz: parent's (64-s) carry → algCallAddbackBeqCarry a b ≠ 0.
  have h_carry_bridge := algCallAddbackBeqCarry_eq_parent_64ms_form a b hshift_nz
  simp only [] at h_carry_bridge
  have hcarry_irreducible : algCallAddbackBeqCarry a b ≠ 0 := by
    rw [h_carry_bridge]; exact hcarry_nz
  -- Apply the closed wrapper.
  have h_wrapper := algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback
    a b hb3nz hshift_nz hborrow hsem hcarry_irreducible
  -- Bridge the wrapper's irreducible-form post1Val to parent's (64-s)-form post1.
  have h_post1_bridge := algCallAddbackBeqPost1Val_eq_parent_64ms_form a b hshift_nz
  simp only [] at h_post1_bridge
  rw [h_post1_bridge] at h_wrapper
  exact h_wrapper

/-- **Sub-lemma: per-limb mod equations using irreducible Post1Limb bundles** (CLOSED).

    Drop-in for the parent adapter's single-addback branch: produces per-limb
    equations `(EvmWord.mod a b).getLimbN i = (Limb{i} >>> s) ||| (Limb{i+1} <<< (64-s))`
    using the irreducible `algCallAddbackBeqPost1Limb{0..3}` bundles, keeping
    the goal small.

    Composes:
      * `parent_post1Val_eq_amod_pow_s_of_single_addback` (val256 fact, parent shape)
      * `algCallAddbackBeqPost1Val_eq_val256_limbs` (val256 ↔ per-limb irreducibles)
      * `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` (val256 → per-limb evmWordIs) -/
theorem mod_n4_call_addback_beq_single_addback_post1_limbs_close
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_nz : algCallAddbackBeqCarry a b ≠ 0) :
    let s := (clzResult (b.getLimbN 3)).1.toNat % 64
    (EvmWord.mod a b).getLimbN 0 =
      ((algCallAddbackBeqPost1Limb0 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb1 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 1 =
      ((algCallAddbackBeqPost1Limb1 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb2 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 2 =
      ((algCallAddbackBeqPost1Limb2 a b) >>> s) |||
        ((algCallAddbackBeqPost1Limb3 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 3 =
      (algCallAddbackBeqPost1Limb3 a b) >>> s := by
  intro s
  -- Step 1: get the val256 fact.
  have h_wrapper := algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback
    a b hb3nz hshift_nz hborrow hsem hcarry_nz
  -- Step 2: rewrite val256 in terms of irreducible per-limb bundles.
  rw [algCallAddbackBeqPost1Val_eq_val256_limbs] at h_wrapper
  -- Step 3: derive bounds on s.
  have h_clz_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_s_pos : 0 < s := by show 0 < _; omega
  have h_s_lt_64 : s < 64 := by show _ < 64; omega
  -- Step 4: apply denorm_4limb to get per-limb equations.
  exact denorm_4limb_eq_mod_of_val256_eq_amod_pow_s
    (a := a) (b := b)
    (X1 := algCallAddbackBeqPost1Limb0 a b)
    (X2 := algCallAddbackBeqPost1Limb1 a b)
    (X3 := algCallAddbackBeqPost1Limb2 a b)
    (X4 := algCallAddbackBeqPost1Limb3 a b)
    h_s_pos h_s_lt_64 hb3nz h_wrapper

/-- **B.5: val256 of double-addback's second-addback equals
    `val256(a) % val256(b) * 2^s`** (CLOSED modulo 2 stubs).

    Mirrors `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback`
    for the **double-addback** branch (carry = 0).

    **Proof structure** (matches single-addback's): direct application
    of `abPrime_val_eq_amod_pow_s_pure_nat` (B.3, CLOSED) with the 6
    closed Word-level preconditions:
    - `algCallAddbackBeqAbPrimeVal_lt_pow256`                      (h_abPrime_lt, CLOSED)
    - `algCallAddbackBeq_amod_pow_s_lt_pow256`                     (h_amod_pow_lt, CLOSED, reused)
    - `algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat`   (h_u4_lt_c3, CLOSED, reused)
    - `algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s`         (h_u4_le, CLOSED, reused)
    - `algCallAddbackBeq_addback_combined_euclidean_carry2`         (h_addback_combined, CLOSED)
    - `algCallAddbackBeq_mulsub_euclidean_double`                  (h_mulsub, CLOSED)

    Issue #1338 Phase B.5. -/
theorem algCallAddbackBeqAbPrimeVal_eq_amod_pow_s_of_double_addback
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    algCallAddbackBeqAbPrimeVal a b =
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) %
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2 ^ ((clzResult (b.getLimbN 3)).1.toNat % 64) := by
  exact abPrime_val_eq_amod_pow_s_pure_nat
    (algCallAddbackBeqAbPrimeVal a b)
    (algCallAddbackBeqMsLowVal a b)
    (val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3))
    (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    ((clzResult (b.getLimbN 3)).1.toNat % 64)
    (algCallAddbackBeqU4 a b).toNat
    (algCallAddbackBeqMsC3 a b).toNat
    (algCallAddbackBeq_mulsub_euclidean_double a b hshift_nz hborrow hcarry2_nz
      hsem hcarry_zero)
    (algCallAddbackBeq_addback_combined_euclidean_carry2 a b hshift_nz
      hcarry2_nz hcarry_zero)
    (algCallAddbackBeqU4_mul_pow256_le_val256_mul_pow_s a b hshift_nz)
    (algCallAddbackBeqAbPrimeVal_lt_pow256 a b)
    (algCallAddbackBeq_amod_pow_s_lt_pow256 a b hb3nz)
    (algCallAddbackBeqU4_toNat_lt_algCallAddbackBeqMsC3_toNat a b hborrow)

/-- **B.7: per-limb mod equations for double-addback** (CLOSED modulo B.5).

    Mirror of `mod_n4_call_addback_beq_single_addback_post1_limbs_close`
    for the double-addback branch (carry = 0). Composes:
      * `algCallAddbackBeqAbPrimeVal_eq_amod_pow_s_of_double_addback` (B.5, sorry)
      * `algCallAddbackBeqAbPrimeVal_eq_val256_limbs` (B.4, closed)
      * `denorm_4limb_eq_mod_of_val256_eq_amod_pow_s` (existing)

    The proof body is fully wired; closure depends only on B.5. -/
theorem mod_n4_call_addback_beq_double_addback_abPrime_limbs_close
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b)
    (hcarry_zero : algCallAddbackBeqCarry a b = 0) :
    let s := (clzResult (b.getLimbN 3)).1.toNat % 64
    (EvmWord.mod a b).getLimbN 0 =
      ((algCallAddbackBeqAbPrimeLimb0 a b) >>> s) |||
        ((algCallAddbackBeqAbPrimeLimb1 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 1 =
      ((algCallAddbackBeqAbPrimeLimb1 a b) >>> s) |||
        ((algCallAddbackBeqAbPrimeLimb2 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 2 =
      ((algCallAddbackBeqAbPrimeLimb2 a b) >>> s) |||
        ((algCallAddbackBeqAbPrimeLimb3 a b) <<< (64 - s)) ∧
    (EvmWord.mod a b).getLimbN 3 =
      (algCallAddbackBeqAbPrimeLimb3 a b) >>> s := by
  intro s
  have h_wrapper := algCallAddbackBeqAbPrimeVal_eq_amod_pow_s_of_double_addback
    a b hb3nz hshift_nz hcarry2_nz hborrow hsem hcarry_zero
  rw [algCallAddbackBeqAbPrimeVal_eq_val256_limbs] at h_wrapper
  have h_clz_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_s_pos : 0 < s := by show 0 < _; omega
  have h_s_lt_64 : s < 64 := by show _ < 64; omega
  exact denorm_4limb_eq_mod_of_val256_eq_amod_pow_s
    (a := a) (b := b)
    (X1 := algCallAddbackBeqAbPrimeLimb0 a b)
    (X2 := algCallAddbackBeqAbPrimeLimb1 a b)
    (X3 := algCallAddbackBeqAbPrimeLimb2 a b)
    (X4 := algCallAddbackBeqAbPrimeLimb3 a b)
    h_s_pos h_s_lt_64 hb3nz h_wrapper

/-- **Call+addback BEQ n=4 MOD denorm adapter** (single-addback CLOSED, double-addback SORRY).

    Stack-level adapter folding the 4 denormalized remainder slots at
    sp+32..sp+56 into `evmWordIs (sp+32) (EvmWord.mod a b)` for the
    call+addback BEQ path.

    Signature uses irreducible Un{i}Out bundles to keep the goal small
    (a previous version had a 246-line proof body wrestling with deep
    inline let-chains). The proof fans out via:
      - `algCallAddbackBeqUn{i}Out_eq_post1Limb{i}_of_single_addback`
        (folds Un{i}Out → Post1Limb{i} under hcarry ≠ 0).
      - `mod_n4_call_addback_beq_single_addback_post1_limbs_close`
        (per-limb mod equations in irreducible form).
      - `evmWordIs_sp32_limbs_eq.symm` (final fold).

    Both branches CLOSED. The double-addback branch (carry = 0) closes
    via B.5 (`mod_n4_call_addback_beq_double_addback_abPrime_limbs_close`),
    which uses the now-closed `algCallAddbackBeq_mulsub_euclidean_double`
    chain (#1338 B.1a → B.1 → B.5 → B.7 cascade). -/
theorem output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm
    (sp : Word) (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let un0Out := algCallAddbackBeqUn0Out a b
    let un1Out := algCallAddbackBeqUn1Out a b
    let un2Out := algCallAddbackBeqUn2Out a b
    let un3Out := algCallAddbackBeqUn3Out a b
    (((sp + 32) ↦ₘ ((un0Out >>> shift) ||| (un1Out <<< (64 - shift)))) **
     ((sp + 40) ↦ₘ ((un1Out >>> shift) ||| (un2Out <<< (64 - shift)))) **
     ((sp + 48) ↦ₘ ((un2Out >>> shift) ||| (un3Out <<< (64 - shift)))) **
     ((sp + 56) ↦ₘ (un3Out >>> shift))) =
    evmWordIs (sp + 32) (EvmWord.mod a b) := by
  intro shift un0Out un1Out un2Out un3Out
  by_cases hcarry : algCallAddbackBeqCarry a b = 0
  · -- Double-addback branch (carry = 0). Wired via B.5 (#1338, blocked on
    -- Knuth-B #1337) → B.7 → parent. Mirror of single-addback's structure.
    rw [show un0Out = algCallAddbackBeqAbPrimeLimb0 a b from
          algCallAddbackBeqUn0Out_eq_abPrimeLimb0_of_double_addback a b hcarry,
        show un1Out = algCallAddbackBeqAbPrimeLimb1 a b from
          algCallAddbackBeqUn1Out_eq_abPrimeLimb1_of_double_addback a b hcarry,
        show un2Out = algCallAddbackBeqAbPrimeLimb2 a b from
          algCallAddbackBeqUn2Out_eq_abPrimeLimb2_of_double_addback a b hcarry,
        show un3Out = algCallAddbackBeqAbPrimeLimb3 a b from
          algCallAddbackBeqUn3Out_eq_abPrimeLimb3_of_double_addback a b hcarry]
    have h_limbs := mod_n4_call_addback_beq_double_addback_abPrime_limbs_close
      a b hb3nz hshift_nz hcarry2_nz hborrow hsem hcarry
    simp only [] at h_limbs
    exact (evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
      h_limbs.1 h_limbs.2.1 h_limbs.2.2.1 h_limbs.2.2.2).symm
  · -- Single-addback branch: fold Un{i}Out → Post1Limb{i} via bridges.
    rw [show un0Out = algCallAddbackBeqPost1Limb0 a b from
          algCallAddbackBeqUn0Out_eq_post1Limb0_of_single_addback a b hcarry,
        show un1Out = algCallAddbackBeqPost1Limb1 a b from
          algCallAddbackBeqUn1Out_eq_post1Limb1_of_single_addback a b hcarry,
        show un2Out = algCallAddbackBeqPost1Limb2 a b from
          algCallAddbackBeqUn2Out_eq_post1Limb2_of_single_addback a b hcarry,
        show un3Out = algCallAddbackBeqPost1Limb3 a b from
          algCallAddbackBeqUn3Out_eq_post1Limb3_of_single_addback a b hcarry]
    have h_limbs := mod_n4_call_addback_beq_single_addback_post1_limbs_close
      a b hb3nz hshift_nz hborrow hsem hcarry
    simp only [] at h_limbs
    exact (evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
      h_limbs.1 h_limbs.2.1 h_limbs.2.2.1 h_limbs.2.2.2).symm

/-- **EVM-stack-level MOD spec on the n=4 call+addback BEQ sub-path.**

    Mirror of `evm_div_n4_call_addback_beq_stack_spec` for MOD. Composes
    the closed `output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm`
    adapter (above) with the runtime + memory bookkeeping from
    `evm_mod_n4_full_call_addback_beq_stack_pre_spec_bundled_within`. Mirrors
    the template from `evm_mod_n4_call_skip_stack_spec_within` (landed in #1207). -/
theorem evm_mod_n4_call_addback_beq_stack_spec_within (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin 340 base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  have h_pre := evm_mod_n4_full_call_addback_beq_stack_pre_spec_bundled_within sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  have hshift_le_63 := clzResult_fst_toNat_le (b.getLimbN 3)
  have hshift_pos : 0 < (clzResult (b.getLimbN 3)).1.toNat := by
    by_contra h
    push Not at h
    apply hshift_nz
    apply BitVec.eq_of_toNat_eq
    rw [show (0 : Word).toNat = 0 from rfl]; omega
  have hmod_eq : (clzResult (b.getLimbN 3)).1.toNat % 64 =
      (clzResult (b.getLimbN 3)).1.toNat := by omega
  have h0se12 : signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1 =
      -((clzResult (b.getLimbN 3)).1) := by rw [signExtend12_0]; simp
  have hanti_toNat_mod :
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64 =
      64 - (clzResult (b.getLimbN 3)).1.toNat := by
    rw [h0se12, BitVec.toNat_neg]
    have : ((clzResult (b.getLimbN 3)).1).toNat ≤ 2^64 := by
      have := ((clzResult (b.getLimbN 3)).1).isLt; omega
    omega
  have h_slot := output_slot_to_evmWordIs_mod_n4_call_addback_beq_denorm sp a b
    hb3nz hshift_nz hcarry2_nz hborrow hsem
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullModN4CallAddbackBeqPost_unfold, denormModPost_unfold] at hq
  -- Fold hq's inline un{i}Out forms to the irreducible Un{i}Out names
  -- (matching the parent adapter's new signature).
  simp only [← algCallAddbackBeqUn0Out_unfold, ← algCallAddbackBeqUn1Out_unfold,
             ← algCallAddbackBeqUn2Out_unfold, ← algCallAddbackBeqUn3Out_unfold] at hq
  apply mod_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.mod a b) = _ from h_slot.symm]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  simp only [hmod_eq, hanti_toNat_mod] at hq ⊢
  xperm_hyp hq

/-- **n=4 shift_nz DIV top-level dispatcher** — routes between
    call+skip (unconditional, hsem auto-discharged) and call+addback
    BEQ paths via the borrow-check disjunction.

    Mirror of `evm_div_n4_shift0_stack_spec` (Shift0Dispatcher.lean) but
    for the shift_nz path. Uses
    `isSkipBorrowN4CallEvm_or_isAddbackBorrowN4CallEvm` as the case-split
    and `evm_div_n4_call_skip_stack_spec_unconditional` (which
    auto-discharges `n4CallSkipSemanticHolds`) for the skip path.

    The addback-BEQ path still requires its own `hsem`
    (`n4CallAddbackBeqSemanticHolds`) and `hcarry2_nz` — these encode
    Knuth-B + addback correctness which haven't been closed yet
    (parked behind PR #1339's bridge stub). -/
theorem evm_div_n4_call_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz_addback :
      isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
    (hsem_addback :
      isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin 340 base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  rcases isSkipBorrowN4CallEvm_or_isAddbackBorrowN4CallEvm a b with hskip | haddback
  · exact cpsTripleWithin_mono_nSteps (by decide) <|
      evm_div_n4_call_skip_stack_spec_unconditional sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_nz halign hbltu hskip
  · exact evm_div_n4_call_addback_beq_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_nz halign hbltu
      (hcarry2_nz_addback haddback) haddback (hsem_addback haddback)

/-- **n=4 shift_nz MOD top-level dispatcher** — mirror of
    `evm_div_n4_call_stack_spec` for MOD. Routes between
    call+skip (auto-discharged) and call+addback BEQ paths.

    Note: MOD's call-addback-beq spec doesn't take `hvalid` (unlike
    DIV's), so the MOD dispatcher's signature is one parameter shorter. -/
theorem evm_mod_n4_call_stack_spec_within (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz_addback :
      isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
    (hsem_addback :
      isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin 340 base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  rcases isSkipBorrowN4CallEvm_or_isAddbackBorrowN4CallEvm a b with hskip | haddback
  · exact cpsTripleWithin_mono_nSteps (by omega)
      (evm_mod_n4_call_skip_stack_spec_unconditional_within sp base a b
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        hbnz hb3nz hshift_nz halign hbltu hskip)
  · exact evm_mod_n4_call_addback_beq_stack_spec_within sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift_nz halign hbltu
      (hcarry2_nz_addback haddback) haddback (hsem_addback haddback)

end EvmAsm.Evm64
