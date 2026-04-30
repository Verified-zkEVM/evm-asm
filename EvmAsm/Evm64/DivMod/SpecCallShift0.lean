/-
  EvmAsm.Evm64.DivMod.SpecCallShift0

  Shift=0 (`b3` already normalized) call-trial DIV/MOD stack specs for the
  n=4 path. Extracted from `SpecCall.lean` to keep that file under the
  file-size cap.

  These six theorems sit on top of `SpecCall`'s base predicates +
  `EvmWordArith.Div128Shift0`'s shift=0 bounds:

  * `n4_shift0_call_skip_div_mod_getLimbN`
  * `evm_div_n4_shift0_call_skip_stack_spec`
  * `n4_shift0_call_skip_mod_getLimbN`
  * `evm_mod_n4_shift0_call_skip_stack_spec`
  * `n4_shift0_call_addback_beq_div_getLimbN`
  * `evm_div_n4_shift0_call_addback_beq_stack_spec`

  The MOD counterpart `evm_mod_n4_shift0_call_addback_beq_stack_spec`
  lives in `Shift0AddbackMod.lean` (it depends on additional lemmas
  proved there).
-/

import EvmAsm.Evm64.DivMod.SpecCall

namespace EvmAsm.Evm64

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)

-- ============================================================================
-- Shift=0 call+skip DIV stack spec (unblocked by PR #1155's Div128Shift0)
-- ============================================================================

/-- **Shift=0 call+skip n=4 div getLimbN bridge.** Under shift=0 (b3 already
    normalized), `isSkipBorrowN4Shift0Evm`, and b ≠ 0: the algorithm's trial
    qHat = `div128Quot 0 a3 b3` equals `(EvmWord.div a b).getLimbN 0`, and
    the upper three limbs of the quotient are zero.

    Simpler than the shift-nz case: `Div128Shift0` gives both bounds
    (`_ge_val256_div` and `_le_one`), and skip-borrow + c3=0 from mulsub's
    Euclidean gives the upper bound `qHat * val256(b) ≤ val256(a)`. -/
theorem n4_shift0_call_skip_div_mod_getLimbN (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    let qHat := div128Quot (0 : Word)
      (a.getLimbN 3) (b.getLimbN 3)
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  simp only []
  set qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3) with hqHat_def
  rw [isSkipBorrowN4Shift0Evm_def] at hborrow
  -- Extract c3 = 0 from the skip-borrow predicate.
  have hc3_zero : mulsubN4_c3 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) = 0 := by
    unfold isSkipBorrowN4Shift0 at hborrow
    simp only [] at hborrow
    by_contra hne
    have h_lt : BitVec.ult (0 : Word)
        (mulsubN4_c3 qHat
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)) = true := by
      rw [EvmWord.ult_iff]
      rw [show (0 : Word).toNat = 0 from rfl]
      exact Nat.pos_of_ne_zero (fun h => hne (BitVec.eq_of_toNat_eq (by simp [h])))
    rw [h_lt] at hborrow
    simp at hborrow
  -- b3 has top bit set (shift=0 normalization), so b3 ≥ 2^63.
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2^63 :=
    clz_zero_imp_msb hshift_z
  -- Lower bound from Div128Shift0.
  have h_ge := div128Quot_shift0_ge_a3_div_b3 (a.getLimbN 3) (b.getLimbN 3) hb3_ge
  -- Bridge to val256: use `a3_div_b3_ge_val256_div` to lift from a3/b3 to val256.
  have hb_nz_or : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hb_pos_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    EvmWord.val256_pos_of_or_ne_zero hb_nz_or
  have h_algo_ge := div128Quot_shift0_ge_val256_div
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_ge hb_pos_val
  simp only [] at h_algo_ge
  -- Upper bound from c3 = 0: mulsubN4_val256_eq gives val256(u) + 0 = val256(un) + qHat * val256(v).
  have h_mulsub := mulsubN4_val256_eq qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  simp only [] at h_mulsub
  rw [show (mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 =
      (0 : Word) from hc3_zero] at h_mulsub
  rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero] at h_mulsub
  have h_un_bound :
      val256 (mulsubN4 qHat
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).1
        (mulsubN4 qHat
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.1
        (mulsubN4 qHat
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.1
        (mulsubN4 qHat
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.1 ≥ 0 :=
    Nat.zero_le _
  have h_qHat_mul_le : qHat.toNat *
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := by
    linarith
  -- Now combine: qHat = val256(a)/val256(b).
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
  have hb_pos : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exfalso; apply hbnz; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  rw [ha_val, hb_val] at h_qHat_mul_le h_algo_ge
  have hq_eq : qHat.toNat = a.toNat / b.toNat := by
    have hle : qHat.toNat ≤ a.toNat / b.toNat :=
      (Nat.le_div_iff_mul_le hb_pos).mpr h_qHat_mul_le
    have hqHat_toNat :
        qHat.toNat = (div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3)).toNat := by
      rw [hqHat_def]
    omega
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div
    rw [if_neg hbnz]
    exact BitVec.toNat_udiv
  set q_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => qHat | 1 => 0 | 2 => 0 | 3 => 0 with hq_target
  have hq_target_toNat : q_target.toNat = qHat.toNat := by
    simp [q_target, EvmWord.fromLimbs_toNat]
  have hq_eq_div : q_target = EvmWord.div a b :=
    BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_3

/-- **EVM-stack-level DIV spec on the n=4 shift=0 call+skip sub-path.**

    Simpler counterpart to `evm_div_n4_call_skip_stack_spec` — under shift=0
    no normalization is applied, so no `n4CallSkipSemanticHolds` hypothesis
    is needed. The semantic correctness follows directly from the
    `Div128Shift0` lemmas merged in PR #1155 (`div128Quot_shift0_ge_val256_div`)
    plus the skip-borrow condition giving c3 = 0.

    Reduces to `evm_div_n4_full_shift0_call_skip_stack_pre_spec_bundled` +
    `n4_shift0_call_skip_div_mod_getLimbN` + postcondition reshape. -/
theorem evm_div_n4_shift0_call_skip_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 126 + 12)
      base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  have h_pre := evm_div_n4_full_shift0_call_skip_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_shift0_call_skip_div_mod_getLimbN a b hbnz hshift_z hborrow
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  -- Reshape the concrete `fullDivN4Shift0CallSkipPost` into
  -- `divN4CallSkipStackPost` using the limb bridge.
  unfold fullDivN4Shift0CallSkipPost at hq
  apply div_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.div a b) =
      (((sp + 32) ↦ₘ (div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3))) **
       ((sp + 40) ↦ₘ (0 : Word)) **
       ((sp + 48) ↦ₘ (0 : Word)) **
       ((sp + 56) ↦ₘ (0 : Word)))
      from by rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
                  hdiv0 hdiv1 hdiv2 hdiv3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- **Shift=0 call+skip n=4 mod getLimbN bridge.** Under the same shift=0
    call-skip conditions, the four mulsubN4 low-limb outputs at sp+32..sp+56
    fold into `evmWordIs (sp+32) (EvmWord.mod a b)`.

    Proof: same shape as `n4_shift0_call_skip_div_mod_getLimbN`, but extracts
    the MOD equalities via `val256_ms_un_eq_val256_mod_of_overestimate`
    (which gives `val256(ms) = val256(a) % val256(b)`). -/
theorem n4_shift0_call_skip_mod_getLimbN (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    let qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (EvmWord.mod a b).getLimbN 0 = ms.1 ∧
    (EvmWord.mod a b).getLimbN 1 = ms.2.1 ∧
    (EvmWord.mod a b).getLimbN 2 = ms.2.2.1 ∧
    (EvmWord.mod a b).getLimbN 3 = ms.2.2.2.1 := by
  simp only []
  set qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3) with hqHat_def
  rw [isSkipBorrowN4Shift0Evm_def] at hborrow
  have hc3_zero : mulsubN4_c3 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) = 0 := by
    unfold isSkipBorrowN4Shift0 at hborrow
    simp only [] at hborrow
    by_contra hne
    have h_lt : BitVec.ult (0 : Word)
        (mulsubN4_c3 qHat
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)) = true := by
      rw [EvmWord.ult_iff]
      rw [show (0 : Word).toNat = 0 from rfl]
      exact Nat.pos_of_ne_zero (fun h => hne (BitVec.eq_of_toNat_eq (by simp [h])))
    rw [h_lt] at hborrow
    simp at hborrow
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2^63 := clz_zero_imp_msb hshift_z
  have hb_nz_or : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hb_pos_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    EvmWord.val256_pos_of_or_ne_zero hb_nz_or
  -- Lower bound qHat ≥ val256(a)/val256(b) (from Div128Shift0).
  have h_algo_ge := div128Quot_shift0_ge_val256_div
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3_ge hb_pos_val
  simp only [] at h_algo_ge
  -- Apply val256_ms_un_eq_val256_mod_of_overestimate to get val256(ms) = val256(a) % val256(b).
  have h_ms_eq_mod := val256_ms_un_eq_val256_mod_of_overestimate
    hb_nz_or h_algo_ge hc3_zero
  simp only [] at h_ms_eq_mod
  -- Bridge to toNat.
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
  rw [ha_val, hb_val] at h_ms_eq_mod
  have hmod_toNat : (EvmWord.mod a b).toNat = a.toNat % b.toNat := by
    unfold EvmWord.mod
    rw [if_neg hbnz]
    exact BitVec.toNat_umod
  set ms := mulsubN4 qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) with hms_def
  set mod_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => ms.1 | 1 => ms.2.1 | 2 => ms.2.2.1 | 3 => ms.2.2.2.1
    with hmod_target
  have hmod_target_toNat : mod_target.toNat = val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := by
    simp [mod_target, EvmWord.fromLimbs_toNat, val256]
  have hmod_eq_ev : mod_target = EvmWord.mod a b :=
    BitVec.eq_of_toNat_eq (by rw [hmod_target_toNat, h_ms_eq_mod, hmod_toNat])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmod_eq_ev]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hmod_eq_ev]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hmod_eq_ev]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod_eq_ev]; exact EvmWord.getLimbN_fromLimbs_3

/-- **EVM-stack-level MOD spec on the n=4 shift=0 call+skip sub-path.**

    MOD counterpart of `evm_div_n4_shift0_call_skip_stack_spec`. Under shift=0
    no normalization is applied, so the mulsub low-4 limbs directly hold the
    MOD result. Semantic correctness follows from `Div128Shift0` + skip-borrow
    giving c3 = 0 + `val256_ms_un_eq_val256_mod_of_overestimate`. -/
theorem evm_mod_n4_shift0_call_skip_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 126 + 12)
      base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  have h_pre := evm_mod_n4_full_shift0_call_skip_stack_pre_spec_bundled sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hborrow
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ :=
    n4_shift0_call_skip_mod_getLimbN a b hbnz hshift_z hborrow
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  unfold fullModN4Shift0CallSkipPost at hq
  apply mod_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
      hmod0 hmod1 hmod2 hmod3]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- **Shift=0 call+addback-BEQ n=4 DIV getLimbN bridge (SCAFFOLD).**

    Under shift=0 + `isAddbackBorrowN4Shift0Evm` (mulsub underflow = c3 ≠ 0)
    + `isAddbackCarry2NzN4Shift0Evm` (BEQ precondition):

    Claim: `q_out = 0 = (EvmWord.div a b).getLimbN 0`, limbs 1-3 = 0.

    Mathematical argument:
    - `qHat = div128Quot 0 a3 b3` satisfies `qHat.toNat ≤ 1` (Div128Shift0
      `le_one`).
    - Borrow fires ⟹ `c3 ≥ 1` ⟹ `qHat * val256(b) > val256(a)` ⟹ `qHat ≥ 1`
      (otherwise `0 * val256(b) = 0 ≤ val256(a)`, no underflow).
    - Combined: `qHat = 1`.
    - `val256(a) < val256(b)` ⟹ `floor(val256(a)/val256(b)) = 0`.
    - Post-first-addback: `q_out = qHat - 1 = 0`, remainder = `val256(a)`.
    - Double-addback branch (`carry = 0`): VACUOUS under shift=0 since
      first-addback's carry = 1 whenever `qHat = 1 ∧ c3 = 1`.

    TODO(#67 follow-up): fill in the proof. The double-addback vacuity is
    the non-trivial step — requires case-splitting on `carry` and deriving
    a contradiction in the `carry = 0` branch via val256 arithmetic. -/
theorem n4_shift0_call_addback_beq_div_getLimbN (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    let qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
                 else qHat + signExtend12 4095
    (EvmWord.div a b).getLimbN 0 = q_out ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  simp only []
  set qHat := div128Quot (0 : Word) (a.getLimbN 3) (b.getLimbN 3) with hqHat_def
  -- Step 1: Extract c3 ≠ 0 from hborrow.
  rw [isAddbackBorrowN4Shift0Evm_def] at hborrow
  unfold isAddbackBorrowN4Shift0 at hborrow
  simp only [] at hborrow
  have hc3_nz : mulsubN4_c3 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) ≠ 0 := by
    intro h_c3_zero
    apply hborrow
    rw [h_c3_zero]
    decide
  -- Step 2: qHat ≤ 1 from Div128Shift0.
  have hb3_ge : (b.getLimbN 3).toNat ≥ 2^63 := clz_zero_imp_msb hshift_z
  have hqHat_le_one : qHat.toNat ≤ 1 := by
    rw [hqHat_def]
    exact div128Quot_shift0_le_one (a.getLimbN 3) (b.getLimbN 3) hb3_ge
  -- Step 3: qHat ≠ 0 (else mulsub c3 = 0, contradicting hc3_nz).
  have hqHat_nz : qHat ≠ 0 := by
    intro h_qHat_zero
    apply hc3_nz
    show (mulsubN4 qHat
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2 = 0
    apply c3_un_zero_of_qHat_mul_le
    rw [h_qHat_zero]
    show (0 : Word).toNat * _ ≤ _
    rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_mul]
    exact Nat.zero_le _
  -- Therefore qHat.toNat = 1.
  have hqHat_eq_one : qHat.toNat = 1 := by
    have h_ne_zero : qHat.toNat ≠ 0 := by
      intro h; apply hqHat_nz; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    omega
  -- Step 4: val256(a) < val256(b) (from mulsub Euclidean + c3 ≠ 0).
  set ms := mulsubN4 qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) with hms_def
  have h_mulsub := mulsubN4_val256_eq qHat
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  simp only [] at h_mulsub
  have hc3_pos : ms.2.2.2.2.toNat ≥ 1 := by
    rcases Nat.eq_zero_or_pos ms.2.2.2.2.toNat with h | h
    · exfalso; apply hc3_nz
      show ms.2.2.2.2 = 0
      apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    · exact h
  have h_val_ms_bound :
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 := EvmWord.val256_bound _ _ _ _
  have h_val_a_lt_b :
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) <
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    -- From h_mulsub: val256(a) + c3*2^256 = val256(ms) + qHat*val256(b)
    -- With qHat.toNat = 1: val256(a) + c3*2^256 = val256(ms) + val256(b).
    -- c3 ≥ 1 and val256(ms) < 2^256 ⟹ val256(a) + 2^256 ≤ val256(ms) + val256(b) < 2^256 + val256(b).
    -- Hence val256(a) < val256(b).
    nlinarith
  -- Step 5: first-addback carry = 1.
  set carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) with hcarry_def
  have h_addback := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  simp only [] at h_addback
  -- Need c3 ≤ 1 to pin c3 = 1. From mulsubN4_c3_le_one with qHat ≤ a/b + 1.
  have hb_nz_or : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hb_pos_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) > 0 :=
    EvmWord.val256_pos_of_or_ne_zero hb_nz_or
  have h_ab_bound :
      val256 (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
             (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
             (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
             (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1 < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  -- From h_mulsub + h_addback: val256(ms) + val256(b) = val256(a) + c3*2^256.
  -- So val256(ab) + carry*2^256 = val256(a) + c3*2^256.
  -- Both c3 and carry are in [0, 2^64) as Words, bounded ≥ 1 (c3) and < some.
  -- Conclude carry ≠ 0: if carry = 0, val256(ab) = val256(a) + c3*2^256 ≥ 2^256. Contradiction.
  have hcarry_nz : carry ≠ 0 := by
    intro h_carry_zero
    have h_carry_toNat : carry.toNat = 0 := by rw [h_carry_zero]; rfl
    -- val256(ms) + val256(b) = val256(ab) + 0 = val256(ab) < 2^256.
    -- But val256(ms) + val256(b) = val256(a) + c3*2^256 ≥ val256(a) + 2^256 ≥ 2^256.
    -- Contradiction.
    have h_ab := h_addback
    rw [h_carry_toNat, Nat.zero_mul, Nat.add_zero] at h_ab
    -- h_ab: val256(ms) + val256(b) = val256(ab)
    -- h_mulsub rearrangement: val256(ms) + val256(b) ≥ val256(a) + 2^256
    have h_pow : (2 : Nat) ^ 256 > 0 := by positivity
    nlinarith
  -- Step 6: q_out = qHat + signExtend12 4095 (single addback branch).
  -- The output's `if carry = 0 then ... else qHat + signExtend12 4095` picks else branch.
  -- q_out.toNat = (1 + (2^64 - 1)) mod 2^64 = 0.
  -- Step 7: (EvmWord.div a b) has all limbs 0.
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
  have hb_pos : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exfalso; apply hbnz; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_a_lt_b : a.toNat < b.toNat := by
    have := h_val_a_lt_b; rw [ha_val, hb_val] at this; exact this
  -- q_out = 0 (via carry ≠ 0, q_out = qHat + signExtend12 4095, qHat = 1).
  have hq_out_eq : (if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
                   else qHat + signExtend12 4095) = (0 : Word) := by
    rw [if_neg hcarry_nz]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hqHat_eq_one, signExtend12_4095_toNat]
    decide
  -- Final step: (EvmWord.div a b) = 0 since a.toNat < b.toNat.
  have hdiv_eq_zero : EvmWord.div a b = 0 := by
    apply BitVec.eq_of_toNat_eq
    unfold EvmWord.div
    rw [if_neg hbnz]
    show (BitVec.udiv a b).toNat = (0 : EvmWord).toNat
    have h_udiv : (BitVec.udiv a b).toNat = a.toNat / b.toNat := by
      show (a / b).toNat = _
      exact BitVec.toNat_udiv
    rw [h_udiv]
    rw [show (0 : EvmWord).toNat = 0 from rfl]
    exact Nat.div_eq_of_lt h_a_lt_b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdiv_eq_zero, EvmWord.getLimbN_zero, hq_out_eq]
  · rw [hdiv_eq_zero]; exact EvmWord.getLimbN_zero _
  · rw [hdiv_eq_zero]; exact EvmWord.getLimbN_zero _
  · rw [hdiv_eq_zero]; exact EvmWord.getLimbN_zero _

/-- **EVM-stack-level DIV spec on the n=4 shift=0 call+addback-BEQ sub-path.**

    Under shift=0 + addback-BEQ conditions, `div a b = 0` (since
    `val256(a) < val256(b)` is forced by borrow firing with qHat ≤ 1).
    Composes pre-spec + bridge + standard reshape. -/
theorem evm_div_n4_shift0_call_addback_beq_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0Evm a b)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 202 + 12)
      base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  have h_pre := evm_div_n4_full_shift0_call_addback_beq_stack_pre_spec_bundled
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hcarry2_nz hborrow
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n4_shift0_call_addback_beq_div_getLimbN a b hbnz hshift_z hborrow
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  unfold fullDivN4Shift0CallAddbackBeqPost at hq
  apply div_n4_call_skip_stack_weaken sp a b h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) _ _ _ _
      hdiv0 hdiv1 hdiv2 hdiv3]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

end EvmAsm.Evm64
