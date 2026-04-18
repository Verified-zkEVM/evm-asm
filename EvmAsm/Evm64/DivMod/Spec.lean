/-
  EvmAsm.Evm64.DivMod.Spec

  Stack-level specs for the 256-bit EVM DIV and MOD programs using evmWordIs.

  Currently covers:
  - Zero divisor path (b = 0): evm_div_bzero_stack_spec, evm_mod_bzero_stack_spec
  - Normal path (b ≠ 0): TODO (needs semantic correctness bridge: EvmWord.div_correct / mod_correct)
-/

import EvmAsm.Evm64.DivMod.Compose
import EvmAsm.Evm64.DivMod.Compose.FullPathN4
import EvmAsm.Evm64.EvmWordArith

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- EvmWord-level runtime condition predicates for the n=4 max path
-- ============================================================================

-- The full-path DIV spec `evm_div_n4_full_max_skip_spec` takes runtime
-- conditions (`isMaxTrialN4`, `isSkipBorrowN4Max`) keyed off eight Word
-- limbs. For the EvmWord-level stack spec, it's more natural to express
-- these on `a b : EvmWord` directly — the wrappers below defer to the
-- Word-level predicates via `a.getLimbN k` / `b.getLimbN k`.

/-- Max trial quotient condition at n=4 in EvmWord form: `u4 ≥ b3'` after
    normalization, i.e., the algorithm uses the maximum trial quotient
    (`signExtend12 4095 = 2^64 - 1`). -/
def isMaxTrialN4Evm (a b : EvmWord) : Prop :=
  isMaxTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)

/-- Skip-addback condition at n=4 max in EvmWord form: the runtime borrow
    check `u4 < mulsubN4_c3` does not fire, so the algorithm skips the
    addback step and uses `q_hat` as the quotient digit. -/
def isSkipBorrowN4MaxEvm (a b : EvmWord) : Prop :=
  isSkipBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isMaxTrialN4Evm_def (a b : EvmWord) :
    isMaxTrialN4Evm a b =
    isMaxTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) := rfl

theorem isSkipBorrowN4MaxEvm_def (a b : EvmWord) :
    isSkipBorrowN4MaxEvm a b =
    isSkipBorrowN4Max (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

-- ============================================================================
-- Stack-level post state for n=4 max-skip DIV
-- ============================================================================

/-- Stack-level postcondition shape for the n=4 DIV max+skip path.

    * `.x12 ↦ᵣ (sp+32)` — EVM stack pointer advanced past the popped second operand.
    * `regOwn` for every scratch register the program touches (`x1, x2, x5, x6,
      x7, x10, x11`). Caller has ownership but no knowledge of the final values.
    * `.x0 ↦ᵣ 0` — the zero register is preserved.
    * `evmWordIs sp a` — first operand preserved at its original location.
    * `evmWordIs (sp+32) (EvmWord.div a b)` — DIV result written over the second
      operand slot.
    * `divScratchOwn sp` — ownership of all 15 scratch cells, values unspecified.

    Paired with the forthcoming `evm_div_n4_max_skip_stack_spec` and derived
    from the concrete `fullDivN4MaxSkipPost` via the `n4_max_skip_div_mod_getLimbN`
    semantic bridge + `divScratchValues_implies_divScratchOwn` weakener. -/
def divN4MaxSkipStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
  divScratchOwn sp

-- ============================================================================
-- DIV: Zero divisor stack spec (b = 0 → result = 0)
-- ============================================================================

/-- Stack-level DIV spec for the zero divisor path: when b = 0, result is 0.
    Uses evmWordIs for the b-operand at sp+32. The a-operand at sp is untouched. -/
theorem evm_div_bzero_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.div a b)) := by
  subst hbz
  -- Normalize (0 : EvmWord).getLimb k to (0 : Word)
  have hg0 : (0 : EvmWord).getLimbN 0 = (0 : Word) := by decide
  have hg1 : (0 : EvmWord).getLimbN 1 = (0 : Word) := by decide
  have hg2 : (0 : EvmWord).getLimbN 2 = (0 : Word) := by decide
  have hg3 : (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  -- Get the limb-level zero-path spec
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have h_raw := evm_div_bzero_spec sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  -- Bridge: div a 0 = 0, getLimb (div a 0) k = 0
  have hr0 : (EvmWord.div a 0).getLimbN 0 = 0 := EvmWord.div_getLimb_zero_right a 0
  have hr1 : (EvmWord.div a 0).getLimbN 1 = 0 := EvmWord.div_getLimb_zero_right a 1
  have hr2 : (EvmWord.div a 0).getLimbN 2 = 0 := EvmWord.div_getLimb_zero_right a 2
  have hr3 : (EvmWord.div a 0).getLimbN 3 = 0 := EvmWord.div_getLimb_zero_right a 3
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

-- ============================================================================
-- MOD: Zero divisor stack spec (b = 0 → result = 0)
-- ============================================================================

/-- Stack-level MOD spec for the zero divisor path: when b = 0, result is 0.
    Uses evmWordIs for the b-operand at sp+32. The a-operand at sp is untouched. -/
theorem evm_mod_bzero_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.mod a b)) := by
  subst hbz
  have hg0 : (0 : EvmWord).getLimbN 0 = (0 : Word) := by decide
  have hg1 : (0 : EvmWord).getLimbN 1 = (0 : Word) := by decide
  have hg2 : (0 : EvmWord).getLimbN 2 = (0 : Word) := by decide
  have hg3 : (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by decide
  have h_raw := evm_mod_bzero_spec sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or
  simp only [hg0, hg1, hg2, hg3] at h_raw
  have hr0 : (EvmWord.mod a 0).getLimbN 0 = 0 := EvmWord.mod_getLimb_zero_right a 0
  have hr1 : (EvmWord.mod a 0).getLimbN 1 = 0 := EvmWord.mod_getLimb_zero_right a 1
  have hr2 : (EvmWord.mod a 0).getLimbN 2 = 0 := EvmWord.mod_getLimb_zero_right a 2
  have hr3 : (EvmWord.mod a 0).getLimbN 3 = 0 := EvmWord.mod_getLimb_zero_right a 3
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      rw [evmWordIs_sp32_limbs_eq sp 0 0 0 0 0 hg0 hg1 hg2 hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      rw [evmWordIs_sp32_limbs_eq sp _ 0 0 0 0 hr0 hr1 hr2 hr3]
      have w0 := sepConj_mono_left (regIs_implies_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

end EvmAsm.Evm64
