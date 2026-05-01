/-
  EvmAsm.Evm64.DivMod.LoopBody.TrialMax

  Extracted from `LoopBody.lean` (Sections 8a + 11).

  `divK_trial_max_full_spec_within`: full trial-quotient max path —
  save j + trial load + BLTU not-taken + trial_max — composing into a
  single base+448 → base+516 spec when `uHi >= vTop`. Used by every
  `LoopBodyN{1..4}.lean` and the `LoopIterN1.{Max,MaxBeq}` files.

  Also relocates the small `divK_trial_max_extended` helper (Section 8a)
  used only by the full-max spec.

  Uses public helpers from `LoopBody.lean`:
  - `lb_sub`, `lb_bltu_taken`, `lb_bltu_ntaken` (now public, made
    non-`private` for this split).
  - `divK_save_trial_load_spec_within`, `divK_trial_max_spec`.
-/

import EvmAsm.Evm64.DivMod.LoopBody

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem lb_trial_max_end {base : Word} :
    (base + trialMaxOff : Word) + 12 = base + div128CallRetOff := by bv_addr
-- ============================================================================
-- Trial quotient MAX path (Section 8a) — extended to sharedDivModCode
-- Used only by `divK_trial_max_full_spec_within` below.
-- ============================================================================

/-- Trial quotient MAX path: qHat = MAX64, skip div128 call.
    2 instructions at base+504. Entry: base+504, Exit: base+516. -/
private theorem divK_trial_max_extended (v11Old : Word) (base : Word) :
    cpsTripleWithin 2 (base + trialMaxOff) (base + div128CallRetOff) (sharedDivModCode base)
      ((.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ 0))
      ((.x11 ↦ᵣ signExtend12 4095) ** (.x0 ↦ᵣ 0)) := by
  have TM := divK_trial_max_spec_within v11Old (base + trialMaxOff)
  dsimp only [] at TM
  rw [lb_trial_max_end] at TM
  exact cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub 14 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub 15 _ _ (by decide) (by bv_addr) (by decide))) TM

-- ============================================================================
-- Section 11: Trial quotient max path (BLTU not-taken)
-- Composes: save_trial_load → BLTU ntaken → trial_max.
-- Entry: base+448, Exit: base+516 with x11 = MAX64.
-- ============================================================================

/-- Trial quotient max path: save j + load + BLTU not-taken + trial_max.
    When uHi >= vTop, sets qHat = MAX64 without calling div128.
    Entry: base+448, Exit: base+516, CodeReq: sharedDivModCode base. -/
theorem divK_trial_max_full_spec_within
    (sp j n jOld v5Old v6Old v7Old v10Old v11Old uHi uLo vTop : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult uHi vTop) :
    let uAddr := sp + signExtend12 4056 - (j + n) <<< (3 : BitVec 6).toNat
    let vtopBase := sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 16 (base + loopBodyOff) (base + div128CallRetOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
       (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) ** (.x11 ↦ᵣ signExtend12 4095) **
       (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
       (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
       (vtopBase + signExtend12 32 ↦ₘ vTop)) := by
  intro uAddr vtopBase
  -- 1. Save j + trial load (base+448 → base+500)
  have STL := divK_save_trial_load_spec_within sp j n jOld v5Old v6Old v7Old v10Old uHi uLo vTop
    base
  dsimp only [] at STL
  -- 2. BLTU x7 x10 12 at base + trialCallOff
  have hbltu_raw := bltu_spec_gen_within .x7 .x10 (12 : BitVec 13) uHi vTop (base + trialCallOff)
  rw [lb_bltu_taken, lb_bltu_ntaken] at hbltu_raw
  have hbltu_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub 13 _ _ (by decide) (by bv_addr) (by decide)) hbltu_raw
  -- Eliminate taken path (⌜BitVec.ult uHi vTop⌝ contradicts hbltu)
  have ntaken := cpsBranchWithin_ntakenPath hbltu_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hbltu hpure)
  -- Strip pure fact
  have ntaken_clean := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp) ntaken
  -- 3. Trial max (base+504 → base+516)
  have TM := divK_trial_max_extended v11Old base
  -- 4. Frame save_trial_load with x11 + x0, compose with BLTU ntaken
  have STLf := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) STL
  have ntaken_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) ntaken_clean
  have STLfntaken_clean := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLf ntaken_framed
  -- 5. Frame BLTU ntaken result with x0 + memory, compose with trial_max
  have TMf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
     (.x5 ↦ᵣ uLo) ** (.x6 ↦ᵣ vtopBase) **
     (.x7 ↦ᵣ uHi) ** (.x10 ↦ᵣ vTop) **
     (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ n) **
     (uAddr ↦ₘ uHi) ** ((uAddr + 8) ↦ₘ uLo) **
     (vtopBase + signExtend12 32 ↦ₘ vTop))
    (by pcFree) TM
  have STLfntaken_cleanTM := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) STLfntaken_clean TMf
  -- 6. Final permutation
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    STLfntaken_cleanTM

end EvmAsm.Evm64
