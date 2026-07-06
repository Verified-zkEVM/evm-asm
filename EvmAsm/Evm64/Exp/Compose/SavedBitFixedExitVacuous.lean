/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedExitVacuous

  The standard merged exit post is unsatisfiable at the block-3 anchored
  pointer `ptr = evmSp + signExtend12 (-(16 + 8*3)) = evmSp + se(-40)`.

  Every branch of `expTwoMulFixedIterMergedExitPost` owns *two* memory cells at
  `evmSp + se(-40)`: the base-frame `a3` cell and the reload/pointer cell
  `(ptr + se0) ↦ nextLimb` (which aliases it when `ptr` is the anchor).  Since a
  separating conjunction forces the two owners onto disjoint sub-states, the
  exit post collapses to `False`.

  This is exactly the discharge the final chain's `hExitU` needs (the standard
  induction hands off to the relaxed block-3 induction at the b=2 boundary, so
  the standard exit is only ever invoked at this anchored pointer), avoiding a
  full standard 4-branch merged exit bridge.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterExits
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePosts
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpResidual
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpReadPrefix

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- An assertion "owns" memory address `a` if every state satisfying it has
    `a` present in memory. -/
private def OwnsMem (P : Assertion) (a : Word) : Prop :=
  ∀ ps, P ps → ps.mem a ≠ none

private theorem memIs_ownsMem (a v : Word) : OwnsMem (a ↦ₘ v) a := by
  intro ps hps
  obtain ⟨he, _⟩ := hps
  subst he
  simp [PartialState.singletonMem]

private theorem memOwn_ownsMem (a : Word) : OwnsMem (memOwn a) a := by
  intro ps hps
  obtain ⟨v, he, _⟩ := hps
  subst he
  simp [PartialState.singletonMem]

private theorem ownsMem_congr {P : Assertion} {a a' : Word}
    (h : a = a') (hP : OwnsMem P a) : OwnsMem P a' := h ▸ hP

private theorem sepConj_ownsMem_left {P Q : Assertion} {a : Word}
    (hP : OwnsMem P a) : OwnsMem (P ** Q) a := by
  intro ps hps
  obtain ⟨h1, h2, _hd, hu, hp1, _⟩ := hps
  subst hu
  intro hcontra
  have h1n : h1.mem a ≠ none := hP h1 hp1
  apply h1n
  simp only [PartialState.union] at hcontra
  rcases hh : h1.mem a with _ | v
  · rfl
  · rw [hh] at hcontra; exact absurd hcontra (by simp)

private theorem sepConj_ownsMem_right {P Q : Assertion} {a : Word}
    (hQ : OwnsMem Q a) : OwnsMem (P ** Q) a := by
  intro ps hps
  obtain ⟨h1, h2, _hd, hu, _, hq2⟩ := hps
  subst hu
  intro hcontra
  have h2n : h2.mem a ≠ none := hQ h2 hq2
  apply h2n
  simp only [PartialState.union] at hcontra
  rcases hh : h1.mem a with _ | v
  · rw [hh] at hcontra; exact hcontra
  · -- h1.mem a = some v, but union gives some v ≠ none, contradiction with hcontra
    rw [hh] at hcontra; exact absurd hcontra (by simp)

private theorem or_ownsMem {A B : Assertion} {a : Word}
    (hA : OwnsMem A a) (hB : OwnsMem B a) :
    OwnsMem (fun h => A h ∨ B h) a := by
  intro ps hps
  rcases hps with h | h
  · exact hA ps h
  · exact hB ps h

private theorem sepConj_ownsMem_collision {P Q : Assertion} {a : Word}
    {ps : PartialState} (hP : OwnsMem P a) (hQ : OwnsMem Q a)
    (h : (P ** Q) ps) : False := by
  obtain ⟨h1, h2, hd, _, hp1, hq2⟩ := h
  rcases hd.2.1 a with h1n | h2n
  · exact hP h1 hp1 h1n
  · exact hQ h2 hq2 h2n

-- Per-named-def OwnsMem facts.  Each unfolds exactly one abbrev, then walks a
-- fixed path (right past earlier conjuncts, then left into the target cell) so
-- elaboration depth stays at the path length — no backtracking search.

private theorem baseFrame_ownsMem (evmSp a0 a1 a2 a3 : Word) :
    OwnsMem (expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3)
      (evmSp + signExtend12 (-40 : BitVec 12)) := by
  unfold expTwoMulFixedIterBaseFrame
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; exact memIs_ownsMem _ _

private theorem pointerPost_ownsMem (ptr nextLimb : Word) :
    OwnsMem (expTwoMulFixedIterPointerPost ptr nextLimb)
      (ptr + signExtend12 (0 : BitVec 12)) := by
  unfold expTwoMulFixedIterPointerPost
  apply sepConj_ownsMem_right; exact memIs_ownsMem _ _

private theorem skipCondRest_ownsMem
    (sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word) :
    OwnsMem (expTwoMulFixedIterSkipCondRest sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base)
      (evmSp + signExtend12 (-40 : BitVec 12)) := by
  unfold expTwoMulFixedIterSkipCondRest
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_left; exact memIs_ownsMem _ _

private theorem reloadCondFrame_ownsMem (e c6 ptr nextLimb : Word) :
    OwnsMem (expTwoMulFixedIterReloadCondFrame e c6 ptr nextLimb)
      (ptr + signExtend12 (0 : BitVec 12)) := by
  unfold expTwoMulFixedIterReloadCondFrame
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_left
  exact memIs_ownsMem _ _

private theorem reloadSkipRest_ownsMem
    (e c6 ptr nextLimb sp evmSp r0 r1 r2 r3 base : Word) :
    OwnsMem (expTwoMulFixedIterReloadSkipRest e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 base)
      (ptr + signExtend12 (0 : BitVec 12)) := by
  unfold expTwoMulFixedIterReloadSkipRest
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_right
  apply sepConj_ownsMem_right; apply sepConj_ownsMem_left
  exact memIs_ownsMem _ _

/-- The standard merged exit post is unsatisfiable whenever the reload/pointer
    cell `(ptr + se0)` aliases the base-frame `a3` cell at `evmSp + se(-40)`
    (which holds at the block-3 anchored pointer).  Every one of the four
    branches owns a memory cell at `evmSp + se(-40)` twice (base `a3` plus the
    pointer cell), so the separating conjunction collapses to `False`. -/
theorem expTwoMulFixedIterMergedExitPost_collision_false
    {e c6 iterCount ptr nextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {ps : PartialState}
    (hptr : ptr + signExtend12 (0 : BitVec 12)
      = evmSp + signExtend12 (-40 : BitVec 12))
    (h : expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps) : False := by
  rw [expTwoMulFixedIterMergedExitPost_eq_caseExitPost] at h
  unfold expTwoMulFixedIterCaseExitPost at h
  rcases h with hSkip | hReload
  · -- skip exit: (SkipCondCountPost ∨ SkipCountPost) ** PointerPost
    unfold expTwoMulFixedIterSkipExitPost at hSkip
    refine sepConj_ownsMem_collision
      (a := evmSp + signExtend12 (-40 : BitVec 12)) ?_
      (ownsMem_congr hptr (pointerPost_ownsMem _ _)) hSkip
    apply or_ownsMem
    · -- SkipCondCountPost owns a3 (inside SkipCondRest)
      unfold expTwoMulFixedIterSkipCondCountPost
      exact sepConj_ownsMem_left
        (sepConj_ownsMem_right (skipCondRest_ownsMem _ _ _ _ _ _ _ _ _ _ _))
    · -- SkipCountPost owns a3 (inside BaseFrame)
      unfold expTwoMulFixedIterSkipCountPost
      exact sepConj_ownsMem_right (baseFrame_ownsMem _ _ _ _ _)
  · unfold expTwoMulFixedIterReloadExitPost at hReload
    rcases hReload with hCond | hSkip2
    · -- ReloadCondCountPost: (x9pkg ** SkipCondRest) ** ReloadCondFrame
      unfold expTwoMulFixedIterReloadCondCountPost at hCond
      refine sepConj_ownsMem_collision
        (a := evmSp + signExtend12 (-40 : BitVec 12))
        (sepConj_ownsMem_right (skipCondRest_ownsMem _ _ _ _ _ _ _ _ _ _ _))
        (ownsMem_congr hptr (reloadCondFrame_ownsMem _ _ _ _)) hCond
    · -- ReloadSkipCountPost: (x9pkg ** ReloadSkipRest) ** BaseFrame
      unfold expTwoMulFixedIterReloadSkipCountPost at hSkip2
      refine sepConj_ownsMem_collision
        (a := evmSp + signExtend12 (-40 : BitVec 12))
        (ownsMem_congr hptr
          (sepConj_ownsMem_right (reloadSkipRest_ownsMem _ _ _ _ _ _ _ _ _ _ _)))
        (baseFrame_ownsMem _ _ _ _ _) hSkip2

end EvmAsm.Evm64.Exp.Compose
