/-
  EvmAsm.Evm64.DivMod.Spec.CallablePost

  Reusable postcondition weakeners for callable DIV/MOD no-NOP dispatcher
  surfaces that frame exact x1/x9 separately.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.Dispatcher

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Public no-NOP DIV callable post with exact caller-framed `x1` and `x9`.
    This is the target surface needed by SDIV's callable handoff. -/
@[irreducible]
def divStackDispatchPostCallableExactFrame
    (sp : Word) (a b : EvmWord) (raVal x9Val : Word) : Assertion :=
  (divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
    (.x9 ↦ᵣ x9Val)

theorem divStackDispatchPostCallableExactFrame_unfold
    {sp : Word} {a b : EvmWord} {raVal x9Val : Word} :
    divStackDispatchPostCallableExactFrame sp a b raVal x9Val =
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  delta divStackDispatchPostCallableExactFrame
  rfl

theorem divStackDispatchPostCallableExactFrame_pcFree
    (sp : Word) (a b : EvmWord) (raVal x9Val : Word) :
    (divStackDispatchPostCallableExactFrame sp a b raVal x9Val).pcFree := by
  rw [divStackDispatchPostCallableExactFrame_unfold,
    divStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold]
  pcFree

/-- Concrete no-NOP DIV callable post bundle produced by the bzero and
    branch-local dispatcher proofs before weakening to the public callable
    postcondition. -/
@[irreducible]
def divConcretePostNoX1Frame (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v6 v7 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
    (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
   ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
      evmWordIs sp a **
      divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0))

theorem divConcretePostNoX1Frame_unfold
    {sp : Word} {a b : EvmWord}
    {x9Val raVal v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
    (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
     ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
        evmWordIs sp a **
        divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)) := by
  delta divConcretePostNoX1Frame
  rfl

theorem divConcretePostNoX1Frame_pcFree
    (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v6 v7 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  rw [divConcretePostNoX1Frame_unfold, divScratchValuesCallNoX1_unfold,
    divScratchValues_unfold]
  pcFree

/-- Concrete no-NOP DIV callable post bundle before weakening, preserving
    exact values for `x5` and `x10` as produced by full-path proofs. -/
@[irreducible]
def divConcretePostNoX1ExactRegsFrame (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
    (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
   ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
      evmWordIs sp a **
      divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0))

theorem divConcretePostNoX1ExactRegsFrame_unfold
    {sp : Word} {a b : EvmWord}
    {x9Val raVal v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    divConcretePostNoX1ExactRegsFrame sp a b x9Val raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
    (((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
     ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
        evmWordIs sp a **
        divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)) := by
  delta divConcretePostNoX1ExactRegsFrame
  rfl

theorem divConcretePostNoX1ExactRegsFrame_pcFree
    (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (divConcretePostNoX1ExactRegsFrame sp a b x9Val raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  rw [divConcretePostNoX1ExactRegsFrame_unfold, divScratchValuesCallNoX1_unfold,
    divScratchValues_unfold]
  pcFree

/-- Weaken the exact-register concrete no-NOP DIV callable post bundle to the
    public callable postcondition plus caller-framed exact `x1` and `x9`. -/
theorem divConcretePostNoX1ExactRegs_weaken_callable_frame
    (sp : Word) (a b : EvmWord)
    {x9Val raVal v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h : PartialState,
      divConcretePostNoX1ExactRegsFrame sp a b x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 h →
      (((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) h) := by
  intro h hp
  rw [divConcretePostNoX1ExactRegsFrame_unfold] at hp
  rw [divStackDispatchPostCallable_unfold]
  simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢
  have hOwn :
      (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** regOwn .x10 ** regOwn .x11 **
        (.x12 ↦ᵣ (sp + 32)) ** regOwn .x2 ** regOwn .x5 **
        regOwn .x6 ** regOwn .x7 ** (.x9 ↦ᵣ x9Val) **
        evmWordIs (sp + 32) (EvmWord.div a b)) h := by
    refine sepConj_mono ?_ ?_ h hp
    · intro hLeft hpLeft
      exact divScratchValuesCallNoX1_implies_divScratchOwnCallNoX1
        sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
          retMem dMem dloMem scratch_un0 hLeft hpLeft
    · apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x10 (v := v10))
      apply sepConj_mono (regIs_implies_regOwn .x11 (v := v11))
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x2 (v := v2))
      apply sepConj_mono (regIs_implies_regOwn .x5 (v := v5))
      apply sepConj_mono (regIs_implies_regOwn .x6 (v := v6))
      apply sepConj_mono (regIs_implies_regOwn .x7 (v := v7))
      exact fun _ hp => hp
  exact by xperm_hyp hOwn

/-- Weaken the concrete no-NOP DIV callable post bundle to the public
    callable postcondition plus the caller-framed exact `x1` and `x9` atoms. -/
theorem divConcretePostNoX1_weaken_callable_frame
    (sp : Word) (a b : EvmWord)
    {x9Val raVal v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h : PartialState,
      divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 h →
      (((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) h) := by
  intro h hp
  rw [divConcretePostNoX1Frame_unfold] at hp
  rw [divStackDispatchPostCallable_unfold]
  simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢
  have hOwn :
      (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** regOwn .x11 ** (.x12 ↦ᵣ (sp + 32)) **
        regOwn .x2 ** regOwn .x6 ** regOwn .x7 ** (.x9 ↦ᵣ x9Val) **
        regOwn .x10 ** regOwn .x5 ** evmWordIs (sp + 32) (EvmWord.div a b)) h := by
    refine sepConj_mono ?_ ?_ h hp
    · intro hLeft hpLeft
      exact divScratchValuesCallNoX1_implies_divScratchOwnCallNoX1
        sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
          retMem dMem dloMem scratch_un0 hLeft hpLeft
    · apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x11 (v := v11))
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x2 (v := v2))
      apply sepConj_mono (regIs_implies_regOwn .x6 (v := v6))
      apply sepConj_mono (regIs_implies_regOwn .x7 (v := v7))
      exact fun _ hp => hp
  exact by xperm_hyp hOwn

/-- Split the historical no-`x1` DIV stack post into the callable public post
    plus separate `x1` ownership. This is the ownership-only bridge; exact
    return-address preservation requires a stronger upstream post. -/
theorem divStackDispatchPostNoX1_weaken_callable_own_x1
    (sp : Word) (a b : EvmWord) :
  ∀ h : PartialState,
      divStackDispatchPostNoX1 sp a b h →
      (divStackDispatchPostCallable sp a b ** regOwn .x1) h := by
  intro h hp
  rw [divStackDispatchPostNoX1_unfold] at hp
  rw [divStackDispatchPostCallable_unfold]
  rw [divScratchOwnCall_unfold] at hp
  rw [divScratchOwnCallNoX1_unfold]
  xperm_hyp hp

/-- Framed variant of `divStackDispatchPostNoX1_weaken_callable_own_x1`
    preserving an exact caller-owned `x9` atom. -/
theorem divStackDispatchPostNoX1_weaken_callable_own_x1_frame_x9
    (sp : Word) (a b : EvmWord) (x9Val : Word) :
  ∀ h : PartialState,
      (divStackDispatchPostNoX1 sp a b ** (.x9 ↦ᵣ x9Val)) h →
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ x9Val)) h := by
  intro h hp
  apply sepConj_mono_left
  · exact fun hLeft hpLeft =>
      divStackDispatchPostNoX1_weaken_callable_own_x1 sp a b hLeft hpLeft
  · exact hp

/-- Weaken an exact caller-framed `x1` callable post to the ownership-only
    callable post shape, preserving an exact caller-owned `x9` atom. -/
theorem divStackDispatchPostCallable_exact_x1_weaken_own_x1_frame_x9
    (sp : Word) (a b : EvmWord) (raVal x9Val : Word) :
  ∀ h : PartialState,
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) h →
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ x9Val)) h := by
  intro h hp
  exact sepConj_mono_left
    (sepConj_mono_right (regIs_implies_regOwn .x1 (v := raVal)))
    h hp

/-- Weaken the named exact callable DIV post frame to the ownership-only
    callable post shape. -/
theorem divStackDispatchPostCallableExactFrame_weaken_own_x1_frame_x9
    (sp : Word) (a b : EvmWord) (raVal x9Val : Word) :
  ∀ h : PartialState,
      divStackDispatchPostCallableExactFrame sp a b raVal x9Val h →
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ x9Val)) h := by
  intro h hp
  rw [divStackDispatchPostCallableExactFrame_unfold] at hp
  exact divStackDispatchPostCallable_exact_x1_weaken_own_x1_frame_x9
    sp a b raVal x9Val h hp

/-- Public no-NOP MOD callable post with exact caller-framed `x1` and `x9`.
    This mirrors `divStackDispatchPostCallableExactFrame` for MOD callers. -/
@[irreducible]
def modStackDispatchPostCallableExactFrame
    (sp : Word) (a b : EvmWord) (raVal x9Val : Word) : Assertion :=
  (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
    (.x9 ↦ᵣ x9Val)

theorem modStackDispatchPostCallableExactFrame_unfold
    {sp : Word} {a b : EvmWord} {raVal x9Val : Word} :
    modStackDispatchPostCallableExactFrame sp a b raVal x9Val =
      ((modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  delta modStackDispatchPostCallableExactFrame
  rfl

theorem modStackDispatchPostCallableExactFrame_pcFree
    (sp : Word) (a b : EvmWord) (raVal x9Val : Word) :
    (modStackDispatchPostCallableExactFrame sp a b raVal x9Val).pcFree := by
  rw [modStackDispatchPostCallableExactFrame_unfold,
    modStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold]
  pcFree

/-- Concrete no-NOP MOD callable post bundle before weakening. -/
@[irreducible]
def modConcretePostNoX1Frame (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v6 v7 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
    (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) **
   ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
      evmWordIs sp a **
      divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0))

theorem modConcretePostNoX1Frame_unfold
    {sp : Word} {a b : EvmWord}
    {x9Val raVal v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    modConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
    (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) **
     ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
      evmWordIs sp a **
      divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)) := by
  delta modConcretePostNoX1Frame
  rfl

theorem modConcretePostNoX1Frame_pcFree
    (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v6 v7 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (modConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  rw [modConcretePostNoX1Frame_unfold, divScratchValuesCallNoX1_unfold,
    divScratchValues_unfold]
  pcFree

/-- Concrete no-NOP MOD callable post bundle before weakening, preserving
    exact values for `x5` and `x10` as produced by full-path proofs. -/
@[irreducible]
def modConcretePostNoX1ExactRegsFrame (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
    (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) **
   ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
      evmWordIs sp a **
      divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0))

theorem modConcretePostNoX1ExactRegsFrame_unfold
    {sp : Word} {a b : EvmWord}
    {x9Val raVal v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    modConcretePostNoX1ExactRegsFrame sp a b x9Val raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
    (((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) **
     ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
        evmWordIs sp a **
        divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)) := by
  delta modConcretePostNoX1ExactRegsFrame
  rfl

theorem modConcretePostNoX1ExactRegsFrame_pcFree
    (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (modConcretePostNoX1ExactRegsFrame sp a b x9Val raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  rw [modConcretePostNoX1ExactRegsFrame_unfold, divScratchValuesCallNoX1_unfold,
    divScratchValues_unfold]
  pcFree

/-- Weaken the exact-register concrete no-NOP MOD callable post bundle to the
    public callable postcondition plus caller-framed exact `x1` and `x9`. -/
theorem modConcretePostNoX1ExactRegs_weaken_callable_frame
    (sp : Word) (a b : EvmWord)
    {x9Val raVal v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h : PartialState,
      modConcretePostNoX1ExactRegsFrame sp a b x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 h →
      (((modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) h) := by
  intro h hp
  rw [modConcretePostNoX1ExactRegsFrame_unfold] at hp
  rw [modStackDispatchPostCallable_unfold]
  simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢
  have hOwn :
      (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** regOwn .x10 ** regOwn .x11 **
        (.x12 ↦ᵣ (sp + 32)) ** regOwn .x2 ** regOwn .x5 **
        regOwn .x6 ** regOwn .x7 ** (.x9 ↦ᵣ x9Val) **
        evmWordIs (sp + 32) (EvmWord.mod a b)) h := by
    refine sepConj_mono ?_ ?_ h hp
    · intro hLeft hpLeft
      exact divScratchValuesCallNoX1_implies_divScratchOwnCallNoX1
        sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
          retMem dMem dloMem scratch_un0 hLeft hpLeft
    · apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x10 (v := v10))
      apply sepConj_mono (regIs_implies_regOwn .x11 (v := v11))
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x2 (v := v2))
      apply sepConj_mono (regIs_implies_regOwn .x5 (v := v5))
      apply sepConj_mono (regIs_implies_regOwn .x6 (v := v6))
      apply sepConj_mono (regIs_implies_regOwn .x7 (v := v7))
      exact fun _ hp => hp
  exact by xperm_hyp hOwn

/-- MOD counterpart of `divConcretePostNoX1_weaken_callable_frame`. -/
theorem modConcretePostNoX1_weaken_callable_frame
    (sp : Word) (a b : EvmWord)
    {x9Val raVal v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h : PartialState,
      modConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 h →
      (((modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) h) := by
  intro h hp
  rw [modConcretePostNoX1Frame_unfold] at hp
  rw [modStackDispatchPostCallable_unfold]
  simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢
  have hOwn :
      (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** regOwn .x11 ** (.x12 ↦ᵣ (sp + 32)) **
        regOwn .x2 ** regOwn .x6 ** regOwn .x7 ** (.x9 ↦ᵣ x9Val) **
        regOwn .x10 ** regOwn .x5 ** evmWordIs (sp + 32) (EvmWord.mod a b)) h := by
    refine sepConj_mono ?_ ?_ h hp
    · intro hLeft hpLeft
      exact divScratchValuesCallNoX1_implies_divScratchOwnCallNoX1
        sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
          retMem dMem dloMem scratch_un0 hLeft hpLeft
    · apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x11 (v := v11))
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x2 (v := v2))
      apply sepConj_mono (regIs_implies_regOwn .x6 (v := v6))
      apply sepConj_mono (regIs_implies_regOwn .x7 (v := v7))
      exact fun _ hp => hp
  exact by xperm_hyp hOwn

/-- Split the historical no-`x1` MOD stack post into the callable public post
    plus separate `x1` ownership. This mirrors
    `divStackDispatchPostNoX1_weaken_callable_own_x1`. -/
theorem modStackDispatchPostNoX1_weaken_callable_own_x1
    (sp : Word) (a b : EvmWord) :
  ∀ h : PartialState,
      modStackDispatchPostNoX1 sp a b h →
      (modStackDispatchPostCallable sp a b ** regOwn .x1) h := by
  intro h hp
  rw [modStackDispatchPostNoX1_unfold] at hp
  rw [modStackDispatchPostCallable_unfold]
  rw [divScratchOwnCall_unfold] at hp
  rw [divScratchOwnCallNoX1_unfold]
  xperm_hyp hp

/-- Framed variant of `modStackDispatchPostNoX1_weaken_callable_own_x1`
    preserving an exact caller-owned `x9` atom. -/
theorem modStackDispatchPostNoX1_weaken_callable_own_x1_frame_x9
    (sp : Word) (a b : EvmWord) (x9Val : Word) :
  ∀ h : PartialState,
      (modStackDispatchPostNoX1 sp a b ** (.x9 ↦ᵣ x9Val)) h →
      ((modStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ x9Val)) h := by
  intro h hp
  apply sepConj_mono_left
  · exact fun hLeft hpLeft =>
      modStackDispatchPostNoX1_weaken_callable_own_x1 sp a b hLeft hpLeft
  · exact hp

end EvmAsm.Evm64
