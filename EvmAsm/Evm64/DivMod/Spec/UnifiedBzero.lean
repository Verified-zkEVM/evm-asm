/-
  EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

  Unified-bound zero-divisor DIV/MOD dispatcher wrappers. This file owns the
  shared bound used by the valid n=1, n=2, and n=3 dispatcher-surface specs.
  The n=4 stack-surface path is intentionally absent while the call-addback
  algorithm is being repaired.

  This file owns `unifiedDivBound : Nat := 946` and the zero-divisor dispatcher wrappers shared by the unified stack specs.

  Pre/post are unchanged; the proof is a single `cpsTripleWithin_mono_nSteps`
  application with `by decide` for the bound inequality.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

  Refs: GH #61, beads `evm-asm-unta` (parent `evm-asm-4keh`, grandparent
  `evm-asm-pb40`).
-/

module

public import EvmAsm.Evm64.DivMod.Spec.Dispatcher
public import EvmAsm.Evm64.DivMod.Spec.N2DivStackSpec
public import EvmAsm.Evm64.DivMod.Spec.N2ModStackSpec
public import EvmAsm.Evm64.DivMod.Spec.N3DivStackSpec
public import EvmAsm.Evm64.DivMod.Spec.N3ModBridge
public import EvmAsm.Evm64.DivMod.Spec.CallablePost

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Unified `cpsTripleWithin` step bound for the dispatcher-surface DIV/MOD
specs across n ∈ {1,2,3,4}. The maximum of the per-`n` bounds:
n=1 = 946, n=2 = 744, n=3 = 542, n=4 = 340. The `_uni` wrappers below lift
each per-`n` spec to this bound via `cpsTripleWithin_mono_nSteps`, so a future
`evm_div_stack_spec` / `evm_mod_stack_spec` can case-split on `n` without
incompatible `nSteps` between branches. -/
def unifiedDivBound : Nat := 946

theorem divStackDispatchPost_weaken_bzero_frame
    (sp : Word) (a b : EvmWord)
    {v1 v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       regOwn .x5 ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       regOwn .x10 ** (.x11 ↦ᵣ v11) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
       divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0) h →
      divStackDispatchPost sp a b h := by
  intro h hp
  delta divStackDispatchPost
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn .x9 (v := v1))
  apply sepConj_mono (regIs_implies_regOwn .x2 (v := v2))
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn .x6 (v := v6))
  apply sepConj_mono (regIs_implies_regOwn .x7 (v := v7))
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn .x11 (v := v11))
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValuesCall_implies_divScratchOwnCall
    sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
      retMem dMem dloMem scratch_un0
  exact hp

theorem evm_div_bzero_stack_spec_within_dispatch_uni (sp base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x11 ↦ᵣ v11) ** evmWordIs sp a **
    divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_div_bzero_stack_spec_within sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (divCode base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCall_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPre_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun _ hq => by
        dsimp [frame] at hq
        refine divStackDispatchPost_weaken_bzero_frame (sp := sp) (a := a) (b := b)
          (v1 := v1) (v2 := v2) (v6 := v6) (v7 := v7) (v11 := v11)
          (q0 := q0) (q1 := q1) (q2 := q2) (q3 := q3)
          (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
          (u4 := u4) (u5 := u5) (u6 := u6) (u7 := u7)
          (shiftMem := shiftMem) (nMem := nMem) (jMem := jMem)
          (retMem := retMem) (dMem := dMem) (dloMem := dloMem)
          (scratch_un0 := scratch_un0) _ ?_
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        exact hq)
      hFramed

theorem evm_div_bzero_stack_spec_within_dispatch_noNop_uni (sp base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x11 ↦ᵣ v11) ** evmWordIs sp a **
    divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_div_bzero_stack_spec_within_noNop sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (divCode_noNop base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCall_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPre_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun _ hq => by
        dsimp [frame] at hq
        refine divStackDispatchPost_weaken_bzero_frame (sp := sp) (a := a) (b := b)
          (v1 := v1) (v2 := v2) (v6 := v6) (v7 := v7) (v11 := v11)
          (q0 := q0) (q1 := q1) (q2 := q2) (q3 := q3)
          (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
          (u4 := u4) (u5 := u5) (u6 := u6) (u7 := u7)
          (shiftMem := shiftMem) (nMem := nMem) (jMem := jMem)
          (retMem := retMem) (dMem := dMem) (dloMem := dloMem)
          (scratch_un0 := scratch_un0) _ ?_
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        exact hq)
      hFramed

/-- v4 zero-divisor DIV dispatcher over the shared no-NOP code surface. -/
theorem evm_div_bzero_stack_spec_within_dispatch_noNop_v4_uni (sp base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
      (divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x11 ↦ᵣ v11) ** evmWordIs sp a **
    divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_div_bzero_stack_spec_within_noNop_v4 sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCall_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPre_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun _ hq => by
        dsimp [frame] at hq
        refine divStackDispatchPost_weaken_bzero_frame (sp := sp) (a := a) (b := b)
          (v1 := v1) (v2 := v2) (v6 := v6) (v7 := v7) (v11 := v11)
          (q0 := q0) (q1 := q1) (q2 := q2) (q3 := q3)
          (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
          (u4 := u4) (u5 := u5) (u6 := u6) (u7 := u7)
          (shiftMem := shiftMem) (nMem := nMem) (jMem := jMem)
          (retMem := retMem) (dMem := dMem) (dloMem := dloMem)
          (scratch_un0 := scratch_un0) _ ?_
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        exact hq)
      hFramed

/-- Framed zero-divisor DIV dispatcher post over `divCode_noNop`, before the
    usual weakening to `divStackDispatchPost`. This keeps the incoming `x1`
    value concrete for callable wrappers that need the following `ret` address
    to remain visible. -/
@[irreducible]
def divBzeroDispatchPostPreservingX1Frame (sp : Word) (a b : EvmWord)
    (v1 v2 v6 v7 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
    (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
  ((.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x11 ↦ᵣ v11) ** evmWordIs sp a **
    divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0)

theorem divBzeroDispatchPostPreservingX1Frame_unfold
    {sp : Word} {a b : EvmWord} {v1 v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    divBzeroDispatchPostPreservingX1Frame sp a b v1 v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
      (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
        (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
       ((.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x11 ↦ᵣ v11) ** evmWordIs sp a **
        divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)) := by
  delta divBzeroDispatchPostPreservingX1Frame
  rfl

theorem divStackDispatchPostNoX1_weaken_bzero_frame
    (sp : Word) (a b : EvmWord)
    {v1 v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h,
      (((.x12 ↦ᵣ (sp + 32)) **
        (.x2 ↦ᵣ v2) ** regOwn .x5 ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** regOwn .x10 ** (.x11 ↦ᵣ v11) **
        (.x0 ↦ᵣ (0 : Word)) **
        evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
        divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0) **
       (.x9 ↦ᵣ v1)) h →
      (divStackDispatchPostNoX1 sp a b ** (.x9 ↦ᵣ v1)) h := by
  intro h hp
  rw [divStackDispatchPostNoX1_unfold]
  apply sepConj_mono_left _ h hp
  intro hLeft hpLeft
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn .x2 (v := v2))
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn .x6 (v := v6))
  apply sepConj_mono (regIs_implies_regOwn .x7 (v := v7))
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn .x11 (v := v11))
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValuesCall_implies_divScratchOwnCall
    sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
      retMem dMem dloMem scratch_un0
  exact hpLeft

theorem divBzeroDispatchPostPreservingX1Frame_weaken_noX1
    (sp : Word) (a b : EvmWord)
    {v1 v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h,
      divBzeroDispatchPostPreservingX1Frame sp a b v1 v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 h →
      (divStackDispatchPostNoX1 sp a b ** (.x9 ↦ᵣ v1)) h := by
  intro h hp
  rw [divBzeroDispatchPostPreservingX1Frame_unfold] at hp
  simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢
  exact divStackDispatchPostNoX1_weaken_bzero_frame
    (sp := sp) (a := a) (b := b) h (by xperm_hyp hp)

/-- Zero-divisor DIV dispatcher over `divCode_noNop`, preserving the exact
    incoming `x1` value in a named framed postcondition. -/
theorem evm_div_bzero_stack_spec_within_dispatch_noNop_preserving_x1_frame_uni
    (sp base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divBzeroDispatchPostPreservingX1Frame sp a b v1 v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x11 ↦ᵣ v11) ** evmWordIs sp a **
    divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_div_bzero_stack_spec_within_noNop sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (divCode_noNop base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCall_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPre_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hq => by
        dsimp [frame] at hq
        rw [divBzeroDispatchPostPreservingX1Frame_unfold]
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        exact hq)
      hFramed

/-- Zero-divisor DIV dispatcher over `divCode_noNop`, preserving the exact
    incoming `x1` value in the callable-ready post shape. -/
theorem evm_div_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni
    (sp base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b ** (.x9 ↦ᵣ v1)) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp =>
    divBzeroDispatchPostPreservingX1Frame_weaken_noX1
      (sp := sp) (a := a) (b := b) h hp)
    (evm_div_bzero_stack_spec_within_dispatch_noNop_preserving_x1_frame_uni
      sp base a b v1 v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz)

/-- Zero-divisor DIV dispatcher over `divCode_noNop` in the concrete callable
    post shape shared by bzero and branch-local dispatcher proofs. -/
theorem evm_div_bzero_stack_spec_within_dispatch_noNop_concrete_callable_uni
    (sp base : Word)
    (a b : EvmWord) (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
    evmWordIs sp a **
    divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_div_bzero_stack_spec_within_noNop sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (divCode_noNop base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCallNoX1_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPreNoX1_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hq => by
        simpa [frame, divConcretePostNoX1Frame_unfold,
          sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq)
      hFramed

/-- v4 zero-divisor DIV dispatcher in the concrete callable post shape shared
    by bzero and branch-local dispatcher proofs. -/
theorem evm_div_bzero_stack_spec_within_dispatch_noNop_v4_concrete_callable_uni
    (sp base : Word)
    (a b : EvmWord) (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
    evmWordIs sp a **
    divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_div_bzero_stack_spec_within_noNop_v4 sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCallNoX1_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPreNoX1_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hq => by
        simpa [frame, divConcretePostNoX1Frame_unfold,
          sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hq)
      hFramed

/-- v4 zero-divisor DIV dispatcher over the shared no-NOP code surface with
    exact `x1` and no `x9` frame. Used by callers that keep `x9` entirely
    caller-framed. -/
theorem evm_div_bzero_stack_spec_within_dispatch_noNop_v4_callable_x1_uni
    (sp base : Word)
    (a b : EvmWord) (raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  let frame : Assertion :=
    (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
    evmWordIs sp a **
    divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_div_bzero_stack_spec_within_noNop_v4 sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCallNoX1_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPreCallable_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hq => by
        dsimp [frame] at hq
        rw [divStackDispatchPostCallable_unfold]
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        have hqOwn :
            (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
              (.x1 ↦ᵣ raVal) ** regOwn .x11 ** (.x12 ↦ᵣ (sp + 32)) **
              regOwn .x2 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x10 ** regOwn .x5 ** evmWordIs (sp + 32) (EvmWord.div a b)) h := by
          refine sepConj_mono ?_ ?_ h hq
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
        exact by xperm_hyp hqOwn)
      hFramed

/-- Zero-divisor DIV dispatcher over `divCode_noNop` in the callable-only
    surface: exact `x1` is preserved for `cc_ret`, and exact `x9` is framed
    separately from the DIV loop-counter ownership surface. -/
theorem evm_div_bzero_stack_spec_within_dispatch_noNop_callable_uni
    (sp base : Word)
    (a b : EvmWord) (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (divConcretePostNoX1_weaken_callable_frame sp a b)
    (evm_div_bzero_stack_spec_within_dispatch_noNop_concrete_callable_uni
      sp base a b x9Val raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz)

/-- Zero-divisor DIV dispatcher over `divCode_noNop` with exact `x1` and no
    `x9` frame. Used by callers that keep `x9` entirely caller-framed. -/
theorem evm_div_bzero_stack_spec_within_dispatch_noNop_callable_x1_uni
    (sp base : Word)
    (a b : EvmWord) (raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  let frame : Assertion :=
    (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
    evmWordIs sp a **
    divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_div_bzero_stack_spec_within_noNop sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (divCode_noNop base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCallNoX1_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPreCallable_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hq => by
        dsimp [frame] at hq
        rw [divStackDispatchPostCallable_unfold]
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        have hqOwn :
            (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
              (.x1 ↦ᵣ raVal) ** regOwn .x11 ** (.x12 ↦ᵣ (sp + 32)) **
              regOwn .x2 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x10 ** regOwn .x5 ** evmWordIs (sp + 32) (EvmWord.div a b)) h := by
          refine sepConj_mono ?_ ?_ h hq
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
        exact by xperm_hyp hqOwn)
      hFramed

theorem modStackDispatchPost_weaken_bzero_frame
    (sp : Word) (a b : EvmWord)
    {v1 v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       regOwn .x5 ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       regOwn .x10 ** (.x11 ↦ᵣ v11) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
       divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0) h →
      modStackDispatchPost sp a b h := by
  intro h hp
  delta modStackDispatchPost
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn .x9 (v := v1))
  apply sepConj_mono (regIs_implies_regOwn .x2 (v := v2))
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn .x6 (v := v6))
  apply sepConj_mono (regIs_implies_regOwn .x7 (v := v7))
  apply sepConj_mono_right
  apply sepConj_mono (regIs_implies_regOwn .x11 (v := v11))
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValuesCall_implies_divScratchOwnCall
    sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
      retMem dMem dloMem scratch_un0
  exact hp

theorem evm_mod_bzero_stack_spec_within_dispatch_uni (sp base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode base)
      (divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x11 ↦ᵣ v11) ** evmWordIs sp a **
    divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero :=
    evm_mod_bzero_stack_spec_within sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin 13 base (base + nopOff) (modCode base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCall_unfold]
      pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPre_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun _ hq => by
        dsimp [frame] at hq
        refine modStackDispatchPost_weaken_bzero_frame (sp := sp) (a := a) (b := b)
          (v1 := v1) (v2 := v2) (v6 := v6) (v7 := v7) (v11 := v11)
          (q0 := q0) (q1 := q1) (q2 := q2) (q3 := q3)
          (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
          (u4 := u4) (u5 := u5) (u6 := u6) (u7 := u7)
          (shiftMem := shiftMem) (nMem := nMem) (jMem := jMem)
          (retMem := retMem) (dMem := dMem) (dloMem := dloMem)
          (scratch_un0 := scratch_un0) _ ?_
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        exact hq)
      hFramed


end EvmAsm.Evm64
