/-
  EvmAsm.Evm64.DivMod.Spec.ModBzeroNoNop

  Dispatch-level zero-divisor MOD spec over `modCode_noNop`, mirroring
  the div-side `evm_div_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni`
  in `Spec/UnifiedBzero.lean`. Placed in a separate file because the unified
  stack spec surface is near the file-size cap.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.Base
public import EvmAsm.Evm64.DivMod.Spec.Dispatcher
public import EvmAsm.Evm64.DivMod.Spec.Unified

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Zero-divisor MOD dispatcher over `modCode_noNop`, preserving the exact
    incoming `x1` value. Mirror of
    `evm_div_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni`
    for the MOD callable. -/
theorem evm_mod_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni
    (sp base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
      (divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPostNoX1 sp a b ** (.x9 ↦ᵣ v1)) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x11 ↦ᵣ v11) ** evmWordIs sp a **
    divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero := evm_mod_bzero_stack_spec_within_noNop sp base a b v5 v10 hbz
  have hFramed :=
    cpsTripleWithin_frameR frame (by dsimp [frame]; rw [divScratchValuesCall_unfold]; pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPre_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hq => by
        -- Use the modBzeroDispatchPostPreservingX1Frame bundle approach:
        -- The POST is exactly the framed form, so weaken is trivial.
        exact modBzeroDispatchPostPreservingX1Frame_weaken_noX1 sp a b h
          (by rw [modBzeroDispatchPostPreservingX1Frame_unfold]; xperm_hyp hq))
      hFramed

/-- Zero-divisor MOD dispatcher over `modCode_noNop` in the callable-only
    surface: exact `x1` is preserved for `cc_ret`, and exact `x9` is framed
    separately from the DIV/MOD loop-counter ownership surface. -/
theorem evm_mod_bzero_stack_spec_within_dispatch_noNop_callable_uni
    (sp base : Word)
    (a b : EvmWord) (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
    evmWordIs sp a **
    divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero := evm_mod_bzero_stack_spec_within_noNop sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (modCode_noNop base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) ** frame)) :=
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
        dsimp [frame] at hq
        rw [modStackDispatchPostCallable_unfold]
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        have hqOwn :
            (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
              (.x1 ↦ᵣ raVal) ** regOwn .x11 ** (.x12 ↦ᵣ (sp + 32)) **
              regOwn .x2 ** regOwn .x6 ** regOwn .x7 ** (.x9 ↦ᵣ x9Val) **
              regOwn .x10 ** regOwn .x5 ** evmWordIs (sp + 32) (EvmWord.mod a b)) h := by
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

/-- Zero-divisor MOD dispatcher over `modCode_noNop` with exact `x1` and no
    `x9` frame. Used by callers whose bzero handoff does not carry `x9` state. -/
theorem evm_mod_bzero_stack_spec_within_dispatch_noNop_callable_x1_uni
    (sp base : Word)
    (a b : EvmWord) (raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  let frame : Assertion :=
    (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
    evmWordIs sp a **
    divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero := evm_mod_bzero_stack_spec_within_noNop sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (modCode_noNop base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) ** frame)) :=
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
        rw [modStackDispatchPostCallable_unfold]
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        have hqOwn :
            (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
              (.x1 ↦ᵣ raVal) ** regOwn .x11 ** (.x12 ↦ᵣ (sp + 32)) **
              regOwn .x2 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x10 ** regOwn .x5 ** evmWordIs (sp + 32) (EvmWord.mod a b)) h := by
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

/-- v4 no-NOP zero-divisor MOD dispatcher with exact `x1` and no `x9` frame. -/
theorem evm_mod_bzero_stack_spec_within_dispatch_noNop_v4_callable_x1_uni
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
      (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  let frame : Assertion :=
    (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
    evmWordIs sp a **
    divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero := evm_mod_bzero_stack_spec_within_noNop_v4 sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) ** frame)) :=
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
        rw [modStackDispatchPostCallable_unfold]
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        have hqOwn :
            (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
              (.x1 ↦ᵣ raVal) ** regOwn .x11 ** (.x12 ↦ᵣ (sp + 32)) **
              regOwn .x2 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x10 ** regOwn .x5 ** evmWordIs (sp + 32) (EvmWord.mod a b)) h := by
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

end EvmAsm.Evm64
