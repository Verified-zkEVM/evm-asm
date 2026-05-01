/-
  EvmAsm.Evm64.DivMod.Spec.Unified

  Unified-bound DIV/MOD stack-spec wrappers. The four per-`n` dispatcher-surface
  specs (n=1, n=2, n=3, n=4) all have different `cpsTripleWithin` step bounds
  (n=1: 946, n=2: 744, n=3: 542, n=4: 340). Before they can be combined into a
  single `evm_div_stack_spec` / `evm_mod_stack_spec` (slice 4keh / 3muq under
  parent #61) via case-split, all four need a shared bound — otherwise the
  case-split branches produce triples with incompatible `nSteps`.

  This file introduces `unifiedDivBound : Nat := 946` (the maximum across n=1..4)
  and `_uni` wrappers for each per-`n` dispatcher-surface spec that lift the
  existing bound to `unifiedDivBound` via `cpsTripleWithin_mono_nSteps`.

  Pre/post are unchanged; the proof is a single `cpsTripleWithin_mono_nSteps`
  application with `by decide` for the bound inequality.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

  Refs: GH #61, beads `evm-asm-unta` (parent `evm-asm-4keh`, grandparent
  `evm-asm-pb40`).
-/

import EvmAsm.Evm64.DivMod.Spec.Dispatcher
import EvmAsm.Evm64.DivMod.Spec.N2DivStackSpec
import EvmAsm.Evm64.DivMod.Spec.N2ModStackSpec
import EvmAsm.Evm64.DivMod.Spec.N3DivStackSpec
import EvmAsm.Evm64.DivMod.Spec.N3ModBridge
import EvmAsm.Evm64.DivMod.N4StackSpecWithin

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
       (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
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
  apply sepConj_mono (regIs_implies_regOwn .x1 (v := v1))
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
    (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
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

theorem modStackDispatchPost_weaken_bzero_frame
    (sp : Word) (a b : EvmWord)
    {v1 v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
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
  apply sepConj_mono (regIs_implies_regOwn .x1 (v := v1))
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
    (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
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

/-! ### DIV `_uni` wrappers -/

/-- Unified-bound wrapper for `evm_div_n1_stack_spec_within_word`. -/
theorem evm_div_n1_stack_spec_within_word_uni
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hdivWord : fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) :=
  cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n1_stack_spec_within_word bltu_3 bltu_2 bltu_1 bltu_0
      sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
      hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for `evm_div_n2_stack_spec_within_word`. -/
theorem evm_div_n2_stack_spec_within_word_uni
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdivWord : fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) :=
  cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n2_stack_spec_within_word bltu_2 bltu_1 bltu_0
      sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1nz
      hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for `evm_div_n3_stack_spec_within_word`. -/
theorem evm_div_n3_stack_spec_within_word_uni
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : isTrialN3_j1 bltu_1 a3 b1 b2)
    (hbltu_0 : isTrialN3_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b2).1).toNat % 64))
      ((b1 <<< (((clzResult b2).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b2 <<< (((clzResult b2).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b3 <<< (((clzResult b2).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64))))
    (hdivWord : fullDivN3QuotientWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b2).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) :=
  cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n3_stack_spec_within_word bltu_1 bltu_0
      sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2nz
      hshift_nz halign hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for `evm_div_n4_stack_spec_within_dispatch`. -/
theorem evm_div_n4_stack_spec_within_dispatch_uni (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz_addback :
      isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
    (hsem_addback :
      isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) :=
  cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n4_stack_spec_within_dispatch sp base a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz halign hbltu hcarry2_nz_addback hsem_addback)

/-! ### MOD `_uni` wrappers -/

/-- Unified-bound wrapper for `evm_mod_n1_stack_spec_within_word`. -/
theorem evm_mod_n1_stack_spec_within_word_uni
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hmodWord : fullModN1RemainderWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) :=
  cpsTripleWithin_mono_nSteps (by decide)
    (evm_mod_n1_stack_spec_within_word bltu_3 bltu_2 bltu_1 bltu_0
      sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
      hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hmodWord)

/-- Unified-bound wrapper for `evm_mod_n2_stack_spec_within_word`. -/
theorem evm_mod_n2_stack_spec_within_word_uni
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hmodWord : fullModN2RemainderWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) :=
  cpsTripleWithin_mono_nSteps (by decide)
    (evm_mod_n2_stack_spec_within_word bltu_2 bltu_1 bltu_0
      sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1nz
      hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2 hmodWord)

/-- Unified-bound wrapper for `evm_mod_n3_stack_spec_within_word`. -/
theorem evm_mod_n3_stack_spec_within_word_uni
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : isTrialN3_j1 bltu_1 a3 b1 b2)
    (hbltu_0 : isTrialN3_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b2).1).toNat % 64))
      ((b1 <<< (((clzResult b2).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b2 <<< (((clzResult b2).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b3 <<< (((clzResult b2).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64))))
    (hmodWord : fullModN3RemainderWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b2).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) :=
  cpsTripleWithin_mono_nSteps (by decide)
    (evm_mod_n3_stack_spec_within_word bltu_1 bltu_0
      sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2nz
      hshift_nz halign hbltu_1 hbltu_0 hcarry2 hmodWord)

/-- Unified-bound wrapper for `evm_mod_n4_stack_spec_within_dispatch`. -/
theorem evm_mod_n4_stack_spec_within_dispatch_uni (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz_addback :
      isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
    (hsem_addback :
      isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) :=
  cpsTripleWithin_mono_nSteps (by decide)
    (evm_mod_n4_stack_spec_within_dispatch sp base a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz halign hbltu hcarry2_nz_addback hsem_addback)

/-! ### Single MOD dispatcher theorem -/

/-- Branch certificate for the single public MOD stack spec.

The constructors mirror the dispatcher branches. Each nonzero branch carries
exactly the semantic side conditions required by the corresponding
`evm_mod_stack_spec_within_*` alias, but states them directly over `a` and `b`
via `getLimbN` instead of exposing separate limb variables in the final theorem.
-/
inductive ModStackSpecCase (base : Word) (a b : EvmWord) where
  | bzero (v1 v2 : Word) (hbz : b = 0)
  | n1Full (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
      (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
      (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
      (hb1z : b.getLimbN 1 = 0)
      (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
      (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
      (hbltu_3 : isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0))
      (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hcarry2 : Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 0 >>> ((signExtend12 (0 : BitVec 12) -
            (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 1 >>> ((signExtend12 (0 : BitVec 12) -
            (clzResult (b.getLimbN 0)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
          (b.getLimbN 2 >>> ((signExtend12 (0 : BitVec 12) -
            (clzResult (b.getLimbN 0)).1).toNat % 64))))
      (hmodWord : fullModN1RemainderWord bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.mod a b)
  | n2Full (bltu_2 bltu_1 bltu_0 : Bool)
      (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
      (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
      (hb1nz : b.getLimbN 1 ≠ 0)
      (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
      (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
      (hbltu_2 : isTrialN2_j2 bltu_2 (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1))
      (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hcarry2 : Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 1)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 1)).1).toNat % 64)) |||
          (b.getLimbN 0 >>> ((signExtend12 (0 : BitVec 12) -
            (clzResult (b.getLimbN 1)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 1)).1).toNat % 64)) |||
          (b.getLimbN 1 >>> ((signExtend12 (0 : BitVec 12) -
            (clzResult (b.getLimbN 1)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 1)).1).toNat % 64)) |||
          (b.getLimbN 2 >>> ((signExtend12 (0 : BitVec 12) -
            (clzResult (b.getLimbN 1)).1).toNat % 64))))
      (hmodWord : fullModN2RemainderWord bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.mod a b)
  | n3Full (bltu_1 bltu_0 : Bool)
      (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
      (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
      (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
      (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
      (hbltu_1 : isTrialN3_j1 bltu_1 (a.getLimbN 3)
        (b.getLimbN 1) (b.getLimbN 2))
      (hbltu_0 : isTrialN3_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hcarry2 : Carry2NzAll
        (b.getLimbN 0 <<< (((clzResult (b.getLimbN 2)).1).toNat % 64))
        ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 2)).1).toNat % 64)) |||
          (b.getLimbN 0 >>> ((signExtend12 (0 : BitVec 12) -
            (clzResult (b.getLimbN 2)).1).toNat % 64)))
        ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 2)).1).toNat % 64)) |||
          (b.getLimbN 1 >>> ((signExtend12 (0 : BitVec 12) -
            (clzResult (b.getLimbN 2)).1).toNat % 64)))
        ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 2)).1).toNat % 64)) |||
          (b.getLimbN 2 >>> ((signExtend12 (0 : BitVec 12) -
            (clzResult (b.getLimbN 2)).1).toNat % 64))))
      (hmodWord : fullModN3RemainderWord bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.mod a b)
  | n4Full
      (hbnz : b ≠ 0)
      (hb3nz : b.getLimbN 3 ≠ 0)
      (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
      (hbltu : isCallTrialN4Evm a b)
      (hcarry2_nz_addback :
        isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
      (hsem_addback :
        isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b)

namespace ModStackSpecCase

def x1 {base : Word} {a b : EvmWord} : ModStackSpecCase base a b → Word
  | .bzero v1 _ _ => v1
  | _ => signExtend12 (4 : BitVec 12) - (4 : Word)

def x2 {base : Word} {a b : EvmWord} : ModStackSpecCase base a b → Word
  | .bzero _ v2 _ => v2
  | .n1Full .. => (clzResult (b.getLimbN 0)).2 >>> (63 : Nat)
  | .n2Full .. => (clzResult (b.getLimbN 1)).2 >>> (63 : Nat)
  | .n3Full .. => (clzResult (b.getLimbN 2)).2 >>> (63 : Nat)
  | .n4Full .. => (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)

end ModStackSpecCase

/-- Single named MOD stack spec over the dispatcher branch certificate. -/
theorem evm_mod_stack_spec (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (branch : ModStackSpecCase base a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) := by
  cases branch with
  | bzero v1 v2 hbz =>
      exact evm_mod_bzero_stack_spec_within_dispatch_uni sp base a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz
  | n1Full bltu_3 bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1z hshift_nz halign
      hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hmodWord =>
      exact evm_mod_n1_stack_spec_within_word_uni
        bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2z hb1z hshift_nz halign
        hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hmodWord
  | n2Full bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1nz hshift_nz halign
      hbltu_2 hbltu_1 hbltu_0 hcarry2 hmodWord =>
      exact evm_mod_n2_stack_spec_within_word_uni
        bltu_2 bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2z hb1nz hshift_nz halign
        hbltu_2 hbltu_1 hbltu_0 hcarry2 hmodWord
  | n3Full bltu_1 bltu_0 hbnz hb3z hb2nz hshift_nz halign
      hbltu_1 hbltu_0 hcarry2 hmodWord =>
      exact evm_mod_n3_stack_spec_within_word_uni
        bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2nz hshift_nz halign
        hbltu_1 hbltu_0 hcarry2 hmodWord
  | n4Full hbnz hb3nz halign hbltu hcarry2_nz_addback hsem_addback =>
      exact evm_mod_n4_stack_spec_within_dispatch_uni sp base a b
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        hbnz hb3nz halign hbltu hcarry2_nz_addback hsem_addback

end EvmAsm.Evm64
