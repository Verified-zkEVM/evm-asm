/-
  EvmAsm.Codegen.Programs.HeaderValidateBaseFeeWitness

  Joint inhabitance witnesses for the header-validate-base-fee contract,
  including the region helpers formerly in HeaderValidateBaseFeeWitnessSupport.
-/

import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpec

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec

abbrev hvbfBytes32 : List (BitVec 8) := List.replicate 32 0

def hvbfRegionCells : List Word :=
  [0x200000, 0x200008, 0x200010, 0x200018,
   0x200100, 0x200108, 0x200110, 0x200118,
   Expected, Expected + 8, Expected + 16, Expected + 24]

def hvbfRegions : Assertion :=
  bytesRegion (0x200000 : Word) hvbfBytes32 **
    bytesRegion (0x200100 : Word) hvbfBytes32 **
    bytesRegion Expected hvbfBytes32

def hvbfRegionsState : PartialState :=
  hvbfRegionCells.foldr (fun a acc => (PartialState.singletonMem a 0).union acc)
    PartialState.empty

private theorem singletonMem_disjoint_ws {a1 a2 : Word} (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 0).Disjoint
      (PartialState.singletonMem a2 0) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a
    right
    simp [PartialState.singletonMem, hne]
  · left
    simp [PartialState.singletonMem, h]

theorem hvbfRegions_inhabited : hvbfRegions hvbfRegionsState := by
  change ((bytesRegion (0x200000 : Word) hvbfBytes32) **
    bytesRegion (0x200100 : Word) hvbfBytes32 **
    bytesRegion Expected hvbfBytes32) hvbfRegionsState
  simp only [bytesRegion, hvbfBytes32]
  simp [List.replicate, bytesRegionAux]
  simp only [sepConj_emp_right', sepConj_assoc']
  change (((0x200000 : Word) ↦ₘ (0 : Word)) **
    ((0x200008 : Word) ↦ₘ (0 : Word)) **
      ((0x200010 : Word) ↦ₘ (0 : Word)) **
        ((0x200018 : Word) ↦ₘ (0 : Word)) **
    ((0x200100 : Word) ↦ₘ (0 : Word)) **
      ((0x200108 : Word) ↦ₘ (0 : Word)) **
        ((0x200110 : Word) ↦ₘ (0 : Word)) **
          ((0x200118 : Word) ↦ₘ (0 : Word)) **
            ((Expected : Word) ↦ₘ (0 : Word)) **
              ((Expected + 8) ↦ₘ (0 : Word)) **
                ((Expected + 16) ↦ₘ (0 : Word)) **
                  ((Expected + 24) ↦ₘ (0 : Word))) _
  have hc := sepConj_foldr_satisfiable
    (atom := fun a : Word => a ↦ₘ (0 : Word))
    (heap := fun a : Word => PartialState.singletonMem a 0)
    (xs := hvbfRegionCells)
    (by
      intro a ha
      simp [hvbfRegionCells] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩)
    (by
      exact List.Pairwise.imp (fun {a1 a2} hne => singletonMem_disjoint_ws hne)
        (by decide))
  simp only [hvbfRegionCells, List.foldr] at hc
  rw [PartialState.union_empty_right] at hc
  rw [sepConj_emp_right'] at hc
  simpa [hvbfRegionsState, hvbfRegionCells, List.foldr,
    PartialState.union_empty_right] using hc

theorem hvbfRegions_disjoint_of_frame (h : PartialState)
    (hmem : ∀ a, h.mem a ≠ none →
      a = (0x0ffff0 : Word) ∨ a = 0x0ffff8 ∨ a = 0x0fffb8 ∨
      a = 0x0fffc0 ∨ a = 0x0fffc8 ∨ a = 0x0fffd0 ∨
      a = 0x0fffd8 ∨ a = 0x0fffe0) :
    h.Disjoint hvbfRegionsState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    right
    simp [hvbfRegionsState, hvbfRegionCells, PartialState.union,
      PartialState.empty, PartialState.singletonMem]
  · intro a
    by_cases hnone : h.mem a = none
    · exact Or.inl hnone
    · right
      have ha := hmem a hnone
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [hvbfRegionsState, hvbfRegionCells, Expected, GuestAddrs.hvbf_expected,
          PartialState.union, PartialState.empty, PartialState.singletonMem]
  · intro a
    right
    simp [hvbfRegionsState, hvbfRegionCells, PartialState.union,
      PartialState.empty, PartialState.singletonMem]
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

/-! ## Joint inhabitance

The wrapper theorem above has two explicit callee premises and a status-indexed
postcondition.  The following witnesses are deliberately constructed for the
whole entry and final assertions at once.  They use the caller-shaped 32-byte
header, parent-base-fee, and expected-scratch regions; no empty byte region is
used to establish inhabitance. -/

theorem header_validate_base_fee_pre_inhabited :
    ∃ h : PartialState,
      hvbfPre (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
        (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
        (100000 : Word) (50000 : Word) (0x200100 : Word)
        1 2 3 4 hvbfBytes32 hvbfBytes32 hvbfBytes32
        (k74FlatFrame empAssertion) h := by
  let fixedRegs : List (Reg × Word) :=
    [(.x1, 0x12340000), (.x2, 0x100000), (.x8, 0x56780000),
     (.x9, 1), (.x18, 2), (.x19, 3), (.x20, 4),
     (.x10, 0x200000), (.x11, 100000), (.x12, 50000), (.x13, 0x200100),
     (.x0, 0)]
  let ownedRegs : List Reg :=
    [.x5, .x6, .x7, .x14, .x15, .x16, .x17, .x28, .x29, .x30, .x31]
  let frameAddrs : List Word :=
    [0x0ffff0, 0x0ffff8, 0x0fffb8, 0x0fffc0, 0x0fffc8, 0x0fffd0,
     0x0fffd8, 0x0fffe0]
  let fixedHeap : (Reg × Word) → PartialState :=
    fun p => PartialState.singletonReg p.1 p.2
  let ownedHeap : Reg → PartialState :=
    fun r => PartialState.singletonReg r 0
  let frameHeap : Word → PartialState :=
    fun a => PartialState.singletonMem a 0
  have singletonReg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
      (hne : r1 ≠ r2) :
      (PartialState.singletonReg r1 v1).Disjoint
        (PartialState.singletonReg r2 v2) := by
    refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
      Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    intro r
    by_cases h : r = r1
    · subst r
      right
      simp [PartialState.singletonReg, hne]
    · left
      simp [PartialState.singletonReg, h]
  have singletonMem_disjoint {a1 a2 : Word} (hne : a1 ≠ a2) :
      (PartialState.singletonMem a1 0).Disjoint
        (PartialState.singletonMem a2 0) := by
    refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
      Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    intro a
    by_cases h : a = a1
    · subst a
      right
      simp [PartialState.singletonMem, hne]
    · left
      simp [PartialState.singletonMem, h]
  have hFixed :
      (fixedRegs.foldr (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion)
        (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro p hp
      simp [fixedHeap, regIs]
    · have hd : fixedRegs.Pairwise (fun p q => p.1 ≠ q.1) := by
        simp [fixedRegs]
      exact List.Pairwise.imp (fun {p q} hpq => singletonReg_disjoint hpq) hd
  have hOwned :
      (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)
        (ownedRegs.foldr (fun r acc => (ownedHeap r).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro r hr
      exact ⟨0, by simp [ownedHeap, regIs]⟩
    · exact List.Pairwise.imp (fun {r1 r2} hne => singletonReg_disjoint hne)
        (by decide)
  have hRegs :
      ((fixedRegs.foldr (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion) **
        (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion))
        ((fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
          PartialState.empty).union
          (ownedRegs.foldr (fun r acc => (ownedHeap r).union acc)
            PartialState.empty)) := by
    exact sepConj_foldr_cross_satisfiable
      (atomL := fun p : Reg × Word => p.1 ↦ᵣ p.2) (heapL := fixedHeap)
      (xs := fixedRegs) (atomR := fun r : Reg => regOwn r)
      (heapR := ownedHeap) (ys := ownedRegs) hFixed hOwned (by
        intro p hp r hr
        apply singletonReg_disjoint
        simp [fixedRegs] at hp
        simp [ownedRegs] at hr
        aesop)
  have hFrame :
      (frameAddrs.foldr (fun a acc => memOwn a ** acc) empAssertion)
        (frameAddrs.foldr (fun a acc => (frameHeap a).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro a ha
      simp [frameAddrs] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        refine ⟨0, rfl, ?_⟩
        apply isValidDwordAccess_of_toNat
        · decide
        · left
          exact ⟨by decide, by decide⟩
    · exact List.Pairwise.imp
        (fun {a1 a2} hne => singletonMem_disjoint hne) (by decide)
  let regState : PartialState :=
    (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
      PartialState.empty).union
      (ownedRegs.foldr (fun r acc => (ownedHeap r).union acc)
        PartialState.empty)
  let frameState : PartialState :=
    frameAddrs.foldr (fun a acc => (frameHeap a).union acc)
      PartialState.empty
  have hRegFrame : regState.Disjoint frameState := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r
      right
      simp [frameState, frameAddrs, frameHeap, PartialState.singletonMem,
        PartialState.union, PartialState.empty]
    · intro a
      left
      simp [regState, fixedRegs, ownedRegs, fixedHeap, ownedHeap,
        PartialState.singletonReg, PartialState.empty,
        PartialState.union]
    · intro a
      exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  have hAll :
      (((fixedRegs.foldr (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion) **
        (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)) **
        (frameAddrs.foldr (fun a acc => memOwn a ** acc) empAssertion))
        (regState.union frameState) := by
    exact ⟨regState, frameState, hRegFrame, rfl, hRegs, hFrame⟩
  have hRegion := hvbfRegions_inhabited
  have hBaseRegion : (regState.union frameState).Disjoint hvbfRegionsState := by
    apply hvbfRegions_disjoint_of_frame
    intro a ha
    simp [regState, frameState, fixedRegs, ownedRegs, fixedHeap, ownedHeap,
      frameAddrs, frameHeap, PartialState.union, PartialState.empty,
      PartialState.singletonReg, PartialState.singletonMem] at ha
    split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
  have hAllRegion :
      (((((fixedRegs.foldr (fun p acc => (p.1 ↦ᵣ p.2) ** acc) empAssertion) **
        (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)) **
        (frameAddrs.foldr (fun a acc => memOwn a ** acc) empAssertion)) **
        hvbfRegions) ((regState.union frameState).union hvbfRegionsState)) := by
    exact ⟨regState.union frameState, hvbfRegionsState, hBaseRegion, rfl,
      hAll, hRegion⟩
  refine ⟨(regState.union frameState).union hvbfRegionsState, ?_⟩
  unfold hvbfPre at ⊢
  dsimp [regState, frameState, fixedRegs, ownedRegs, frameAddrs,
    fixedHeap, ownedHeap, frameHeap, hvbfRegions, hvbfBytes32,
    frameSlotsOwn, hvbfFrame, k73Frame, k74FlatFrame]
    at hAllRegion ⊢
  simp [sepConj_assoc', sepConj_emp_right', signExtend12]
    at hAllRegion ⊢
  xperm_chunked hAllRegion

/- The three disjuncts of `hvbfFinalAny` are separately inhabitable. -/
theorem header_validate_base_fee_final_inhabited
    (status out11 : Word) :
    ∃ h : PartialState,
      hvbfFinal (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
        (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
        1 25000 25000 3 4 50000 (0x200100 : Word) status out11
        hvbfBytes32 hvbfBytes32 hvbfBytes32 (k74FlatFrame empAssertion) h := by
  let fixedRegs : List Reg :=
    [.x1, .x2, .x8, .x18, .x10, .x11, .x9, .x19, .x20, .x0]
  let fixedVal : Reg → Word := fun r => match r with
    | .x1 => 0x12340000
    | .x2 => 0x100000
    | .x8 => 0x56780000
    | .x18 => 25000
    | .x10 => status
    | .x11 => out11
    | .x9 => 1
    | .x19 => 3
    | .x20 => 4
    | .x13 => Expected
    | .x0 => 0
    | _ => 0
  let ownedRegs : List Reg :=
    [.x5, .x6, .x7, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29, .x30, .x31]
  let fixedMems : List (Word × Word) :=
    [(0x0ffff0, 0x12340000), (0x0ffff8, 0x56780000),
     (0x0fffb8, H + 40), (0x0fffc0, 0x200000), (0x0fffc8, 1),
     (0x0fffd0, 25000), (0x0fffd8, 3), (0x0fffe0, 4)]
  let fixedHeap : Reg → PartialState :=
    fun r => PartialState.singletonReg r (fixedVal r)
  let ownedHeap : Reg → PartialState :=
    fun r => PartialState.singletonReg r 0
  let memHeap : (Word × Word) → PartialState :=
    fun p => PartialState.singletonMem p.1 p.2
  have singletonReg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
      (hne : r1 ≠ r2) :
      (PartialState.singletonReg r1 v1).Disjoint
        (PartialState.singletonReg r2 v2) := by
    refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
      Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    intro r
    by_cases h : r = r1
    · subst r
      right
      simp [PartialState.singletonReg, hne]
    · left
      simp [PartialState.singletonReg, h]
  have singletonMem_disjoint {a1 a2 v1 v2 : Word} (hne : a1 ≠ a2) :
      (PartialState.singletonMem a1 v1).Disjoint
        (PartialState.singletonMem a2 v2) := by
    refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
      Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    intro a
    by_cases h : a = a1
    · subst a
      right
      simp [PartialState.singletonMem, hne]
    · left
      simp [PartialState.singletonMem, h]
  have hFixed :
      (fixedRegs.foldr (fun r acc => (r ↦ᵣ fixedVal r) ** acc) empAssertion)
        (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro r hr
      simp [fixedHeap, fixedVal, regIs]
    · exact List.Pairwise.imp (fun {r1 r2} hne => singletonReg_disjoint hne)
        (by decide)
  have hOwned :
      (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)
        (ownedRegs.foldr (fun r acc => (ownedHeap r).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro r hr
      exact ⟨0, by simp [ownedHeap, regIs]⟩
    · exact List.Pairwise.imp (fun {r1 r2} hne => singletonReg_disjoint hne)
        (by decide)
  have hRegs := sepConj_foldr_cross_satisfiable
    (atomL := fun r : Reg => r ↦ᵣ fixedVal r) (heapL := fixedHeap)
    (xs := fixedRegs) (atomR := fun r : Reg => regOwn r)
    (heapR := ownedHeap) (ys := ownedRegs) hFixed hOwned (by
      intro r1 hr1 r2 hr2
      apply singletonReg_disjoint
      simp [fixedRegs] at hr1
      simp [ownedRegs] at hr2
      aesop)
  have hMems :
      (fixedMems.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion)
        (fixedMems.foldr (fun p acc => (memHeap p).union acc)
          PartialState.empty) := by
    apply sepConj_foldr_satisfiable
    · intro p hp
      simp [fixedMems] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals
        refine ⟨rfl, ?_⟩
        apply isValidDwordAccess_of_toNat
        · decide
        · left
          exact ⟨by decide, by decide⟩
    · exact List.Pairwise.imp
        (fun {p q} hpq => singletonMem_disjoint hpq) (by decide)
  let regState : PartialState :=
    (fixedRegs.foldr (fun p acc => (fixedHeap p).union acc)
      PartialState.empty).union
      (ownedRegs.foldr (fun r acc => (ownedHeap r).union acc)
        PartialState.empty)
  let memState : PartialState :=
    fixedMems.foldr (fun p acc => (memHeap p).union acc) PartialState.empty
  have hRegMem : regState.Disjoint memState := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r
      right
      simp [memState, fixedMems, memHeap, PartialState.singletonMem,
        PartialState.union, PartialState.empty]
    · intro a
      left
      simp [regState, fixedRegs, ownedRegs, fixedHeap, ownedHeap,
        PartialState.singletonReg, PartialState.union, PartialState.empty]
    · intro a
      exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  have hAll :
      (((fixedRegs.foldr (fun r acc => (r ↦ᵣ fixedVal r) ** acc) empAssertion) **
        (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)) **
        (fixedMems.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion))
        (regState.union memState) := by
    exact ⟨regState, memState, hRegMem, rfl, hRegs, hMems⟩
  have hRegion := hvbfRegions_inhabited
  have hBaseRegion : (regState.union memState).Disjoint hvbfRegionsState := by
    apply hvbfRegions_disjoint_of_frame
    intro a ha
    simp [regState, memState, fixedRegs, ownedRegs, fixedHeap, ownedHeap,
      fixedMems, memHeap, PartialState.union, PartialState.empty,
      PartialState.singletonReg, PartialState.singletonMem] at ha
    split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
    all_goals split at ha <;> simp_all
  have hAllRegion :
      (((((fixedRegs.foldr (fun r acc => (r ↦ᵣ fixedVal r) ** acc) empAssertion) **
        (ownedRegs.foldr (fun r acc => regOwn r ** acc) empAssertion)) **
        (fixedMems.foldr (fun p acc => (p.1 ↦ₘ p.2) ** acc) empAssertion)) **
        hvbfRegions) ((regState.union memState).union hvbfRegionsState)) := by
    exact ⟨regState.union memState, hvbfRegionsState, hBaseRegion, rfl,
      hAll, hRegion⟩
  refine ⟨(regState.union memState).union hvbfRegionsState, ?_⟩
  unfold hvbfFinal
  dsimp [regState, memState, fixedRegs, fixedVal, ownedRegs, fixedMems,
    fixedHeap, ownedHeap, memHeap, hvbfRegions, hvbfBytes32, tailRest,
    tailRestCore, frameSlotsSaved, hvbfSaved, k73Saved, hvbfFrame, k73Frame,
    k74FlatFrame]
    at hAllRegion ⊢
  simp [sepConj_assoc', sepConj_emp_right', signExtend12]
    at hAllRegion ⊢
  xperm_chunked hAllRegion

theorem header_validate_base_fee_final_arms_inhabited :
    (∃ h, hvbfFinal (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
      (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
      1 25000 25000 3 4 50000 (0x200100 : Word) 2 50000
      hvbfBytes32 hvbfBytes32 hvbfBytes32 (k74FlatFrame empAssertion) h) ∧
    (∃ h, hvbfFinal (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
      (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
      1 25000 25000 3 4 50000 (0x200100 : Word) 0 Expected
      hvbfBytes32 hvbfBytes32 hvbfBytes32 (k74FlatFrame empAssertion) h) ∧
    (∃ h, hvbfFinal (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
      (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
      1 25000 25000 3 4 50000 (0x200100 : Word) 1 Expected
      hvbfBytes32 hvbfBytes32 hvbfBytes32 (k74FlatFrame empAssertion) h) := by
  exact ⟨header_validate_base_fee_final_inhabited 2 50000,
    header_validate_base_fee_final_inhabited 0 Expected,
    header_validate_base_fee_final_inhabited 1 Expected⟩

end EvmAsm.Codegen.HeaderValidateBaseFeeSpec
