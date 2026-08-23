import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeWitnessSupport

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec

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
        1 2 3 4 hvbfBytes32 hvbfBytes32 hvbfBytes32 empAssertion h := by
  let fixedRegs : List (Reg × Word) :=
    [(.x1, 0x12340000), (.x2, 0x100000), (.x8, 0x56780000),
     (.x9, 1), (.x18, 2), (.x19, 3), (.x20, 4),
     (.x10, 0x200000), (.x11, 100000), (.x12, 50000), (.x13, 0x200100),
     (.x0, 0)]
  let ownedRegs : List Reg := [.x5, .x6, .x7, .x28, .x29, .x30, .x31]
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
    frameSlotsOwn, hvbfFrame, k73Frame]
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
        1 25000 3 4 50000 (0x200100 : Word) status out11
        hvbfBytes32 hvbfBytes32 hvbfBytes32 empAssertion h := by
  let fixedRegs : List Reg :=
    [.x1, .x2, .x8, .x18, .x10, .x11, .x9, .x19, .x20, .x12, .x0]
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
    | .x12 => 0x200100
    | .x13 => Expected
    | .x0 => 0
    | _ => 0
  let ownedRegs : List Reg :=
    [.x5, .x6, .x7, .x13, .x28, .x29, .x30, .x31]
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
    tailRestCore, frameSlotsSaved, hvbfSaved, k73Saved, hvbfFrame, k73Frame]
    at hAllRegion ⊢
  simp [sepConj_assoc', sepConj_emp_right', signExtend12]
    at hAllRegion ⊢
  xperm_chunked hAllRegion

theorem header_validate_base_fee_final_arms_inhabited :
    (∃ h, hvbfFinal (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
      (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
      1 25000 3 4 50000 (0x200100 : Word) 2 50000
      hvbfBytes32 hvbfBytes32 hvbfBytes32 empAssertion h) ∧
    (∃ h, hvbfFinal (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
      (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
      1 25000 3 4 50000 (0x200100 : Word) 0 Expected
      hvbfBytes32 hvbfBytes32 hvbfBytes32 empAssertion h) ∧
    (∃ h, hvbfFinal (0x100000 : Word) (0x0ffff0 : Word) (0x0fffb8 : Word)
      (0x12340000 : Word) (0x56780000 : Word) (0x200000 : Word)
      1 25000 3 4 50000 (0x200100 : Word) 1 Expected
      hvbfBytes32 hvbfBytes32 hvbfBytes32 empAssertion h) := by
  exact ⟨header_validate_base_fee_final_inhabited 2 50000,
    header_validate_base_fee_final_inhabited 0 Expected,
    header_validate_base_fee_final_inhabited 1 Expected⟩

end EvmAsm.Codegen.HeaderValidateBaseFeeSpec
