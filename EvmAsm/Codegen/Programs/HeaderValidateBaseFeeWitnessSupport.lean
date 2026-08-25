import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpec

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

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

private theorem singletonMem_disjoint {a1 a2 : Word} (hne : a1 ≠ a2) :
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
      exact List.Pairwise.imp (fun {a1 a2} hne => singletonMem_disjoint hne)
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

end EvmAsm.Codegen.HeaderValidateBaseFeeSpec
