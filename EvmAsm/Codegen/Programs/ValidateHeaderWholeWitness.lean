/-
  EvmAsm.Codegen.Programs.ValidateHeaderWholeWitness

  Concrete non-vacuity witnesses for `validateHeaderCorePre` (#12346).

  These theorems only show that the caller-side atom conjunction is
  satisfiable.  They do not discharge `validate_header_cps_compose`: the
  machine route contract remains an explicit, undischarged premise and the
  routine has no semantic callers yet.  In particular, the non-empty frame
  below is intentional; an `empAssertion` witness alone would not demonstrate
  that a real framed resource can coexist with the caller-owned atoms.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderWhole

namespace EvmAsm.Codegen.ValidateHeaderWhole

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm

abbrev hcoreWitnessSpC : Word := 0x10000
abbrev hcoreWitnessSp0 : Word := 0x10038
abbrev hcoreWitnessHeader : Word := 0x20000
abbrev hcoreWitnessParent : Word := 0x30000
abbrev hcoreWitnessGAddr : Word := 0x40000

def hcoreWitnessGBytes : List (BitVec 8) :=
  [1, 2, 3, 4, 5, 6, 7, 8]

def hcoreWitnessRegs : List (Reg × Word) :=
  [(.x1, 0), (.x2, hcoreWitnessSpC), (.x8, hcoreWitnessHeader), (.x9, 1),
   (.x18, hcoreWitnessParent), (.x19, 2), (.x20, 3), (.x21, 4),
   (.x10, hcoreWitnessHeader), (.x11, 1), (.x12, hcoreWitnessParent),
   (.x13, 2), (.x14, 3), (.x15, 4)]

def hcoreWitnessMems : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, 1), (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, 2), (hcoreWitnessSpC + 40, 3),
   (hcoreWitnessSpC + 48, 4),
   (hcoreWitnessGAddr, packBytes hcoreWitnessGBytes)]

def hcoreWitnessMemsNoG : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, 1), (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, 2), (hcoreWitnessSpC + 40, 3),
   (hcoreWitnessSpC + 48, 4)]

private def hcoreWitnessRegHeap : (Reg × Word) → PartialState :=
  fun p => PartialState.singletonReg p.1 p.2

private def hcoreWitnessMemHeap : (Word × Word) → PartialState :=
  fun p => PartialState.singletonMem p.1 p.2

private def hcoreWitnessRegAtom : (Reg × Word) → Assertion :=
  fun p => p.1 ↦ᵣ p.2

private def hcoreWitnessMemAtom : (Word × Word) → Assertion :=
  fun p => p.1 ↦ₘ p.2

private def hcoreWitnessRegFold : Assertion :=
  hcoreWitnessRegs.foldr (fun p acc => hcoreWitnessRegAtom p ** acc) empAssertion

private def hcoreWitnessMemFold : Assertion :=
  hcoreWitnessMems.foldr (fun p acc => hcoreWitnessMemAtom p ** acc) empAssertion

private def hcoreWitnessRegHeapFold : PartialState :=
  hcoreWitnessRegs.foldr
    (fun p acc => (hcoreWitnessRegHeap p).union acc) PartialState.empty

private def hcoreWitnessMemHeapFold : PartialState :=
  hcoreWitnessMems.foldr
    (fun p acc => (hcoreWitnessMemHeap p).union acc) PartialState.empty

private def hcoreWitnessMemFoldNoG : Assertion :=
  hcoreWitnessMemsNoG.foldr
    (fun p acc => hcoreWitnessMemAtom p ** acc) empAssertion

private def hcoreWitnessMemHeapFoldNoG : PartialState :=
  hcoreWitnessMemsNoG.foldr
    (fun p acc => (hcoreWitnessMemHeap p).union acc) PartialState.empty

private theorem hcoreWitnessRegFold_sat :
    hcoreWitnessRegFold hcoreWitnessRegHeapFold := by
  apply sepConj_foldr_satisfiable hcoreWitnessRegAtom
    hcoreWitnessRegHeap hcoreWitnessRegs
  · intro p hp
    rfl
  · have hd : hcoreWitnessRegs.Pairwise (fun p q => p.1 ≠ q.1) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h =>
        EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantRegSingletonDisjoint h)
      hd

private theorem hcoreWitnessMemFold_sat :
    hcoreWitnessMemFold hcoreWitnessMemHeapFold := by
  apply sepConj_foldr_satisfiable hcoreWitnessMemAtom
    hcoreWitnessMemHeap hcoreWitnessMems
  · intro p hp
    rcases p with ⟨a, v⟩
    rcases (by simpa [hcoreWitnessMems] using hp) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals exact ⟨rfl, by decide⟩
  · have hd : hcoreWitnessMems.Pairwise (fun p q => p.1 ≠ q.1) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h =>
        EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantMemSingletonDisjoint h)
      hd

private theorem hcoreWitnessMemFoldNoG_sat :
    hcoreWitnessMemFoldNoG hcoreWitnessMemHeapFoldNoG := by
  apply sepConj_foldr_satisfiable hcoreWitnessMemAtom
    hcoreWitnessMemHeap hcoreWitnessMemsNoG
  · intro p hp
    rcases p with ⟨a, v⟩
    rcases (by simpa [hcoreWitnessMemsNoG] using hp) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals exact ⟨rfl, by decide⟩
  · have hd : hcoreWitnessMemsNoG.Pairwise (fun p q => p.1 ≠ q.1) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h =>
        EvmAsm.Codegen.ValidateHeaderCompose.routeInhabitantMemSingletonDisjoint h)
      hd

private theorem hcoreWitnessFold_cross :
    ∀ p ∈ hcoreWitnessRegs, ∀ q ∈ hcoreWitnessMems,
      (hcoreWitnessRegHeap p).Disjoint (hcoreWitnessMemHeap q) := by
  intro p hp q hq
  unfold hcoreWitnessRegHeap hcoreWitnessMemHeap
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem hcoreWitnessFoldNoG_cross :
    ∀ p ∈ hcoreWitnessRegs, ∀ q ∈ hcoreWitnessMemsNoG,
      (hcoreWitnessRegHeap p).Disjoint (hcoreWitnessMemHeap q) := by
  intro p hp q hq
  unfold hcoreWitnessRegHeap hcoreWitnessMemHeap
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private def hcoreWitnessAssertion : Assertion :=
  hcoreWitnessRegFold ** hcoreWitnessMemFold

private def hcoreWitnessHeap : PartialState :=
  hcoreWitnessRegHeapFold.union hcoreWitnessMemHeapFold

private theorem hcoreWitnessSat :
    hcoreWitnessAssertion hcoreWitnessHeap := by
  exact sepConj_foldr_cross_satisfiable hcoreWitnessRegAtom
    hcoreWitnessRegHeap hcoreWitnessRegs hcoreWitnessMemAtom
    hcoreWitnessMemHeap hcoreWitnessMems hcoreWitnessRegFold_sat
    hcoreWitnessMemFold_sat hcoreWitnessFold_cross

private def hcoreWitnessAssertionNoG : Assertion :=
  hcoreWitnessRegFold ** hcoreWitnessMemFoldNoG

private def hcoreWitnessHeapNoG : PartialState :=
  hcoreWitnessRegHeapFold.union hcoreWitnessMemHeapFoldNoG

private theorem hcoreWitnessSatNoG :
    hcoreWitnessAssertionNoG hcoreWitnessHeapNoG := by
  exact sepConj_foldr_cross_satisfiable hcoreWitnessRegAtom
    hcoreWitnessRegHeap hcoreWitnessRegs hcoreWitnessMemAtom
    hcoreWitnessMemHeap hcoreWitnessMemsNoG hcoreWitnessRegFold_sat
    hcoreWitnessMemFoldNoG_sat hcoreWitnessFoldNoG_cross

/-- The full core precondition is inhabited with a real, non-empty frame.

The frame is eight concrete bytes at `0x40000`, separated from all fourteen
register atoms and seven stack cells.  This is the primary non-vacuity witness;
it demonstrates that the abstract frame can carry content rather than merely
being instantiated with `empAssertion`. -/
theorem validateHeaderCorePre_nonempty_G :
    validateHeaderCorePre hcoreWitnessSpC 0 hcoreWitnessHeader 1
      hcoreWitnessParent 2 3 4 hcoreWitnessHeader 1 hcoreWitnessParent 2 3 4
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) hcoreWitnessHeap := by
  simpa [hcoreWitnessAssertion, hcoreWitnessRegFold, hcoreWitnessMemFold,
    hcoreWitnessRegAtom, hcoreWitnessMemAtom, hcoreWitnessRegs,
    hcoreWitnessMems, validateHeaderCorePre, hcoreWitnessSpC,
    hcoreWitnessHeader, hcoreWitnessParent, hcoreWitnessGAddr,
    hcoreWitnessGBytes, bytesRegion, bytesRegionAux,
    sepConj_emp_right', sepConj_assoc'] using hcoreWitnessSat

/-- The same atom conjunction is satisfiable when the abstract frame is empty.

This is intentionally retained beside the non-empty witness for comparison:
an `empAssertion` proof alone would not establish that a real framed resource
can coexist with the caller-owned atoms. -/
theorem validateHeaderCorePre_emp_G :
    ∃ h : PartialState,
      validateHeaderCorePre hcoreWitnessSpC 0 hcoreWitnessHeader 1
        hcoreWitnessParent 2 3 4 hcoreWitnessHeader 1 hcoreWitnessParent 2 3 4
        empAssertion h := by
  refine ⟨hcoreWitnessHeapNoG, ?_⟩
  simpa [hcoreWitnessAssertionNoG, hcoreWitnessRegFold,
    hcoreWitnessMemFoldNoG, hcoreWitnessRegAtom, hcoreWitnessMemAtom,
    hcoreWitnessRegs, hcoreWitnessMemsNoG, validateHeaderCorePre,
    hcoreWitnessSpC, hcoreWitnessHeader, hcoreWitnessParent,
    sepConj_emp_right', sepConj_assoc'] using hcoreWitnessSatNoG

/-- The complete caller-side premise conjunction is inhabited with the
non-empty frame, including the stack-pointer relation, return-address
alignment, frame `pcFree`, and `validateHeaderCorePre` itself.  This is a
non-vacuity result only: the abstract `hcore` route premise is still
undischarged and has no semantic callers. -/
theorem validateHeaderCorePremises_nonempty_G :
    ∃ h : PartialState,
      hcoreWitnessSpC = hcoreWitnessSp0 + signExtend12 (-56 : BitVec 12) ∧
      ((0 : Word) &&& ~~~(1 : Word) = 0) ∧
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes).pcFree ∧
      validateHeaderCorePre hcoreWitnessSpC 0 hcoreWitnessHeader 1
        hcoreWitnessParent 2 3 4 hcoreWitnessHeader 1 hcoreWitnessParent 2 3 4
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) h := by
  refine ⟨hcoreWitnessHeap, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact bytesRegion_pcFree _ _
  · exact validateHeaderCorePre_nonempty_G

end EvmAsm.Codegen.ValidateHeaderWhole
