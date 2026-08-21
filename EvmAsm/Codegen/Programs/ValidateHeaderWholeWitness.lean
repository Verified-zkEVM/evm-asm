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
open EvmAsm.Codegen.ValidateHeaderCompose
open EvmAsm.Codegen.ValidateHeaderInlineArms

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

/-! ## A concrete hcore counterexample

The core precondition does not own the header bytes that the first instruction
loads.  The following state gives that missing cell to a frame with value
zero while the SpecRef header says `number = 1`.  The linked code therefore
takes the status-1 arm although the status-1 postcondition is false.  This is
kept as a kernel-checked regression witness rather than papering over the
missing input relation with another hcore premise. -/

def hcoreCounterHeader : EvmAsm.Stateless.SpecRef.Header :=
  { isCurrentFork := true, parentHash := List.replicate 32 0,
    ommersHash := List.replicate 32 0, coinbase := List.replicate 20 0,
    stateRoot := List.replicate 32 0, transactionsRoot := List.replicate 32 0,
    receiptRoot := List.replicate 32 0, bloom := List.replicate 256 0,
    difficulty := 0, number := 1, gasLimit := 30000000, gasUsed := 0,
    timestamp := 1, extraData := [], prevRandao := List.replicate 32 0,
    nonce := List.replicate 8 0, baseFeePerGas := 7,
    withdrawalsRoot := List.replicate 32 0, blobGasUsed := 0,
    excessBlobGas := 0, parentBeaconBlockRoot := List.replicate 32 0,
    requestsHash := List.replicate 32 0,
    blockAccessListHash := List.replicate 32 0, slotNumber := 1 }

def hcoreCounterCell : Word := hcoreWitnessHeader + 64

def hcoreCounterHeap : PartialState :=
  hcoreWitnessHeap.union (PartialState.singletonMem hcoreCounterCell 0)

def hcoreCounterState : MachineState where
  regs := fun r => (hcoreCounterHeap.regs r).getD 0
  mem := fun a => (hcoreCounterHeap.mem a).getD 0
  code := callerCode
  pc := H + 56

private theorem hcoreCounterHeap_compatible :
    hcoreCounterHeap.CompatibleWith hcoreCounterState := by
  have hx0 : hcoreCounterHeap.regs .x0 = none := by
    simp [hcoreCounterHeap, hcoreWitnessHeap, PartialState.union,
      hcoreWitnessRegHeapFold, hcoreWitnessMemHeapFold,
      hcoreWitnessRegHeap, hcoreWitnessMemHeap, hcoreWitnessRegs,
      hcoreWitnessMems, PartialState.singletonReg,
      PartialState.singletonMem, PartialState.empty]
  have hcode : ∀ a, hcoreCounterHeap.code a = none := by
    intro a
    simp [hcoreCounterHeap, hcoreWitnessHeap, PartialState.union,
      hcoreWitnessRegHeapFold, hcoreWitnessMemHeapFold,
      hcoreWitnessRegHeap, hcoreWitnessMemHeap,
      hcoreWitnessRegs, hcoreWitnessMems,
      PartialState.singletonReg, PartialState.singletonMem,
      PartialState.empty]
  have hpc : hcoreCounterHeap.pc = none := by
    simp [hcoreCounterHeap, hcoreWitnessHeap, PartialState.union,
      hcoreWitnessRegHeapFold, hcoreWitnessMemHeapFold,
      hcoreWitnessRegHeap, hcoreWitnessMemHeap,
      hcoreWitnessRegs, hcoreWitnessMems,
      PartialState.singletonReg, PartialState.singletonMem,
      PartialState.empty]
  have hpublic : hcoreCounterHeap.publicValues = none := by
    simp [hcoreCounterHeap, hcoreWitnessHeap, PartialState.union,
      hcoreWitnessRegHeapFold, hcoreWitnessMemHeapFold,
      hcoreWitnessRegHeap, hcoreWitnessMemHeap,
      hcoreWitnessRegs, hcoreWitnessMems,
      PartialState.singletonReg, PartialState.singletonMem,
      PartialState.empty]
  have hprivate : hcoreCounterHeap.privateInput = none := by
    simp [hcoreCounterHeap, hcoreWitnessHeap, PartialState.union,
      hcoreWitnessRegHeapFold, hcoreWitnessMemHeapFold,
      hcoreWitnessRegHeap, hcoreWitnessMemHeap,
      hcoreWitnessRegs, hcoreWitnessMems,
      PartialState.singletonReg, PartialState.singletonMem,
      PartialState.empty]
  have hinput : hcoreCounterHeap.inputBufBase = none := by
    simp [hcoreCounterHeap, hcoreWitnessHeap, PartialState.union,
      hcoreWitnessRegHeapFold, hcoreWitnessMemHeapFold,
      hcoreWitnessRegHeap, hcoreWitnessMemHeap,
      hcoreWitnessRegs, hcoreWitnessMems,
      PartialState.singletonReg, PartialState.singletonMem,
      PartialState.empty]
  unfold PartialState.CompatibleWith hcoreCounterState
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v hv
    cases r
    · simp [hx0] at hv
    all_goals
      simp only [MachineState.getReg]
      rw [hv]
      rfl
  · intro a v hv
    simp only [MachineState.getMem]
    rw [hv]
    rfl
  · intro a i hi
    rw [hcode a] at hi
    cases hi
  · intro v hv
    rw [hpc] at hv
    cases hv
  · intro v hv
    rw [hpublic] at hv
    cases hv
  · intro v hv
    rw [hprivate] at hv
    cases hv
  · intro v hv
    rw [hinput] at hv
    cases hv

private theorem hcoreWitnessHeap_counterCell_none :
    hcoreWitnessHeap.mem hcoreCounterCell = none := by
  simp [hcoreWitnessHeap, hcoreWitnessRegHeapFold,
    hcoreWitnessMemHeapFold, hcoreWitnessRegHeap, hcoreWitnessMemHeap,
    hcoreWitnessRegs, hcoreWitnessMems, hcoreCounterCell,
    hcoreWitnessHeader, PartialState.union, PartialState.singletonReg,
    PartialState.singletonMem, PartialState.empty]

private theorem hcoreCounterHeap_disjoint :
    hcoreWitnessHeap.Disjoint (PartialState.singletonMem hcoreCounterCell 0) := by
  refine ⟨fun _ => Or.inr rfl, ?_, fun _ => Or.inr rfl,
    Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
  intro a
  by_cases ha : a = hcoreCounterCell
  · exact Or.inl (by simpa [ha] using hcoreWitnessHeap_counterCell_none)
  · exact Or.inr (by simp [PartialState.singletonMem, ha])

theorem hcoreCounterPre_holds :
    (validateHeaderCorePre hcoreWitnessSpC 0 hcoreWitnessHeader 1
      hcoreWitnessParent 2 3 4 hcoreWitnessHeader 1 hcoreWitnessParent 2 3 4
      ((bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) **
        memIs hcoreCounterCell 0)).holdsFor hcoreCounterState := by
  refine ⟨hcoreCounterHeap, hcoreCounterHeap_compatible, ?_⟩
  have hcell : memIs hcoreCounterCell 0
      (PartialState.singletonMem hcoreCounterCell 0) := by
    exact ⟨rfl, by decide⟩
  have hassert :
      (hcoreWitnessAssertion ** memIs hcoreCounterCell 0)
        hcoreCounterHeap := by
    exact ⟨hcoreWitnessHeap, PartialState.singletonMem hcoreCounterCell 0,
      hcoreCounterHeap_disjoint, rfl, hcoreWitnessSat, hcell⟩
  simpa [validateHeaderCorePre, hcoreWitnessAssertion,
    hcoreWitnessRegFold, hcoreWitnessMemFold, hcoreWitnessRegAtom,
    hcoreWitnessMemAtom, hcoreWitnessRegs, hcoreWitnessMems,
    hcoreWitnessSpC, hcoreWitnessHeader, hcoreWitnessParent,
    hcoreWitnessGAddr, hcoreWitnessGBytes, hcoreCounterCell,
    bytesRegion, bytesRegionAux, sepConj_emp_right', sepConj_assoc'] using hassert

private theorem hcoreCounter_step4_pc :
    (stepN 4 hcoreCounterState).map MachineState.pc = some (H + 352) := by
  simp only [stepN, hcoreCounterState, Option.bind]
  simp [step,
    hcoreCounterHeap,
    hcoreWitnessHeap, hcoreWitnessRegHeapFold, hcoreWitnessMemHeapFold,
    hcoreWitnessRegHeap, hcoreWitnessMemHeap, hcoreWitnessRegs,
    hcoreWitnessMems, hcoreCounterCell, hcoreWitnessHeader,
    PartialState.union,
    PartialState.singletonReg,
    PartialState.singletonMem, PartialState.empty,
    isValidDwordAccess, isValidMemAddr, isAligned8, Rv64.MEM_START,
    Rv64.MEM_END, Rv64.INPUT_MEM_START, Rv64.INPUT_MEM_END,
    Rv64.RAM_MEM_START, Rv64.RAM_MEM_END]; decide

private theorem hcoreCounter_step4_x10 :
    (stepN 4 hcoreCounterState).map (fun s => s.getReg .x10) = some 1 := by
  simp only [stepN, hcoreCounterState, Option.bind]
  simp [step,
    hcoreCounterHeap,
    hcoreWitnessHeap, hcoreWitnessRegHeapFold, hcoreWitnessMemHeapFold,
    hcoreWitnessRegHeap, hcoreWitnessMemHeap, hcoreWitnessRegs,
    hcoreWitnessMems, hcoreCounterCell, hcoreWitnessHeader,
    PartialState.union,
    PartialState.singletonReg,
    PartialState.singletonMem, PartialState.empty,
    isValidDwordAccess, isValidMemAddr, isAligned8, Rv64.MEM_START,
    Rv64.MEM_END, Rv64.INPUT_MEM_START, Rv64.INPUT_MEM_END,
    Rv64.RAM_MEM_START, Rv64.RAM_MEM_END]; decide

private theorem hcoreCounter_step1_pc :
    (stepN 1 hcoreCounterState).map MachineState.pc = some (H + 60) := by
  simp only [stepN, hcoreCounterState, Option.bind]
  simp [step, hcoreCounterHeap,
    hcoreWitnessHeap, hcoreWitnessRegHeapFold, hcoreWitnessMemHeapFold,
    hcoreWitnessRegHeap, hcoreWitnessMemHeap, hcoreWitnessRegs,
    hcoreWitnessMems, hcoreCounterCell, hcoreWitnessHeader,
    PartialState.union, PartialState.singletonReg,
    PartialState.singletonMem, PartialState.empty,
    isValidDwordAccess, isValidMemAddr, isAligned8, Rv64.MEM_START,
    Rv64.MEM_END, Rv64.INPUT_MEM_START, Rv64.INPUT_MEM_END,
    Rv64.RAM_MEM_START, Rv64.RAM_MEM_END]; decide

private theorem hcoreCounter_step2_pc :
    (stepN 2 hcoreCounterState).map MachineState.pc = some (H + 260) := by
  simp only [stepN, hcoreCounterState, Option.bind]
  simp [step,
    hcoreCounterHeap, hcoreWitnessHeap, hcoreWitnessRegHeapFold,
    hcoreWitnessMemHeapFold, hcoreWitnessRegHeap, hcoreWitnessMemHeap,
    hcoreWitnessRegs, hcoreWitnessMems, hcoreCounterCell, hcoreWitnessHeader,
    PartialState.union,
    PartialState.singletonReg, PartialState.singletonMem, PartialState.empty,
    isValidDwordAccess, isValidMemAddr, isAligned8, Rv64.MEM_START,
    Rv64.MEM_END, Rv64.INPUT_MEM_START, Rv64.INPUT_MEM_END,
    Rv64.RAM_MEM_START, Rv64.RAM_MEM_END]; decide

private theorem hcoreCounter_step3_pc :
    (stepN 3 hcoreCounterState).map MachineState.pc = some (H + 264) := by
  simp only [stepN, hcoreCounterState, Option.bind]
  simp [step,
    hcoreCounterHeap, hcoreWitnessHeap, hcoreWitnessRegHeapFold,
    hcoreWitnessMemHeapFold, hcoreWitnessRegHeap, hcoreWitnessMemHeap,
    hcoreWitnessRegs, hcoreWitnessMems, hcoreCounterCell, hcoreWitnessHeader,
    PartialState.union,
    PartialState.singletonReg, PartialState.singletonMem, PartialState.empty,
    isValidDwordAccess, isValidMemAddr, isAligned8, Rv64.MEM_START,
    Rv64.MEM_END, Rv64.INPUT_MEM_START, Rv64.INPUT_MEM_END,
    Rv64.RAM_MEM_START, Rv64.RAM_MEM_END]; decide

private theorem corePost_status_and_result
    (parentSpec headerSpec : EvmAsm.Stateless.SpecRef.Header)
    (status spC raIn headerPtr : Word)
    (rawBytes : List (BitVec 8))
    (o1 o8 o9 o18 o19 o20 o21 : Word) (G : Assertion)
    {s : MachineState}
    (hpost : (validateHeaderCorePost parentSpec headerSpec status spC raIn
      headerPtr rawBytes o1 o8 o9 o18 o19 o20 o21 G).holdsFor s) :
    s.getReg .x10 = status ∧
      validateHeaderStatusResult parentSpec headerSpec status headerPtr rawBytes := by
  have hreg := holdsFor_sepConj_elim_left hpost
  have hreg' : s.getReg .x10 = status := holdsFor_regIs.mp hreg
  have hp := hpost
  unfold validateHeaderCorePost at hp
  extract_pure_deep hp
  have hresult := holdsFor_pure.mp (holdsFor_sepConj_elim_left hp)
  exact ⟨hreg', hresult⟩

theorem validateHeaderCoreContract_counterexample :
    ¬ validateHeaderCoreContract 4 callerCode
      hcoreCounterHeader hcoreCounterHeader
      hcoreWitnessSpC 0 hcoreWitnessHeader 1 hcoreWitnessParent 2 3 4
      [] 0 hcoreWitnessHeader 1 hcoreWitnessParent 2 3 4
      ((bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) **
        memIs hcoreCounterCell 0) := by
  intro hcore
  have hR : empAssertion.pcFree := pcFree_emp
  have hcr : callerCode.SatisfiedBy hcoreCounterState := by
    intro a i hi
    simpa only [hcoreCounterState] using hi
  have hPR :
      (validateHeaderCorePre hcoreWitnessSpC 0 hcoreWitnessHeader 1
        hcoreWitnessParent 2 3 4 hcoreWitnessHeader 1 hcoreWitnessParent 2 3 4
        ((bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) **
          memIs hcoreCounterCell 0) ** empAssertion).holdsFor
        hcoreCounterState := by
    obtain ⟨h, hc, hp⟩ := hcoreCounterPre_holds
    refine ⟨h, hc, ?_⟩
    exact ⟨h, PartialState.empty,
      ⟨fun _ => Or.inr rfl, fun _ => Or.inr rfl, fun _ => Or.inr rfl,
        Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl⟩,
      PartialState.union_empty_right, hp, rfl⟩
  obtain ⟨k, hk, s', hstep, exit, hex, hpcExit, hpost⟩ :=
    hcore empAssertion hR hcoreCounterState hcr hPR rfl
  have hExitPC : exit.1 = H + 352 := by
    simp [validateHeaderCoreExits] at hex
    rcases hex with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp_all
  have hsPc : s'.pc = H + 352 := hpcExit ▸ hExitPC
  have hkle : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hkle with rfl | rfl | rfl | rfl | rfl
  · have htarget :
        (stepN 0 hcoreCounterState).map MachineState.pc = some (H + 352) := by
      rw [hstep]
      simp [hsPc]
    simp [stepN, hcoreCounterState] at htarget
  · have htarget :
        (stepN 1 hcoreCounterState).map MachineState.pc = some (H + 352) := by
      rw [hstep]
      simp [hsPc]
    rw [hcoreCounter_step1_pc] at htarget
    simp at htarget
  · have htarget :
        (stepN 2 hcoreCounterState).map MachineState.pc = some (H + 352) := by
      rw [hstep]
      simp [hsPc]
    rw [hcoreCounter_step2_pc] at htarget
    simp at htarget
  · have htarget :
        (stepN 3 hcoreCounterState).map MachineState.pc = some (H + 352) := by
      rw [hstep]
      simp [hsPc]
    rw [hcoreCounter_step3_pc] at htarget
    simp at htarget
  · have hx10 : s'.getReg .x10 = 1 := by
      have hx := hcoreCounter_step4_x10
      rw [hstep] at hx
      simpa using hx
    have hfalse :
        ¬ validateHeaderStatusResult hcoreCounterHeader hcoreCounterHeader 1
          hcoreWitnessHeader [] := by
      simp [validateHeaderStatusResult]
      decide
    have hpostCase : ∀ (status : Word),
        (validateHeaderCorePost hcoreCounterHeader hcoreCounterHeader status
          hcoreWitnessSpC 0 hcoreWitnessHeader [] 0 hcoreWitnessHeader
          1 hcoreWitnessParent 2 3 4
          ((bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) **
            memIs hcoreCounterCell 0) ** empAssertion).holdsFor s' →
        s'.getReg .x10 = status ∧
          validateHeaderStatusResult hcoreCounterHeader hcoreCounterHeader status
            hcoreWitnessHeader [] := by
      intro status hp
      exact corePost_status_and_result hcoreCounterHeader hcoreCounterHeader status
        hcoreWitnessSpC 0 hcoreWitnessHeader [] 0 hcoreWitnessHeader
        1 hcoreWitnessParent 2 3 4
        ((bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) **
          memIs hcoreCounterCell 0) (holdsFor_sepConj_elim_left hp)
    simp [validateHeaderCoreExits] at hex
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      have hsr := hpostCase _ hpost
      rcases hsr with ⟨hstatus, hresult⟩
      first
      | bv_omega
      | exact hfalse hresult

end EvmAsm.Codegen.ValidateHeaderWhole
