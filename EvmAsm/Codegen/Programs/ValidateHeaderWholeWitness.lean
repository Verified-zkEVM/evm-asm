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

set_option maxRecDepth 8000

namespace EvmAsm.Codegen.ValidateHeaderWhole

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCompose
open EvmAsm.Codegen.ValidateHeaderInlineArms

abbrev hcoreWitnessSpC : Word := 0x10000
abbrev hcoreWitnessSp0 : Word := 0x10038
abbrev hcoreWitnessHeader : Word := 0x20000
abbrev hcoreWitnessParent : Word := 0x30000
abbrev hcoreWitnessParent2 : Word := 0x31000
abbrev hcoreWitnessGAddr : Word := 0x40000

def hcoreWitnessHeaderSpec : EvmAsm.Stateless.SpecRef.Header :=
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

def hcoreWitnessHeaderStruct : List (BitVec 8) :=
  headerCoreStructBytes hcoreWitnessHeaderSpec

def hcoreWitnessParentStruct : List (BitVec 8) :=
  headerCoreStructBytes hcoreWitnessHeaderSpec

def hcoreWitnessGBytes : List (BitVec 8) :=
  [1, 2, 3, 4, 5, 6, 7, 8]

def hcoreWitnessRegs : List (Reg × Word) :=
  [(.x1, 0), (.x2, hcoreWitnessSpC), (.x8, hcoreWitnessHeader), (.x9, 1),
   (.x18, hcoreWitnessParent), (.x19, hcoreWitnessParent2), (.x20, 3), (.x21, 4),
   (.x10, hcoreWitnessHeader), (.x11, 1), (.x12, hcoreWitnessParent),
   (.x13, hcoreWitnessParent2), (.x14, 3), (.x15, 4)]

def hcoreWitnessStructMems (base : Word) (bs : List (BitVec 8)) : List (Word × Word) :=
  [(base, packBytes (bs.take 8)),
   (base + 8, packBytes ((bs.drop 8).take 8)),
   (base + 16, packBytes ((bs.drop 16).take 8)),
   (base + 24, packBytes ((bs.drop 24).take 8)),
   (base + 32, packBytes ((bs.drop 32).take 8)),
   (base + 40, packBytes ((bs.drop 40).take 8)),
   (base + 48, packBytes ((bs.drop 48).take 8)),
   (base + 56, packBytes ((bs.drop 56).take 8)),
   (base + 64, packBytes ((bs.drop 64).take 8)),
   (base + 72, packBytes ((bs.drop 72).take 8)),
   (base + 80, packBytes ((bs.drop 80).take 8)),
   (base + 88, packBytes ((bs.drop 88).take 8)),
   (base + 96, packBytes ((bs.drop 96).take 8)),
   (base + 104, packBytes ((bs.drop 104).take 8)),
   (base + 112, packBytes ((bs.drop 112).take 8)),
   (base + 120, packBytes ((bs.drop 120).take 8)),
   (base + 128, packBytes ((bs.drop 128).take 8)),
   (base + 136, packBytes ((bs.drop 136).take 8))]

def hcoreWitnessMems : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, 1), (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, hcoreWitnessParent2), (hcoreWitnessSpC + 40, 3),
   (hcoreWitnessSpC + 48, 4)] ++
  hcoreWitnessStructMems hcoreWitnessParent hcoreWitnessHeaderStruct ++
  hcoreWitnessStructMems hcoreWitnessParent2 hcoreWitnessParentStruct ++
  [(hcoreWitnessGAddr, packBytes hcoreWitnessGBytes)]

def hcoreWitnessMemsNoG : List (Word × Word) :=
  [(hcoreWitnessSpC, 0), (hcoreWitnessSpC + 8, hcoreWitnessHeader),
   (hcoreWitnessSpC + 16, 1), (hcoreWitnessSpC + 24, hcoreWitnessParent),
   (hcoreWitnessSpC + 32, hcoreWitnessParent2), (hcoreWitnessSpC + 40, 3),
   (hcoreWitnessSpC + 48, 4)] ++
  hcoreWitnessStructMems hcoreWitnessParent hcoreWitnessHeaderStruct ++
  hcoreWitnessStructMems hcoreWitnessParent2 hcoreWitnessParentStruct

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
    simp [hcoreWitnessMems, hcoreWitnessStructMems] at hp
    rcases hp with
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩
    all_goals
      simp only [hcoreWitnessMemAtom, hcoreWitnessMemHeap, memIs,
        PartialState.singletonMem]
      exact ⟨by trivial, by decide⟩
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
    simp [hcoreWitnessMemsNoG, hcoreWitnessStructMems] at hp
    rcases hp with
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩ |       ⟨rfl, rfl⟩
    all_goals
      simp only [hcoreWitnessMemAtom, hcoreWitnessMemHeap, memIs,
        PartialState.singletonMem]
      exact ⟨by trivial, by decide⟩
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
    validateHeaderCorePre hcoreWitnessHeaderSpec hcoreWitnessHeaderSpec
      hcoreWitnessSpC 0 hcoreWitnessHeader 1
      hcoreWitnessParent hcoreWitnessParent2 3 4
      hcoreWitnessHeaderStruct hcoreWitnessParentStruct
      hcoreWitnessHeader 1 hcoreWitnessParent hcoreWitnessParent2 3 4
      (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) hcoreWitnessHeap := by
  simpa [hcoreWitnessAssertion, hcoreWitnessRegFold, hcoreWitnessMemFold,
    hcoreWitnessRegAtom, hcoreWitnessMemAtom, hcoreWitnessRegs,
    hcoreWitnessMems, hcoreWitnessStructMems, hcoreWitnessHeaderStruct,
    hcoreWitnessParentStruct, headerCoreStructBytes, hcoreWitnessHeaderSpec,
    validateHeaderCorePre, validateHeaderCoreFrame, headerCoreStructRelation,
    hcoreWitnessSpC, hcoreWitnessHeader,
    hcoreWitnessParent, hcoreWitnessGAddr, hcoreWitnessGBytes,
    bytesRegion, bytesRegionAux,
    pure_true_eq_emp, sepConj_emp_right', sepConj_assoc'] using hcoreWitnessSat

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
      validateHeaderCorePre hcoreWitnessHeaderSpec hcoreWitnessHeaderSpec
        hcoreWitnessSpC 0 hcoreWitnessHeader 1
        hcoreWitnessParent hcoreWitnessParent2 3 4
        hcoreWitnessHeaderStruct hcoreWitnessParentStruct
        hcoreWitnessHeader 1 hcoreWitnessParent hcoreWitnessParent2 3 4
        (bytesRegion hcoreWitnessGAddr hcoreWitnessGBytes) h := by
  refine ⟨hcoreWitnessHeap, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact bytesRegion_pcFree _ _
  · exact validateHeaderCorePre_nonempty_G

end EvmAsm.Codegen.ValidateHeaderWhole
