/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmptySat

  #12193: concrete MachineState model for the empty-miss whole-routine pre.
  Satisfiability is a MODEL — production reachability of count=0 ∧ enable=1
  is settled separately by the k3 call-order trace.

  Pattern: atom list + sepConj_foldr_satisfiable (codex wclh_sample_entryState_exists).
-/
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmpty
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Word

namespace EvmAsm.Codegen.WitnessLookupByHashIndexedEmptySat

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec

private abbrev B : Word := (IndexedB : Word)
private abbrev CR : CodeReq := fullCode

/-! ## Sample values -/

def emptySampleSp0 : Word := (0xa0050000 : Word)
def emptySampleRet : Word := (0x80006300 : Word)
def emptySampleHashPtr : Word := (0x40000010 : Word)
def emptySampleOutOff : Word := (0xa0010008 : Word)
def emptySampleOutLen : Word := (0xa0010010 : Word)

def emptySampleSaved : IndexedSaved where
  ra := emptySampleRet
  s0 := (0x101 : Word)
  s1 := (0x202 : Word)
  s2 := (0x303 : Word)
  s3 := (0x404 : Word)
  s4 := (0x505 : Word)
  s5 := (0x606 : Word)
  s6 := (0x707 : Word)

def emptySampleNewSp : Word :=
  emptySampleSp0 + signExtend12 (-64 : BitVec 12)

theorem emptySampleNewSp_eq : emptySampleNewSp = (0xa004ffc0 : Word) := by
  unfold emptySampleNewSp emptySampleSp0; decide

theorem emptySampleRet_even :
    (emptySampleRet &&& ~~~(1 : Word)) = emptySampleRet := by
  unfold emptySampleRet; decide

/-- Whole-routine empty-miss pre at the sample point (matches Empty.lean top). -/
def emptyEntryPre : Assertion :=
  ((.x2 ↦ᵣ emptySampleSp0) **
    regsAt indexedFrame (indexedSavedVals emptySampleSaved) **
    (.x12 ↦ᵣ emptySampleHashPtr) ** (.x13 ↦ᵣ emptySampleOutOff) **
    (.x14 ↦ᵣ emptySampleOutLen) **
    (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
    frameSlotsOwn indexedFrame emptySampleNewSp **
    (WidxCountLoc ↦ₘ (0 : Word)))

/-! ## Atom vocabulary -/

private structure MemAtom where
  a : Word
  v : Word
  valid : isValidDwordAccess a = true

private inductive EmptyAtom where
  | reg (r : Reg) (v : Word)
  | mem (m : MemAtom)
  | own (m : MemAtom)

private def emptyAtomAssertion : EmptyAtom → Assertion
  | .reg r v => (r ↦ᵣ v)
  | .mem m => (m.a ↦ₘ m.v)
  | .own m => memOwn m.a

private def emptyAtomHeap : EmptyAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .mem m => PartialState.singletonMem m.a m.v
  | .own m => PartialState.singletonMem m.a 0

private inductive EmptyResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def emptyAtomResource : EmptyAtom → EmptyResource
  | .reg r _ => .reg r
  | .mem m => .mem m.a
  | .own m => .mem m.a

private theorem empty_reg_reg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r; right; simp [PartialState.singletonReg, hne]
  · left; simp [PartialState.singletonReg, h]

private theorem empty_mem_mem_disjoint {a1 a2 : Word} {v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a; right; simp [PartialState.singletonMem, hne]
  · left; simp [PartialState.singletonMem, h]

private theorem empty_reg_mem_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem empty_mem_reg_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  empty_reg_mem_disjoint.symm

private theorem emptyAtomHeap_disjoint_of_resource_ne {x y : EmptyAtom}
    (h : emptyAtomResource x ≠ emptyAtomResource y) :
    (emptyAtomHeap x).Disjoint (emptyAtomHeap y) := by
  cases x <;> cases y
  · apply empty_reg_reg_disjoint; simpa [emptyAtomResource] using h
  · exact empty_reg_mem_disjoint
  · exact empty_reg_mem_disjoint
  · exact empty_mem_reg_disjoint
  · apply empty_mem_mem_disjoint; simpa [emptyAtomResource] using h
  · apply empty_mem_mem_disjoint; simpa [emptyAtomResource] using h
  · exact empty_mem_reg_disjoint
  · apply empty_mem_mem_disjoint; simpa [emptyAtomResource] using h
  · apply empty_mem_mem_disjoint; simpa [emptyAtomResource] using h

/-! ## Concrete slot addresses (page-aligned newSp + offs) -/

private theorem empty_sign0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem empty_sign8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem empty_sign16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
private theorem empty_sign24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
private theorem empty_sign32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
private theorem empty_sign40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide
private theorem empty_sign48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
private theorem empty_sign56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

-- Concrete frame-slot bases (newSp = 0xa004ffc0).
private def S0 : Word := (0xa004ffc0 : Word)
private def S8 : Word := (0xa004ffc8 : Word)
private def S16 : Word := (0xa004ffd0 : Word)
private def S24 : Word := (0xa004ffd8 : Word)
private def S32 : Word := (0xa004ffe0 : Word)
private def S40 : Word := (0xa004ffe8 : Word)
private def S48 : Word := (0xa004fff0 : Word)
private def S56 : Word := (0xa004fff8 : Word)

private theorem emptySlotAddr0 :
    emptySampleNewSp + signExtend12 (0 : BitVec 12) = S0 := by
  simp only [emptySampleNewSp_eq, empty_sign0, S0]; decide
private theorem emptySlotAddr8 :
    emptySampleNewSp + signExtend12 (8 : BitVec 12) = S8 := by
  simp only [emptySampleNewSp_eq, empty_sign8, S8]; decide
private theorem emptySlotAddr16 :
    emptySampleNewSp + signExtend12 (16 : BitVec 12) = S16 := by
  simp only [emptySampleNewSp_eq, empty_sign16, S16]; decide
private theorem emptySlotAddr24 :
    emptySampleNewSp + signExtend12 (24 : BitVec 12) = S24 := by
  simp only [emptySampleNewSp_eq, empty_sign24, S24]; decide
private theorem emptySlotAddr32 :
    emptySampleNewSp + signExtend12 (32 : BitVec 12) = S32 := by
  simp only [emptySampleNewSp_eq, empty_sign32, S32]; decide
private theorem emptySlotAddr40 :
    emptySampleNewSp + signExtend12 (40 : BitVec 12) = S40 := by
  simp only [emptySampleNewSp_eq, empty_sign40, S40]; decide
private theorem emptySlotAddr48 :
    emptySampleNewSp + signExtend12 (48 : BitVec 12) = S48 := by
  simp only [emptySampleNewSp_eq, empty_sign48, S48]; decide
private theorem emptySlotAddr56 :
    emptySampleNewSp + signExtend12 (56 : BitVec 12) = S56 := by
  simp only [emptySampleNewSp_eq, empty_sign56, S56]; decide

private theorem emptySlot0_valid : isValidDwordAccess S0 = true := by unfold S0; decide
private theorem emptySlot8_valid : isValidDwordAccess S8 = true := by unfold S8; decide
private theorem emptySlot16_valid : isValidDwordAccess S16 = true := by unfold S16; decide
private theorem emptySlot24_valid : isValidDwordAccess S24 = true := by unfold S24; decide
private theorem emptySlot32_valid : isValidDwordAccess S32 = true := by unfold S32; decide
private theorem emptySlot40_valid : isValidDwordAccess S40 = true := by unfold S40; decide
private theorem emptySlot48_valid : isValidDwordAccess S48 = true := by unfold S48; decide
private theorem emptySlot56_valid : isValidDwordAccess S56 = true := by unfold S56; decide

private theorem WidxCountLoc_valid :
    isValidDwordAccess WidxCountLoc = true := by
  unfold WidxCountLoc GuestAddrs.widx_count; decide

private def mkOwn (a : Word) (h : isValidDwordAccess a = true) : MemAtom :=
  ⟨a, 0, h⟩

/-! ## Flat atom list matching flattened `emptyEntryPre` order

    x2 · frame regs · x12 · x13 · x14 · x5 · x10 · frame slots · count -/

private def emptyAtoms : List EmptyAtom :=
  [ .reg .x2 emptySampleSp0
  , .reg .x1 emptySampleRet
  , .reg .x8 (0x101 : Word)
  , .reg .x9 (0x202 : Word)
  , .reg .x18 (0x303 : Word)
  , .reg .x19 (0x404 : Word)
  , .reg .x20 (0x505 : Word)
  , .reg .x21 (0x606 : Word)
  , .reg .x22 (0x707 : Word)
  , .reg .x12 emptySampleHashPtr
  , .reg .x13 emptySampleOutOff
  , .reg .x14 emptySampleOutLen
  , .reg .x5 (0 : Word)
  , .reg .x10 (0 : Word)
  , .own (mkOwn S0 emptySlot0_valid)
  , .own (mkOwn S8 emptySlot8_valid)
  , .own (mkOwn S16 emptySlot16_valid)
  , .own (mkOwn S24 emptySlot24_valid)
  , .own (mkOwn S32 emptySlot32_valid)
  , .own (mkOwn S40 emptySlot40_valid)
  , .own (mkOwn S48 emptySlot48_valid)
  , .own (mkOwn S56 emptySlot56_valid)
  , .mem ⟨WidxCountLoc, 0, WidxCountLoc_valid⟩
  ]

private theorem emptyAtoms_resource_pairwise :
    emptyAtoms.Pairwise
      (fun x y => emptyAtomResource x ≠ emptyAtomResource y) := by
  unfold emptyAtoms emptySampleSp0 emptySampleRet
    emptySampleHashPtr emptySampleOutOff emptySampleOutLen
    mkOwn S0 S8 S16 S24 S32 S40 S48 S56
    WidxCountLoc GuestAddrs.widx_count
  decide

private theorem emptyAtoms_hsat :
    (emptyAtoms.foldr (fun x acc => emptyAtomAssertion x ** acc) empAssertion)
      (emptyAtoms.foldr (fun x acc => (emptyAtomHeap x).union acc)
        PartialState.empty) := by
  apply EvmAsm.Rv64.SAsm.sepConj_foldr_satisfiable
    emptyAtomAssertion emptyAtomHeap emptyAtoms
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | mem m => exact ⟨rfl, m.valid⟩
    | own m => exact ⟨0, rfl, m.valid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => emptyAtomHeap_disjoint_of_resource_ne h)
      emptyAtoms_resource_pairwise

private def emptyEntryHeap : PartialState :=
  emptyAtoms.foldr (fun x acc => (emptyAtomHeap x).union acc) PartialState.empty

/-- Concrete machine state mirroring `emptyEntryHeap`; code = CR. -/
def emptySampleState : MachineState where
  regs := fun r =>
    match emptyEntryHeap.regs r with
    | some v => v
    | none => (0 : Word)
  mem := fun a =>
    match emptyEntryHeap.mem a with
    | some v => v
    | none => (0 : Word)
  code := CR
  pc := B

private theorem emptyEntryHeap_x0 :
    emptyEntryHeap.regs .x0 = none := by
  unfold emptyEntryHeap emptyAtoms emptyAtomHeap emptySampleSp0 emptySampleRet
    emptySampleHashPtr emptySampleOutOff emptySampleOutLen
    mkOwn S0 S8 S16 S24 S32 S40 S48 S56
  decide

private theorem emptySampleState_getReg (r : Reg) (hr : r ≠ .x0) :
    emptySampleState.getReg r =
      (match emptyEntryHeap.regs r with | some v => v | none => (0 : Word)) := by
  cases r <;> simp_all [emptySampleState, MachineState.getReg]

private theorem emptySampleState_getMem (a : Word) :
    emptySampleState.getMem a =
      (match emptyEntryHeap.mem a with | some v => v | none => (0 : Word)) := by
  rfl

-- Singleton reg/mem heaps carry no code; the fold inherits that.
private theorem emptyAtomHeap_code_none (x : EmptyAtom) (a : Word) :
    (emptyAtomHeap x).code a = none := by
  cases x <;> rfl

private theorem emptyEntryHeap_code_none (a : Word) :
    emptyEntryHeap.code a = none := by
  unfold emptyEntryHeap
  induction emptyAtoms with
  | nil => rfl
  | cons x xs ih =>
    -- head atom carries no code; union code = tail code
    change (match (emptyAtomHeap x).code a with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (emptyAtomHeap y).union acc)
          PartialState.empty).code a) = none
    rw [emptyAtomHeap_code_none x a, ih]

private theorem emptyEntryHeap_pc_none : emptyEntryHeap.pc = none := by
  unfold emptyEntryHeap
  induction emptyAtoms with
  | nil => rfl
  | cons x xs ih =>
    have hx : (emptyAtomHeap x).pc = none := by cases x <;> rfl
    change (match (emptyAtomHeap x).pc with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (emptyAtomHeap y).union acc)
          PartialState.empty).pc) = none
    rw [hx, ih]

private theorem emptyEntryHeap_CompatibleWith :
    emptyEntryHeap.CompatibleWith emptySampleState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v h
    by_cases hr : r = .x0
    · subst r
      rw [emptyEntryHeap_x0] at h
      cases h
    · rw [emptySampleState_getReg r hr, h]
  · intro a v h
    rw [emptySampleState_getMem a, h]
  · intro a i h
    rw [emptyEntryHeap_code_none a] at h
    cases h
  · intro v h
    rw [emptyEntryHeap_pc_none] at h
    cases h
  · intro v h; cases h
  · intro v h; cases h
  · intro v h; cases h

/-- Flattened frameSlotsOwn at the sample newSp. -/
private theorem frameSlotsOwn_emptySample :
    frameSlotsOwn indexedFrame emptySampleNewSp =
      (memOwn S0 ** memOwn S8 ** memOwn S16 ** memOwn S24 **
        memOwn S32 ** memOwn S40 ** memOwn S48 ** memOwn S56) := by
  unfold frameSlotsOwn indexedFrame
  simp only [List.foldr, emptySlotAddr0, emptySlotAddr8, emptySlotAddr16,
    emptySlotAddr24, emptySlotAddr32, emptySlotAddr40, emptySlotAddr48,
    emptySlotAddr56, sepConj_emp_right']

/-- Flattened atom-fold assertion. -/
private def emptyAtomsAssert : Assertion :=
  emptyAtoms.foldr (fun x acc => emptyAtomAssertion x ** acc) empAssertion

private theorem emptyEntryPre_eq_atomsAssert :
    emptyEntryPre = emptyAtomsAssert := by
  -- Expand structural folds on the left
  unfold emptyEntryPre
  rw [regsAt_indexedFrame emptySampleSaved, frameSlotsOwn_emptySample]
  -- Expand the atom fold on the right
  unfold emptyAtomsAssert emptyAtoms emptyAtomAssertion mkOwn
  simp only [List.foldr]
  -- Concrete sample values
  simp only [emptySampleSaved, emptySampleRet,
    emptySampleSp0, emptySampleHashPtr, emptySampleOutOff, emptySampleOutLen,
    sepConj_emp_right']
  -- Flatten nested (P ** Q) ** R groups into right-assoc fold shape
  simp only [sepConj_assoc']

/-- ⭐ Concrete model: empty-miss whole-routine pre is inhabited. -/
theorem empty_entryState_exists :
    emptySampleState.pc = B ∧
    CR.SatisfiedBy emptySampleState ∧
    emptyEntryPre.holdsFor emptySampleState := by
  refine ⟨rfl, ?_, ?_⟩
  · intro a i h; exact h
  · refine ⟨emptyEntryHeap, emptyEntryHeap_CompatibleWith, ?_⟩
    rw [emptyEntryPre_eq_atomsAssert]
    exact emptyAtoms_hsat

/-- Closed triple instantiation at the sample point (secondary witness). -/
theorem empty_miss_sample_triple :
    cpsTripleWithin 28 B emptySampleRet CR
      emptyEntryPre
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ emptySampleRet) ** (.x2 ↦ᵣ emptySampleSp0) **
        (.x8 ↦ᵣ emptySampleSaved.s0) ** (.x9 ↦ᵣ emptySampleSaved.s1) **
        (.x18 ↦ᵣ emptySampleSaved.s2) ** (.x19 ↦ᵣ emptySampleSaved.s3) **
        (.x20 ↦ᵣ emptySampleSaved.s4) ** (.x21 ↦ᵣ emptySampleSaved.s5) **
        (.x22 ↦ᵣ emptySampleSaved.s6) **
        frameSlotsSaved indexedFrame emptySampleNewSp
          (indexedSavedVals emptySampleSaved) **
        ((.x5 : Reg) ↦ᵣ WidxCountLoc) ** (WidxCountLoc ↦ₘ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ emptySampleHashPtr) **
        ((.x13 : Reg) ↦ᵣ emptySampleOutOff) **
        ((.x14 : Reg) ↦ᵣ emptySampleOutLen)) := by
  have h := witness_lookup_by_hash_indexed_spec_within_empty
    emptySampleSp0 emptySampleRet emptySampleSaved
    emptySampleHashPtr emptySampleOutOff emptySampleOutLen
    (0 : Word) (0 : Word) emptySampleRet_even
  simpa [emptyEntryPre, emptySampleNewSp] using h

end EvmAsm.Codegen.WitnessLookupByHashIndexedEmptySat
