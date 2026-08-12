/-
  EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedOneHitSat

  #12193: concrete MachineState model for the one-hit whole-routine pre.
  Satisfiability is a MODEL (coverHit domain: count=1, matching hash).
-/
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedOneHitStores
import EvmAsm.Codegen.Programs.WitnessLookupByHashIndexedEmptySat
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Word
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Codegen.WitnessLookupByHashIndexedOneHitSat

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmpty
open EvmAsm.Codegen.WitnessLookupByHashIndexedEmptySat
open EvmAsm.Codegen.WitnessLookupByHashIndexedOneHit
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec

private abbrev B : Word := (IndexedB : Word)
private abbrev CR : CodeReq := fullCode

/-! ## Sample values -/

def hitSampleSp0 : Word := emptySampleSp0
def hitSampleRet : Word := emptySampleRet
def hitSampleHashPtr : Word := emptySampleHashPtr
def hitSampleOutOff : Word := emptySampleOutOff
def hitSampleOutLen : Word := emptySampleOutLen
def hitSampleOffOld : Word := (0xAAAA : Word)
def hitSampleLenOld : Word := (0xBBBB : Word)
def hitSampleV5 : Word := (0 : Word)
def hitSampleV10 : Word := (0 : Word)
def hitSampleSaved : IndexedSaved := emptySampleSaved
def hitSampleNewSp : Word := emptySampleNewSp

theorem hitSampleNewSp_eq : hitSampleNewSp = (0xa004ffc0 : Word) := emptySampleNewSp_eq
theorem hitSampleRet_even :
    (hitSampleRet &&& ~~~(1 : Word)) = hitSampleRet := emptySampleRet_even

private def hitHashDword : Word := (0x0101010101010101 : Word)

private theorem hitHashDword_eq :
    packBytes (List.replicate 8 (1 : BitVec 8)) = hitHashDword := by
  unfold packBytes hitHashDword; decide

/-- Whole-routine one-hit pre at the sample point. -/
def hitEntryPre : Assertion :=
  ((.x2 ↦ᵣ hitSampleSp0) **
    regsAt indexedFrame (indexedSavedVals { hitSampleSaved with ra := hitSampleRet }) **
    (.x12 ↦ᵣ hitSampleHashPtr) ** (.x13 ↦ᵣ hitSampleOutOff) **
    (.x14 ↦ᵣ hitSampleOutLen) **
    (.x5 ↦ᵣ hitSampleV5) ** (.x10 ↦ᵣ hitSampleV10) **
    frameSlotsOwn indexedFrame hitSampleNewSp **
    (WidxCountLoc ↦ₘ (1 : Word)) **
    hitExposedZeros **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    hitHashBytes hitSampleHashPtr **
    hitCells hitSampleOutOff hitSampleOutLen hitSampleOffOld hitSampleLenOld)

/-! ## Atom vocabulary -/

private structure MemAtom where
  a : Word
  v : Word
  valid : isValidDwordAccess a = true

private inductive HitAtom where
  | reg (r : Reg) (v : Word)
  | mem (m : MemAtom)
  | own (m : MemAtom)

private def hitAtomAssertion : HitAtom → Assertion
  | .reg r v => (r ↦ᵣ v)
  | .mem m => (m.a ↦ₘ m.v)
  | .own m => memOwn m.a

private def hitAtomHeap : HitAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .mem m => PartialState.singletonMem m.a m.v
  | .own m => PartialState.singletonMem m.a 0

private inductive HitResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def hitAtomResource : HitAtom → HitResource
  | .reg r _ => .reg r
  | .mem m => .mem m.a
  | .own m => .mem m.a

private theorem hit_reg_reg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r; right; simp [PartialState.singletonReg, hne]
  · left; simp [PartialState.singletonReg, h]

private theorem hit_mem_mem_disjoint {a1 a2 : Word} {v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a; right; simp [PartialState.singletonMem, hne]
  · left; simp [PartialState.singletonMem, h]

private theorem hit_reg_mem_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) :=
  ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem hit_mem_reg_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  hit_reg_mem_disjoint.symm

private theorem hitAtomHeap_disjoint_of_resource_ne {x y : HitAtom}
    (h : hitAtomResource x ≠ hitAtomResource y) :
    (hitAtomHeap x).Disjoint (hitAtomHeap y) := by
  cases x <;> cases y
  · apply hit_reg_reg_disjoint; simpa [hitAtomResource] using h
  · exact hit_reg_mem_disjoint
  · exact hit_reg_mem_disjoint
  · exact hit_mem_reg_disjoint
  · apply hit_mem_mem_disjoint; simpa [hitAtomResource] using h
  · apply hit_mem_mem_disjoint; simpa [hitAtomResource] using h
  · exact hit_mem_reg_disjoint
  · apply hit_mem_mem_disjoint; simpa [hitAtomResource] using h
  · apply hit_mem_mem_disjoint; simpa [hitAtomResource] using h

/-! ## Concrete addresses -/

private def S0 : Word := (0xa004ffc0 : Word)
private def S8 : Word := (0xa004ffc8 : Word)
private def S16 : Word := (0xa004ffd0 : Word)
private def S24 : Word := (0xa004ffd8 : Word)
private def S32s : Word := (0xa004ffe0 : Word)
private def S40s : Word := (0xa004ffe8 : Word)
private def S48 : Word := (0xa004fff0 : Word)
private def S56 : Word := (0xa004fff8 : Word)

private theorem se0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem se16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
private theorem se24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
private theorem se32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
private theorem se40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide
private theorem se48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
private theorem se56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

private theorem sa0 : hitSampleNewSp + signExtend12 (0 : BitVec 12) = S0 := by
  simp only [hitSampleNewSp, emptySampleNewSp_eq, se0, S0]; decide
private theorem sa8 : hitSampleNewSp + signExtend12 (8 : BitVec 12) = S8 := by
  simp only [hitSampleNewSp, emptySampleNewSp_eq, se8, S8]; decide
private theorem sa16 : hitSampleNewSp + signExtend12 (16 : BitVec 12) = S16 := by
  simp only [hitSampleNewSp, emptySampleNewSp_eq, se16, S16]; decide
private theorem sa24 : hitSampleNewSp + signExtend12 (24 : BitVec 12) = S24 := by
  simp only [hitSampleNewSp, emptySampleNewSp_eq, se24, S24]; decide
private theorem sa32 : hitSampleNewSp + signExtend12 (32 : BitVec 12) = S32s := by
  simp only [hitSampleNewSp, emptySampleNewSp_eq, se32, S32s]; decide
private theorem sa40 : hitSampleNewSp + signExtend12 (40 : BitVec 12) = S40s := by
  simp only [hitSampleNewSp, emptySampleNewSp_eq, se40, S40s]; decide
private theorem sa48 : hitSampleNewSp + signExtend12 (48 : BitVec 12) = S48 := by
  simp only [hitSampleNewSp, emptySampleNewSp_eq, se48, S48]; decide
private theorem sa56 : hitSampleNewSp + signExtend12 (56 : BitVec 12) = S56 := by
  simp only [hitSampleNewSp, emptySampleNewSp_eq, se56, S56]; decide

private theorem S0v : isValidDwordAccess S0 = true := by unfold S0; decide
private theorem S8v : isValidDwordAccess S8 = true := by unfold S8; decide
private theorem S16v : isValidDwordAccess S16 = true := by unfold S16; decide
private theorem S24v : isValidDwordAccess S24 = true := by unfold S24; decide
private theorem S32sv : isValidDwordAccess S32s = true := by unfold S32s; decide
private theorem S40sv : isValidDwordAccess S40s = true := by unfold S40s; decide
private theorem S48v : isValidDwordAccess S48 = true := by unfold S48; decide
private theorem S56v : isValidDwordAccess S56 = true := by unfold S56; decide
private theorem WCv : isValidDwordAccess WidxCountLoc = true := by
  unfold WidxCountLoc GuestAddrs.widx_count; decide

-- Record base (flat offsets match bytesRegion_coverHit)
private def R0 : Word := (0xa2e07088 : Word)
private def R8 : Word := (0xa2e07090 : Word)
private def R16 : Word := (0xa2e07098 : Word)
private def R24 : Word := (0xa2e070a0 : Word)
private def R32 : Word := (0xa2e070a8 : Word)
private def R40 : Word := (0xa2e070b0 : Word)
private theorem R0v : isValidDwordAccess R0 = true := by unfold R0; decide
private theorem R8v : isValidDwordAccess R8 = true := by unfold R8; decide
private theorem R16v : isValidDwordAccess R16 = true := by unfold R16; decide
private theorem R24v : isValidDwordAccess R24 = true := by unfold R24; decide
private theorem R32v : isValidDwordAccess R32 = true := by unfold R32; decide
private theorem R40v : isValidDwordAccess R40 = true := by unfold R40; decide
private theorem WRB_eq : WidxRecordsBase = R0 := by
  unfold WidxRecordsBase GuestAddrs.widx_records R0; decide
private theorem hitOff_eq : hitOffAddr = R32 := by
  simp only [hitOffAddr, WRB_eq, R0, R32]; decide
private theorem hitLen_eq : hitLenAddr = R40 := by
  simp only [hitLenAddr, WRB_eq, R0, R40]; decide

-- Hash ptr
private def H0 : Word := (0x40000010 : Word)
private def H8 : Word := (0x40000018 : Word)
private def H16 : Word := (0x40000020 : Word)
private def H24 : Word := (0x40000028 : Word)
private theorem H0v : isValidDwordAccess H0 = true := by unfold H0; decide
private theorem H8v : isValidDwordAccess H8 = true := by unfold H8; decide
private theorem H16v : isValidDwordAccess H16 = true := by unfold H16; decide
private theorem H24v : isValidDwordAccess H24 = true := by unfold H24; decide
private theorem HP_eq : hitSampleHashPtr = H0 := by
  unfold hitSampleHashPtr emptySampleHashPtr H0; decide

private def OO : Word := (0xa0010008 : Word)
private def OL : Word := (0xa0010010 : Word)
private theorem OOv : isValidDwordAccess OO = true := by unfold OO; decide
private theorem OLv : isValidDwordAccess OL = true := by unfold OL; decide
private theorem OO_eq : hitSampleOutOff = OO := by
  unfold hitSampleOutOff emptySampleOutOff OO; decide
private theorem OL_eq : hitSampleOutLen = OL := by
  unfold hitSampleOutLen emptySampleOutLen OL; decide

private def mkOwn (a : Word) (h : isValidDwordAccess a = true) : MemAtom := ⟨a, 0, h⟩
private def mkMem (a v : Word) (h : isValidDwordAccess a = true) : MemAtom := ⟨a, v, h⟩

private def hitAtoms : List HitAtom :=
  [ .reg .x2 hitSampleSp0, .reg .x1 hitSampleRet
  , .reg .x8 (0x101 : Word), .reg .x9 (0x202 : Word)
  , .reg .x18 (0x303 : Word), .reg .x19 (0x404 : Word)
  , .reg .x20 (0x505 : Word), .reg .x21 (0x606 : Word), .reg .x22 (0x707 : Word)
  , .reg .x12 hitSampleHashPtr, .reg .x13 hitSampleOutOff, .reg .x14 hitSampleOutLen
  , .reg .x5 hitSampleV5, .reg .x10 hitSampleV10
  , .own (mkOwn S0 S0v), .own (mkOwn S8 S8v), .own (mkOwn S16 S16v), .own (mkOwn S24 S24v)
  , .own (mkOwn S32s S32sv), .own (mkOwn S40s S40sv), .own (mkOwn S48 S48v), .own (mkOwn S56 S56v)
  , .mem (mkMem WidxCountLoc 1 WCv)
  , .reg .x6 0, .reg .x7 0, .reg .x11 0, .reg .x15 0, .reg .x16 0, .reg .x17 0
  , .reg .x28 0, .reg .x29 0, .reg .x30 0, .reg .x31 0
  , .reg .x0 0
  , .mem (mkMem R0 hitHashDword R0v), .mem (mkMem R8 hitHashDword R8v)
  , .mem (mkMem R16 hitHashDword R16v), .mem (mkMem R24 hitHashDword R24v)
  , .mem (mkMem H0 hitHashDword H0v), .mem (mkMem H8 hitHashDword H8v)
  , .mem (mkMem H16 hitHashDword H16v), .mem (mkMem H24 hitHashDword H24v)
  , .mem (mkMem R32 hitOffW R32v), .mem (mkMem R40 hitLenW R40v)
  , .mem (mkMem OO hitSampleOffOld OOv), .mem (mkMem OL hitSampleLenOld OLv)
  ]

private theorem hitAtoms_resource_pairwise :
    hitAtoms.Pairwise (fun x y => hitAtomResource x ≠ hitAtomResource y) := by
  unfold hitAtoms hitSampleSp0 hitSampleRet hitSampleHashPtr hitSampleOutOff
    hitSampleOutLen hitSampleV5 hitSampleV10 hitSampleOffOld hitSampleLenOld
    emptySampleSp0 emptySampleRet emptySampleHashPtr emptySampleOutOff emptySampleOutLen
    mkOwn mkMem S0 S8 S16 S24 S32s S40s S48 S56
    R0 R8 R16 R24 R32 R40 H0 H8 H16 H24 OO OL
    hitHashDword hitOffW hitLenW WidxCountLoc GuestAddrs.widx_count
  decide

private theorem hitAtoms_hsat :
    (hitAtoms.foldr (fun x acc => hitAtomAssertion x ** acc) empAssertion)
      (hitAtoms.foldr (fun x acc => (hitAtomHeap x).union acc) PartialState.empty) := by
  apply EvmAsm.Rv64.SAsm.sepConj_foldr_satisfiable hitAtomAssertion hitAtomHeap hitAtoms
  · intro x hx; cases x with
    | reg r v => exact rfl
    | mem m => exact ⟨rfl, m.valid⟩
    | own m => exact ⟨0, rfl, m.valid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => hitAtomHeap_disjoint_of_resource_ne h)
      hitAtoms_resource_pairwise

private def hitEntryHeap : PartialState :=
  hitAtoms.foldr (fun x acc => (hitAtomHeap x).union acc) PartialState.empty

def hitSampleState : MachineState where
  regs := fun r => match hitEntryHeap.regs r with | some v => v | none => 0
  mem := fun a => match hitEntryHeap.mem a with | some v => v | none => 0
  code := CR
  pc := B

private theorem hitEntryHeap_x0_some : hitEntryHeap.regs .x0 = some 0 := by
  unfold hitEntryHeap hitAtoms hitAtomHeap
    hitSampleSp0 hitSampleRet hitSampleHashPtr hitSampleOutOff hitSampleOutLen
    hitSampleV5 hitSampleV10 hitSampleOffOld hitSampleLenOld
    emptySampleSp0 emptySampleRet emptySampleHashPtr emptySampleOutOff emptySampleOutLen
    mkOwn mkMem S0 S8 S16 S24 S32s S40s S48 S56
    R0 R8 R16 R24 R32 R40 H0 H8 H16 H24 OO OL
    hitHashDword hitOffW hitLenW WidxCountLoc GuestAddrs.widx_count
  decide

private theorem hitSampleState_getReg (r : Reg) (hr : r ≠ .x0) :
    hitSampleState.getReg r =
      (match hitEntryHeap.regs r with | some v => v | none => (0 : Word)) := by
  cases r <;> simp_all [hitSampleState, MachineState.getReg]

private theorem hitSampleState_getReg_x0 : hitSampleState.getReg .x0 = 0 := by
  simp [MachineState.getReg]

private theorem hitSampleState_getMem (a : Word) :
    hitSampleState.getMem a =
      (match hitEntryHeap.mem a with | some v => v | none => 0) := rfl

private theorem hitAtomHeap_code_none (x : HitAtom) (a : Word) :
    (hitAtomHeap x).code a = none := by cases x <;> rfl

private theorem hitEntryHeap_code_none (a : Word) :
    hitEntryHeap.code a = none := by
  unfold hitEntryHeap
  induction hitAtoms with
  | nil => rfl
  | cons x xs ih =>
    change (match (hitAtomHeap x).code a with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (hitAtomHeap y).union acc) PartialState.empty).code a) = none
    rw [hitAtomHeap_code_none x a, ih]

private theorem hitEntryHeap_pc_none : hitEntryHeap.pc = none := by
  unfold hitEntryHeap
  induction hitAtoms with
  | nil => rfl
  | cons x xs ih =>
    have hx : (hitAtomHeap x).pc = none := by cases x <;> rfl
    change (match (hitAtomHeap x).pc with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (hitAtomHeap y).union acc) PartialState.empty).pc) = none
    rw [hx, ih]

private theorem hitEntryHeap_CompatibleWith :
    hitEntryHeap.CompatibleWith hitSampleState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v h
    by_cases hr : r = .x0
    · subst r; rw [hitEntryHeap_x0_some] at h
      simp only [Option.some.injEq] at h
      rw [hitSampleState_getReg_x0, h]
    · rw [hitSampleState_getReg r hr, h]
  · intro a v h; rw [hitSampleState_getMem a, h]
  · intro a i h; rw [hitEntryHeap_code_none a] at h; cases h
  · intro v h; rw [hitEntryHeap_pc_none] at h; cases h
  · intro v h; cases h
  · intro v h; cases h
  · intro v h; cases h

/-! ## Flatten structural pieces -/

private theorem frameSlotsOwn_hit :
    frameSlotsOwn indexedFrame hitSampleNewSp =
      (memOwn S0 ** memOwn S8 ** memOwn S16 ** memOwn S24 **
        memOwn S32s ** memOwn S40s ** memOwn S48 ** memOwn S56) := by
  unfold frameSlotsOwn indexedFrame
  simp only [List.foldr, sepConj_emp_right']
  rw [sa0, sa8, sa16, sa24, sa32, sa40, sa48, sa56]

private abbrev ones8 : List (BitVec 8) := List.replicate 8 (1 : BitVec 8)
private abbrev ones16 : List (BitVec 8) := List.replicate 16 (1 : BitVec 8)
private abbrev ones24 : List (BitVec 8) := List.replicate 24 (1 : BitVec 8)
private abbrev ones32 : List (BitVec 8) := List.replicate 32 (1 : BitVec 8)

private theorem coverHitHash_eq_ones32 : coverHitHash = ones32 := rfl
private theorem ones8_pack : packBytes ones8 = hitHashDword := hitHashDword_eq
private theorem ones32_ne : ones32 ≠ [] := by decide
private theorem ones24_ne : ones24 ≠ [] := by decide
private theorem ones16_ne : ones16 ≠ [] := by decide
private theorem ones8_ne : ones8 ≠ [] := by decide
private theorem ones32_take8 : ones32.take 8 = ones8 := by decide
private theorem ones32_drop8 : ones32.drop 8 = ones24 := by decide
private theorem ones24_take8 : ones24.take 8 = ones8 := by decide
private theorem ones24_drop8 : ones24.drop 8 = ones16 := by decide
private theorem ones16_take8 : ones16.take 8 = ones8 := by decide
private theorem ones16_drop8 : ones16.drop 8 = ones8 := by decide
private theorem ones8_take8 : ones8.take 8 = ones8 := by decide
private theorem ones8_drop8 : ones8.drop 8 = ([] : List (BitVec 8)) := by decide

/-- 32-byte all-ones region expands to 4 dwords. -/
private theorem bytesRegion_coverHit (base : Word) :
    bytesRegion base coverHitHash =
      ((base ↦ₘ hitHashDword) ** ((base + 8) ↦ₘ hitHashDword) **
        ((base + 16) ↦ₘ hitHashDword) ** ((base + 24) ↦ₘ hitHashDword)) := by
  rw [coverHitHash_eq_ones32]
  -- Peel 1
  rw [bytesRegion_eq_cons base ones32 ones32_ne, ones32_take8, ones32_drop8, ones8_pack]
  -- Peel 2
  rw [bytesRegion_eq_cons (base + 8) ones24 ones24_ne, ones24_take8, ones24_drop8, ones8_pack]
  -- Peel 3
  rw [bytesRegion_eq_cons (base + 8 + 8) ones16 ones16_ne, ones16_take8, ones16_drop8, ones8_pack]
  -- Peel 4
  rw [bytesRegion_eq_cons (base + 8 + 8 + 8) ones8 ones8_ne, ones8_take8, ones8_drop8,
    ones8_pack, bytesRegion_nil]
  -- Flatten addresses + strip trailing emp
  rw [show (base + 8 + 8 + 8 : Word) = base + 24 from by bv_omega,
      show (base + 8 + 8 : Word) = base + 16 from by bv_omega,
      sepConj_emp_right']

private theorem hitHashBytes_flat :
    hitHashBytes hitSampleHashPtr =
      ((R0 ↦ₘ hitHashDword) ** (R8 ↦ₘ hitHashDword) **
        (R16 ↦ₘ hitHashDword) ** (R24 ↦ₘ hitHashDword) **
        (H0 ↦ₘ hitHashDword) ** (H8 ↦ₘ hitHashDword) **
        (H16 ↦ₘ hitHashDword) ** (H24 ↦ₘ hitHashDword)) := by
  unfold hitHashBytes
  rw [bytesRegion_coverHit WidxRecordsBase, bytesRegion_coverHit hitSampleHashPtr]
  have hR8 : R0 + 8 = R8 := by unfold R0 R8; decide
  have hR16 : R0 + 16 = R16 := by unfold R0 R16; decide
  have hR24 : R0 + 24 = R24 := by unfold R0 R24; decide
  have hH8 : H0 + 8 = H8 := by unfold H0 H8; decide
  have hH16 : H0 + 16 = H16 := by unfold H0 H16; decide
  have hH24 : H0 + 24 = H24 := by unfold H0 H24; decide
  simp only [WRB_eq, HP_eq, hR8, hR16, hR24, hH8, hH16, hH24, sepConj_assoc']

private theorem hitCells_flat :
    hitCells hitSampleOutOff hitSampleOutLen hitSampleOffOld hitSampleLenOld =
      ((R32 ↦ₘ hitOffW) ** (R40 ↦ₘ hitLenW) **
        (OO ↦ₘ hitSampleOffOld) ** (OL ↦ₘ hitSampleLenOld)) := by
  unfold hitCells
  simp only [hitOff_eq, hitLen_eq, OO_eq, OL_eq]

private def hitAtomsAssert : Assertion :=
  hitAtoms.foldr (fun x acc => hitAtomAssertion x ** acc) empAssertion

private theorem hitEntryPre_eq_atomsAssert :
    hitEntryPre = hitAtomsAssert := by
  unfold hitEntryPre
  rw [regsAt_indexedFrame { hitSampleSaved with ra := hitSampleRet },
    frameSlotsOwn_hit, hitHashBytes_flat, hitCells_flat]
  unfold hitAtomsAssert hitAtoms hitAtomAssertion mkOwn mkMem hitExposedZeros
  simp only [List.foldr]
  simp only [hitSampleSaved, emptySampleSaved, hitSampleRet, emptySampleRet,
    hitSampleSp0, emptySampleSp0, hitSampleHashPtr, emptySampleHashPtr,
    hitSampleOutOff, emptySampleOutOff, hitSampleOutLen, emptySampleOutLen,
    hitSampleV5, hitSampleV10, hitSampleOffOld, hitSampleLenOld,
    hitOffW, hitLenW, sepConj_emp_right', sepConj_assoc']

/-- ⭐ Concrete model: one-hit whole-routine pre is inhabited. -/
theorem hit_entryState_exists :
    hitSampleState.pc = B ∧
    CR.SatisfiedBy hitSampleState ∧
    hitEntryPre.holdsFor hitSampleState := by
  refine ⟨rfl, ?_, ?_⟩
  · intro a i h; exact h
  · refine ⟨hitEntryHeap, hitEntryHeap_CompatibleWith, ?_⟩
    rw [hitEntryPre_eq_atomsAssert]
    exact hitAtoms_hsat

/-- Closed triple at the sample point (secondary witness). -/
theorem one_hit_sample_triple :
    cpsTripleWithin 343 B hitSampleRet CR
      hitEntryPre
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ hitSampleRet) ** (.x2 ↦ᵣ hitSampleSp0) **
        (.x8 ↦ᵣ hitSampleSaved.s0) ** (.x9 ↦ᵣ hitSampleSaved.s1) **
        (.x18 ↦ᵣ hitSampleSaved.s2) ** (.x19 ↦ᵣ hitSampleSaved.s3) **
        (.x20 ↦ᵣ hitSampleSaved.s4) ** (.x21 ↦ᵣ hitSampleSaved.s5) **
        (.x22 ↦ᵣ hitSampleSaved.s6) **
        frameSlotsSaved indexedFrame hitSampleNewSp
          (indexedSavedVals { hitSampleSaved with ra := hitSampleRet }) **
        (hitOffAddr ↦ₘ hitOffW) ** (hitLenAddr ↦ₘ hitLenW) **
        (hitSampleOutOff ↦ₘ hitOffW) ** (hitSampleOutLen ↦ₘ hitLenW) **
        ((.x5 : Reg) ↦ᵣ hitLenW) **
        hitCmp32Extra hitSampleHashPtr) := by
  have hbaseR : WidxRecordsBase.toNat = 0xa2e07088 := by
    unfold WidxRecordsBase GuestAddrs.widx_records; decide
  have hbaseH : hitSampleHashPtr.toNat = 0x40000010 := by
    unfold hitSampleHashPtr emptySampleHashPtr; decide
  have hvalidR : ∀ k, k < 32 →
      isValidByteAccess (WidxRecordsBase + BitVec.ofNat 64 k) = true := by
    intro k hk
    have hk64 : k < 2 ^ 64 := Nat.lt_trans hk (by decide)
    have hsum : (WidxRecordsBase + BitVec.ofNat 64 k).toNat = 0xa2e07088 + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbaseR, Nat.mod_eq_of_lt hk64,
        Nat.mod_eq_of_lt (by omega)]
    -- isValidMemAddr = ((MEM ∨ INPUT) ∨ RAM); RAM is the rightmost disjunct
    simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    refine Or.inr ?_
    constructor
    · rw [hsum]; change RAM_MEM_START ≤ 0xa2e07088 + k; unfold RAM_MEM_START; omega
    · rw [hsum]; change 0xa2e07088 + k ≤ RAM_MEM_END; unfold RAM_MEM_END; omega
  have hvalidH : ∀ k, k < 32 →
      isValidByteAccess (hitSampleHashPtr + BitVec.ofNat 64 k) = true := by
    intro k hk
    have hk64 : k < 2 ^ 64 := Nat.lt_trans hk (by decide)
    have hsum : (hitSampleHashPtr + BitVec.ofNat 64 k).toNat = 0x40000010 + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbaseH, Nat.mod_eq_of_lt hk64,
        Nat.mod_eq_of_lt (by omega)]
    -- INPUT is left-nested: Or.inl (Or.inr INPUT)
    simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    refine Or.inl (Or.inr ?_)
    constructor
    · rw [hsum]; change INPUT_MEM_START ≤ 0x40000010 + k; unfold INPUT_MEM_START; omega
    · rw [hsum]; change 0x40000010 + k ≤ INPUT_MEM_END; unfold INPUT_MEM_END; omega
  have h := witness_lookup_by_hash_indexed_spec_within_one_hit
    hitSampleSp0 hitSampleRet hitSampleSaved
    hitSampleHashPtr hitSampleOutOff hitSampleOutLen
    hitSampleOffOld hitSampleLenOld hitSampleV5 hitSampleV10
    hitSampleRet_even
    (by unfold hitSampleHashPtr emptySampleHashPtr; decide)
    (by unfold hitSampleHashPtr emptySampleHashPtr; decide)
    hvalidR hvalidH
  simpa [hitEntryPre, hitSampleNewSp, hitSampleSaved] using h

end EvmAsm.Codegen.WitnessLookupByHashIndexedOneHitSat
