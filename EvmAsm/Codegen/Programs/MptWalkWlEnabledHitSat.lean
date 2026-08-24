/-
  EvmAsm.Codegen.Programs.MptWalkWlEnabledHitSat

  #12036 — **concrete `MachineState` model for the hit residual's
  precondition** at the root walk site.

  `MptWalkWlEnabledHit` establishes `wlCallWithinShapeHitEn` at pc 35 / 101 /
  210. That is a `cpsTripleWithin`, so it would be vacuously true if its
  precondition had no model. #12690 recorded exactly that gap ("no exhibited
  `MachineState` model of the parent's `wlhHitCallerPre`", the callee's having
  one at `hit_entryState_exists`). This module closes it: an explicit state
  whose register file and memory satisfy

      (x1 ↦ vOld) ** (x2 ↦ sp0) ** stackFree sp0 16 ** wlhSregs vals **
      wlhHitArgs …

  — the residual's pre with `F := emp` — at concrete sample values on the
  `widx_count = 1` hit domain.

  Method is the one `WitnessLookupByHashIndexedOneHitSat` uses: flatten the
  assertion into a list of resource atoms, show the atoms occupy pairwise
  distinct resources (so their heaps are pairwise disjoint), and hand the list
  to `sepConj_foldr_satisfiable`.

  ⚠️ SAY SO: this is a MODEL of the precondition, not a claim about the domain
  being *reached* by the walk at run time, and it is the `widx_count = 1` hit
  domain only.
-/
import EvmAsm.Codegen.Programs.MptWalkWlEnabledHit
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Word
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Codegen.MptWalkWlEnabledHitSat

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptWalkSpec
open EvmAsm.Codegen.WitnessLookupByHashSpec
open EvmAsm.Codegen.WitnessLookupByHashIndexedSpec
  (WidxCountLoc WidxRecordsBase indexedFrame)
open EvmAsm.Codegen.WitnessLookupByHashIndexedOneHit
  (hitOffAddr hitLenAddr hitOffW hitLenW hitCells hitHashBytes coverHitHash)

set_option maxRecDepth 8000

/-! ## §1  Sample values -/

/-- Sample caller stack pointer (RAM; the same one the callee's model uses). -/
def satSp0 : Word := (0xa0050000 : Word)

/-- This routine's own frame base. -/
def satNsp : Word := satSp0 + signExtend12 (-64 : BitVec 12)

/-- The nested `witness_lookup_by_hash_indexed` frame base. -/
def satNsp2 : Word := satNsp + signExtend12 (-64 : BitVec 12)

def satVOld : Word := (0x11 : Word)

/-- The register map of the sample instance. Only `vals .x1` is constrained by
    the residual (it must be the call's return address); the callee-saved
    values are arbitrary, so one constant map serves. -/
def satVals : Reg → Word := fun _ => pc 35 + 4
def satV5 : Word := (0x33 : Word)
def satV6 : Word := (0x44 : Word)
def satSecPtr : Word := (0x55 : Word)
def satSecLen : Word := (0x66 : Word)
def satOffOld : Word := (0x77 : Word)
def satLenOld : Word := (0x88 : Word)
def satW7 : Word := (0x91 : Word)
def satW15 : Word := (0x92 : Word)
def satW16 : Word := (0x93 : Word)
def satW17 : Word := (0x94 : Word)
def satW28 : Word := (0x95 : Word)
def satW29 : Word := (0x96 : Word)
def satW30 : Word := (0x97 : Word)
def satW31 : Word := (0x98 : Word)
def satNCalls : Word := (0xa1 : Word)
def satNIdx : Word := (0xa2 : Word)
def satNHit : Word := (0xa3 : Word)
def satNMiss : Word := (0xa4 : Word)
def satNLin : Word := (0xa5 : Word)
def satNLast : Word := (0xa6 : Word)
def satNMax : Word := (0xa7 : Word)
def satNLinMiss : Word := (0xa8 : Word)

/-- The residual's precondition at the sample point, with `F := emp` erased. -/
def satSitePre : Assertion :=
  ((.x1 : Reg) ↦ᵣ satVOld) ** ((.x2 : Reg) ↦ᵣ satSp0) ** stackFree satSp0 16 **
  wlhSregs satVals **
  wlhHitArgs satV5 satV6 satSecPtr satSecLen MwLookupHash MwLookupOff
    MwLookupLen satOffOld satLenOld
    satW7 satW15 satW16 satW17 satW28 satW29 satW30 satW31
    satNCalls satNIdx satNHit satNMiss satNLin satNLast satNMax satNLinMiss

/-! ## §2  Atom vocabulary (mirrors `WitnessLookupByHashIndexedOneHitSat`) -/

private structure MemAtom where
  a : Word
  v : Word
  valid : isValidDwordAccess a = true

private inductive SatAtom where
  | reg (r : Reg) (v : Word)
  | mem (m : MemAtom)
  | own (m : MemAtom)

private def satAtomAssertion : SatAtom → Assertion
  | .reg r v => (r ↦ᵣ v)
  | .mem m => (m.a ↦ₘ m.v)
  | .own m => memOwn m.a

private def satAtomHeap : SatAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .mem m => PartialState.singletonMem m.a m.v
  | .own m => PartialState.singletonMem m.a 0

private inductive SatResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def satAtomResource : SatAtom → SatResource
  | .reg r _ => .reg r
  | .mem m => .mem m.a
  | .own m => .mem m.a

private theorem sat_reg_reg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
    (hne : r1 ≠ r2) :
    (PartialState.singletonReg r1 v1).Disjoint
      (PartialState.singletonReg r2 v2) := by
  refine ⟨?_, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro r
  by_cases h : r = r1
  · subst r; right; simp [PartialState.singletonReg, hne]
  · left; simp [PartialState.singletonReg, h]

private theorem sat_mem_mem_disjoint {a1 a2 : Word} {v1 v2 : Word}
    (hne : a1 ≠ a2) :
    (PartialState.singletonMem a1 v1).Disjoint
      (PartialState.singletonMem a2 v2) := by
  refine ⟨fun _ => Or.inl rfl, ?_, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  intro a
  by_cases h : a = a1
  · subst a; right; simp [PartialState.singletonMem, hne]
  · left; simp [PartialState.singletonMem, h]

private theorem sat_reg_mem_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) :=
  ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem sat_mem_reg_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  sat_reg_mem_disjoint.symm

private theorem satAtomHeap_disjoint_of_resource_ne {x y : SatAtom}
    (h : satAtomResource x ≠ satAtomResource y) :
    (satAtomHeap x).Disjoint (satAtomHeap y) := by
  cases x <;> cases y
  · apply sat_reg_reg_disjoint; simpa [satAtomResource] using h
  · exact sat_reg_mem_disjoint
  · exact sat_reg_mem_disjoint
  · exact sat_mem_reg_disjoint
  · apply sat_mem_mem_disjoint; simpa [satAtomResource] using h
  · apply sat_mem_mem_disjoint; simpa [satAtomResource] using h
  · exact sat_mem_reg_disjoint
  · apply sat_mem_mem_disjoint; simpa [satAtomResource] using h
  · apply sat_mem_mem_disjoint; simpa [satAtomResource] using h

/-! ## §3  Concrete addresses -/

private def FS (base : Word) (ofs : BitVec 12) : Word := base + signExtend12 ofs

/-- Dwords of the 32-byte `widx_records` hash. -/
private def RB0 : Word := WidxRecordsBase
private def RB1 : Word := WidxRecordsBase + 8
private def RB2 : Word := WidxRecordsBase + 16
private def RB3 : Word := WidxRecordsBase + 24

/-- Dwords of the 32-byte target hash at `mw_lookup_hash`. -/
private def HB0 : Word := MwLookupHash
private def HB1 : Word := MwLookupHash + 8
private def HB2 : Word := MwLookupHash + 16
private def HB3 : Word := MwLookupHash + 24

private def satHashDword : Word := (0x0101010101010101 : Word)

private theorem satHashDword_eq :
    packBytes (List.replicate 8 (1 : BitVec 8)) = satHashDword := by
  unfold packBytes satHashDword; decide

private def mkOwn (a : Word) (h : isValidDwordAccess a = true) : MemAtom :=
  ⟨a, 0, h⟩
private def mkMem (a v : Word) (h : isValidDwordAccess a = true) : MemAtom :=
  ⟨a, v, h⟩

/-! ## §4  Atom list, in the assertion's own left-to-right order -/

private def satAtoms : List SatAtom :=
  [ .reg .x1 satVOld, .reg .x2 satSp0
  -- stackFree sp0 16 = nested indexed frame (8) ** this routine's frame (8)
  , .own (mkOwn (FS satNsp2 (0 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp2 (8 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp2 (16 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp2 (24 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp2 (32 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp2 (40 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp2 (48 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp2 (56 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp (0 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp (8 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp (16 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp (24 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp (32 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp (40 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp (48 : BitVec 12)) (by decide))
  , .own (mkOwn (FS satNsp (56 : BitVec 12)) (by decide))
  -- wlhSregs
  , .reg .x8 (pc 35 + 4), .reg .x9 (pc 35 + 4), .reg .x18 (pc 35 + 4)
  , .reg .x19 (pc 35 + 4), .reg .x20 (pc 35 + 4), .reg .x21 (pc 35 + 4)
  , .reg .x22 (pc 35 + 4)
  -- wlhHitArgs: x0/x5/x6
  , .reg .x0 (0 : Word), .reg .x5 satV5, .reg .x6 satV6
  -- wlhHitAregs
  , .reg .x10 satSecPtr, .reg .x11 satSecLen, .reg .x12 MwLookupHash
  , .reg .x13 MwLookupOff, .reg .x14 MwLookupLen
  -- wlhHitCells
  , .mem (mkMem CallsLoc satNCalls (by decide))
  , .mem (mkMem WidxEnLoc (1 : Word) (by decide))
  , .mem (mkMem SecPtrLoc satSecPtr (by decide))
  , .mem (mkMem SecLenLoc satSecLen (by decide))
  , .mem (mkMem WidxCountLoc (1 : Word) (by decide))
  , .mem (mkMem IdxCallsLoc satNIdx (by decide))
  , .mem (mkMem IdxMissLoc satNMiss (by decide))
  , .mem (mkMem LinCallsLoc satNLin (by decide))
  , .mem (mkMem LinLastLoc satNLast (by decide))
  , .mem (mkMem LinMaxLoc satNMax (by decide))
  , .mem (mkMem LinMissLoc satNLinMiss (by decide))
  -- exposed temps
  , .reg .x7 satW7, .reg .x15 satW15, .reg .x16 satW16, .reg .x17 satW17
  , .reg .x28 satW28, .reg .x29 satW29, .reg .x30 satW30, .reg .x31 satW31
  -- indexed_hits
  , .mem (mkMem IdxHitLoc satNHit (by decide))
  -- hitHashBytes: record hash then target hash, both all-ones
  , .mem (mkMem RB0 satHashDword (by decide))
  , .mem (mkMem RB1 satHashDword (by decide))
  , .mem (mkMem RB2 satHashDword (by decide))
  , .mem (mkMem RB3 satHashDword (by decide))
  , .mem (mkMem HB0 satHashDword (by decide))
  , .mem (mkMem HB1 satHashDword (by decide))
  , .mem (mkMem HB2 satHashDword (by decide))
  , .mem (mkMem HB3 satHashDword (by decide))
  -- hitCells
  , .mem (mkMem hitOffAddr hitOffW (by decide))
  , .mem (mkMem hitLenAddr hitLenW (by decide))
  , .mem (mkMem MwLookupOff satOffOld (by decide))
  , .mem (mkMem MwLookupLen satLenOld (by decide))
  ]

private theorem satAtoms_resource_pairwise :
    satAtoms.Pairwise (fun x y => satAtomResource x ≠ satAtomResource y) := by
  decide

private theorem satAtoms_hsat :
    (satAtoms.foldr (fun x acc => satAtomAssertion x ** acc) empAssertion)
      (satAtoms.foldr (fun x acc => (satAtomHeap x).union acc)
        PartialState.empty) := by
  apply EvmAsm.Rv64.SAsm.sepConj_foldr_satisfiable satAtomAssertion satAtomHeap
    satAtoms
  · intro x hx; cases x with
    | reg r v => exact rfl
    | mem m => exact ⟨rfl, m.valid⟩
    | own m => exact ⟨0, rfl, m.valid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => satAtomHeap_disjoint_of_resource_ne h)
      satAtoms_resource_pairwise

/-! ## §5  The state -/

private def satHeap : PartialState :=
  satAtoms.foldr (fun x acc => (satAtomHeap x).union acc) PartialState.empty

/-- Concrete machine state at the root walk site. -/
def satState : MachineState where
  regs := fun r => match satHeap.regs r with | some v => v | none => 0
  mem := fun a => match satHeap.mem a with | some v => v | none => 0
  code := fullCode
  pc := pc 35

private theorem satHeap_x0_some : satHeap.regs .x0 = some 0 := by
  unfold satHeap satAtoms satAtomHeap mkOwn mkMem
  decide

private theorem satState_getReg (r : Reg) (hr : r ≠ .x0) :
    satState.getReg r =
      (match satHeap.regs r with | some v => v | none => (0 : Word)) := by
  cases r <;> simp_all [satState, MachineState.getReg]

private theorem satState_getReg_x0 : satState.getReg .x0 = 0 := by
  simp [MachineState.getReg]

private theorem satState_getMem (a : Word) :
    satState.getMem a =
      (match satHeap.mem a with | some v => v | none => 0) := rfl

private theorem satAtomHeap_code_none (x : SatAtom) (a : Word) :
    (satAtomHeap x).code a = none := by cases x <;> rfl

private theorem satHeap_code_none (a : Word) : satHeap.code a = none := by
  unfold satHeap
  induction satAtoms with
  | nil => rfl
  | cons x xs ih =>
    change (match (satAtomHeap x).code a with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (satAtomHeap y).union acc)
          PartialState.empty).code a) = none
    rw [satAtomHeap_code_none x a, ih]

private theorem satHeap_pc_none : satHeap.pc = none := by
  unfold satHeap
  induction satAtoms with
  | nil => rfl
  | cons x xs ih =>
    have hx : (satAtomHeap x).pc = none := by cases x <;> rfl
    change (match (satAtomHeap x).pc with
      | some v => some v | none =>
        (xs.foldr (fun y acc => (satAtomHeap y).union acc)
          PartialState.empty).pc) = none
    rw [hx, ih]

private theorem satHeap_CompatibleWith : satHeap.CompatibleWith satState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r v h
    by_cases hr : r = .x0
    · subst r; rw [satHeap_x0_some] at h
      simp only [Option.some.injEq] at h
      rw [satState_getReg_x0, h]
    · rw [satState_getReg r hr, h]
  · intro a v h; rw [satState_getMem a, h]
  · intro a i h; rw [satHeap_code_none a] at h; cases h
  · intro v h; rw [satHeap_pc_none] at h; cases h
  · intro v h; cases h
  · intro v h; cases h
  · intro v h; cases h

/-! ## §6  Flatten the structural pieces -/

private theorem stackFree16_flat :
    stackFree satSp0 16 =
      ((memOwn (FS satNsp2 (0 : BitVec 12)) ** memOwn (FS satNsp2 (8 : BitVec 12)) **
        memOwn (FS satNsp2 (16 : BitVec 12)) ** memOwn (FS satNsp2 (24 : BitVec 12)) **
        memOwn (FS satNsp2 (32 : BitVec 12)) ** memOwn (FS satNsp2 (40 : BitVec 12)) **
        memOwn (FS satNsp2 (48 : BitVec 12)) ** memOwn (FS satNsp2 (56 : BitVec 12))) **
       (memOwn (FS satNsp (0 : BitVec 12)) ** memOwn (FS satNsp (8 : BitVec 12)) **
        memOwn (FS satNsp (16 : BitVec 12)) ** memOwn (FS satNsp (24 : BitVec 12)) **
        memOwn (FS satNsp (32 : BitVec 12)) ** memOwn (FS satNsp (40 : BitVec 12)) **
        memOwn (FS satNsp (48 : BitVec 12)) ** memOwn (FS satNsp (56 : BitVec 12)))) := by
  rw [stackFree16_eq_nested_parent satSp0]
  unfold frameSlotsOwn indexedFrame wlhFrame FS satNsp2 satNsp
  simp only [List.foldr, sepConj_emp_right']

private abbrev ones8 : List (BitVec 8) := List.replicate 8 (1 : BitVec 8)
private abbrev ones16 : List (BitVec 8) := List.replicate 16 (1 : BitVec 8)
private abbrev ones24 : List (BitVec 8) := List.replicate 24 (1 : BitVec 8)
private abbrev ones32 : List (BitVec 8) := List.replicate 32 (1 : BitVec 8)

private theorem coverHitHash_eq_ones32 : coverHitHash = ones32 := rfl
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

/-- A 32-byte all-ones region is four all-ones dwords. -/
private theorem bytesRegion_coverHit (base : Word) :
    bytesRegion base coverHitHash =
      ((base ↦ₘ satHashDword) ** ((base + 8) ↦ₘ satHashDword) **
        ((base + 16) ↦ₘ satHashDword) ** ((base + 24) ↦ₘ satHashDword)) := by
  rw [coverHitHash_eq_ones32]
  rw [bytesRegion_eq_cons base ones32 ones32_ne, ones32_take8, ones32_drop8,
    satHashDword_eq]
  rw [bytesRegion_eq_cons (base + 8) ones24 ones24_ne, ones24_take8, ones24_drop8,
    satHashDword_eq]
  rw [bytesRegion_eq_cons (base + 8 + 8) ones16 ones16_ne, ones16_take8,
    ones16_drop8, satHashDword_eq]
  rw [bytesRegion_eq_cons (base + 8 + 8 + 8) ones8 ones8_ne, ones8_take8,
    ones8_drop8, satHashDword_eq, bytesRegion_nil]
  rw [show (base + 8 + 8 + 8 : Word) = base + 24 from by bv_omega,
      show (base + 8 + 8 : Word) = base + 16 from by bv_omega,
      sepConj_emp_right']

private theorem hitHashBytes_flat :
    hitHashBytes MwLookupHash =
      ((RB0 ↦ₘ satHashDword) ** (RB1 ↦ₘ satHashDword) **
        (RB2 ↦ₘ satHashDword) ** (RB3 ↦ₘ satHashDword) **
        (HB0 ↦ₘ satHashDword) ** (HB1 ↦ₘ satHashDword) **
        (HB2 ↦ₘ satHashDword) ** (HB3 ↦ₘ satHashDword)) := by
  unfold hitHashBytes
  rw [bytesRegion_coverHit WidxRecordsBase, bytesRegion_coverHit MwLookupHash]
  unfold RB0 RB1 RB2 RB3 HB0 HB1 HB2 HB3
  simp only [sepConj_assoc']

private def satAtomsAssert : Assertion :=
  satAtoms.foldr (fun x acc => satAtomAssertion x ** acc) empAssertion

private theorem satSitePre_eq_atomsAssert : satSitePre = satAtomsAssert := by
  unfold satSitePre wlhSregs wlhHitArgs wlhHitAregs wlhHitCells hitCells
  rw [stackFree16_flat, hitHashBytes_flat]
  unfold satAtomsAssert satAtoms satAtomAssertion mkOwn mkMem satVals
  simp only [List.foldr, sepConj_emp_right', sepConj_assoc']

/-! ## §7  The model -/

/-- ⭐ **Concrete model**: the hit residual's precondition at the root walk
    site is inhabited, so the fuel-402 `callWithin` it carries is not a
    vacuous triple. Domain: `widx_count = 1` (SAY SO). -/
theorem hit_site_entryState_exists :
    satState.pc = pc 35 ∧
    fullCode.SatisfiedBy satState ∧
    satSitePre.holdsFor satState := by
  refine ⟨rfl, ?_, ?_⟩
  · intro a i h; exact h
  · refine ⟨satHeap, satHeap_CompatibleWith, ?_⟩
    rw [satSitePre_eq_atomsAssert]
    exact satAtoms_hsat

/-- ⭐ The residual instance the model belongs to. Same arguments as
    `satSitePre`, so `hit_site_entryState_exists` is a model of THIS
    residual's precondition, not of a lookalike assertion. -/
theorem sample_site_shape :
    wlCallWithinShapeHitEn fullCode (pc 35) satVOld satSp0 satVals
      satV5 satV6 satSecPtr satSecLen MwLookupHash MwLookupOff MwLookupLen
      satOffOld satLenOld
      satW7 satW15 satW16 satW17 satW28 satW29 satW30 satW31
      satNCalls satNIdx satNHit satNMiss satNLin satNLast satNMax satNLinMiss
      (jalOff GuestAddrs.witness_lookup_by_hash (GuestAddrs.mpt_walk + 140))
      empAssertion :=
  root_wl_enabled_hit_shape_sat satVOld satSp0 satV5 satV6 satSecPtr satSecLen
    MwLookupOff MwLookupLen satOffOld satLenOld
    satW7 satW15 satW16 satW17 satW28 satW29 satW30 satW31
    satNCalls satNIdx satNHit satNMiss satNLin satNLast satNMax satNLinMiss

/-- `sample_site_shape`'s residual carries `F := emp`, so its precondition is
    `satSitePre ** emp`, which IS `satSitePre`. -/
theorem sample_site_pre_eq : (satSitePre ** empAssertion) = satSitePre :=
  sepConj_emp_right' _

end EvmAsm.Codegen.MptWalkWlEnabledHitSat
