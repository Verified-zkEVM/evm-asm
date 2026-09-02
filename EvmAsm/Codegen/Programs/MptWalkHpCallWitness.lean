/-
  Non-vacuity witnesses for the hp-call adapters and the SHA residual.

  The ext/leaf call-site frames retain the two dwords below the hp frame;
  hp owns the six shallow frame cells itself.  These witnesses make that
  ownership split constructive rather than relying on the fact that the
  corresponding CPS theorems elaborate.
-/
import EvmAsm.Codegen.Programs.MptWalkExtHpCall
import EvmAsm.Codegen.Programs.MptWalkLeafHpCall
import EvmAsm.Codegen.Programs.ExecutionRequestsHashHashOneBody

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.HpDecodeNibblesSAsm
open EvmAsm.Codegen.ExecutionRequestsHashShaResidual
open EvmAsm.Codegen.ExecutionRequestsHashHashOne

/-! ## A connective-level atom model -/

private structure HpMemAtom where
  a : Word
  v : Word
  valid : isValidDwordAccess a = true

private inductive HpAtom where
  | reg (r : Reg) (v : Word)
  | mem (m : HpMemAtom)
  | own (m : HpMemAtom)

private def hpAtomAssertion : HpAtom → Assertion
  | .reg r v => r ↦ᵣ v
  | .mem m => m.a ↦ₘ m.v
  | .own m => memOwn m.a

private def hpAtomHeap : HpAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .mem m => PartialState.singletonMem m.a m.v
  | .own m => PartialState.singletonMem m.a 0

private inductive HpResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def hpAtomResource : HpAtom → HpResource
  | .reg r _ => .reg r
  | .mem m => .mem m.a
  | .own m => .mem m.a

private theorem hp_reg_reg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
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

private theorem hp_mem_mem_disjoint {a1 a2 : Word} {v1 v2 : Word}
    (hne : a1 ≠ a2) :
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

private theorem hp_reg_mem_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem hp_mem_reg_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  hp_reg_mem_disjoint.symm

private theorem hpAtomHeap_disjoint_of_resource_ne {x y : HpAtom}
    (h : hpAtomResource x ≠ hpAtomResource y) :
    (hpAtomHeap x).Disjoint (hpAtomHeap y) := by
  cases x <;> cases y
  · apply hp_reg_reg_disjoint
    simpa [hpAtomResource] using h
  · exact hp_reg_mem_disjoint
  · exact hp_reg_mem_disjoint
  · exact hp_mem_reg_disjoint
  · apply hp_mem_mem_disjoint
    simpa [hpAtomResource] using h
  · apply hp_mem_mem_disjoint
    simpa [hpAtomResource] using h
  · exact hp_mem_reg_disjoint
  · apply hp_mem_mem_disjoint
    simpa [hpAtomResource] using h
  · apply hp_mem_mem_disjoint
    simpa [hpAtomResource] using h

/-! ## Shared ext/leaf concrete state -/

private def hpSatSp : Word := (0xa0040000 : Word)
private def hpSatNode : Word := (0x50000000 : Word)
private def hpSatPath : List (BitVec 8) := [0]
private def hpSatBuf : List (BitVec 8) := [0]
private def hpSatWs : WalkSaved where
  ra := 0
  s0 := 0
  s1 := 0
  s2 := 0
  s3 := 0
  s4 := 0
  s5 := 0
  s6 := 0
  s7 := 0
  s8 := 0

/- The list follows the whole precondition's connective structure, but its
   proof is checked through one global resource key for every atom. -/
private def hpSatAtoms : List HpAtom :=
  [ .reg .x1 0
  , .reg .x2 hpSatSp
  , .reg .x8 0
  , .reg .x9 0
  , .reg .x18 0
  , .reg .x19 0
  , .reg .x20 0
  , .reg .x10 hpSatNode
  , .reg .x11 1
  , .reg .x12 MwNibbleBuf
  , .reg .x13 MwNibbleCount
  , .reg .x14 MwIsLeaf
  , .reg .x5 0
  , .reg .x6 0
  , .reg .x7 0
  , .reg .x28 0
  , .reg .x29 0
  , .reg .x30 0
  , .reg .x31 0
  , .reg .x0 0
  , .own ⟨hpSatSp + signExtend12 (-48 : BitVec 12) + signExtend12 (0 : BitVec 12), 0, by decide⟩
  , .own ⟨hpSatSp + signExtend12 (-48 : BitVec 12) + signExtend12 (8 : BitVec 12), 0, by decide⟩
  , .own ⟨hpSatSp + signExtend12 (-48 : BitVec 12) + signExtend12 (16 : BitVec 12), 0, by decide⟩
  , .own ⟨hpSatSp + signExtend12 (-48 : BitVec 12) + signExtend12 (24 : BitVec 12), 0, by decide⟩
  , .own ⟨hpSatSp + signExtend12 (-48 : BitVec 12) + signExtend12 (32 : BitVec 12), 0, by decide⟩
  , .own ⟨hpSatSp + signExtend12 (-48 : BitVec 12) + signExtend12 (40 : BitVec 12), 0, by decide⟩
  , .mem ⟨hpSatSp, 0, by decide⟩
  , .mem ⟨hpSatSp + 8, 0, by decide⟩
  , .mem ⟨hpSatSp + 16, 0, by decide⟩
  , .mem ⟨hpSatSp + 24, 0, by decide⟩
  , .mem ⟨hpSatSp + 32, 0, by decide⟩
  , .mem ⟨hpSatSp + 40, 0, by decide⟩
  , .mem ⟨hpSatSp + 48, 0, by decide⟩
  , .mem ⟨hpSatSp + 56, 0, by decide⟩
  , .mem ⟨hpSatSp + 64, 0, by decide⟩
  , .mem ⟨hpSatSp + 72, 0, by decide⟩
  , .reg .x23 hpSatNode
  , .mem ⟨MwPathOff, 0, by decide⟩
  , .mem ⟨MwPathLen, 1, by decide⟩
  , .own ⟨(hpSatSp + signExtend12 (-48 : BitVec 12)) - BitVec.ofNat 64 (8 * (2 : Nat)), 0, by decide⟩
  , .own ⟨(hpSatSp + signExtend12 (-48 : BitVec 12)) - BitVec.ofNat 64 (8 * (1 : Nat)), 0, by decide⟩
  , .mem ⟨hpSatNode, packBytes [0], by decide⟩
  , .mem ⟨MwNibbleBuf, packBytes [0], by decide⟩
  , .mem ⟨MwNibbleCount, 0, by decide⟩
  , .mem ⟨MwIsLeaf, 0, by decide⟩
  ]

private theorem hpSatAtoms_resource_pairwise :
    hpSatAtoms.Pairwise
      (fun x y => hpAtomResource x ≠ hpAtomResource y) := by
  unfold hpSatAtoms hpAtomResource hpSatSp hpSatNode
  decide

private def hpSatHeap : PartialState :=
  hpSatAtoms.foldr (fun x acc => (hpAtomHeap x).union acc) PartialState.empty

private theorem hpSatAtoms_hsat :
    (hpSatAtoms.foldr (fun x acc => hpAtomAssertion x ** acc) empAssertion)
      hpSatHeap := by
  apply sepConj_foldr_satisfiable hpAtomAssertion hpAtomHeap hpSatAtoms
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | mem m => exact ⟨rfl, m.valid⟩
    | own m => exact ⟨0, rfl, m.valid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => hpAtomHeap_disjoint_of_resource_ne h)
      hpSatAtoms_resource_pairwise

theorem ext_hp_call_pre_non_degenerate_inhabited :
    ∃ h : PartialState,
      (((.x1 ↦ᵣ (0 : Word)) **
        hdnCallEntry hpSatSp (extHpVals (pc 147 + 4) 0 0 0 0 0)
          hpSatNode MwNibbleBuf MwNibbleCount MwIsLeaf
          hpSatPath hpSatBuf 0 0 0 0 0 0 0 0 0) **
        extHpCallFrame hpSatSp hpSatWs hpSatNode 0 1) h := by
  refine ⟨hpSatHeap, ?_⟩
  have hsat := hpSatAtoms_hsat
  simp [hpAtomAssertion, hpAtomHeap, hdnCallEntry, hdnFrame,
    hdnSavedTail, hdnSavedTailDesc, extHpVals, hdnCallerPre,
    extHpCallFrame, walkSavedFrame, frameSlotsOwn, stackFree,
    hpSatHeap, hpSatAtoms, hpSatPath, hpSatBuf, hpSatWs,
    bytesRegion, bytesRegionAux, packBytes, signExtend12,
    sepConj_emp_right', sepConj_assoc'] at hsat ⊢
  xperm_hyp hsat

theorem leaf_hp_call_pre_non_degenerate_inhabited :
    ∃ h : PartialState,
      (((.x1 ↦ᵣ (0 : Word)) **
        hdnCallEntry hpSatSp (leafHpVals (pc 242 + 4) 0 0 0 0 0)
          hpSatNode MwNibbleBuf MwNibbleCount MwIsLeaf
          hpSatPath hpSatBuf 0 0 0 0 0 0 0 0 0) **
        leafHpCallFrame hpSatSp hpSatWs hpSatNode 0 1) h := by
  simpa [leafHpCallFrame, leafHpVals, extHpCallFrame, extHpVals,
    hdnCallEntry, hdnSavedTail, hdnSavedTailDesc] using
    ext_hp_call_pre_non_degenerate_inhabited

/-! ## SHA residual entry precondition

This is the assertion-level whole precondition of the residual call.  It is
deliberately not a witness for `shaCallWithinShape` itself: that proposition
also contains the still-independent callee CPS triple. -/

private def hpShaBody : List (BitVec 8) := [0]
private def hpShaOld : List (BitVec 8) := List.replicate 32 0
private def hpShaBodyPtr : Word := (0x50000000 : Word)
private def hpShaDestPtr : Word := (0x60000000 : Word)

private def hpShaAtoms : List HpAtom :=
  [ .reg .x1 (B1 + 4)
  , .reg .x2 hpSatSp
  , .reg .x10 Blob
  , .reg .x11 (BitVec.ofNat 64 2)
  , .reg .x12 hpShaDestPtr
  , .reg .x0 0
  , .own ⟨hpSatSp - BitVec.ofNat 64 (8 * 6), 0, by decide⟩
  , .own ⟨hpSatSp - BitVec.ofNat 64 (8 * 5), 0, by decide⟩
  , .own ⟨hpSatSp - BitVec.ofNat 64 (8 * 4), 0, by decide⟩
  , .own ⟨hpSatSp - BitVec.ofNat 64 (8 * 3), 0, by decide⟩
  , .own ⟨hpSatSp - BitVec.ofNat 64 (8 * 2), 0, by decide⟩
  , .own ⟨hpSatSp - BitVec.ofNat 64 (8 * 1), 0, by decide⟩
  , .mem ⟨Blob, packBytes [0, 0], by decide⟩
  , .mem ⟨hpShaDestPtr, packBytes (List.replicate 8 0), by decide⟩
  , .mem ⟨hpShaDestPtr + 8, packBytes (List.replicate 8 0), by decide⟩
  , .mem ⟨hpShaDestPtr + 16, packBytes (List.replicate 8 0), by decide⟩
  , .mem ⟨hpShaDestPtr + 24, packBytes (List.replicate 8 0), by decide⟩
  , .reg .x13 hpShaBodyPtr
  , .reg .x14 0
  , .reg .x26 (BitVec.ofNat 64 2)
  , .reg .x24 hpShaDestPtr
  , .mem ⟨hpShaBodyPtr, packBytes [0], by decide⟩
  , .mem ⟨hpSatSp, B1 + 4, by decide⟩
  ]

private theorem hpShaAtoms_resource_pairwise :
    hpShaAtoms.Pairwise
      (fun x y => hpAtomResource x ≠ hpAtomResource y) := by
  unfold hpShaAtoms hpAtomResource hpSatSp hpShaBodyPtr hpShaDestPtr
  decide

private def hpShaHeap : PartialState :=
  hpShaAtoms.foldr (fun x acc => (hpAtomHeap x).union acc) PartialState.empty

private theorem hpShaAtoms_hsat :
    (hpShaAtoms.foldr (fun x acc => hpAtomAssertion x ** acc) empAssertion)
      hpShaHeap := by
  apply sepConj_foldr_satisfiable hpAtomAssertion hpAtomHeap hpShaAtoms
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | mem m => exact ⟨rfl, m.valid⟩
    | own m => exact ⟨0, rfl, m.valid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => hpAtomHeap_disjoint_of_resource_ne h)
      hpShaAtoms_resource_pairwise

theorem hash_one_sha_residual_pre_non_degenerate_inhabited :
    ∃ h : PartialState,
      (((.x1 ↦ᵣ (B1 + 4)) **
        shaCallEntry hpSatSp Blob (BitVec.ofNat 64 2) hpShaDestPtr
          (hashOneBlob (typeByte (0 : Word)) hpShaBody) hpShaOld) **
        ((.x13 ↦ᵣ hpShaBodyPtr) ** (.x14 ↦ᵣ (0 : Word)) **
          (.x26 ↦ᵣ (BitVec.ofNat 64 2)) ** (.x24 ↦ᵣ hpShaDestPtr) **
          bytesRegion hpShaBodyPtr hpShaBody **
          (hpSatSp ↦ₘ (B1 + 4)) ** empAssertion)) h := by
  refine ⟨hpShaHeap, ?_⟩
  have hsat := hpShaAtoms_hsat
  simp [hpAtomAssertion, hpAtomHeap, shaCallEntry, stackFree,
    hpShaHeap, hpShaAtoms, hpShaBody, hpShaOld, hpShaBodyPtr, hpShaDestPtr,
    hashOneBlob, typeByte, bytesRegion, bytesRegionAux, packBytes,
    sepConj_emp_right', sepConj_assoc'] at hsat ⊢
  xperm_hyp hsat

end EvmAsm.Codegen.MptWalkSpec
