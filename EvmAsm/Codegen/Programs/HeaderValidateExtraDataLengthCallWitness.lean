/-
  EvmAsm.Codegen.Programs.HeaderValidateExtraDataLengthCallWitness

  A constructive non-vacuity witness for the H+176 call to
  `header_validate_extra_data_length`.

  The companion refutation proves that the caller's exact-fit relation makes
  `listLen + 9 ≤ bytes.length` impossible.  This file deliberately proves the
  other half only: after omitting that one conjunct, the complete call-frame
  assertion and its remaining static hypotheses are jointly inhabitable at a
  concrete, non-degenerate point.  The byte region is eight bytes and the K20
  frame owns all seven saved-register cells, so the witness is not an `emp`
  artefact.  It does not claim that the independent `hslack` premise is
  satisfiable at this caller, nor that this is the only caller.
-/

import EvmAsm.Codegen.Programs.HeaderValidateExcessBlobGasSpec
import EvmAsm.Rv64.MemSat

namespace EvmAsm.Codegen.ValidateHeaderCorrespondence

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Concrete exact-fit call-site values -/

private def witnessSp0 : Word := 0x10000
private def witnessSpH : Word := 0xfff0
private def witnessNewSp : Word := 0xffb0
private def witnessListBase : Word := 0x20000
private def witnessListLenW : Word := BitVec.ofNat 64 8
private def witnessBytes : List (BitVec 8) := [1, 2, 3, 4, 5, 6, 7, 8]
private def witnessSaved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved where
  ra := HeaderValidateExtraDataLengthSpec.H + 32
  s0 := 0
  s1 := 0
  s2 := 0
  s3 := 0
  s4 := 0
  s5 := 0

/-! ## One resource key per separating-conjunction atom -/

private structure WitnessMem where
  a : Word
  v : Word
  valid : isValidDwordAccess a = true

private inductive WitnessAtom where
  | reg (r : Reg) (v : Word)
  | regOwn (r : Reg)
  | mem (m : WitnessMem)
  | memOwn (m : WitnessMem)

private def witnessAtomAssertion : WitnessAtom → Assertion
  | .reg r v => r ↦ᵣ v
  | .regOwn r => regOwn r
  | .mem m => m.a ↦ₘ m.v
  | .memOwn m => memOwn m.a

private def witnessAtomHeap : WitnessAtom → PartialState
  | .reg r v => PartialState.singletonReg r v
  | .regOwn r => PartialState.singletonReg r 0
  | .mem m => PartialState.singletonMem m.a m.v
  | .memOwn m => PartialState.singletonMem m.a 0

private inductive WitnessResource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def witnessAtomResource : WitnessAtom → WitnessResource
  | .reg r _ => .reg r
  | .regOwn r => .reg r
  | .mem m => .mem m.a
  | .memOwn m => .mem m.a

private theorem witness_reg_reg_disjoint {r1 r2 : Reg} {v1 v2 : Word}
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

private theorem witness_mem_mem_disjoint {a1 a2 : Word} {v1 v2 : Word}
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

private theorem witness_reg_mem_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) := by
  exact ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem witness_mem_reg_disjoint {r : Reg} {a : Word} {v w : Word} :
    (PartialState.singletonMem a v).Disjoint
      (PartialState.singletonReg r w) :=
  witness_reg_mem_disjoint.symm

private theorem witnessAtomHeap_disjoint_of_resource_ne {x y : WitnessAtom}
    (h : witnessAtomResource x ≠ witnessAtomResource y) :
    (witnessAtomHeap x).Disjoint (witnessAtomHeap y) := by
  cases x <;> cases y
  · apply witness_reg_reg_disjoint
    simpa [witnessAtomResource] using h
  · apply witness_reg_reg_disjoint
    simpa [witnessAtomResource] using h
  · exact witness_reg_mem_disjoint
  · exact witness_reg_mem_disjoint
  · apply witness_reg_reg_disjoint
    simpa [witnessAtomResource] using h
  · apply witness_reg_reg_disjoint
    simpa [witnessAtomResource] using h
  · exact witness_reg_mem_disjoint
  · exact witness_reg_mem_disjoint
  · exact witness_mem_reg_disjoint
  · exact witness_mem_reg_disjoint
  · apply witness_mem_mem_disjoint
    simpa [witnessAtomResource] using h
  · apply witness_mem_mem_disjoint
    simpa [witnessAtomResource] using h
  · exact witness_mem_reg_disjoint
  · exact witness_mem_reg_disjoint
  · apply witness_mem_mem_disjoint
    simpa [witnessAtomResource] using h
  · apply witness_mem_mem_disjoint
    simpa [witnessAtomResource] using h

/-! The atom list mirrors `extraDataCallFrame` exactly, with the linking `x1`
register placed first.  `memOwn` marks the seven K20 stack slots while the
byte region is a real single dword containing eight bytes. -/

private def witnessAtoms : List WitnessAtom :=
  [ .reg .x1 0
  , .reg .x2 witnessSp0
  , .mem ⟨witnessSpH, 0, by decide⟩
  , .reg .x10 witnessListBase
  , .reg .x11 witnessListLenW
  , .reg .x12 0
  , .reg .x13 0
  , .reg .x14 0
  , .reg .x8 witnessSaved.s0
  , .reg .x9 witnessSaved.s1
  , .reg .x18 witnessSaved.s2
  , .reg .x19 witnessSaved.s3
  , .reg .x20 witnessSaved.s4
  , .reg .x21 witnessSaved.s5
  , .regOwn .x5
  , .regOwn .x6
  , .regOwn .x7
  , .regOwn .x28
  , .regOwn .x29
  , .regOwn .x30
  , .regOwn .x31
  , .reg .x0 0
  , .mem ⟨witnessListBase, packBytes witnessBytes, by decide⟩
  , .memOwn ⟨witnessNewSp, 0, by decide⟩
  , .memOwn ⟨witnessNewSp + 8, 0, by decide⟩
  , .memOwn ⟨witnessNewSp + 16, 0, by decide⟩
  , .memOwn ⟨witnessNewSp + 24, 0, by decide⟩
  , .memOwn ⟨witnessNewSp + 32, 0, by decide⟩
  , .memOwn ⟨witnessNewSp + 40, 0, by decide⟩
  , .memOwn ⟨witnessNewSp + 48, 0, by decide⟩
  , .mem ⟨HeaderValidateExtraDataLengthSpec.Off, 0, by decide⟩
  , .mem ⟨HeaderValidateExtraDataLengthSpec.Len, 0, by decide⟩
  ]

private theorem witnessAtoms_resource_pairwise :
    witnessAtoms.Pairwise
      (fun x y => witnessAtomResource x ≠ witnessAtomResource y) := by
  unfold witnessAtoms witnessAtomResource witnessSp0 witnessSpH witnessNewSp
    witnessListBase witnessListLenW witnessSaved
  decide

private def witnessHeap : PartialState :=
  witnessAtoms.foldr (fun x acc => (witnessAtomHeap x).union acc) PartialState.empty

private theorem witnessAtoms_hsat :
    (witnessAtoms.foldr (fun x acc => witnessAtomAssertion x ** acc) empAssertion)
      witnessHeap := by
  apply sepConj_foldr_satisfiable witnessAtomAssertion witnessAtomHeap witnessAtoms
  · intro x hx
    cases x with
    | reg r v => exact rfl
    | regOwn r => exact ⟨0, rfl⟩
    | mem m => exact ⟨rfl, m.valid⟩
    | memOwn m => exact ⟨0, rfl, m.valid⟩
  · exact List.Pairwise.imp
      (fun {_ _} h => witnessAtomHeap_disjoint_of_resource_ne h)
      witnessAtoms_resource_pairwise

private theorem witness_assertion_inhabited :
    ∃ h : PartialState,
      ((.x1 ↦ᵣ (0 : Word)) **
        extraDataCallFrame witnessSp0 0 witnessSpH witnessNewSp witnessListBase
          witnessListLenW 0 0 0 0 0 witnessSaved witnessBytes) h := by
  refine ⟨witnessHeap, ?_⟩
  have hsat := witnessAtoms_hsat
  simp [witnessAtomAssertion, witnessAtomHeap, witnessHeap, witnessAtoms,
    witnessSp0, witnessSpH, witnessNewSp, witnessListBase, witnessListLenW,
    witnessBytes, witnessSaved, extraDataCallFrame,
    bytesRegion, bytesRegionAux, packBytes, frameSlotsOwn,
    EvmAsm.Codegen.RlpListNthItemSAsm.listNthFrame,
    HeaderValidateExtraDataLengthSpec.Off,
    HeaderValidateExtraDataLengthSpec.Len,
    signExtend12, sepConj_emp_right', sepConj_assoc'] at hsat ⊢
  xperm_hyp hsat

/-- The whole remaining H+176 call premise is jointly inhabited at an
exact-fit, non-degenerate point.  The omitted `listLen + 9 ≤ bytes.length`
conjunct is the separate arithmetic refutation; this theorem proves that the
failure is not caused by any other register, frame, address, or byte-region
atom. -/
theorem validate_header_extra_data_length_call_rest_non_degenerate_inhabited :
    ∃ h : PartialState,
      witnessSpH = witnessSp0 + signExtend12 (-16 : BitVec 12) ∧
      witnessNewSp = witnessSpH + signExtend12 (-64 : BitVec 12) ∧
      witnessListLenW = BitVec.ofNat 64 8 ∧
      8 = witnessBytes.length ∧
      witnessListBase.toNat % 8 = 0 ∧
      witnessListBase.toNat + witnessBytes.length < 2 ^ 64 ∧
      (∀ k, k < witnessBytes.length →
        isValidByteAccess (witnessListBase + BitVec.ofNat 64 k) = true) ∧
      witnessSaved.ra = HeaderValidateExtraDataLengthSpec.H + 32 ∧
      ((.x1 ↦ᵣ (0 : Word)) **
        extraDataCallFrame witnessSp0 0 witnessSpH witnessNewSp witnessListBase
          witnessListLenW 0 0 0 0 0 witnessSaved witnessBytes) h := by
  obtain ⟨h, hh⟩ := witness_assertion_inhabited
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hh⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

#print axioms validate_header_extra_data_length_call_rest_non_degenerate_inhabited

end EvmAsm.Codegen.ValidateHeaderCorrespondence
