/-
  EvmAsm.Codegen.Programs.HeaderValidatePostMergeCallWitness

  A constructive non-vacuity witness for the H+192 call to
  `header_validate_post_merge`.

  The K67 whole-routine triple `header_validate_post_merge_spec_within`
  (HeaderValidatePostMergeFinal.lean) exists on main and concludes in the
  ADAPTER shape with the five-way disjunctive post `k67PostRet`.  The call-spec
  `validate_header_post_merge_call_spec_within` needs a SINGLE-status
  `postMergeCalleePost`; the gap is a SHAPE mismatch (unselected arm), not a
  missing triple.  This file proves the hcallee premise IS jointly inhabitable
  at the H+192 caller shape — at a concrete, non-degenerate point, at the
  granularity of the whole conjunction `(.x1 ↦ Ret) ** postMergeEntryRest …`
  (not each half separately).  It does NOT discharge the hcallee: the
  selection lemma that picks the status-0 arm out of `k67PostRet` remains the
  specified piece of work.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderPostMergeCorrespondence
import EvmAsm.Codegen.Programs.ChainValidatePostMergeFullSpec
import EvmAsm.Rv64.MemSat

namespace EvmAsm.Codegen.ValidateHeaderPostMergeCorrespondence

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Concrete non-degenerate call-site values -/

private def witnessSpC : Word := 0x10000
private def witnessHeader : Word := 0x20000
private def witnessHeaderLen : Word := BitVec.ofNat 64 8
private def witnessS4 : Word := 0x30000
private def witnessS5 : Word := BitVec.ofNat 64 16
private def witnessThisStruct : Word := 0x40000
private def witnessParentStruct : Word := 0x50000
private def witnessBytes : List (BitVec 8) := [1, 2, 3, 4, 5, 6, 7, 8]
private def witnessVals : Reg → Word :=
  fun r =>
    if r = .x8 then witnessHeader else
    if r = .x9 then witnessHeaderLen else
    if r = .x18 then witnessThisStruct else
    if r = .x19 then witnessParentStruct else 0

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

/-! The atom list mirrors `(.x1 ↦ Ret) ** postMergeEntryRest …` exactly.
  The linking `x1` register is placed first.  The header byte region is a real
  single dword containing eight bytes; the empty-ommer-hash constant region is
  the four dwords of `cvpmfEmptyOmmerHashBytes` at `GuestAddrs.empty_ommers_hash`
  (the `.data` pin).  `memOwn` marks the six K67 saved slots. -/

private def witnessAtoms : List WitnessAtom :=
  [ .reg .x1 Ret
  , .reg .x2 witnessSpC
  , .memOwn ⟨witnessSpC + signExtend12 (-48 : BitVec 12) + (0 : Word), 0, by decide⟩
  , .memOwn ⟨witnessSpC + signExtend12 (-48 : BitVec 12) + 8, 0, by decide⟩
  , .memOwn ⟨witnessSpC + signExtend12 (-48 : BitVec 12) + 16, 0, by decide⟩
  , .memOwn ⟨witnessSpC + signExtend12 (-48 : BitVec 12) + 24, 0, by decide⟩
  , .memOwn ⟨witnessSpC + signExtend12 (-48 : BitVec 12) + 32, 0, by decide⟩
  , .memOwn ⟨witnessSpC + signExtend12 (-48 : BitVec 12) + 40, 0, by decide⟩
  , .reg .x8 (witnessVals .x8)
  , .reg .x9 (witnessVals .x9)
  , .reg .x18 (witnessVals .x18)
  , .reg .x19 (witnessVals .x19)
  , .reg .x20 witnessS4
  , .reg .x21 witnessS5
  , .reg .x10 witnessHeader
  , .reg .x11 witnessHeaderLen
  , .regOwn .x12
  , .regOwn .x13
  , .regOwn .x14
  , .regOwn .x5
  , .regOwn .x6
  , .regOwn .x7
  , .regOwn .x28
  , .regOwn .x29
  , .regOwn .x30
  , .regOwn .x31
  , .reg .x0 0
  , .mem ⟨witnessHeader, packBytes witnessBytes, by decide⟩
  , .mem ⟨(GuestAddrs.empty_ommers_hash : Word) + 0,
      packBytes (ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes.take 8), by decide⟩
  , .mem ⟨(GuestAddrs.empty_ommers_hash : Word) + 8,
      packBytes ((ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes.drop 8).take 8), by decide⟩
  , .mem ⟨(GuestAddrs.empty_ommers_hash : Word) + 8 + 8,
      packBytes ((ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes.drop 16).take 8), by decide⟩
  , .mem ⟨(GuestAddrs.empty_ommers_hash : Word) + 8 + 8 + 8,
      packBytes ((ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes.drop 24).take 8), by decide⟩
  ]

private theorem witnessAtoms_resource_pairwise :
    witnessAtoms.Pairwise
      (fun x y => witnessAtomResource x ≠ witnessAtomResource y) := by
  unfold witnessAtoms witnessAtomResource witnessSpC witnessHeader
    witnessHeaderLen witnessS4 witnessS5 witnessBytes witnessVals
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
      ((.x1 ↦ᵣ Ret) **
        postMergeEntryRest witnessSpC witnessHeader witnessHeaderLen
          witnessS4 witnessS5 witnessVals witnessBytes) h := by
  refine ⟨witnessHeap, ?_⟩
  have hsat := witnessAtoms_hsat
  simp [witnessAtomAssertion, witnessAtomHeap, witnessHeap, witnessAtoms,
    witnessSpC, witnessHeader, witnessHeaderLen, witnessS4, witnessS5,
    witnessThisStruct, witnessParentStruct, witnessBytes, witnessVals,
    postMergeEntryRest, postMergeFrame, postMergeSavedFrame,
    bytesRegion, bytesRegionAux, packBytes, frameSlotsOwn,
    regsAt, signExtend12, sepConj_emp_right', sepConj_assoc',
    ChainValidatePostMergeFullSpec.cvpmfEmptyOmmerHashBytes] at hsat ⊢
  xperm_hyp hsat

/-- The whole H+192 call premise is jointly inhabited at a non-degenerate
point.  At the granularity of the conjunction: every conjunct of
`(.x1 ↦ Ret) ** postMergeEntryRest witnessSpC witnessHeader witnessHeaderLen
witnessS4 witnessS5 witnessVals witnessBytes` holds on one heap.  It does NOT
discharge `hcallee`: the selection of a single status out of `k67PostRet`
remains the specified piece of work. -/
theorem header_validate_post_merge_call_pre_non_degenerate_inhabited :
    ∃ h : PartialState,
      witnessHeader ≠ (GuestAddrs.empty_ommers_hash : Word) ∧
      0 < witnessBytes.length ∧
      witnessS4 ≠ witnessS5 ∧
      witnessHeader.toNat % 8 = 0 ∧
      (∀ k, k < witnessBytes.length →
        isValidByteAccess (witnessHeader + BitVec.ofNat 64 k) = true) ∧
      ((.x1 ↦ᵣ Ret) **
        postMergeEntryRest witnessSpC witnessHeader witnessHeaderLen
          witnessS4 witnessS5 witnessVals witnessBytes) h := by
  obtain ⟨h, hh⟩ := witness_assertion_inhabited
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, hh⟩
  · decide
  · decide
  · decide
  · decide
  · have hfin : ∀ k : Fin 8,
      isValidByteAccess (witnessHeader + BitVec.ofNat 64 k.val) = true := by
      intro k
      fin_cases k <;> decide
    intro k hk
    exact hfin ⟨k, by simpa [witnessBytes] using hk⟩

#print axioms header_validate_post_merge_call_pre_non_degenerate_inhabited

end EvmAsm.Codegen.ValidateHeaderPostMergeCorrespondence