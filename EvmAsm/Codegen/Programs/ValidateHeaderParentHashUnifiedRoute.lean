/-
  Caller-side plumbing for the unified parent-hash contract (#12346 item 8).

  The parent-hash call is made after the validate-header prologue has
  installed the parent RLP pointer in x20.  The continuation ambient therefore
  owns the child-frame stack and scratch/BSS regions, but deliberately leaves
  x20 to the route's post-prologue register assertion.  This prevents the
  ambient from claiming an entry-time x20 that the caller does not provide.
-/

import EvmAsm.Codegen.Programs.ValidateHeaderParentHashAdapter

namespace EvmAsm.Codegen.ValidateHeaderCompose

open EvmAsm EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.ValidateHeaderCorrespondence
open EvmAsm.Codegen.ValidateHeaderParentHashCorrespondence
open EvmAsm.Codegen.HeaderValidateParentHashSpec
open EvmAsm.Rv64.RLP

noncomputable section

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_regOwns _)

/-- The unified continuation ambient after the caller has supplied x20.

`hvphSuccKeccakAmb` also owns x20.  At the H+244 call seam that cell is
already produced by `postMerge_status0_to_parent_hash_args`, so this residual
form is what can actually be framed through that caller route. -/
def hvphSuccKeccakTail
    (spC : Word) (os out0 : List (BitVec 8)) (F : Assertion) : Assertion :=
  stackFree spC 4 **
  regOwns [.x14, .x15, .x16, .x17] **
  bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
  bytesRegion Computed out0 ** F

theorem hvphSuccKeccakTail_pcFree
    (spC : Word) (os out0 : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) : (hvphSuccKeccakTail spC os out0 F).pcFree := by
  unfold hvphSuccKeccakTail
  pcf
  exact hF

/-! ## The real H+196 → H+248 caller seam

The theorem below is intentionally a direct consumer of
`validate_header_parent_hash_unified_call_spec_within`.  The route carries the
physical claimed/computed/zk3 resources and child-frame stack from the
post-prologue seam; it does not replace them by an unconstrained `G`.
-/

set_option maxRecDepth 8000 in
theorem postMerge_status0_to_parent_hash_unified_call
    {cr calleeCode : CodeReq} {n : Nat}
    (spC childSp header headerLen s4 s5 oldRa : Word)
    (vals : Reg → Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hchild : childSp = spC + signExtend12 (-32 : BitVec 12))
    (hvals8 : vals .x8 = header)
    (hvals9 : vals .x9 = headerLen)
    (hvals18 : vals .x18 = s4)
    (hdisj : (CodeReq.singleton
      ValidateHeaderParentHashCorrespondence.A
      (.JAL .x1 (jalOff GuestAddrs.header_validate_parent_hash
        (GuestAddrs.validate_header + 244)))).Disjoint calleeCode)
    (hcallerDisj : parentHashRouteFrameCaller.Disjoint calleeCode)
    (hcode : ∀ a i, (parentHashRouteFrameCaller.union calleeCode) a = some i →
      cr a = some i)
    (hcallee : cpsTripleWithin n
      ValidateHeaderParentHashCorrespondence.Callee
      ValidateHeaderParentHashCorrespondence.Ret calleeCode
      ((.x1 ↦ᵣ ValidateHeaderParentHashCorrespondence.Ret) **
        ValidateHeaderParentHashCorrespondence.hvphEntryRest
          spC header headerLen s4 s5 vals thisBytes parentBytes **
        claimedOwn C0 **
        hvphSuccKeccakAmb childSp s4 os (List.replicate 32 0) G)
      (hvphUnifiedPost spC childSp
        ValidateHeaderParentHashCorrespondence.Ret header s4 s5 vals s4
        thisBytes parentBytes C0 N rem os G)) :
    cpsTripleWithin (5 + (1 + n))
      (parentHashRouteFrameH + 196)
      ValidateHeaderParentHashCorrespondence.Ret cr
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ header) ** (.x9 ↦ᵣ headerLen) **
        (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (0 : Word)) **
        parentHashRouteFrame spC oldRa header s4 vals thisBytes parentBytes **
        claimedOwn C0 **
        hvphSuccKeccakTail childSp os (List.replicate 32 0) G)
      ((.x21 ↦ᵣ s5) **
        hvphUnifiedPost spC childSp
          ValidateHeaderParentHashCorrespondence.Ret header s4 s5 vals s4
          thisBytes parentBytes C0 N rem os G) := by
  let tail := hvphSuccKeccakTail childSp os (List.replicate 32 0) G
  let F := parentHashRouteFrame spC oldRa header s4 vals thisBytes parentBytes **
    claimedOwn C0 ** tail
  have hF : F.pcFree := by
    dsimp [F, tail]
    pcf
    exact hG
  have hroute := postMerge_status0_to_parent_hash_args
    (header := header) (headerLen := headerLen) (s4 := s4) (s5 := s5)
    (F := F) hF
  have hcallerCode : ∀ a i, parentHashRouteFrameCaller a = some i → cr a = some i := by
    intro a i hi
    exact hcode a i (CodeReq.union_mono_left a i hi)
  have hrouteC := cpsTripleWithin_extend_code hcallerCode hroute
  have hcall :=
    validate_header_parent_hash_unified_call_spec_within
      (cr := cr) (calleeCode := calleeCode) (n := n)
      spC childSp header headerLen s4 s5 oldRa vals
      thisBytes parentBytes C0 N rem os s4 G hG
      hdisj hcallerDisj hcode hcallee
  have hx21 : ((.x21 ↦ᵣ s5) : Assertion).pcFree := pcFree_regIs
  have hcallF := cpsTripleWithin_frameR ((.x21 ↦ᵣ s5) : Assertion) hx21 hcall
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold F tail hvphSuccKeccakTail at hp
      unfold parentHashRouteFrame at hp
      unfold ValidateHeaderParentHashCorrespondence.hvphEntryRest
        hvphSuccKeccakAmb
      have hneg : signExtend12 (-32 : BitVec 12) =
          signExtend12 (BitVec.ofNat 12 4064) := by decide
      have hbase : spC + signExtend12 (-32 : BitVec 12) =
          spC + signExtend12 (BitVec.ofNat 12 4064) := by rw [hneg]
      rw [hchild] at hp
      rw [hchild] at ⊢
      rw [hbase] at ⊢
      rw [hbase] at hp
      rw [hvals18] at hp
      simp [hvals8, hvals9, hvals18,
        ValidateHeaderParentHashCorrespondence.hvphSavedFrame,
        EvmAsm.Rv64.SAsm.regsAt, EvmAsm.Rv64.SAsm.regOwns,
        HeaderValidateParentHashSpec.Computed, sepConj_emp_right'] at hp ⊢
      xperm_hyp hp)
    hrouteC hcallF
  refine cpsTripleWithin_weaken
    (fun _ hp => by simpa [F, tail, sepConj_assoc'] using hp)
    (fun _ hq => by xperm_hyp hq)
    hseq

/-! ## Applied-ambient non-vacuity witness

The route's new resources are not merely names in a postcondition.  The
concrete witness below supplies the post-prologue `x20`, four free stack cells,
the four temporary registers, and the four dwords of `Computed`.  The empty
`zk3_state` and `Claimed` regions are intentional: they exercise the same
resource shape without smuggling in an unrelated payload.  The final theorem
combines this ambient with the existing `hvphEntryRest_inhabited` witness, so
the complete unified-call precondition is inhabited at one concrete frame.
-/

private inductive item8Atom where
  | regVal (r : Reg) (v : Word)
  | regOwn (r : Reg)
  | memVal (a v : Word) (hvalid : isValidDwordAccess a = true)
  | memOwn (a : Word) (hvalid : isValidDwordAccess a = true)

private inductive item8Resource where
  | reg (r : Reg)
  | mem (a : Word)
  deriving DecidableEq

private def item8AtomResource : item8Atom → item8Resource
  | .regVal r _ => .reg r
  | .regOwn r => .reg r
  | .memVal a _ _ => .mem a
  | .memOwn a _ => .mem a

private def item8AtomAssertion : item8Atom → Assertion
  | .regVal r v => r ↦ᵣ v
  | .regOwn r => regOwn r
  | .memVal a v _ => a ↦ₘ v
  | .memOwn a _ => memOwn a

private def item8AtomHeap : item8Atom → PartialState
  | .regVal r v => PartialState.singletonReg r v
  | .regOwn r => PartialState.singletonReg r 0
  | .memVal a v _ => PartialState.singletonMem a v
  | .memOwn a _ => PartialState.singletonMem a 0

private abbrev item8SpC : Word := 0xFE8
private abbrev item8ChildSp : Word := 0xFC8
private abbrev item8S4 : Word := 0x3000
private abbrev item8C0 : List (BitVec 8) := List.replicate 32 0
private abbrev item8Os : List (BitVec 8) := List.replicate 200 0
private abbrev item8Out0 : List (BitVec 8) := List.replicate 32 0

private def item8Atoms : List item8Atom :=
  [ .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed + 8) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed + 16) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_claimed + 24) 0 (by decide)
  , .regVal .x20 item8S4
  , .memOwn (item8ChildSp - BitVec.ofNat 64 32) (by decide)
  , .memOwn (item8ChildSp - BitVec.ofNat 64 24) (by decide)
  , .memOwn (item8ChildSp - BitVec.ofNat 64 16) (by decide)
  , .memOwn (item8ChildSp - BitVec.ofNat 64 8) (by decide)
  , .regOwn .x14, .regOwn .x15, .regOwn .x16, .regOwn .x17
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 8) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 16) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 24) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 32) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 40) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 48) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 56) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 64) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 72) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 80) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 88) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 96) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 104) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 112) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 120) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 128) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 136) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 144) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 152) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 160) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 168) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 176) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 184) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.zk3_state + 192) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed + 8) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed + 16) 0 (by decide)
  , .memVal (BitVec.ofNat 64 GuestAddrs.hvph_computed + 24) 0 (by decide) ]

private def item8AtomsAssertion : Assertion :=
  item8Atoms.foldr (fun x acc => item8AtomAssertion x ** acc) empAssertion

private def item8AtomsHeap : PartialState :=
  item8Atoms.foldr (fun x acc => (item8AtomHeap x).union acc) PartialState.empty

private theorem item8RegRegDisjoint {r1 r2 : Reg} {v1 v2 : Word}
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

private theorem item8MemMemDisjoint {a1 a2 v1 v2 : Word}
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

private theorem item8RegMemDisjoint {r : Reg} {a v w : Word} :
    (PartialState.singletonReg r v).Disjoint
      (PartialState.singletonMem a w) :=
  ⟨fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun _ => Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

private theorem item8AtomHeapDisjoint_of_resource_ne {x y : item8Atom}
    (h : item8AtomResource x ≠ item8AtomResource y) :
    (item8AtomHeap x).Disjoint (item8AtomHeap y) := by
  cases x <;> cases y
  · apply item8RegRegDisjoint
    simpa [item8AtomResource] using h
  · apply item8RegRegDisjoint
    simpa [item8AtomResource] using h
  · exact item8RegMemDisjoint
  · exact item8RegMemDisjoint
  · apply item8RegRegDisjoint
    simpa [item8AtomResource] using h
  · apply item8RegRegDisjoint
    simpa [item8AtomResource] using h
  · exact item8RegMemDisjoint
  · exact item8RegMemDisjoint
  · exact item8RegMemDisjoint.symm
  · exact item8RegMemDisjoint.symm
  · apply item8MemMemDisjoint
    simpa [item8AtomResource] using h
  · apply item8MemMemDisjoint
    simpa [item8AtomResource] using h
  · exact item8RegMemDisjoint.symm
  · exact item8RegMemDisjoint.symm
  · apply item8MemMemDisjoint
    simpa [item8AtomResource] using h
  · apply item8MemMemDisjoint
    simpa [item8AtomResource] using h

private theorem item8Atoms_sat : item8AtomsAssertion item8AtomsHeap := by
  apply sepConj_foldr_satisfiable item8AtomAssertion item8AtomHeap item8Atoms
  · intro x hx
    cases x with
    | regVal r v => rfl
    | regOwn r => exact ⟨0, rfl⟩
    | memVal a v hvalid => exact ⟨rfl, hvalid⟩
    | memOwn a hvalid => exact ⟨0, rfl, hvalid⟩
  · have hpair : item8Atoms.Pairwise
        (fun x y => item8AtomResource x ≠ item8AtomResource y) := by
      decide
    exact List.Pairwise.imp
      (fun {_ _} h => item8AtomHeapDisjoint_of_resource_ne h) hpair

set_option maxRecDepth 8000 in
private theorem item8Atoms_assertion_eq :
    item8AtomsAssertion =
      (claimedOwn item8C0 ** (.x20 ↦ᵣ item8S4) ** stackFree item8ChildSp 4 **
        regOwns [.x14, .x15, .x16, .x17] **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) item8Os **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.hvph_computed) item8Out0) := by
  funext h
  have hzero :
      packBytes ([0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] :
        List (BitVec 8)) = (0 : Word) := by decide
  simp [item8AtomsAssertion, item8Atoms, item8AtomAssertion, stackFree,
    regOwns, bytesRegion, bytesRegionAux, item8C0, item8Os, item8Out0,
    hzero, BitVec.add_assoc, sepConj_emp_right',
    sepConj_assoc']

theorem parentHashUnifiedAmbient_inhabited :
    ∃ h : PartialState,
      (claimedOwn item8C0 **
        hvphSuccKeccakAmb item8ChildSp item8S4 item8Os item8Out0 empAssertion) h := by
  refine ⟨item8AtomsHeap, ?_⟩
  have hsat := item8Atoms_sat
  rw [item8Atoms_assertion_eq] at hsat
  simpa [hvphSuccKeccakAmb, sepConj_emp_left', sepConj_emp_right'] using hsat

end

end EvmAsm.Codegen.ValidateHeaderCompose
