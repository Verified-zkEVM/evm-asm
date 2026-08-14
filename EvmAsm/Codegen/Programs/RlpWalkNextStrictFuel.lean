/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuel

  Continuation-level machine contracts for #12300.  The structural fuel model
  and validator-side contracts live in sibling modules; this file develops the
  shared-machine half of the strict LIST knot.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelModel
import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelContracts
import EvmAsm.Codegen.Programs.RlpWalkNextStrictTie
import EvmAsm.Rv64.RLP.WalkItemDeterminism
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.Tactics.XPermPure
import EvmAsm.Rv64.Tactics.DropPure

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-! The concrete nested-call boundary is `V+36 → V+40`: the payload's JAL
enters `rlp_walk_next_nested`, and the continuation starts at the instruction
after that call.  This specialization keeps the call code and the
continuation code separate (with one static disjointness proof), while the
success value remains fully indexed by `post`. -/

theorem validate_nested_success_path_dep_bind
    {α : Type} {nCall nCont : Nat} {callCode contCode : CodeReq}
    {P R : Assertion} {post : α → Assertion} (exit_ : Word)
    (hd : callCode.Disjoint contCode)
    (hcall : cpsTripleWithin nCall (validateEntry + 36) (validateEntry + 40)
      callCode P (cpsDepPost post))
    (hcont : ∀ a, cpsTripleWithin nCont (validateEntry + 40) exit_ contCode
      (post a) R) :
    cpsTripleWithin (nCall + nCont) (validateEntry + 36) exit_ (callCode.union contCode)
      P R :=
  cpsTripleWithin_seq_dep_post hd hcall hcont

theorem validate_nested_jal_success_dep_bind
    {nCall nCont : Nat} {calleeEntry : Word} {calleeCode contCode : CodeReq}
    {α : Type} {P R : Assertion} {post : α → Assertion}
    (oldRa : Word) (offset : BitVec 21) (exit_ : Word)
    (hoffset : (validateEntry + 36) + signExtend21 offset = calleeEntry)
    (halign : ((validateEntry + 40) &&& ~~~(1 : Word)) = validateEntry + 40)
    (hP : P.pcFree)
    (hcallCode : (CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).Disjoint calleeCode)
    (hcallee : cpsTripleWithin nCall calleeEntry (validateEntry + 40) calleeCode
      ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post))
    (hdisj : (CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union calleeCode |>.Disjoint contCode)
    (hcont : ∀ a, cpsTripleWithin nCont (validateEntry + 40) exit_ contCode (post a) R) :
    cpsTripleWithin (1 + nCall + nCont) (validateEntry + 36) exit_
      ((CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union calleeCode |>.union contCode)
      ((regIs .x1 oldRa) ** P) R := by
  have hcall' := WP.cpsCallWithin (vOld := oldRa) offset hoffset halign hP hcallCode hcallee
  exact cpsTripleWithin_seq_dep_post hdisj hcall' hcont

theorem validate_nested_alias_dep_hcallee
    {nShared : Nat} {α : Type} {P : Assertion} {post : α → Assertion}
    (hP : P.pcFree)
    (hdisj : (CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
      (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
        (GuestAddrs.rlp_walk_next_nested + 0)))).Disjoint
      RlpWalkNextStrictTie.sharedCode)
    (hshared : cpsTripleWithin nShared (GuestAddrs.rlp_walk_next_shared : Word)
      (validateEntry + 40) RlpWalkNextStrictTie.sharedCode
      ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post)) :
    cpsTripleWithin (1 + nShared) (GuestAddrs.rlp_walk_next_nested : Word)
      (validateEntry + 40)
      ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
        (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
          (GuestAddrs.rlp_walk_next_nested + 0)))).union
        RlpWalkNextStrictTie.sharedCode)
      ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post) := by
  have hj := jal_x0_spec_gen_within
    (jalOff GuestAddrs.rlp_walk_next_shared
      (GuestAddrs.rlp_walk_next_nested + 0))
    (GuestAddrs.rlp_walk_next_nested : Word)
  rw [show (GuestAddrs.rlp_walk_next_nested : Word) +
      signExtend21 (jalOff GuestAddrs.rlp_walk_next_shared
        (GuestAddrs.rlp_walk_next_nested + 0)) =
      (GuestAddrs.rlp_walk_next_shared : Word) from by decide] at hj
  have hj' := cpsTripleWithin_frameR
    ((regIs .x1 (validateEntry + 40)) ** P)
    (by apply pcFree_sepConj <;> first | exact pcFree_regIs | exact hP) hj
  have hj'' := cpsTripleWithin_weaken
    (fun h hp => (sepConj_emp_left h).mpr hp)
    (fun h hp => (sepConj_emp_left h).mp hp) hj'
  exact cpsTripleWithin_seq hdisj hj'' hshared

/-! The nested entry is not a third recursive family.  It is one concrete
    `JAL x0` adapter whose structural index is inherited from the Shared
    contract it enters; the extra instruction contributes only to the CPS
    step bound.  This is the machine-level specialization of the two-family
    induction shape recorded in `RlpWalkNextStrictFuelModel`. -/

theorem validate_nested_alias_indexed
    {fuel : Nat} {α : Type} {P : Assertion} {post : α → Assertion}
    (hP : P.pcFree)
    (hdisj : (CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
      (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
        (GuestAddrs.rlp_walk_next_nested + 0)))).Disjoint
      RlpWalkNextStrictTie.sharedCode)
    (hshared : IndexedCpsContract fuel
      (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post)) :
    Nonempty (IndexedCpsContract fuel
      (GuestAddrs.rlp_walk_next_nested : Word) (validateEntry + 40)
      ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
        (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
          (GuestAddrs.rlp_walk_next_nested + 0)))).union
        RlpWalkNextStrictTie.sharedCode)
      ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post)) := by
  refine ⟨⟨1 + hshared.steps, ?_⟩⟩
  exact validate_nested_alias_dep_hcallee hP hdisj hshared.proof

/-! These are the two *actual* CPS family predicates.  They retain the
    machine entry/exit and dependent post shape; only the structural `fuel`
    is abstracted.  The existential `steps` lives inside `IndexedCpsContract`,
    so the induction cannot accidentally use a CPS bound as its termination
    index. -/

def sharedIndexedFamily
    {α : Type} (P : Assertion) (post : α → Assertion) (fuel : Nat) : Prop :=
  Nonempty (IndexedCpsContract fuel
    (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
    RlpWalkNextStrictTie.sharedCode
    ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post))

def validateIndexedFamily
    (P R : Assertion) (exit_ : Word) (wholeCode : CodeReq)
    (fuel : Nat) : Prop :=
  Nonempty (IndexedCpsContract fuel
    (validateEntry + 36) exit_ wholeCode
    ((regIs .x1 (validateEntry + 40)) ** P) R)

/-! This is the first real two-family induction consumer.  Its hypotheses are
    the remaining contract builders: the Shared builder must discharge the
    short/long setup using the smaller Validate family, and the Validate
    builder must discharge the status/continuation arms using the smaller
    Shared family.  They are explicit rather than hidden in a tactic block.
    Once supplied, the result is a pair of actual `IndexedCpsContract`s, not
    an abstract semantic witness. -/

theorem actual_strict_walk_two_family_induction
    {α : Type} {P : Assertion} {post : α → Assertion}
    {exit_ : Word} {wholeCode : CodeReq} {R : Assertion}
    (hshared : ∀ fuel,
      (∀ k, k < fuel →
        sharedIndexedFamily P post k ∧
        validateIndexedFamily P R exit_ wholeCode k) →
      sharedIndexedFamily P post fuel)
    (hvalidate : ∀ fuel,
      (∀ k, k < fuel →
        sharedIndexedFamily P post k ∧
        validateIndexedFamily P R exit_ wholeCode k) →
      validateIndexedFamily P R exit_ wholeCode fuel) :
    ∀ fuel,
      sharedIndexedFamily P post fuel ∧
      validateIndexedFamily P R exit_ wholeCode fuel := by
  apply cycleFuel_mutual_strong_induction
  intro fuel ih
  exact ⟨hshared fuel ih, hvalidate fuel ih⟩

/-! The first half of the mutual knot.  This is the complete non-empty
    validator arm, parameterised by the shared LIST-arm contract.  The
    premise is intentionally the S-entry-to-V+40 dependent contract rather
    than `shared_validate_status_dep`: the nested tail returns at V+40, while
    the latter theorem starts after the shared validator return at S+164. -/
theorem rlp_validate_payload_nonempty_cps_under_shared
    {nShared nCont : Nat} {α : Type}
    {P R : Assertion} {post : α → Assertion}
    {contCode : CodeReq}
    (oldRa exit_ : Word) (offset : BitVec 21)
    (hoffset : (validateEntry + 36) + signExtend21 offset =
      (GuestAddrs.rlp_walk_next_nested : Word))
    (halign : ((validateEntry + 40) &&& ~~~(1 : Word)) = validateEntry + 40)
    (hP : P.pcFree)
    (hcallCode : (CodeReq.singleton (validateEntry + 36)
      (.JAL .x1 offset)).Disjoint
      ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
        (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
          (GuestAddrs.rlp_walk_next_nested + 0)))).union
        RlpWalkNextStrictTie.sharedCode))
    (hsharedDisj : (CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
      (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
        (GuestAddrs.rlp_walk_next_nested + 0)))).Disjoint
      RlpWalkNextStrictTie.sharedCode)
    (houterDisj :
      ((CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union
        ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
          (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
            (GuestAddrs.rlp_walk_next_nested + 0)))).union
          RlpWalkNextStrictTie.sharedCode)).Disjoint contCode)
    (hshared : cpsTripleWithin nShared
      (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x1 (validateEntry + 40)) ** P) (cpsDepPost post))
    (hcont : ∀ a, cpsTripleWithin nCont (validateEntry + 40) exit_
      contCode (post a) R) :
    cpsTripleWithin (1 + (1 + nShared) + nCont) (validateEntry + 36) exit_
      ((CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union
        ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
          (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
            (GuestAddrs.rlp_walk_next_nested + 0)))).union
          RlpWalkNextStrictTie.sharedCode) |>.union contCode)
      ((regIs .x1 oldRa) ** P) R := by
  have hcallee := validate_nested_alias_dep_hcallee hP hsharedDisj hshared
  exact validate_nested_jal_success_dep_bind (nCall := 1 + nShared)
    (nCont := nCont) (calleeEntry := GuestAddrs.rlp_walk_next_nested)
    (calleeCode := (CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
      (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
        (GuestAddrs.rlp_walk_next_nested + 0)))).union
      RlpWalkNextStrictTie.sharedCode)
    oldRa offset exit_ hoffset halign hP hcallCode hcallee houterDisj hcont

def rlp_validate_payload_success_post
    (sp raVal cursor endPtr : Word) (P : Assertion) : Assertion :=
  (((regIs .x2 (sp + 32)) ** (regIs .x10 (0 : Word)) **
      (regIs .x1 raVal) ** (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) **
      (memIs (sp + 16) endPtr)) ** (regIs .x0 (0 : Word))) ** P

def rlp_validate_payload_success_pre
    (sp raVal cursor endPtr : Word) (P : Assertion) : Assertion :=
  (((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x1 raVal) **
      (regIs .x5 endPtr) ** (regIs .x11 endPtr) ** (memIs sp raVal) **
      (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr)) **
      (regIs .x0 (0 : Word))) ** P

def rlp_validate_payload_failure_post
    (sp raVal cursor endPtr : Word) (P : Assertion) : Assertion :=
  (((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) **
      (regIs .x1 raVal) ** (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
      (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
      (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr)) ** P)

def rlp_validate_payload_precheck_post
    (sp raVal cursor endPtr : Word) (P : Assertion) : Assertion :=
  ((regIs .x10 cursor) ** (regIs .x5 endPtr)) ** (regIs .x2 sp) **
    (regIs .x1 raVal) ** (regIs .x11 endPtr) ** (regIs .x0 (0 : Word)) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 16) endPtr) ** P

/-! The prefix and terminal arms are composable without closing the mutual
    LIST knot.  This theorem carries the shared-arm contract as a premise and
    leaves only the continuation at `V+40` abstract.  Thus it states the whole
    validator entry contract (empty, precheck failure, nested failure, and the
    result continuation), while the eventual fuel induction can discharge the
    continuation premise separately.  The `post` family is where the decoded
    cursor/length witness is preserved. -/
theorem rlp_validate_payload_cps_under_shared
    {nShared nCont : Nat} {α : Type}
    {P R : Assertion} {post : α → Assertion}
    {contCode wholeCode : CodeReq}
    (sp raVal cursor endPtr x5Old exit_ : Word) (offset : BitVec 21)
    (hoffset : (validateEntry + 36) + signExtend21 offset =
      (GuestAddrs.rlp_walk_next_nested : Word))
    (halign : ((validateEntry + 40) &&& ~~~(1 : Word)) = validateEntry + 40)
    (hP : P.pcFree)
    (hcallCode : (CodeReq.singleton (validateEntry + 36)
      (.JAL .x1 offset)).Disjoint
      ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
        (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
          (GuestAddrs.rlp_walk_next_nested + 0)))).union
        RlpWalkNextStrictTie.sharedCode))
    (hsharedDisj : (CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
      (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
        (GuestAddrs.rlp_walk_next_nested + 0)))).Disjoint
      RlpWalkNextStrictTie.sharedCode)
    (houterDisj :
      ((CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union
        ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
          (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
            (GuestAddrs.rlp_walk_next_nested + 0)))).union
          RlpWalkNextStrictTie.sharedCode)).Disjoint contCode)
    (hvalidateSub : ∀ a i, validateCR a = some i → wholeCode a = some i)
    (hbodySub : ∀ a i,
      (((CodeReq.singleton (validateEntry + 36) (.JAL .x1 offset)).union
        ((CodeReq.singleton (GuestAddrs.rlp_walk_next_nested : Word)
          (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
            (GuestAddrs.rlp_walk_next_nested + 0)))).union
          RlpWalkNextStrictTie.sharedCode)).union contCode) a = some i →
      wholeCode a = some i)
    (hshared : cpsTripleWithin nShared
      (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x1 (validateEntry + 40)) **
        ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x11 endPtr) **
          (regIs .x5 endPtr) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
          (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr) ** P))
      (cpsDepPost post))
    (hcont : ∀ a, cpsTripleWithin nCont (validateEntry + 40) exit_
      contCode (post a) R)
    (hexit : exit_ = raVal &&& ~~~(1 : Word))
    (hsuccessPost : ∀ h,
      rlp_validate_payload_success_post sp raVal cursor endPtr P h → R h)
    (hfailPost : ∀ h,
      rlp_validate_payload_failure_post sp raVal cursor endPtr P h → R h) :
    cpsTripleWithin
      (9 + max 4 (max 4 (1 + (1 + nShared) + nCont))) validateEntry exit_ wholeCode
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
       (regIs .x10 cursor) ** (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
       (regIs .x0 (0 : Word)) ** memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P) R := by
  let bodyP : Assertion :=
    ((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x11 endPtr) **
      (regIs .x5 endPtr) ** (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
      (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr) **
      P)
  have hbodyP : bodyP.pcFree := by
    simp only [bodyP]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_pure
      | exact hP
  have hbody := rlp_validate_payload_nonempty_cps_under_shared
    (P := bodyP) (R := R) (post := post) (contCode := contCode)
    raVal exit_ offset hoffset halign hbodyP hcallCode hsharedDisj houterDisj
    (by simpa [bodyP] using hshared) hcont
  have hfail := validate_failure_tail_cps sp raVal cursor endPtr endPtr raVal endPtr
  have hfail' := cpsTripleWithin_frameR P hP hfail
  have hfailExit := hfail'
  rw [← hexit] at hfailExit
  have hfailCode := cpsTripleWithin_extend_code hvalidateSub hfailExit
  have hsuccess := validate_success_tail_cps sp raVal cursor endPtr
  have hsuccess' := cpsTripleWithin_frameR P hP
    (cpsTripleWithin_frameR (regIs .x0 (0 : Word)) (by exact pcFree_regIs) hsuccess)
  have hsuccessExit := hsuccess'
  rw [← hexit] at hsuccessExit
  have hsuccessCode := cpsTripleWithin_extend_code hvalidateSub hsuccessExit
  have hpre := validate_precheck_branch_cps cursor endPtr
  have hpre0 := cpsBranchWithin_frameR
    (((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x11 endPtr) **
      (regIs .x0 (0 : Word)) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) **
      (memIs (sp + 16) endPtr) ** P))
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hP)
    hpre
  have hpre' : cpsBranchWithin 1 (validateEntry + 32) wholeCode
      (((regIs .x10 cursor) ** (regIs .x5 endPtr)) **
        ((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x11 endPtr) **
          (regIs .x0 (0 : Word)) **
          (memIs sp raVal) ** (memIs (sp + 8) cursor) **
          (memIs (sp + 16) endPtr) ** P))
      (validateEntry + 76)
      (((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x1 raVal) **
        (regIs .x5 endPtr) ** (regIs .x11 endPtr) ** (regIs .x0 (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) cursor) **
        (memIs (sp + 16) endPtr) ** P))
      (validateEntry + 36) ((regIs .x1 raVal) ** bodyP) := by
    apply cpsBranchWithin_extend_code hvalidateSub
    refine cpsBranchWithin_weaken (fun _ hp => hp)
      (fun _ hp => by xperm_pure hp)
      (fun _ hp => by xperm_pure hp) hpre0
  have hbody' := cpsTripleWithin_extend_code hbodySub hbody
  have hpreBody := cpsBranchWithin_merge_same_cr hpre'
    (cpsTripleWithin_mono_nSteps (Nat.le_max_left
      4 (1 + (1 + nShared) + nCont))
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) hfailPost hfailCode))
      (cpsTripleWithin_mono_nSteps (Nat.le_max_right
      4 (1 + (1 + nShared) + nCont)) hbody')
  have hpreBody' : cpsTripleWithin
      (1 + max 4 (1 + (1 + nShared) + nCont)) (validateEntry + 32) exit_ wholeCode
      (rlp_validate_payload_precheck_post sp raVal cursor endPtr P) R := by
    exact hpreBody
  have hpreBodyMax : cpsTripleWithin
      (max 4 (1 + max 4 (1 + (1 + nShared) + nCont)))
      (validateEntry + 32) exit_ wholeCode
      (rlp_validate_payload_precheck_post sp raVal cursor endPtr P) R :=
    cpsTripleWithin_mono_nSteps (Nat.le_max_right
      4 (1 + max 4 (1 + (1 + nShared) + nCont))) hpreBody'
  have hempty := validate_empty_branch_cps cursor endPtr
  have hempty' := cpsBranchWithin_frameR
    (((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x11 endPtr) **
      (regIs .x0 (0 : Word)) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) **
      (memIs (sp + 16) endPtr) ** P))
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hP)
    hempty
  have hemptyNoPure : cpsBranchWithin 1 (validateEntry + 28) validateCR
      (((regIs .x10 cursor) ** (regIs .x5 endPtr)) **
        ((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x11 endPtr) **
          (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
          (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr) ** P))
      (validateEntry + 60)
      (rlp_validate_payload_success_pre sp raVal cursor endPtr P)
      (validateEntry + 32)
      (rlp_validate_payload_precheck_post sp raVal cursor endPtr P) := by
    refine cpsBranchWithin_weaken (fun _ hp => hp) (fun _ hp => by
      drop_pure hp
      unfold rlp_validate_payload_success_pre
      xperm_chunked hp) (fun _ hp => by
      drop_pure hp
      unfold rlp_validate_payload_precheck_post
      xperm_chunked hp) hempty'
  have hemptyCode := cpsBranchWithin_extend_code hvalidateSub hemptyNoPure
  have hemptyAll := cpsBranchWithin_merge_same_cr hemptyCode
    (cpsTripleWithin_mono_nSteps (Nat.le_max_left
      4 (1 + max 4 (1 + (1 + nShared) + nCont)))
      (cpsTripleWithin_weaken (fun _ hp => by
        unfold rlp_validate_payload_success_pre at hp
        xperm_hyp hp) hsuccessPost hsuccessCode))
      hpreBodyMax
  have hload := validate_loads_cps sp cursor endPtr x5Old
  have hload' := cpsTripleWithin_frameR P hP
    (cpsTripleWithin_frameR
      (regIs .x1 raVal ** memIs sp raVal ** regIs .x0 (0 : Word))
      (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) hload)
  have hloadCode := cpsTripleWithin_extend_code hvalidateSub hload'
  have hpro := validate_prologue_cps sp raVal cursor endPtr
  have hpro' := cpsTripleWithin_frameR
    (regIs .x5 x5Old ** regIs .x0 (0 : Word) ** P)
    (by repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact hP) hpro
  have hproCode := cpsTripleWithin_extend_code hvalidateSub hpro'
  have h1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hloadCode hemptyAll
  have h2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hproCode h1
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => hp) h2)

/-! ## Shared-to-validator call boundary

The LIST arm reaches the validator at `S+156` with a real `JAL .x1` and
returns at `S+160`.  This theorem is the code/frame mapping for that call,
kept dependent in the same way as the nested validator call above: the
successful validator result chooses the continuation witness.  It deliberately
stops at the call boundary; the empty and failure tails, and the nonempty
mutual continuation, are separate consumers of this contract. -/

theorem validate_call_dep_hcallee
    {n : Nat} {α : Type} {P : Assertion} {post : α → Assertion}
    (oldRa : Word) (hP : P.pcFree)
    (hcallee : cpsTripleWithin n (GuestAddrs.rlp_validate_payload : Word)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      ((.x1 ↦ᵣ (RlpWalkNextStrictTie.S + 160)) ** P) (cpsDepPost post)) :
    cpsTripleWithin (1 + n) (RlpWalkNextStrictTie.S + 156)
      (RlpWalkNextStrictTie.S + 160)
      ((CodeReq.singleton (RlpWalkNextStrictTie.S + 156)
        (.JAL .x1 (jalOff GuestAddrs.rlp_validate_payload
          (GuestAddrs.rlp_walk_next_shared + 156)))).union validateCR)
      ((.x1 ↦ᵣ oldRa) ** P) (cpsDepPost post) := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := RlpWalkNextStrictTie.S + 156)
    (calleeEntry := (GuestAddrs.rlp_validate_payload : Word)) (vOld := oldRa)
    (calleeCode := validateCR) (Prest := P) (Q := cpsDepPost post)
    (jalOff GuestAddrs.rlp_validate_payload
      (GuestAddrs.rlp_walk_next_shared + 156))
    (by decide) (by decide) hP
    (CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len
        (GuestAddrs.rlp_validate_payload : Word) rlpValidatePayload_prog 23
        (RlpWalkNextStrictTie.S + 156) (by rfl) (by
        intro k hk heq
        have hS : (RlpWalkNextStrictTie.S + 156).toNat = 2147503536 := by decide
        have hV : (GuestAddrs.rlp_validate_payload : Word).toNat = 2147503588 := by decide
        have h := congrArg BitVec.toNat heq
        rw [hS] at h
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hV] at h
        omega))) hcallee
  exact hcall

/-! First list-parser edge in the shared callee: after the list-prefix class,
`BLTU x6,248` selects the short-list payload-start arm at `S+148` or the
long-list length decoder at `S+88`. -/

theorem shared_list_length_prefix_branch (pfx : Word) :
    cpsBranchWithin 1 (RlpWalkNextStrictTie.S + 84)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 pfx) ** (regIs .x7 (248 : Word)))
      (RlpWalkNextStrictTie.S + 148)
        ((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) ** pure (BitVec.ult pfx (248 : Word)))
      (RlpWalkNextStrictTie.S + 88)
        ((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) ** pure (¬ BitVec.ult pfx (248 : Word))) := by
  have h := bltu_spec_gen_within .x6 .x7 (64 : BitVec 13) pfx (248 : Word)
    (RlpWalkNextStrictTie.S + 84)
  rw [show (RlpWalkNextStrictTie.S + 84) + signExtend13 (64 : BitVec 13) =
      RlpWalkNextStrictTie.S + 148 from by
        rw [show signExtend13 (64 : BitVec 13) = (64 : Word) from by decide]
        bv_omega,
      show RlpWalkNextStrictTie.S + 84 + 4 = RlpWalkNextStrictTie.S + 88 by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 21 (RlpWalkNextStrictTie.S + 84)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))) h

theorem shared_list_depth_branch (depth : Word) :
    cpsBranchWithin 1 (RlpWalkNextStrictTie.S + 68)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x9 depth) ** (regIs .x7 (1024 : Word)))
      (RlpWalkNextStrictTie.S + 168)
        ((regIs .x9 depth) ** (regIs .x7 (1024 : Word)) ** pure (¬ BitVec.ult depth (1024 : Word)))
      (RlpWalkNextStrictTie.S + 72)
        ((regIs .x9 depth) ** (regIs .x7 (1024 : Word)) ** pure (BitVec.ult depth (1024 : Word))) := by
  have h := bgeu_spec_gen_within .x9 .x7 (100 : BitVec 13) depth (1024 : Word)
    (RlpWalkNextStrictTie.S + 68)
  rw [show (RlpWalkNextStrictTie.S + 68) + signExtend13 (100 : BitVec 13) =
      RlpWalkNextStrictTie.S + 168 from by
        rw [show signExtend13 (100 : BitVec 13) = (100 : Word) from by decide]
        bv_omega,
      show RlpWalkNextStrictTie.S + 68 + 4 = RlpWalkNextStrictTie.S + 72 by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 17 (RlpWalkNextStrictTie.S + 68)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))) h

theorem shared_list_depth_increment (depth : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 72)
      (RlpWalkNextStrictTie.S + 76) RlpWalkNextStrictTie.sharedCode
      ((regIs .x9 depth) ** (regIs .x7 (1024 : Word)))
      ((regIs .x9 (depth + 1)) ** (regIs .x7 (1024 : Word))) := by
  have h := addi_spec_gen_same_within .x9 depth (1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 72) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show RlpWalkNextStrictTie.S + 72 + 4 = RlpWalkNextStrictTie.S + 76 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 72)
      (.ADDI .x9 .x9 (1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 18 (RlpWalkNextStrictTie.S + 72)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR (regIs .x7 (1024 : Word))
    (by exact pcFree_regIs) hcode
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe

theorem shared_list_length_limit (endPtr : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 80)
      (RlpWalkNextStrictTie.S + 84) RlpWalkNextStrictTie.sharedCode
      ((regIs .x7 (1024 : Word)) ** (regIs .x11 endPtr))
      ((regIs .x7 (248 : Word)) ** (regIs .x11 endPtr)) := by
  have h := li_spec_gen_within .x7 (1024 : Word) (248 : Word)
    (RlpWalkNextStrictTie.S + 80) (by decide)
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 80)
      (.LI .x7 (248 : Word)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 20 (RlpWalkNextStrictTie.S + 80)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR (regIs .x11 endPtr)
    (by exact pcFree_regIs) hcode
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe

theorem shared_long_prefix_branch (remaining : Word) :
    cpsBranchWithin 1 (RlpWalkNextStrictTie.S + 108)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x28 remaining) ** (regIs .x0 (0 : Word)))
      (RlpWalkNextStrictTie.S + 136)
        ((regIs .x28 remaining) ** (regIs .x0 (0 : Word)) ** pure (remaining = 0))
      (RlpWalkNextStrictTie.S + 112)
        ((regIs .x28 remaining) ** (regIs .x0 (0 : Word)) ** pure (remaining ≠ 0)) := by
  have h := beq_spec_gen_within .x28 .x0 (28 : BitVec 13) remaining (0 : Word)
    (RlpWalkNextStrictTie.S + 108)
  rw [show (RlpWalkNextStrictTie.S + 108) + signExtend13 (28 : BitVec 13) =
      RlpWalkNextStrictTie.S + 136 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]
        bv_omega,
      show RlpWalkNextStrictTie.S + 108 + 4 = RlpWalkNextStrictTie.S + 112 by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 27 (RlpWalkNextStrictTie.S + 108)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))) h

theorem shared_validate_result_branch (status : Word) :
    cpsBranchWithin 1 (RlpWalkNextStrictTie.S + 164)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x10 status) ** (regIs .x0 (0 : Word)))
      (RlpWalkNextStrictTie.S + 184)
        ((regIs .x10 status) ** (regIs .x0 (0 : Word)) ** pure (status = 0))
      (RlpWalkNextStrictTie.S + 168)
        ((regIs .x10 status) ** (regIs .x0 (0 : Word)) ** pure (status ≠ 0)) := by
  have h := beq_spec_gen_within .x10 .x0 (20 : BitVec 13) status (0 : Word)
    (RlpWalkNextStrictTie.S + 164)
  rw [show (RlpWalkNextStrictTie.S + 164) + signExtend13 (20 : BitVec 13) =
      RlpWalkNextStrictTie.S + 184 from by
        rw [show signExtend13 (20 : BitVec 13) = (20 : Word) from by decide]
        bv_omega,
      show RlpWalkNextStrictTie.S + 164 + 4 = RlpWalkNextStrictTie.S + 168 by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 41 (RlpWalkNextStrictTie.S + 164)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))) h

/-! Full status integration.  The two exits are kept separate: success passes
through the six-instruction epilogue at `S+184`, while failure executes its
four setup instructions and returns from `S+196`, with the core spill values
still intact. -/
theorem shared_validate_status_dep
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen : Word)
    (r : ValidateResult) :
    cpsNBranchWithin 14 (RlpWalkNextStrictTie.S + 164)
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x10 r.status) ** (regIs .x0 (0 : Word))) **
       ((sharedValidateStatusFrame sp raVal cursor outerNext outerStatus outerLen r) **
        ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝))
      [(raVal &&& ~~~1,
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base) (floor := floor)
          (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
          endPtr sp raVal cursor outerNext outerStatus outerLen r),
       (raVal &&& ~~~1,
        sharedValidateStatusFailurePost (bytes := bytes) (base := base) (floor := floor)
          (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
          endPtr sp raVal cursor outerNext outerStatus outerLen r)] := by
  have hbr0 := shared_validate_result_branch r.status
  have hbr := cpsBranchWithin_frameR
    ((sharedValidateStatusFrame sp raVal cursor outerNext outerStatus outerLen r) **
      ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
    (by pcf_validate_cps) hbr0
  have hsucc0 := shared_validate_status_success_tail
    (bytes := bytes) (base := base) (floor := floor)
    (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
    endPtr sp raVal outerNext outerStatus outerLen r
  have hsuccCursor := cpsTripleWithin_frameR (memIs (sp + 8) cursor)
    (by pcf_validate_cps) hsucc0
  have hsucc := cpsTripleWithin_frameR (regIs .x0 (0 : Word))
    (by pcf_validate_cps) hsuccCursor
  have hsuccFacts := cpsTripleWithin_frameR (⌜r.status = 0⌝)
    (by pcf_validate_cps) hsucc
  have hfail0 := shared_validate_status_failure_tail
    sp raVal cursor outerNext outerStatus outerLen r
  have hfail := cpsTripleWithin_frameR
    (⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
    (by pcf_validate_cps) hfail0
  have hfail' : cpsTripleWithin 7 (RlpWalkNextStrictTie.S + 168)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.sharedCode
      (((regIs .x10 r.status) ** (regIs .x0 (0 : Word)) **
        ⌜r.status ≠ 0⌝) **
          (sharedValidateStatusFrame sp raVal cursor outerNext outerStatus outerLen r) **
          ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
      (sharedValidateStatusFailurePost (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen r) := by
    simp only [RlpWalkNextStrictTie.S] at hfail
    simp only [sharedValidateStatusFrame, RlpWalkNextStrictTie.S]
    simp only [sharedValidateStatusFailurePost]
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) hfail
  have hfailN := cpsTripleWithin_as_cpsNBranchWithin hfail'
  have hbranch := cpsBranchWithin_cons_cpsNBranchWithin_same_cr hbr hfailN
  have hsucc' : cpsTripleWithin 6 (RlpWalkNextStrictTie.S + 184)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.sharedCode
      (((regIs .x10 r.status) ** (regIs .x0 (0 : Word)) **
        ⌜r.status = 0⌝) **
          (sharedValidateStatusFrame sp raVal cursor outerNext outerStatus outerLen r) **
          ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
      (sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen r) := by
    simp only [RlpWalkNextStrictTie.S] at hsuccFacts
    simp only [sharedValidateStatusFrame, RlpWalkNextStrictTie.S]
    simp only [sharedValidateStatusSuccessPost]
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) hsuccFacts
  have hsuccN := cpsTripleWithin_as_cpsNBranchWithin hsucc'
  have hall := cpsNBranchWithin_extend_head_nbranch hbranch hsuccN
  exact hall


theorem shared_long_prefix_decrement (remaining cursor : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 128)
      (RlpWalkNextStrictTie.S + 132) RlpWalkNextStrictTie.sharedCode
      ((regIs .x28 remaining) ** (regIs .x29 cursor))
      ((regIs .x28 (remaining - 1)) ** (regIs .x29 cursor)) := by
  have h := addi_spec_gen_same_within .x28 remaining (-1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 128) (by decide)
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
    show remaining + (-1 : Word) = remaining - 1 by bv_omega,
    show RlpWalkNextStrictTie.S + 128 + 4 = RlpWalkNextStrictTie.S + 132 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 128)
      (.ADDI .x28 .x28 (-1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 32 (RlpWalkNextStrictTie.S + 128)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR (regIs .x29 cursor)
    (by exact pcFree_regIs) hcode
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe

theorem shared_long_prefix_cursor_increment (cursor remaining : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 124)
      (RlpWalkNextStrictTie.S + 128) RlpWalkNextStrictTie.sharedCode
      ((regIs .x29 cursor) ** (regIs .x28 remaining))
      ((regIs .x29 (cursor + 1)) ** (regIs .x28 remaining)) := by
  have h := addi_spec_gen_same_within .x29 cursor (1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 124) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show RlpWalkNextStrictTie.S + 124 + 4 = RlpWalkNextStrictTie.S + 128 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 124)
      (.ADDI .x29 .x29 (1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 31 (RlpWalkNextStrictTie.S + 124)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR (regIs .x28 remaining)
    (by exact pcFree_regIs) hcode
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe

theorem shared_long_prefix_loop_backedge (cursor remaining : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 132)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x0 (0 : Word)) ** (regIs .x29 cursor) ** (regIs .x28 remaining))
      ((regIs .x0 (0 : Word)) ** (regIs .x29 cursor) ** (regIs .x28 remaining)) := by
  have h := jal_x0_spec_gen_within (-24 : BitVec 21)
    (RlpWalkNextStrictTie.S + 132)
  rw [show (RlpWalkNextStrictTie.S + 132) +
      signExtend21 (-24 : BitVec 21) = RlpWalkNextStrictTie.S + 108 from by
        rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]
        bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 132)
      (.JAL .x0 (-24 : BitVec 21)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 33 (RlpWalkNextStrictTie.S + 132)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR
    ((regIs .x0 (0 : Word)) ** (regIs .x29 cursor) ** (regIs .x28 remaining))
    (by apply pcFree_sepConj <;> first | exact pcFree_regIs | apply pcFree_sepConj <;> exact pcFree_regIs)
    hcode
  have hframe' := cpsTripleWithin_weaken
    (fun h hp => (sepConj_emp_left h).mpr hp)
    (fun h hp => (sepConj_emp_left h).mp hp) hframe
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe'

theorem shared_long_prefix_payload_base (cursor pfx oldOut : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 136)
      (RlpWalkNextStrictTie.S + 140) RlpWalkNextStrictTie.sharedCode
      ((regIs .x12 oldOut) ** (regIs .x5 cursor) ** (regIs .x13 pfx))
      ((regIs .x12 (cursor + pfx)) ** (regIs .x5 cursor) ** (regIs .x13 pfx)) := by
  have h := add_spec_gen_within .x12 .x5 .x13 cursor pfx oldOut
    (RlpWalkNextStrictTie.S + 136) (by decide)
  rw [show RlpWalkNextStrictTie.S + 136 + 4 = RlpWalkNextStrictTie.S + 140 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 136)
      (.ADD .x12 .x5 .x13) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 34 (RlpWalkNextStrictTie.S + 136)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_payload_start (cursor pfx : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 140)
      (RlpWalkNextStrictTie.S + 144) RlpWalkNextStrictTie.sharedCode
      ((regIs .x12 (cursor + pfx)) ** (regIs .x5 cursor) ** (regIs .x13 pfx))
      ((regIs .x12 (cursor + pfx + 1)) ** (regIs .x5 cursor) ** (regIs .x13 pfx)) := by
  have h := addi_spec_gen_same_within .x12 (cursor + pfx) (1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 140) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show (cursor + pfx) + (1 : Word) = cursor + pfx + 1 by bv_omega,
    show RlpWalkNextStrictTie.S + 140 + 4 = RlpWalkNextStrictTie.S + 144 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 140)
      (.ADDI .x12 .x12 (1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 35 (RlpWalkNextStrictTie.S + 140)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR
    ((regIs .x5 cursor) ** (regIs .x13 pfx))
    (by apply pcFree_sepConj <;> exact pcFree_regIs) hcode
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe

theorem shared_long_prefix_to_validator (payload : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 144)
      (RlpWalkNextStrictTie.S + 152) RlpWalkNextStrictTie.sharedCode
      (regIs .x12 payload) (regIs .x12 payload) := by
  have h := jal_x0_spec_gen_within (8 : BitVec 21)
    (RlpWalkNextStrictTie.S + 144)
  rw [show (RlpWalkNextStrictTie.S + 144) +
      signExtend21 (8 : BitVec 21) = RlpWalkNextStrictTie.S + 152 from by
        rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
        bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 144)
      (.JAL .x0 (8 : BitVec 21)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 36 (RlpWalkNextStrictTie.S + 144)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  have hframe := cpsTripleWithin_frameR (regIs .x12 payload)
    (by exact pcFree_regIs) hcode
  have hframe' := cpsTripleWithin_weaken
    (fun h hp => (sepConj_emp_left h).mpr hp)
    (fun h hp => (sepConj_emp_left h).mp hp) hframe
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hframe'

theorem shared_long_prefix_shift (acc : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 112)
      (RlpWalkNextStrictTie.S + 116) RlpWalkNextStrictTie.sharedCode
      (regIs .x30 acc) (regIs .x30 (acc <<< 8)) := by
  have h := slli_spec_gen_same_within .x30 acc (8 : BitVec 6)
    (RlpWalkNextStrictTie.S + 112) (by decide)
  rw [show RlpWalkNextStrictTie.S + 112 + 4 = RlpWalkNextStrictTie.S + 116 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 112)
      (.SLLI .x30 .x30 (8 : BitVec 6)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 28 (RlpWalkNextStrictTie.S + 112)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_load_byte
    (cursor oldByte dwordAddr wordVal : Word)
    (halign : alignToDword cursor = dwordAddr)
    (hvalid : isValidByteAccess cursor = true) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 116)
      (RlpWalkNextStrictTie.S + 120) RlpWalkNextStrictTie.sharedCode
      ((regIs .x29 cursor) ** (regIs .x31 oldByte) ** (dwordAddr ↦ₘ wordVal))
      ((regIs .x29 cursor) **
        (regIs .x31 ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
        (dwordAddr ↦ₘ wordVal)) := by
  have h := lbu_spec_gen_within .x31 .x29 cursor oldByte
    (0 : BitVec 12) (RlpWalkNextStrictTie.S + 116)
    dwordAddr wordVal (by decide) (by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show cursor + (0 : Word) = cursor by bv_omega]
      exact halign) (by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show cursor + (0 : Word) = cursor by bv_omega]
      exact hvalid)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show cursor + (0 : Word) = cursor by bv_omega,
    show RlpWalkNextStrictTie.S + 116 + 4 = RlpWalkNextStrictTie.S + 120 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 116)
      (.LBU .x31 .x29 (0 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 29 (RlpWalkNextStrictTie.S + 116)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_accumulate_byte (acc byte : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 120)
      (RlpWalkNextStrictTie.S + 124) RlpWalkNextStrictTie.sharedCode
      ((regIs .x30 acc) ** (regIs .x31 byte))
      ((regIs .x30 (acc ||| byte)) ** (regIs .x31 byte)) := by
  have h := or_spec_gen_rd_eq_rs1_within .x30 .x31 acc byte
    (RlpWalkNextStrictTie.S + 120) (by decide)
  rw [show RlpWalkNextStrictTie.S + 120 + 4 = RlpWalkNextStrictTie.S + 124 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 120)
      (.OR .x30 .x30 .x31) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 30 (RlpWalkNextStrictTie.S + 120)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_init_acc (oldAcc : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 104)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      (regIs .x30 oldAcc) (regIs .x30 (0 : Word)) := by
  have h := li_spec_gen_within .x30 oldAcc (0 : Word)
    (RlpWalkNextStrictTie.S + 104) (by decide)
  rw [show RlpWalkNextStrictTie.S + 104 + 4 = RlpWalkNextStrictTie.S + 108 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 104)
      (.LI .x30 (0 : Word)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 26 (RlpWalkNextStrictTie.S + 104)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_list_load_end (sp endPtr oldEnd : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 76)
      (RlpWalkNextStrictTie.S + 80) RlpWalkNextStrictTie.sharedCode
      ((regIs .x2 sp) ** (regIs .x11 oldEnd) ** ((sp + 24) ↦ₘ endPtr))
      ((regIs .x2 sp) ** (regIs .x11 endPtr) ** ((sp + 24) ↦ₘ endPtr)) := by
  have h := ld_spec_gen_within .x11 .x2 sp oldEnd endPtr
    (24 : BitVec 12) (RlpWalkNextStrictTie.S + 76) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show RlpWalkNextStrictTie.S + 76 + 4 = RlpWalkNextStrictTie.S + 80 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 76)
      (.LD .x11 .x2 (24 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 19 (RlpWalkNextStrictTie.S + 76)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  exact cpsTripleWithin_extend_code hmono h

theorem shared_list_load_cursor (sp cursor oldCursor : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 48)
      (RlpWalkNextStrictTie.S + 52) RlpWalkNextStrictTie.sharedCode
      ((regIs .x2 sp) ** (regIs .x5 oldCursor) ** ((sp + 8) ↦ₘ cursor))
      ((regIs .x2 sp) ** (regIs .x5 cursor) ** ((sp + 8) ↦ₘ cursor)) := by
  have h := ld_spec_gen_within .x5 .x2 sp oldCursor cursor
    (8 : BitVec 12) (RlpWalkNextStrictTie.S + 48) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show RlpWalkNextStrictTie.S + 48 + 4 = RlpWalkNextStrictTie.S + 52 by decide] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 48)
      (.LD .x5 .x2 (8 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 12 (RlpWalkNextStrictTie.S + 48)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by decide))
  exact cpsTripleWithin_extend_code hmono h

theorem shared_list_length_prefix_load (sp cursor oldByte : Word)
    (halign : alignToDword cursor = cursor &&& ~~~(7 : Word))
    (hvalid : isValidByteAccess cursor = true) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 52)
      (RlpWalkNextStrictTie.S + 56) RlpWalkNextStrictTie.sharedCode
      ((regIs .x5 cursor) ** (regIs .x6 oldByte) **
        ((cursor &&& ~~~(7 : Word)) ↦ₘ sp))
      ((regIs .x5 cursor) **
        (regIs .x6 ((extractByte sp (byteOffset cursor)).zeroExtend 64)) **
        ((cursor &&& ~~~(7 : Word)) ↦ₘ sp)) := by
  have h := lbu_spec_gen_within .x6 .x5 cursor oldByte
    (0 : BitVec 12) (RlpWalkNextStrictTie.S + 52)
    (cursor &&& ~~~(7 : Word)) sp (by decide) (by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show cursor + (0 : Word) = cursor by bv_omega]
      exact halign) (by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show cursor + (0 : Word) = cursor by bv_omega]
      exact hvalid)
  rw [show RlpWalkNextStrictTie.S + 52 + 4 = RlpWalkNextStrictTie.S + 56 by decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show cursor + (0 : Word) = cursor by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 52)
      (.LBU .x6 .x5 (0 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 13 (RlpWalkNextStrictTie.S + 52)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by decide))
  exact cpsTripleWithin_extend_code hmono h

theorem shared_short_list_payload_start (cursor oldPayload : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 148)
      (RlpWalkNextStrictTie.S + 152) RlpWalkNextStrictTie.sharedCode
      ((regIs .x5 cursor) ** (regIs .x12 oldPayload))
      ((regIs .x5 cursor) ** (regIs .x12 (cursor + 1))) := by
  have h := addi_spec_gen_within .x12 .x5 oldPayload cursor (1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 148) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show RlpWalkNextStrictTie.S + 148 + 4 = RlpWalkNextStrictTie.S + 152 by decide] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 148)
      (.ADDI .x12 .x5 (1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 37 (RlpWalkNextStrictTie.S + 148)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by decide))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_payload_handoff (payload oldPayload : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 152)
      (RlpWalkNextStrictTie.S + 156) RlpWalkNextStrictTie.sharedCode
      ((regIs .x10 oldPayload) ** (regIs .x12 payload))
      ((regIs .x10 payload) ** (regIs .x12 payload)) := by
  have h := mv_spec_gen_within .x10 .x12 payload oldPayload
    (RlpWalkNextStrictTie.S + 152) (by decide)
  rw [show RlpWalkNextStrictTie.S + 152 + 4 = RlpWalkNextStrictTie.S + 156 by decide] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 152)
      (.MV .x10 .x12) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 38 (RlpWalkNextStrictTie.S + 152)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by decide))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_depth_decrement (depth : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 160)
      (RlpWalkNextStrictTie.S + 164) RlpWalkNextStrictTie.sharedCode
      (regIs .x9 depth) (regIs .x9 (depth - 1)) := by
  have h := addi_spec_gen_same_within .x9 depth (-1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 160) (by decide)
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
    show depth + (-1 : Word) = depth - 1 by bv_omega,
    show RlpWalkNextStrictTie.S + 160 + 4 = RlpWalkNextStrictTie.S + 164 by decide] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 160)
      (.ADDI .x9 .x9 (-1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 40 (RlpWalkNextStrictTie.S + 160)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by decide))
  exact cpsTripleWithin_extend_code hmono h

/-! ## Shared LIST arm under the validator contract

The length-prefix branch is the shared side of the mutual knot.  The two
continuation premises below are deliberately named `...UnderValidator`: each
one includes its corresponding payload-start/long-length work, the validator
call, and the status continuation (and therefore can instantiate
`rlp_validate_payload_cps_under_shared`).  This theorem supplies the missing
common branch composition without duplicating that call proof.  In
particular, the short and long arms must agree on one continuation post, while
their step bounds may differ; the larger bound is used for the CPS merge.

The remaining non-structural premise is therefore the long-length decoder
contract.  Its loop is the only part not discharged by the per-instruction
contracts above; it is where the `cycleFuel`/`ValidateFuel` knot will be
instantiated next. -/
theorem shared_list_arm_cps_under_validator
    {nShort nLong : Nat} {P R : Assertion}
    (pfx exit_ : Word) (hP : P.pcFree)
    (hshortUnderValidator :
      cpsTripleWithin nShort (RlpWalkNextStrictTie.S + 148) exit_
        RlpWalkNextStrictTie.sharedCode
        (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
            pure (BitVec.ult pfx (248 : Word))) ** P) R)
    (hlongUnderValidator :
      cpsTripleWithin nLong (RlpWalkNextStrictTie.S + 88) exit_
        RlpWalkNextStrictTie.sharedCode
        (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
            pure (¬ BitVec.ult pfx (248 : Word))) ** P) R) :
    cpsTripleWithin (1 + max nShort nLong) (RlpWalkNextStrictTie.S + 84) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word))) ** P) R := by
  have hbr0 := shared_list_length_prefix_branch pfx
  have hbr := cpsBranchWithin_frameR P hP hbr0
  have hshort := cpsTripleWithin_mono_nSteps
    (Nat.le_max_left nShort nLong) hshortUnderValidator
  have hlong := cpsTripleWithin_mono_nSteps
    (Nat.le_max_right nShort nLong) hlongUnderValidator
  exact cpsBranchWithin_merge_same_cr hbr hshort hlong

theorem shared_list_arm_contract_from_adapter
    {parentFuel childFuel : Nat} {Validator : Prop}
    {pfx exit_ : Word} {P R : Assertion}
    (hP : P.pcFree)
    (h : SharedListValidatorAdapter parentFuel childFuel Validator pfx exit_ P R) :
    ∃ nSteps, cpsTripleWithin nSteps (RlpWalkNextStrictTie.S + 84) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word))) ** P) R := by
  let hs := h.short h.validator
  let hl := h.long h.validator
  refine ⟨1 + max hs.steps hl.steps, ?_⟩
  exact shared_list_arm_cps_under_validator pfx exit_ hP hs.proof hl.proof

/-! Instantiate the record with the two arm contracts already proved in this
file.  The `Validator` parameter is intentionally left abstract here: this
constructor is an integration witness for the CPS bounds, not a claim that
the short/long setup has already been derived from a particular validator
post.  The latter dependency is exactly what the two adapter fields expose to
the eventual cycleFuel induction. -/
def shared_list_arm_adapter_from_existing
    {parentFuel childFuel : Nat} {Validator : Prop}
    {pfx exit_ : Word} {P R : Assertion}
    (hdecrease : childFuel < parentFuel) (hvalidator : Validator)
    (hshort : IndexedCpsContract parentFuel
      (RlpWalkNextStrictTie.S + 148) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
        pure (BitVec.ult pfx (248 : Word))) ** P) R)
    (hlong : IndexedCpsContract parentFuel
      (RlpWalkNextStrictTie.S + 88) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
        pure (¬ BitVec.ult pfx (248 : Word))) ** P) R) :
    SharedListValidatorAdapter parentFuel childFuel Validator pfx exit_ P R :=
  { decrease := hdecrease
    validator := hvalidator
    short := fun _ => hshort
    long := fun _ => hlong }

theorem shared_list_arm_existing_contract_instantiated
    {parentFuel childFuel : Nat} {Validator : Prop}
    {pfx exit_ : Word} {P R : Assertion}
    (hP : P.pcFree) (hdecrease : childFuel < parentFuel)
    (hvalidator : Validator)
    (hshort : IndexedCpsContract parentFuel
      (RlpWalkNextStrictTie.S + 148) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
        pure (BitVec.ult pfx (248 : Word))) ** P) R)
    (hlong : IndexedCpsContract parentFuel
      (RlpWalkNextStrictTie.S + 88) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
        pure (¬ BitVec.ult pfx (248 : Word))) ** P) R) :
    ∃ nSteps, cpsTripleWithin nSteps (RlpWalkNextStrictTie.S + 84) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word))) ** P) R := by
  exact shared_list_arm_contract_from_adapter hP
    (shared_list_arm_adapter_from_existing hdecrease hvalidator hshort hlong)


end EvmAsm.Codegen.RlpWalkNextStrictFuel
