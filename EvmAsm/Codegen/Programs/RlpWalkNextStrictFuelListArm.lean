/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelListArm

  The shared LIST arm's entry bridge and recursive continuation packaging for
  #12300 / #12457.  Split out of `RlpWalkNextStrictFuel.lean` to keep that file
  under the 1500-line Codegen/Programs cap (check-file-size.sh).
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuel

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP
/-! The list arm's entry bridge.  `prefix_branch` is a two-sided branch, but
the production tie previously consumed only its byte-string (`taken`) side in
`contOk`.  Keep the LIST side explicit here: the not-taken branch is followed
by the depth guard, depth increment, end-pointer reload, and the `248` limit
load, landing at the short/long length-prefix split at `S+84`.

The branch facts are hypotheses of this theorem rather than conclusions
smuggled in through a caller-specific precondition.  In particular, the
termination/fuel argument starts only after this fixed setup; the recursive
payload work is supplied by the continuation contracts below. -/
theorem shared_list_prefix_to_length_branch
    (pfx depth sp old11 endPtr : Word)
    (hlist : ¬ BitVec.ult pfx (192 : Word))
    (hdepth : BitVec.ult depth (rlpRecursiveDecodeDepthCap : Word)) :
    cpsTripleWithin 6 (RlpWalkNextStrictTie.S + 60)
      (RlpWalkNextStrictTie.S + 84) RlpWalkNextStrictTie.sharedCode
      ((regIs .x2 sp) ** (regIs .x6 pfx) ** (regIs .x7 (192 : Word)) **
        (regIs .x9 depth) **
        (regIs .x11 old11) ** (memIs (sp + 24) endPtr))
      ((regIs .x2 sp) ** (regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
        (regIs .x9 (depth + 1)) ** (regIs .x11 endPtr) **
        (memIs (sp + 24) endPtr)) := by
  have hprefix0 := RlpWalkNextStrictTie.prefix_branch pfx (192 : Word)
  have hprefix := cpsBranchWithin_ntakenPath hprefix0 (by
    intro _ hq
    obtain ⟨_, _, _, _, _, hpure⟩ := hq
    exact hlist ((sepConj_pure_right _).mp hpure).2)
  have hprefix' := cpsTripleWithin_weaken (fun _ hp => hp)
    sepConj_strip_pure_end2 hprefix
  have hprefixF := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x9 depth) ** (regIs .x11 old11) **
      (memIs (sp + 24) endPtr))
    (by pcf_validate_cps) hprefix'

  have hdepth0 := shared_list_depth_branch depth
  have hdepth' := cpsBranchWithin_ntakenPath hdepth0 (by
    intro _ hq
    obtain ⟨_, _, _, _, _, hpure⟩ := hq
    exact ((sepConj_pure_right _).mp hpure).2 hdepth)
  have hdepth'' := cpsTripleWithin_weaken (fun _ hp => hp)
    sepConj_strip_pure_end2 hdepth'
  have hli := li_spec_gen_within .x7 (192 : Word)
    (rlpRecursiveDecodeDepthCap : Word)
    (RlpWalkNextStrictTie.S + 64) (by decide)
  rw [show RlpWalkNextStrictTie.S + 64 + 4 =
      RlpWalkNextStrictTie.S + 68 by bv_omega] at hli
  have hliMono : ∀ a i,
      CodeReq.singleton (RlpWalkNextStrictTie.S + 64)
        (.LI .x7 (rlpRecursiveDecodeDepthCap : Word)) a = some i →
      RlpWalkNextStrictTie.sharedCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr
      RlpWalkNextStrictTie.S rlpWalkNextShared_prog 16
      (RlpWalkNextStrictTie.S + 64)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hliE := cpsTripleWithin_extend_code hliMono hli
  have hliF := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x6 pfx) ** (regIs .x9 depth) **
      (regIs .x11 old11) **
      (memIs (sp + 24) endPtr))
    (by pcf_validate_cps) hliE
  have hdepthF := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x6 pfx) ** (regIs .x11 old11) **
      (memIs (sp + 24) endPtr))
    (by pcf_validate_cps) hdepth''

  have hinc := shared_list_depth_increment depth
  have hincF := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x6 pfx) ** (regIs .x11 old11) **
      (memIs (sp + 24) endPtr))
    (by pcf_validate_cps) hinc
  have hld := ld_spec_gen_within .x11 .x2 sp old11 endPtr
    (24 : BitVec 12) (RlpWalkNextStrictTie.S + 76) (by decide)
  rw [show sp + signExtend12 (24 : BitVec 12) = sp + 24 by
        rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]] at hld
  rw [show RlpWalkNextStrictTie.S + 76 + 4 =
      RlpWalkNextStrictTie.S + 80 by bv_omega] at hld
  have hldMono : ∀ a i,
      CodeReq.singleton (RlpWalkNextStrictTie.S + 76)
        (.LD .x11 .x2 (24 : BitVec 12)) a = some i →
      RlpWalkNextStrictTie.sharedCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr
      RlpWalkNextStrictTie.S rlpWalkNextShared_prog 19
      (RlpWalkNextStrictTie.S + 76)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hldE := cpsTripleWithin_extend_code hldMono hld
  have hldF := cpsTripleWithin_frameR
    ((regIs .x6 pfx) ** (regIs .x7 (rlpRecursiveDecodeDepthCap : Word)) **
      (regIs .x9 (depth + 1)))
    (by pcf_validate_cps) hldE
  have hload := shared_list_length_limit endPtr
  have hloadF := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x6 pfx) ** (regIs .x9 (depth + 1)) **
      (memIs (sp + 24) endPtr))
    (by pcf_validate_cps) hload

  have h1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hprefixF hliF
  have h2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) h1 hdepthF
  have h3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) h2 hincF
  have h4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h3 hldF
  have h5 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h4 hloadF
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) h5)

/-! Consume the fixed LIST-entry bridge together with an arm continuation.  This
is deliberately separate from `shared_list_arm_cps_under_validator`: the
latter starts at the length-prefix branch (`S+84`), while this theorem starts
at the production prefix classifier (`S+60`).  Keeping the six fixed setup
instructions here makes the shared branch's opposite exit explicit without
pretending that the recursive validator contract has already been derived. -/
theorem shared_list_arm_from_prefix
    {nArm : Nat} {P R : Assertion}
    (pfx depth sp old11 endPtr exit_ : Word)
    (hP : P.pcFree)
    (hlist : ¬ BitVec.ult pfx (192 : Word))
    (hdepth : BitVec.ult depth (rlpRecursiveDecodeDepthCap : Word))
    (hArm : cpsTripleWithin nArm (RlpWalkNextStrictTie.S + 84) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x2 sp) ** (regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
        (regIs .x9 (depth + 1)) ** (regIs .x11 endPtr) **
        (memIs (sp + 24) endPtr)) ** P) R) :
    cpsTripleWithin (6 + nArm) (RlpWalkNextStrictTie.S + 60) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x2 sp) ** (regIs .x6 pfx) ** (regIs .x7 (192 : Word)) **
        (regIs .x9 depth) ** (regIs .x11 old11) **
        (memIs (sp + 24) endPtr)) ** P) R := by
  have hsetup := shared_list_prefix_to_length_branch
    pfx depth sp old11 endPtr hlist hdepth
  have hsetupF := cpsTripleWithin_frameR P hP hsetup
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hsetupF hArm

/-! A recursive LIST continuation packages the fixed six-instruction bridge
with a child-indexed arm contract.  `parentFuel` and `childFuel` are kept
separate from the CPS step count: the former is the caller's structural
`cycleFuel` index, while the latter is the smaller index supplied by the
validator/nested-call induction hypothesis.  The bridge itself consumes six
machine steps; it does not manufacture or cap the child's CPS bound. -/
def shared_list_recursive_continuation
    {parentFuel childFuel : Nat} {P R : Assertion}
    (pfx depth sp old11 endPtr exit_ : Word)
    (hP : P.pcFree)
    (hdecrease : childFuel < parentFuel)
    (hlist : ¬ BitVec.ult pfx (192 : Word))
    (hdepth : BitVec.ult depth (rlpRecursiveDecodeDepthCap : Word))
    (hArm : IndexedCpsContract childFuel
      (RlpWalkNextStrictTie.S + 84) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x2 sp) ** (regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
        (regIs .x9 (depth + 1)) ** (regIs .x11 endPtr) **
        (memIs (sp + 24) endPtr)) ** P) R) :
    IndexedCpsContract parentFuel
      (RlpWalkNextStrictTie.S + 60) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x2 sp) ** (regIs .x6 pfx) ** (regIs .x7 (192 : Word)) **
        (regIs .x9 depth) ** (regIs .x11 old11) **
      (memIs (sp + 24) endPtr)) ** P) R := by
  have _hdecrease := hdecrease
  have hbridge := shared_list_arm_from_prefix
    pfx depth sp old11 endPtr exit_ hP hlist hdepth hArm.proof
  exact ⟨6 + hArm.steps, hbridge⟩

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
        sharedCR
        (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
            pure (BitVec.ult pfx (248 : Word))) ** P) R)
    (hlongUnderValidator :
      cpsTripleWithin nLong (RlpWalkNextStrictTie.S + 88) exit_
        sharedCR
        (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
            pure (¬ BitVec.ult pfx (248 : Word))) ** P) R) :
    cpsTripleWithin (1 + max nShort nLong) (RlpWalkNextStrictTie.S + 84) exit_
      sharedCR
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word))) ** P) R := by
  have hbr0 := shared_list_length_prefix_branch pfx
  have hbr := cpsBranchWithin_frameR P hP hbr0
  have hshort := cpsTripleWithin_mono_nSteps
    (Nat.le_max_left nShort nLong) hshortUnderValidator
  have hlong := cpsTripleWithin_mono_nSteps
    (Nat.le_max_right nShort nLong) hlongUnderValidator
  have hbrE := cpsBranchWithin_extend_code
    (cr' := sharedCR) (fun _ _ h => CodeReq.union_hit h) hbr
  exact cpsBranchWithin_merge_same_cr hbrE hshort hlong

theorem shared_list_arm_contract_from_adapter
    {parentFuel childFuel : Nat} {Validator : Prop}
    {pfx exit_ : Word} {P R : Assertion}
    (hP : P.pcFree)
    (h : SharedListValidatorAdapter parentFuel childFuel Validator pfx exit_ P R) :
    ∃ nSteps, cpsTripleWithin nSteps (RlpWalkNextStrictTie.S + 84) exit_
      sharedCR
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
      sharedCR
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
        pure (BitVec.ult pfx (248 : Word))) ** P) R)
    (hlong : IndexedCpsContract parentFuel
      (RlpWalkNextStrictTie.S + 88) exit_
      sharedCR
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
      sharedCR
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
        pure (BitVec.ult pfx (248 : Word))) ** P) R)
    (hlong : IndexedCpsContract parentFuel
      (RlpWalkNextStrictTie.S + 88) exit_
      sharedCR
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
        pure (¬ BitVec.ult pfx (248 : Word))) ** P) R) :
    ∃ nSteps, cpsTripleWithin nSteps (RlpWalkNextStrictTie.S + 84) exit_
      sharedCR
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word))) ** P) R := by
  exact shared_list_arm_contract_from_adapter hP
    (shared_list_arm_adapter_from_existing hdecrease hvalidator hshort hlong)



end EvmAsm.Codegen.RlpWalkNextStrictFuel
