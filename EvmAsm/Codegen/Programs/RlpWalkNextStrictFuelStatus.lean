/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelStatus

  Shared-status integration for the strict LIST knot (#12419): the S+164
  branch that merges nested-validate success/failure into the shared epilogue,
  plus the `regOwn .x12` wrapper that opens the arbitrary incoming `x12` left
  by the nested call.

  Split out of `RlpWalkNextStrictFuel.lean` because that file sat at the
  Programs hard cap (1500) after the #12419 statement corrections; the
  `_at` / `regOwn` material and the nonempty ZeroReload wiring belong here
  rather than trimming the load-bearing justifications that made those
  corrections sound.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuel
import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelContracts
import EvmAsm.Codegen.Programs.RlpWalkNextStrictTie
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-! ## Shared validate-status branch (S+164)

The two exits are kept separate: success passes through the six-instruction
epilogue at `S+184`, while failure executes its four setup instructions and
returns from `S+196`, with the core spill values still intact. -/

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

/-- Value-parameterized family member: `x12` pinned to an arbitrary `x12Old`.

The status handler RELOADS `x12` on both arms — `li x12,0` on failure (S+176)
and `ld x12,40(sp)` (= `outerLen`) on success (via `tail_block` at S+192) —
so the incoming value is dead.  The nested validate call returns `regOwn .x12`
precisely because no instruction in `rlpValidatePayload_prog` writes it: at
the aggregate success exit it holds the LAST child's `len` (nested-call
residue), which is outcome-dependent and unobservable under in-degree 1 with
SP restored (#12419).  `shared_validate_status_dep` opens the existential over
`x12Old` via `cpsNBranchWithin_of_forall_regIs_to_regOwn_perm`. -/
theorem shared_validate_status_dep_at
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen x12Old : Word)
    (r : ValidateResult) :
    cpsNBranchWithin 14 (RlpWalkNextStrictTie.S + 164)
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x10 r.status) ** (regIs .x0 (0 : Word))) **
       ((sharedValidateStatusFrameAt sp raVal cursor outerNext outerStatus
          outerLen x12Old r) **
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
    ((sharedValidateStatusFrameAt sp raVal cursor outerNext outerStatus
        outerLen x12Old r) **
      ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
    (by pcf_validate_cps) hbr0
  have hsucc0 := shared_validate_status_success_tail
    (bytes := bytes) (base := base) (floor := floor)
    (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
    endPtr sp raVal outerNext outerStatus outerLen x12Old r
  have hsuccCursor := cpsTripleWithin_frameR (memIs (sp + 8) cursor)
    (by pcf_validate_cps) hsucc0
  have hsucc := cpsTripleWithin_frameR (regIs .x0 (0 : Word))
    (by pcf_validate_cps) hsuccCursor
  have hsuccFacts := cpsTripleWithin_frameR (⌜r.status = 0⌝)
    (by pcf_validate_cps) hsucc
  have hfail0 := shared_validate_status_failure_tail
    sp raVal cursor outerNext outerStatus outerLen x12Old r
  have hfail := cpsTripleWithin_frameR
    (⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
    (by pcf_validate_cps) hfail0
  have hfail' : cpsTripleWithin 7 (RlpWalkNextStrictTie.S + 168)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.sharedCode
      (((regIs .x10 r.status) ** (regIs .x0 (0 : Word)) **
        ⌜r.status ≠ 0⌝) **
          (sharedValidateStatusFrameAt sp raVal cursor outerNext outerStatus
            outerLen x12Old r) **
          ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
      (sharedValidateStatusFailurePost (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen r) := by
    simp only [RlpWalkNextStrictTie.S] at hfail
    simp only [sharedValidateStatusFrameAt, RlpWalkNextStrictTie.S]
    simp only [sharedValidateStatusFailurePost]
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) hfail
  have hfailN := cpsTripleWithin_as_cpsNBranchWithin hfail'
  have hbranch := cpsBranchWithin_cons_cpsNBranchWithin_same_cr hbr hfailN
  have hsucc' : cpsTripleWithin 6 (RlpWalkNextStrictTie.S + 184)
      (raVal &&& ~~~1) RlpWalkNextStrictTie.sharedCode
      (((regIs .x10 r.status) ** (regIs .x0 (0 : Word)) **
        ⌜r.status = 0⌝) **
          (sharedValidateStatusFrameAt sp raVal cursor outerNext outerStatus
            outerLen x12Old r) **
          ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)
      (sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen r) := by
    simp only [RlpWalkNextStrictTie.S] at hsuccFacts
    simp only [sharedValidateStatusFrameAt, RlpWalkNextStrictTie.S]
    simp only [sharedValidateStatusSuccessPost]
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by xperm_chunked hp) hsuccFacts
  have hsuccN := cpsTripleWithin_as_cpsNBranchWithin hsucc'
  have hall := cpsNBranchWithin_extend_head_nbranch hbranch hsuccN
  exact hall

/-- `x12`-owning wrapper over `shared_validate_status_dep_at`.

The incoming `x12` value is dead: the status handler reloads it on both arms
(`li x12,0` on failure; `ld x12,40(sp)` = `outerLen` on success).  The nested
validate call therefore returns `regOwn .x12`, not a pinned value — at the
aggregate success exit it held the LAST child's `len` (nested-call residue),
which is outcome-dependent and unobservable under in-degree 1 with SP restored
(#12419; same justification chain as the `sp+8` `memOwn` correction).  Opens
the existential over `x12Old` via
`cpsNBranchWithin_of_forall_regIs_to_regOwn_perm`. -/
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
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm (r := .x12)
    (P := ((regIs .x10 r.status) ** (regIs .x0 (0 : Word))) **
      (((regIs .x11 r.cursor) **
        (regIs .x1 (RlpWalkNextStrictTie.S + 160)) ** (regIs .x2 sp) **
        (memIs sp raVal) ** (memIs (sp + 8) cursor) **
        (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
        (memIs (sp + 40) outerLen)) **
        ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝))
    ?hpre ?hfam
  · intro h hp
    simp only [sharedValidateStatusFrame] at hp
    xperm_chunked hp
  · intro x12Old
    refine cpsNBranchWithin_weaken_pre ?_
      (shared_validate_status_dep_at (bytes := bytes) (base := base) (floor := floor)
        (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
        endPtr sp raVal cursor outerNext outerStatus outerLen x12Old r)
    intro h hp
    simp only [sharedValidateStatusFrameAt]
    xperm_chunked hp

end EvmAsm.Codegen.RlpWalkNextStrictFuel
