/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachineCont

  Shared LIST-arm validate-call adapters and depth+status continuation
  for #12419 (split from RlpWalkNextStrictFuelMachine for the Programs
  1500-line cap).

  The short/long validate-call arm helpers moved to
  RlpWalkNextStrictFuelMachineArms (further split for the same 1500-line
  cap); this file keeps the depth+status continuation, the Entry→knot
  composition, the post bridge, and the knot body.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachine
import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachineArms

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP


/-- Long-arm `pfx = 247` (zero length-of-length): preamble then immediate
zero-remaining exit to payload base `S+136`. -/
theorem shared_long_prefix_preamble_zero_to_payload
    (listBase old7 oldRem old13 old29 oldAcc : Word) :
    cpsTripleWithin 6 (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 136) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 (247 : Word)) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x30 oldAcc) ** (regIs .x0 (0 : Word)))
      ((regIs .x6 (247 : Word)) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (0 : Word)) ** (regIs .x13 (0 : Word)) **
        (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
        (regIs .x30 (0 : Word)) ** (regIs .x0 (0 : Word))) := by
  have hpre0 := shared_long_prefix_preamble (247 : Word) listBase old7 oldRem
    old13 old29 oldAcc
  have hpre := cpsTripleWithin_frameR (regIs .x0 (0 : Word))
    (by exact pcFree_regIs) hpre0
  -- After preamble: remaining = 247 - 247 = 0 at S+108; take zero exit.
  have hbr0 := shared_long_prefix_branch (0 : Word)
  have htaken0 := cpsBranchWithin_takenStripPure2 hbr0 (by
    intro _ hQf
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).mp h_rest).2)
  have htaken := cpsTripleWithin_frameR
    ((regIs .x6 (247 : Word)) ** (regIs .x7 (247 : Word)) **
      (regIs .x13 (0 : Word)) ** (regIs .x5 listBase) **
      (regIs .x29 (listBase + 1)) ** (regIs .x30 (0 : Word)))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    htaken0
  have hrem0 : (247 : Word) - 247 = 0 := by decide
  have hpre' : cpsTripleWithin 5 (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 (247 : Word)) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x30 oldAcc) ** (regIs .x0 (0 : Word)))
      ((regIs .x6 (247 : Word)) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (0 : Word)) ** (regIs .x13 (0 : Word)) **
        (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
        (regIs .x30 (0 : Word)) ** (regIs .x0 (0 : Word))) := by
    have hpre1 : cpsTripleWithin 5 (RlpWalkNextStrictTie.S + 88)
        (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
        ((regIs .x6 (247 : Word)) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
          (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
          (regIs .x30 oldAcc) ** (regIs .x0 (0 : Word)))
        ((regIs .x6 (247 : Word)) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 ((247 : Word) - 247)) ** (regIs .x13 ((247 : Word) - 247)) **
          (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
          (regIs .x30 (0 : Word)) ** (regIs .x0 (0 : Word))) :=
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by xperm_hyp hp) hpre
    simpa [hrem0] using hpre1
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hpre' htaken
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hseq

/-- Long-arm preamble + `n`-byte length decode to payload base. Requires
`pfx - 247 = ofNat n` so the remaining counter matches the loop fuel. -/
theorem shared_long_prefix_preamble_n_iter_to_payload
    (n : Nat) (hn : n ≤ 8)
    (pfx listBase old7 oldRem old13 old29 oldAcc oldByte
      dwordAddr wordVal : Word)
    (hrem : pfx - 247 = BitVec.ofNat 64 n)
    (hwin : ∀ i, i < n →
      alignToDword ((listBase + 1) + BitVec.ofNat 64 i) = dwordAddr ∧
      isValidByteAccess ((listBase + 1) + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (5 + (7 * n + 1)) (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 136) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x30 oldAcc) ** (regIs .x31 oldByte) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
      ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (0 : Word)) ** (regIs .x13 (BitVec.ofNat 64 n)) **
        (regIs .x5 listBase) **
        (regIs .x29 ((listBase + 1) + BitVec.ofNat 64 n)) **
        (regIs .x30 (sharedLongAcc wordVal (0 : Word) (listBase + 1) n)) **
        (regIs .x31 (sharedLongLastByte wordVal (listBase + 1) oldByte n)) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  have hpre0 := shared_long_prefix_preamble pfx listBase old7 oldRem
    old13 old29 oldAcc
  have hpre := cpsTripleWithin_frameR
    ((regIs .x31 oldByte) ** (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs)
    hpre0
  have hloop0 := shared_long_prefix_n_iter n hn (0 : Word) (listBase + 1)
    oldByte dwordAddr wordVal hwin
  have hloop := cpsTripleWithin_frameR
    ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
      (regIs .x13 (BitVec.ofNat 64 n)) ** (regIs .x5 listBase))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hloop0
  have hpre' : cpsTripleWithin 5 (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x30 oldAcc) ** (regIs .x31 oldByte) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
      ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (BitVec.ofNat 64 n)) ** (regIs .x13 (BitVec.ofNat 64 n)) **
        (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
        (regIs .x30 (0 : Word)) ** (regIs .x31 oldByte) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
    have hpre1 : cpsTripleWithin 5 (RlpWalkNextStrictTie.S + 88)
        (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
        ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
          (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
          (regIs .x30 oldAcc) ** (regIs .x31 oldByte) **
          (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
        ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 (pfx - 247)) ** (regIs .x13 (pfx - 247)) **
          (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
          (regIs .x30 (0 : Word)) ** (regIs .x31 oldByte) **
          (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) :=
      cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hp => by xperm_chunked hp) hpre
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => by
        rw [← hrem]
        exact hp) hpre1
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hpre' hloop
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => by xperm_chunked hp) hseq

/-! ## Depth + status continuation after validate return

`shared_validate_status_dep` already merges success/failure from `S+164`.
These lemmas attach the depth decrement at `S+160` and collapse the two
status exits (same PC) to a single post when both arms imply it. -/

/-- Precondition at `S+160` for depth+status: depth register plus the status
branch frame already used by `shared_validate_status_dep`. -/
def sharedAfterValidatePre
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (r : ValidateResult) : Assertion :=
  ((regIs .x9 depth) **
    (((regIs .x10 r.status) ** (regIs .x0 (0 : Word))) **
      ((sharedValidateStatusFrame sp raVal cursor outerNext outerStatus
        outerLen r) **
        ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝)))

/-- Status precondition matching `shared_validate_status_dep` (no depth). -/
private def sharedValidateStatusPre
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen : Word)
    (r : ValidateResult) : Assertion :=
  (((regIs .x10 r.status) ** (regIs .x0 (0 : Word))) **
    ((sharedValidateStatusFrame sp raVal cursor outerNext outerStatus
      outerLen r) **
      ⌜validateResultFacts bytes base floor cursorOff endOff fuel endPtr r⌝))

theorem shared_after_validate_depth_status
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (r : ValidateResult) :
    cpsNBranchWithin 15 (RlpWalkNextStrictTie.S + 160)
      RlpWalkNextStrictTie.sharedCode
      (sharedAfterValidatePre (bytes := bytes) (base := base) (floor := floor)
        (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
        endPtr sp raVal cursor outerNext outerStatus outerLen depth r)
      [(raVal &&& ~~~1,
        ((regIs .x9 (depth - 1)) **
          sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
            (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
            (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
            outerLen r)),
       (raVal &&& ~~~1,
        ((regIs .x9 (depth - 1)) **
          sharedValidateStatusFailurePost (bytes := bytes) (base := base)
            (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
            (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
            outerLen r))] := by
  let statusPre :=
    sharedValidateStatusPre (bytes := bytes) (base := base) (floor := floor)
      (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
      endPtr sp raVal cursor outerNext outerStatus outerLen r
  have hdepth :
      cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 160)
        (RlpWalkNextStrictTie.S + 164) RlpWalkNextStrictTie.sharedCode
        (sharedAfterValidatePre (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen depth r)
        ((regIs .x9 (depth - 1)) ** statusPre) := by
    simpa [sharedAfterValidatePre, sharedValidateStatusPre, statusPre] using
      (shared_validate_return_depth depth statusPre (by pcf_validate_cps))
  have hstatus0 := shared_validate_status_dep (bytes := bytes) (base := base)
    (floor := floor) (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
    endPtr sp raVal cursor outerNext outerStatus outerLen r
  -- Frame depth on the RIGHT; mid is then `statusPre ** x9`, which permutes
  -- from the depth-post `x9 ** statusPre`.
  have hstatusFr :
      cpsNBranchWithin 14 (RlpWalkNextStrictTie.S + 164)
        RlpWalkNextStrictTie.sharedCode
        (statusPre ** (regIs .x9 (depth - 1)))
        [(raVal &&& ~~~1,
          (sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
            (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
            (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
            outerLen r **
            (regIs .x9 (depth - 1)))),
         (raVal &&& ~~~1,
          (sharedValidateStatusFailurePost (bytes := bytes) (base := base)
            (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
            (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
            outerLen r **
            (regIs .x9 (depth - 1))))] := by
    simpa [sharedValidateStatusPre, statusPre] using
      (cpsNBranchWithin_frameR
        (by exact pcFree_regIs : (regIs .x9 (depth - 1)).pcFree) hstatus0)
  have hseq :=
    cpsTripleWithin_seq_cpsNBranchWithin_perm_same_cr
      (fun _ hp => by xperm_chunked hp) hdepth hstatusFr
  refine cpsNBranchWithin_weaken_posts hseq ?_
  intro ex hmem
  cases hmem with
  | head =>
    refine ⟨_, List.Mem.head _, rfl, fun _ hp => by xperm_chunked hp⟩
  | tail _ htail =>
    cases htail with
    | head =>
      refine ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, fun _ hp => by
        xperm_chunked hp⟩
    | tail _ hnil =>
      exact nomatch hnil

/-- Collapse depth+status to a single exit post `R` when both arms imply it. -/
theorem shared_after_validate_cont
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    {R : Assertion}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (r : ValidateResult)
    (hsucc : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hfail : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp) :
    cpsTripleWithin 15 (RlpWalkNextStrictTie.S + 160) (raVal &&& ~~~1)
      RlpWalkNextStrictTie.sharedCode
      (sharedAfterValidatePre (bytes := bytes) (base := base) (floor := floor)
        (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
        endPtr sp raVal cursor outerNext outerStatus outerLen depth r)
      R := by
  have hbr :=
    shared_after_validate_depth_status (bytes := bytes) (base := base)
      (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
      (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
      depth r
  intro Frame hFrame s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, ex, hmem, hpc', hQR⟩ :=
    hbr Frame hFrame s hcr hPR hpc
  cases hmem with
  | head =>
    -- `ex = (raVal &&& ~~~1, successPost)`; `hpc'` already targets the exit.
    exact ⟨k, hk, s', hstep, hpc', by
      obtain ⟨hw, hc, hq, hf, hd, hu, hQ, hF⟩ := hQR
      exact ⟨hw, hc, hq, hf, hd, hu, hsucc _ hQ, hF⟩⟩
  | tail _ htail =>
    cases htail with
    | head =>
      exact ⟨k, hk, s', hstep, hpc', by
        obtain ⟨hw, hc, hq, hf, hd, hu, hQ, hF⟩ := hQR
        exact ⟨hw, hc, hq, hf, hd, hu, hfail _ hQ, hF⟩⟩
    | tail _ hnil =>
      exact nomatch hnil

/-- `hcont` witness for `*_validate_then_cont`: every validate result continues
through depth+status to `raVal &&& ~~~1` with post `R`, once both status arms
imply `R`.  Extended onto `sharedCode ∪ validateCR`. -/
theorem shared_after_validate_cont_family
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    {R : Assertion}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (hsucc : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hfail : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp) :
    ∀ r, cpsTripleWithin 15 (RlpWalkNextStrictTie.S + 160) (raVal &&& ~~~1)
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      (sharedAfterValidatePre (bytes := bytes) (base := base) (floor := floor)
        (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
        endPtr sp raVal cursor outerNext outerStatus outerLen depth r)
      R := fun r =>
  cpsTripleWithin_extend_code
    (fun _ _ h => CodeReq.union_hit h)
    (shared_after_validate_cont (bytes := bytes) (base := base)
      (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
      (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
      depth r (hsucc r) (hfail r))

/-- Caller ambient preserved across the validate call and combined with
`validateResultPost` to recover `sharedAfterValidatePre`. -/
def sharedValidateCallerAmbient
    (sp raVal cursor outerNext outerStatus outerLen depth : Word) : Assertion :=
  ((regIs .x9 depth) ** (regIs .x0 (0 : Word)) **
    (regIs .x1 (RlpWalkNextStrictTie.S + 160)) ** (regIs .x2 sp) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
    (memIs (sp + 40) outerLen))

/-- Shared cells that may sit in validate's ambient `P` at call entry: depth and
outer spills, excluding `x0`/`x1`/`x2` which the validate ABI owns.  Using this
(instead of full `sharedValidateCallerAmbient`) in `*_validate_then_status`'s
`hval` avoids a separating double-claim on `x1`. -/
def sharedValidateCallerRest
    (sp raVal cursor outerNext outerStatus outerLen depth : Word) : Assertion :=
  ((regIs .x9 depth) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
    (memIs (sp + 40) outerLen))

theorem sharedValidateCallerAmbient_of_rest
    (sp raVal cursor outerNext outerStatus outerLen depth : Word) :
    ∀ hp,
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) ** (regIs .x2 sp) **
        (regIs .x0 (0 : Word)) **
        sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth) hp →
      sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
        outerLen depth hp := by
  intro hp h
  simp only [sharedValidateCallerAmbient, sharedValidateCallerRest] at h ⊢
  xperm_chunked h

/-- Validate scratch after return: values forgotten, ownership retained. -/
def validateCallerSlack (sp_v : Word) : Assertion :=
  ((memOwn sp_v) ** (memOwn (sp_v + 8)) ** (memOwn (sp_v + 16)))

/-! The live shared LIST call pins `x5`/`x12` before entering Validate:
`x5 = listBase` and `x12 = listBase + 1`.  The generic cycle precondition
deliberately owns those registers without pinning their values, because the
validator's nested Shared call is allowed to clobber them.  At this seam we
therefore replace (rather than frame on top of) the two `regOwn` atoms with
the caller's concrete `regIs` values.  The frame cells stay `memOwn`: the
Validate prologue and its sibling loop write all three cells. -/
def validateCyclePrePinned
    (bytes : List (BitVec 8)) (base : Word) (fuel cursorOff endOff : Nat)
    (sp raVal x5Val x12Val : Word) (P : Assertion) : Assertion :=
  (((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
      (regIs .x0 (0 : Word)) **
      (regIs .x10 (base + BitVec.ofNat 64 cursorOff)) **
      (regIs .x11 (base + BitVec.ofNat 64 endOff)) **
      (regIs .x5 x5Val) ** (regIs .x12 x12Val) **
      memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
      bytesRegion base bytes ** ⌜ValidateFuel bytes fuel cursorOff endOff⌝) ** P)

theorem validateMachineContract_proof_pinned
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursorOff endOff : Nat}
    {sp raVal exit_ : Word} {wholeCode : CodeReq} {P : Assertion}
    (C : ValidateMachineContract bytes base floor fuel cursorOff endOff
      sp raVal exit_ wholeCode P) (x5Val x12Val : Word) :
    cpsTripleWithin C.steps validateEntry exit_ wholeCode
      (validateCyclePrePinned bytes base fuel cursorOff endOff
        sp raVal x5Val x12Val P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  refine cpsTripleWithin_weaken ?_ (fun _ h => h) C.proof
  intro hp h
  let pinnedBody : Assertion :=
    ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
      (regIs .x0 (0 : Word)) **
      (regIs .x10 (base + BitVec.ofNat 64 cursorOff)) **
      (regIs .x11 (base + BitVec.ofNat 64 endOff)) **
      (regIs .x5 x5Val) ** (regIs .x12 x12Val) **
      memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
      bytesRegion base bytes ** ⌜ValidateFuel bytes fuel cursorOff endOff⌝)
  let ownedBody : Assertion :=
    ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
      (regIs .x0 (0 : Word)) **
      (regIs .x10 (base + BitVec.ofNat 64 cursorOff)) **
      (regIs .x11 (base + BitVec.ofNat 64 endOff)) **
      regOwn .x5 ** regOwn .x12 **
      memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
      bytesRegion base bytes ** ⌜ValidateFuel bytes fuel cursorOff endOff⌝)
  change (pinnedBody ** P) hp at h
  change (ownedBody ** P) hp
  -- The pinned registers are consumed once, then forgotten to ownership for
  -- the generic machine contract; no duplicate register atom is introduced.
  have hbody : ∀ h, pinnedBody h → ownedBody h := by
    intro h hp
    simp only [pinnedBody, ownedBody] at hp ⊢
    exact sepConj_mono (fun _ h => h)
      (sepConj_mono (fun _ h => h)
        (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => h)
            (sepConj_mono (fun _ h => h)
              (sepConj_mono (regIs_implies_regOwn .x5)
                (sepConj_mono (regIs_implies_regOwn .x12)
                  (fun _ h => h))))))) h hp
  exact sepConj_mono hbody (fun _ h => h) hp h

theorem sharedAfterValidatePre_of_validate_return
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (r : ValidateResult) :
    ∀ hp,
      (sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
        outerLen depth **
        validateResultPost bytes base floor cursorOff endOff fuel endPtr r) hp →
      sharedAfterValidatePre (bytes := bytes) (base := base) (floor := floor)
        (cursorOff := cursorOff) (endOff := endOff) (fuel := fuel)
        endPtr sp raVal cursor outerNext outerStatus outerLen depth r hp := by
  intro hp h
  -- Unfold both sides; `sharedValidateStatusFrame` is the caller ambient
  -- with `x11`/`x12` taken from the validate result.
  simp only [sharedAfterValidatePre,
    sharedValidateCallerAmbient, sharedValidateStatusFrame,
    validateResultPost] at h ⊢
  xperm_chunked h

/-- `hcont` when the validate callee returns `validateResultPost` framed by
the caller ambient: weaken to `sharedAfterValidatePre`, then run
depth+status. -/
theorem shared_after_validate_cont_from_result
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    {R : Assertion}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (r : ValidateResult)
    (hsucc : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hfail : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp) :
    cpsTripleWithin 15 (RlpWalkNextStrictTie.S + 160) (raVal &&& ~~~1)
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      (sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
        outerLen depth **
        validateResultPost bytes base floor cursorOff endOff fuel endPtr r)
      R :=
  cpsTripleWithin_weaken
    (sharedAfterValidatePre_of_validate_return (bytes := bytes) (base := base)
      (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
      (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
      depth r)
    (fun _ hp => hp)
    (cpsTripleWithin_extend_code
      (fun _ _ h => CodeReq.union_hit h)
      (shared_after_validate_cont (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
        depth r hsucc hfail))

/-- Same continuation with validate scratch `memOwn` framed through (precise SL
keeps those cells after `validateCyclePost_to_callerAmbient`). -/
theorem shared_after_validate_cont_from_result_frame_slack
    {bytes : List (BitVec 8)} {base : Word} {floor cursorOff endOff fuel : Nat}
    {R : Assertion}
    (endPtr sp raVal cursor outerNext outerStatus outerLen depth sp_v : Word)
    (r : ValidateResult)
    (hsucc : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp)
    (hfail : ∀ hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus
          outerLen r) hp →
      R hp) :
    cpsTripleWithin 15 (RlpWalkNextStrictTie.S + 160) (raVal &&& ~~~1)
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      (sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
        outerLen depth **
        validateResultPost bytes base floor cursorOff endOff fuel endPtr r **
        validateCallerSlack sp_v)
      (R ** validateCallerSlack sp_v) := by
  have hslack : (validateCallerSlack sp_v).pcFree := by
    simp only [validateCallerSlack]
    pcf_validate_cps
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hp => hp)
    (cpsTripleWithin_frameR (validateCallerSlack sp_v) hslack
      (shared_after_validate_cont_from_result (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := fuel) endPtr sp raVal cursor outerNext outerStatus outerLen
        depth r hsucc hfail))

/-- `validateCyclePost` is the dependent-post packaging of the validate
return frame + preserved pre resources + `validateResultPost`. -/
theorem validateCyclePost_eq_cpsDepPost
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal : Word) (P : Assertion) :
    validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P =
      cpsDepPost (fun r =>
        ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
          (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
          memOwn (sp + 8) **
          (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
          regOwn .x5 **
          bytesRegion base bytes **
          ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
          (validateResultPost bytes base floor cursorOff endOff fuel
            (base + BitVec.ofNat 64 endOff) r) ** P)) := rfl

/-! ## Entry → knot composition

`validate_entry_to_knot_cps` lands at `V+36` with the post-prologue frame
(`x2 = sp`, spills filled).  `ValidateMachineContract.proof` is packaged against
`validateCyclePre` (entry-shaped `x2 = sp+32`) at that same PC — that packaging
does not match the machine mid-state.  The bind below is the honest interface:
sequence entry→knot with a knot body whose precondition is the real
post-prologue frame. -/

/-- Nonempty, well-ordered payload: prologue through precheck not-taken,
landing at the knot entry `V+36` with the post-prologue frame. -/
theorem validate_entry_to_knot_cps
    (sp raVal cursor endPtr x5Old : Word)
    (hne : cursor ≠ endPtr) (horder : endPtr.ult cursor ≠ true) :
    cpsTripleWithin 9 validateEntry (validateEntry + 36) validateCR
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16))
      ((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
        (memIs sp raVal) ** (memIs (sp + 8) cursor) **
        (memIs (sp + 16) endPtr)) := by
  have hpro := validate_prologue_cps sp raVal cursor endPtr
  have hpro' := cpsTripleWithin_frameR (regIs .x5 x5Old) (by pcf_validate_cps) hpro
  have hload := validate_loads_cps sp cursor endPtr x5Old endPtr
  have hload' := cpsTripleWithin_frameR
    ((regIs .x1 raVal) ** (memIs sp raVal)) (by pcf_validate_cps) hload
  have hempty := validate_empty_branch_cps cursor endPtr
  have hntakenEmpty0 := cpsBranchWithin_ntakenStripPure2 hempty (by
    intro _ hQt
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
    exact absurd ((sepConj_pure_right _).mp h_rest).2 hne)
  have hntakenEmpty := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x11 endPtr) ** (regIs .x1 raVal) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
    (by pcf_validate_cps) hntakenEmpty0
  have hpre := validate_precheck_branch_cps cursor endPtr
  have hntakenPre0 := cpsBranchWithin_ntakenStripPure2 hpre (by
    intro _ hQt
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
    exact absurd ((sepConj_pure_right _).mp h_rest).2 horder)
  have hntakenPre := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x11 endPtr) ** (regIs .x1 raVal) **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr))
    (by pcf_validate_cps) hntakenPre0
  have s1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hpro' hload'
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s1 hntakenEmpty
  have s3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s2 hntakenPre
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) s3)

/-- Post-prologue / knot-entry frame produced by `validate_entry_to_knot_cps`. -/
def validateKnotFrame
    (sp raVal cursor endPtr : Word) : Assertion :=
  ((regIs .x2 sp) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
    (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 16) endPtr))

theorem validate_entry_then_knot_dep
    {α : Type} {nKnot : Nat} {P : Assertion} {post : α → Assertion}
    (sp raVal cursor endPtr x5Old exit_ : Word)
    (hne : cursor ≠ endPtr) (horder : endPtr.ult cursor ≠ true)
    (hP : P.pcFree)
    (hknot : cpsTripleWithin nKnot (validateEntry + 36) exit_ validateCR
      (validateKnotFrame sp raVal cursor endPtr ** P) (cpsDepPost post)) :
    cpsTripleWithin (9 + nKnot) validateEntry exit_ validateCR
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P)
      (cpsDepPost post) := by
  have hentry0 := validate_entry_to_knot_cps sp raVal cursor endPtr x5Old
    hne horder
  have hentry := cpsTripleWithin_frameR P hP hentry0
  have hentry' : cpsTripleWithin 9 validateEntry (validateEntry + 36) validateCR
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P)
      (validateKnotFrame sp raVal cursor endPtr ** P) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by
        simp only [validateKnotFrame]
        xperm_chunked hp) hentry
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hentry' hknot

/-- Same bind with `wholeCode` extending `validateCR` (MachineContract code). -/
theorem validate_entry_then_knot_dep_extend
    {α : Type} {nKnot : Nat} {P : Assertion} {post : α → Assertion}
    {wholeCode : CodeReq}
    (sp raVal cursor endPtr x5Old exit_ : Word)
    (hne : cursor ≠ endPtr) (horder : endPtr.ult cursor ≠ true)
    (hP : P.pcFree)
    (hvalidateSub : ∀ a i, validateCR a = some i → wholeCode a = some i)
    (hknot : cpsTripleWithin nKnot (validateEntry + 36) exit_ wholeCode
      (validateKnotFrame sp raVal cursor endPtr ** P) (cpsDepPost post)) :
    cpsTripleWithin (9 + nKnot) validateEntry exit_ wholeCode
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P)
      (cpsDepPost post) := by
  have hentry0 := validate_entry_to_knot_cps sp raVal cursor endPtr x5Old
    hne horder
  have hentryU := cpsTripleWithin_extend_code hvalidateSub hentry0
  have hentry := cpsTripleWithin_frameR P hP hentryU
  have hentry' : cpsTripleWithin 9 validateEntry (validateEntry + 36) wholeCode
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P)
      (validateKnotFrame sp raVal cursor endPtr ** P) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by
        simp only [validateKnotFrame]
        xperm_chunked hp) hentry
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hentry' hknot

/-- Lift a knot body stated with `validateCyclePost` into the dependent-post
bind (definitional via `validateCyclePost_eq_cpsDepPost`). -/
theorem validate_entry_then_knot_cycle_post
    {nKnot : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {wholeCode : CodeReq}
    (sp raVal cursor endPtr x5Old exit_ : Word)
    (hne : cursor ≠ endPtr) (horder : endPtr.ult cursor ≠ true)
    (hP : P.pcFree)
    (hvalidateSub : ∀ a i, validateCR a = some i → wholeCode a = some i)
    (hknot : cpsTripleWithin nKnot (validateEntry + 36) exit_ wholeCode
      (validateKnotFrame sp raVal cursor endPtr ** P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)) :
    cpsTripleWithin (9 + nKnot) validateEntry exit_ wholeCode
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) ** P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  simpa [validateCyclePost_eq_cpsDepPost] using
    (validate_entry_then_knot_dep_extend (α := ValidateResult)
      (post := fun r =>
        ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
          (regIs .x0 (0 : Word)) ** (memIs sp raVal) **
          memOwn (sp + 8) **
          (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
          regOwn .x5 **
          bytesRegion base bytes **
          ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
          (validateResultPost bytes base floor cursorOff endOff fuel
            (base + BitVec.ofNat 64 endOff) r) ** P))
      sp raVal cursor endPtr x5Old exit_ hne horder hP hvalidateSub
      (by simpa [validateCyclePost_eq_cpsDepPost] using hknot))

/-- Shared-frame cells preserved across validate but not part of validate's
own 32-byte frame (`sp_v = sp_shared - 32`).  Depth + zero + outer spills. -/
def sharedValidateCallerExtras
    (sp outerNext outerStatus outerLen depth : Word) : Assertion :=
  ((regIs .x9 depth) ** (regIs .x0 (0 : Word)) **
    (memIs (sp + 24) outerNext) ** (memIs (sp + 32) outerStatus) **
    (memIs (sp + 40) outerLen))

theorem sharedValidateCallerAmbient_of_extras
    (sp raVal cursor outerNext outerStatus outerLen depth : Word) :
    ∀ hp,
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) ** (regIs .x2 sp) **
        (memIs sp raVal) ** (memIs (sp + 8) cursor) **
        sharedValidateCallerExtras sp outerNext outerStatus outerLen depth) hp →
      sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
        outerLen depth hp := by
  intro hp h
  simp only [sharedValidateCallerAmbient, sharedValidateCallerExtras] at h ⊢
  xperm_chunked h

/-- Frame shared extras through `validate_entry_then_knot_dep` (validateCR). -/
theorem validate_entry_then_knot_dep_frame_extras
    {α : Type} {nKnot : Nat} {P : Assertion} {post : α → Assertion}
    (sp raVal cursor endPtr x5Old exit_ outerNext outerStatus outerLen
      depth : Word)
    (hne : cursor ≠ endPtr) (horder : endPtr.ult cursor ≠ true)
    (hP : P.pcFree)
    (hknot : cpsTripleWithin nKnot (validateEntry + 36) exit_ validateCR
      (validateKnotFrame sp raVal cursor endPtr **
        sharedValidateCallerExtras sp outerNext outerStatus outerLen depth **
        P)
      (cpsDepPost post)) :
    cpsTripleWithin (9 + nKnot) validateEntry exit_ validateCR
      ((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) ** (regIs .x10 cursor) **
        (regIs .x11 endPtr) ** (regIs .x5 x5Old) **
        memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
        sharedValidateCallerExtras sp outerNext outerStatus outerLen depth **
        P)
      (cpsDepPost post) := by
  have hextras :
      (sharedValidateCallerExtras sp outerNext outerStatus outerLen depth).pcFree := by
    simp only [sharedValidateCallerExtras]
    pcf_validate_cps
  have hP' : (sharedValidateCallerExtras sp outerNext outerStatus outerLen depth **
      P).pcFree := pcFree_sepConj hextras hP
  have hknot' :
      cpsTripleWithin nKnot (validateEntry + 36) exit_ validateCR
        (validateKnotFrame sp raVal cursor endPtr **
          (sharedValidateCallerExtras sp outerNext outerStatus outerLen depth **
            P))
        (cpsDepPost post) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => hp) hknot
  exact validate_entry_then_knot_dep sp raVal cursor endPtr x5Old exit_
    hne horder hP' hknot'

/-- From `validateCyclePre` at `validateEntry` through prologue/precheck to
`validateKnotFrame` at `V+36`, preserving the ambient fuel/bytes/`P` frame. -/
theorem validate_cycle_pre_to_knot
    {bytes : List (BitVec 8)} {base : Word} {fuel cursorOff endOff : Nat}
    {P : Assertion}
    (sp raVal : Word)
    (hne : (base + BitVec.ofNat 64 cursorOff) ≠
      (base + BitVec.ofNat 64 endOff))
    (horder : (base + BitVec.ofNat 64 endOff).ult
      (base + BitVec.ofNat 64 cursorOff) ≠ true)
    (hP : P.pcFree) :
    cpsTripleWithin 9 validateEntry (validateEntry + 36) validateCR
      (validateCyclePre bytes base fuel cursorOff endOff sp raVal P)
      (validateKnotFrame sp raVal
        (base + BitVec.ofNat 64 cursorOff)
        (base + BitVec.ofNat 64 endOff) **
        (regIs .x0 (0 : Word)) ** regOwn .x12 **
        bytesRegion base bytes **
        ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P) := by
  let cursor := base + BitVec.ofNat 64 cursorOff
  let endPtr := base + BitVec.ofNat 64 endOff
  let ambient : Assertion :=
    ((regIs .x0 (0 : Word)) ** regOwn .x12 ** bytesRegion base bytes **
      ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
  have hambientPc : ambient.pcFree := by
    simp only [ambient]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_pure
      | exact hP
      | exact bytesRegion_pcFree _ _
  have hforall : ∀ x5Old,
      cpsTripleWithin 9 validateEntry (validateEntry + 36) validateCR
        ((((regIs .x2 (sp + 32)) ** (regIs .x1 raVal) **
          (regIs .x10 cursor) ** (regIs .x11 endPtr) **
          memOwn sp ** memOwn (sp + 8) ** memOwn (sp + 16) **
          ambient) ** (regIs .x5 x5Old)))
        (validateKnotFrame sp raVal cursor endPtr ** ambient) := by
    intro x5Old
    have hentry0 := validate_entry_to_knot_cps sp raVal cursor endPtr x5Old
      hne horder
    have hentry := cpsTripleWithin_frameR ambient hambientPc hentry0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hp => by
        simp only [validateKnotFrame, ambient, cursor, endPtr]
        xperm_chunked hp) hentry
  have hown :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) hforall
  have hpre : cpsTripleWithin 9 validateEntry (validateEntry + 36) validateCR
      (validateCyclePre bytes base fuel cursorOff endOff sp raVal P)
      (validateKnotFrame sp raVal cursor endPtr ** ambient) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [validateCyclePre, ambient, cursor, endPtr] at hp ⊢
        xperm_chunked hp)
      (fun _ hp => hp) hown
  simpa [ambient, cursor, endPtr] using hpre

/-- Package an entry-level `ValidateMachineContract.proof` from a knot body
on `validateKnotFrame` (the honest `V+36` mid-state). -/
theorem validate_machine_proof_of_knot
    {nKnot : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {wholeCode : CodeReq}
    (sp raVal exit_ : Word)
    (hne : (base + BitVec.ofNat 64 cursorOff) ≠
      (base + BitVec.ofNat 64 endOff))
    (horder : (base + BitVec.ofNat 64 endOff).ult
      (base + BitVec.ofNat 64 cursorOff) ≠ true)
    (hP : P.pcFree)
    (hvalidateSub : ∀ a i, validateCR a = some i → wholeCode a = some i)
    (hknot : cpsTripleWithin nKnot (validateEntry + 36) exit_ wholeCode
      (validateKnotFrame sp raVal
        (base + BitVec.ofNat 64 cursorOff)
        (base + BitVec.ofNat 64 endOff) **
        (regIs .x0 (0 : Word)) ** regOwn .x12 **
        bytesRegion base bytes **
        ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)) :
    ∃ steps, cpsTripleWithin steps validateEntry exit_ wholeCode
      (validateCyclePre bytes base fuel cursorOff endOff sp raVal P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  let cursor := base + BitVec.ofNat 64 cursorOff
  let endPtr := base + BitVec.ofNat 64 endOff
  have htoKnot0 := validate_cycle_pre_to_knot (bytes := bytes) (base := base)
    (fuel := fuel) (cursorOff := cursorOff) (endOff := endOff) (P := P)
    sp raVal hne horder hP
  have htoKnot := cpsTripleWithin_extend_code hvalidateSub htoKnot0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) htoKnot hknot
  exact ⟨9 + nKnot, hseq⟩

/-- Discharge `ValidateFromSharedGoal` by packaging: nested alias from the
Shared family, plus a supplied entry-level CPS proof. -/
theorem validateFromSharedGoal_discharge
    (bytes : List (BitVec 8)) (base : Word) (floor fuel : Nat)
    (cursorOff endOff : Nat) (sp raVal exit_ : Word)
    (wholeCode : CodeReq) (P : Assertion) :
    ValidateFromSharedGoal bytes base floor fuel cursorOff endOff
      sp raVal exit_ wholeCode P := by
  intro hexit hP hvalidateSub hbase_aligned hcursor hwindow hover hnowrap
    hvalid hitem hK hsharedFam hproof
  have hdisjShared :
      (CodeReq.singleton (rlpWalkNextNestedOfflineAddr : Word)
        (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
          (rlpWalkNextNestedOfflineAddr + 0)))).Disjoint
        RlpWalkNextStrictTie.sharedCode :=
    CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len
        RlpWalkNextStrictTie.S rlpWalkNextShared_prog 52
        (rlpWalkNextNestedOfflineAddr : Word)
        RlpWalkNextStrictTie.shared_length
        (by
          intro k hk heq
          have hS : RlpWalkNextStrictTie.S.toNat =
              GuestAddrs.rlp_walk_next_shared := by decide
          have hN : (rlpWalkNextNestedOfflineAddr : Word).toNat =
              GuestAddrs.rlp_walk_next_shared - 4 := by decide
          simp only [GuestAddrs.rlp_walk_next_shared] at hS
          have h := congrArg BitVec.toNat heq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h
          rw [hS, hN] at h
          norm_num [rlpWalkNextNestedOfflineAddr,
            GuestAddrs.rlp_walk_next_shared] at h
          omega))
  have hdisjValidate :
      (CodeReq.singleton (rlpWalkNextNestedOfflineAddr : Word)
        (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
          (rlpWalkNextNestedOfflineAddr + 0)))).Disjoint validateCR :=
    CodeReq.Disjoint.singleton_ofProg
      (by decide)
  have hdisj :
      (CodeReq.singleton (rlpWalkNextNestedOfflineAddr : Word)
        (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
          (rlpWalkNextNestedOfflineAddr + 0)))).Disjoint sharedCR :=
    CodeReq.Disjoint.union_right hdisjShared hdisjValidate
  have hnested : ∀ k, k < fuel →
      Nonempty (IndexedCpsContract k
        (rlpWalkNextNestedOfflineAddr : Word) (validateEntry + 40)
        nestedMachineCode
        ((regIs .x1 (validateEntry + 40)) ** P)
        (cpsDepPost (validateResultDependentPost bytes base floor
          cursorOff endOff fuel))) := by
    intro k hk
    obtain ⟨hshared⟩ := hsharedFam k hk
    simpa [nestedMachineCode] using
      (validate_nested_alias_indexed (fuel := k) hP hdisj hshared)
  exact validate_machine_contract_statement
    hbase_aligned hcursor hwindow hover hnowrap hvalid hexit hP
    hvalidateSub hsharedFam hnested hitem hK hproof

/-! ## Validate entry proof → call-site `hval` (post bridge)

`validateCyclePost` → caller ambient + result + `validateCallerSlack` +
`validatePreservedResources`.  Call-site *pre* → `validateCyclePre` still
open under `SharedListArmsFromValidateGoal`. -/

theorem validateCyclePost_to_callerAmbient
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp_v sp raVal cursor outerNext outerStatus outerLen depth : Word)
    (hsp : sp = sp_v + 32)
    (hra : raVal = RlpWalkNextStrictTie.S + 160) :
    ∀ hp,
      validateCyclePost bytes base floor fuel cursorOff endOff sp_v raVal
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth) hp →
      (cpsDepPost (fun r =>
        sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
          outerLen depth **
          validateResultPost bytes base floor cursorOff endOff fuel
            (base + BitVec.ofNat 64 endOff) r **
          validateCallerSlack sp_v **
          validatePreservedResources bytes base fuel cursorOff endOff)) hp := by
  intro hp h
  subst hsp hra
  simp only [validateCyclePost, cpsDepPost, sharedValidateCallerAmbient,
    sharedValidateCallerRest, validateCallerSlack, validatePreservedResources] at h ⊢
  rcases h with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  -- Group as (ambient shape) ** result ** memIs-slack ** preserved, then memIs→memOwn.
  have e8 : sp_v + 32 + 8 = sp_v + 40 := by bv_omega
  have e24 : sp_v + 32 + 24 = sp_v + 56 := by bv_omega
  have e32 : sp_v + 32 + 32 = sp_v + 64 := by bv_omega
  have e40 : sp_v + 32 + 40 = sp_v + 72 := by bv_omega
  let ambient' : Assertion :=
    ((regIs .x9 depth) ** (regIs .x0 (0 : Word)) **
      (regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
      (regIs .x2 (sp_v + 32)) **
      (memIs (sp_v + 32) (RlpWalkNextStrictTie.S + 160)) **
      (memIs (sp_v + 40) cursor) **
      (memIs (sp_v + 56) outerNext) **
      (memIs (sp_v + 64) outerStatus) **
      (memIs (sp_v + 72) outerLen))
  let slackIs : Assertion :=
    ((memIs sp_v (RlpWalkNextStrictTie.S + 160)) **
      memOwn (sp_v + 8) **
      (memIs (sp_v + 16) (base + BitVec.ofNat 64 endOff)))
  let result' : Assertion :=
    validateResultPost bytes base floor cursorOff endOff fuel
      (base + BitVec.ofNat 64 endOff) r
  let preserved : Assertion :=
    validatePreservedResources bytes base fuel cursorOff endOff
  have hr1 : (ambient' ** result' ** slackIs ** preserved) hp := by
    have hr' := hr
    simp only [e8, e24, e32, e40, ambient', result', slackIs, preserved,
      validatePreservedResources] at hr' ⊢
    xperm_chunked hr'
  rw [e8, e24, e32, e40]
  -- `**` is right-assoc: ambient' ** (result' ** (slackIs ** preserved)).
  have hr2 : (ambient' ** result' ** validateCallerSlack sp_v ** preserved) hp := by
    have hslack :
        ∀ hq, slackIs hq → validateCallerSlack sp_v hq :=
      sepConj_mono memIs_implies_memOwn
        (sepConj_mono (fun _ h => h) memIs_implies_memOwn)
    have hinner :
        ∀ hq, (slackIs ** preserved) hq →
          (validateCallerSlack sp_v ** preserved) hq :=
      sepConj_mono_left hslack
    have hmid :
        ∀ hq, (result' ** slackIs ** preserved) hq →
          (result' ** validateCallerSlack sp_v ** preserved) hq :=
      sepConj_mono_right hinner
    exact sepConj_mono_right hmid hp
      (by simpa [slackIs, validateCallerSlack] using hr1)
  simpa [ambient', result', preserved, validatePreservedResources,
    validateCallerSlack] using hr2

/-- Post-only packaging: same cyclePre, ambient-shaped post (+ validate slack
+ preserved bytes/fuel/`x5`). -/
theorem validate_machine_proof_post_to_ambient
    {n : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat}
    (sp_v sp raVal cursor outerNext outerStatus outerLen depth endPtr : Word)
    (hsp : sp = sp_v + 32)
    (hra : raVal = RlpWalkNextStrictTie.S + 160)
    (hend : endPtr = base + BitVec.ofNat 64 endOff)
    (hproof : cpsTripleWithin n validateEntry
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      (validateCyclePre bytes base fuel cursorOff endOff sp_v raVal
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth))
      (validateCyclePost bytes base floor fuel cursorOff endOff sp_v raVal
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth))) :
    cpsTripleWithin n validateEntry
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      (validateCyclePre bytes base fuel cursorOff endOff sp_v raVal
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth))
      (cpsDepPost (fun r =>
        sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
          outerLen depth **
          validateResultPost bytes base floor cursorOff endOff fuel endPtr r **
          validateCallerSlack sp_v **
          validatePreservedResources bytes base fuel cursorOff endOff)) := by
  have hpost := validateCyclePost_to_callerAmbient
    bytes base floor fuel cursorOff endOff sp_v sp raVal cursor outerNext
    outerStatus outerLen depth hsp hra
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hproof
  intro hp h
  have h' := hpost hp h
  simpa [hend] using h'

/-! ## Knot body under smaller Shared (induction edge)

`rlp_validate_payload_nonempty_cps_under_shared` peels `x1` then runs the
nested Shared call.  `validateKnotFrameRest` is the post-prologue frame
without `x1`, so the nonempty pre rearranges to `validateKnotFrame ** ambient`.
The `hcont` family (V+40 → `validateCyclePost`) is the remaining Validate-side
status residual at child fuel. -/

def validateKnotFrameRest
    (sp raVal cursor endPtr : Word) : Assertion :=
  ((regIs .x2 sp) ** (regIs .x10 cursor) **
    (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
    (memIs sp raVal) ** (memIs (sp + 8) cursor) **
    (memIs (sp + 16) endPtr) **
    validateKnotSharedFrame sp)

/-- Resources that the Shared call must return at the `V+40` continuation.

The Shared body restores `x2` and `x1`, but the continuation only needs the
restored stack pointer and the saved return word in memory: its first return
arm reloads `x1` from `0(x2)`.  It does not touch the caller-side cells at
`sp`, `sp+8`, or `sp+16`; those are therefore framed through the call.  `x0`
is a hardware invariant and is deliberately not carried as a frame atom.
`x5` is different: the linked body uses it as `t0` and does not restore its
value, so the interface carries ownership rather than a value assertion. -/
def validateKnotContinuationFrame
    (bytes : List (BitVec 8)) (base : Word)
    (fuel cursorOff endOff : Nat) (sp raVal : Word) (P : Assertion) : Assertion :=
  (((regIs .x2 sp) ** (memIs sp raVal) ** memOwn (sp + 8) **
    (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) ** regOwn .x5 **
    validateKnotSharedFrame sp ** bytesRegion base bytes **
    ⌜ValidateFuel bytes fuel cursorOff endOff⌝) ** P)

/-- Shared-call input at the knot seam after replacing the clobbered `x5`
value pin by its ownership token.  `x10`/`x11` and `x12` remain value/ownership
inputs because Shared consumes them to produce the indexed result post. -/
def validateKnotSharedCallPre
    (bytes : List (BitVec 8)) (base : Word)
    (fuel cursorOff endOff : Nat) (sp raVal cursor endPtr : Word)
    (P : Assertion) : Assertion :=
  (((regIs .x2 sp) ** (regIs .x10 cursor) ** (regIs .x11 endPtr) **
    (regIs .x0 (0 : Word)) ** regOwn .x5 ** regOwn .x12 ** (memIs sp raVal) **
    (memIs (sp + 8) cursor) ** (memIs (sp + 16) endPtr) **
    validateKnotSharedFrame sp ** bytesRegion base bytes **
    ⌜ValidateFuel bytes fuel cursorOff endOff⌝) ** P)

/-- Result family published by Shared for the V+40 continuation. -/
def validateKnotSharedResultPost
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal : Word) (P : Assertion) : ValidateResult → Assertion :=
  fun r =>
    (validateKnotContinuationFrame bytes base fuel cursorOff endOff sp raVal P **
      validateResultPost bytes base floor cursorOff endOff fuel
        (base + BitVec.ofNat 64 endOff) r)

theorem validateKnotFrame_of_rest
    (sp raVal cursor endPtr : Word) :
    ∀ hp,
      ((regIs .x1 raVal) ** validateKnotFrameRest sp raVal cursor endPtr) hp →
      (validateKnotFrame sp raVal cursor endPtr **
        validateKnotSharedFrame sp) hp := by
  intro hp h
  simp only [validateKnotFrame, validateKnotFrameRest] at h ⊢
  xperm_chunked h

theorem validate_knot_body_under_shared
    {nShared nCont : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {contCode wholeCode : CodeReq}
    (sp raVal x1Old exit_ : Word)
    (hoffset : (validateEntry + 36) + signExtend21
      (jalOff rlpWalkNextNestedOfflineAddr
        (GuestAddrs.rlp_validate_payload + 36)) =
      (rlpWalkNextNestedOfflineAddr : Word))
    (halign : ((validateEntry + 40) &&& ~~~(1 : Word)) = validateEntry + 40)
    (hP : P.pcFree)
    (hcallCode : validateKnotCallCode.Disjoint nestedCR)
    (hsharedDisj : (CodeReq.singleton (rlpWalkNextNestedOfflineAddr : Word)
      (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
        (rlpWalkNextNestedOfflineAddr + 0)))).Disjoint sharedCR)
    (hbodyDisjoint : (validateKnotCallCode.union nestedCR).Disjoint contCode)
    (hbodySub : ∀ a i,
      validateKnotBodyCode contCode a = some i →
      wholeCode a = some i)
    (hshared : cpsTripleWithin nShared
      (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
      sharedCR
      ((regIs .x1 (validateEntry + 40)) **
        validateKnotSharedCallPre bytes base fuel cursorOff endOff sp raVal
          (base + BitVec.ofNat 64 cursorOff)
          (base + BitVec.ofNat 64 endOff) P)
      (cpsDepPost (validateKnotSharedResultPost bytes base floor
        fuel cursorOff endOff sp raVal P)))
    (hcont : ∀ r, cpsTripleWithin nCont (validateEntry + 40) exit_ contCode
      (validateKnotSharedResultPost bytes base floor fuel cursorOff endOff
        sp raVal P r)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)) :
    cpsTripleWithin (1 + (1 + nShared) + nCont) (validateEntry + 36) exit_ wholeCode
      (validateKnotBodyPre bytes base fuel cursorOff endOff sp raVal x1Old P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  let cursor := base + BitVec.ofNat 64 cursorOff
  let endPtr := base + BitVec.ofNat 64 endOff
  let bodyP : Assertion :=
    validateKnotSharedCallPre bytes base fuel cursorOff endOff sp raVal
      cursor endPtr P
  have hbodyP : bodyP.pcFree := by
    simp only [bodyP, validateKnotSharedCallPre]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_pure
      | exact hP
      | exact bytesRegion_pcFree _ _
  have hshared' :
      cpsTripleWithin nShared
        (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
        sharedCR
        ((regIs .x1 (validateEntry + 40)) ** bodyP)
        (cpsDepPost (validateKnotSharedResultPost bytes base floor fuel
          cursorOff endOff sp raVal P)) := by
    simpa [bodyP, cursor, endPtr] using hshared
  have hbody0 := rlp_validate_payload_nonempty_cps_under_shared
    (P := bodyP)
    (R := validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)
    (post := validateKnotSharedResultPost bytes base floor fuel cursorOff endOff
      sp raVal P)
    (contCode := contCode)
    x1Old exit_
      (jalOff rlpWalkNextNestedOfflineAddr
        (GuestAddrs.rlp_validate_payload + 36))
      hoffset halign hbodyP hcallCode hsharedDisj hbodyDisjoint
    hshared' hcont
  have hbody := cpsTripleWithin_extend_code hbodySub hbody0
  refine cpsTripleWithin_weaken ?_ (fun _ hp => hp) hbody
  intro hp h
  -- The body theorem is already parametric in the incoming `x1`; rearrange
  -- its frame-shaped precondition into the contract's explicit pre.
  simp only [validateKnotBodyPre, bodyP, validateKnotSharedCallPre, cursor,
    endPtr] at h ⊢
  let rest : Assertion :=
    (((regIs .x1 x1Old) ** (regIs .x2 sp) **
      (regIs .x10 cursor) ** (regIs .x11 endPtr) **
      (regIs .x0 (0 : Word)) ** regOwn .x12 **
      (memIs sp raVal) ** (memIs (sp + 8) cursor) **
      (memIs (sp + 16) endPtr) ** validateKnotSharedFrame sp **
      bytesRegion base bytes **
      ⌜ValidateFuel bytes fuel cursorOff endOff⌝) ** P)
  have hReordered : ((regIs .x5 endPtr) ** rest) hp := by
    simp only [rest]
    xperm_chunked h
  have hOwned : (regOwn .x5 ** rest) hp :=
    sepConj_mono (regIs_implies_regOwn .x5) (fun _ h => h) hp hReordered
  have hFinal := hOwned
  simp only [rest] at hFinal
  xperm_chunked hFinal

/-! Package the V+36 composition as the strengthened machine contract.  This
adapter is deliberately conditional on the *real* Shared and V+40
continuation triples: it constructs the `proof` field from the emitted call
seam, rather than storing the adapter itself as an unconsumed premise. -/
def validate_knot_body_contract_of_shared
    {nShared nCont : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {contCode wholeCode : CodeReq}
    (sp raVal exit_ : Word)
    (hbase_aligned : base.toNat % 8 = 0)
    (hcursor : cursorOff ≤ endOff)
    (hwindow : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64)
    (hvalid : ∀ off, off < endOff →
      isValidByteAccess (base + BitVec.ofNat 64 off) = true)
    (hexit : exit_ = raVal &&& ~~~(1 : Word))
    (hP : P.pcFree)
    (hoffset : (validateEntry + 36) + signExtend21
      (jalOff rlpWalkNextNestedOfflineAddr
        (GuestAddrs.rlp_validate_payload + 36)) =
      (rlpWalkNextNestedOfflineAddr : Word))
    (halign : ((validateEntry + 40) &&& ~~~(1 : Word)) = validateEntry + 40)
    (hcallCode : validateKnotCallCode.Disjoint nestedCR)
    (hsharedDisj : (CodeReq.singleton (rlpWalkNextNestedOfflineAddr : Word)
      (.JAL .x0 (jalOff GuestAddrs.rlp_walk_next_shared
        (rlpWalkNextNestedOfflineAddr + 0)))).Disjoint sharedCR)
    (hbodyDisjoint : (validateKnotCallCode.union nestedCR).Disjoint contCode)
    (hbodySub : ∀ a i,
      validateKnotBodyCode contCode a = some i →
      wholeCode a = some i)
    (hshared : cpsTripleWithin nShared
      (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
      sharedCR
      ((regIs .x1 (validateEntry + 40)) **
        validateKnotSharedCallPre bytes base fuel cursorOff endOff sp raVal
          (base + BitVec.ofNat 64 cursorOff)
          (base + BitVec.ofNat 64 endOff) P)
      (cpsDepPost (validateKnotSharedResultPost bytes base floor
        fuel cursorOff endOff sp raVal P)))
    (hcont : ∀ r, cpsTripleWithin nCont (validateEntry + 40) exit_ contCode
      (validateKnotSharedResultPost bytes base floor fuel cursorOff endOff
        sp raVal P r)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)) :
    ValidateKnotBodyContract bytes base floor fuel cursorOff endOff
      sp raVal exit_ wholeCode P := by
  refine
    { hbase_aligned := hbase_aligned
      hcursor := hcursor
      hwindow := hwindow
      hover := hover
      hnowrap := hnowrap
      hvalid := hvalid
      hexit := hexit
      hP := hP
      continuationCode := contCode
      bodyCode := validateKnotBodyCode contCode
      hbodyCode := rfl
      hbodyDisjoint := hbodyDisjoint
      hbodySub := hbodySub
      steps := 1 + (1 + nShared) + nCont
      proof := ?_ }
  intro x1Old
  exact validate_knot_body_under_shared
    sp raVal x1Old exit_ hoffset halign hP hcallCode hsharedDisj
    hbodyDisjoint hbodySub hshared hcont

/-- Enriched short-arm call-site resources intended to imply `validateCyclePre`.
Residual: precise-SL `x12` drop into the cycle ABI; named for Goal quotes. -/
def sharedShortValidateCallPre
    (bytes : List (BitVec 8)) (base : Word) (fuel cursorOff endOff : Nat)
    (listBase sp_v sp raVal cursor outerNext outerStatus outerLen depth
      endPtr : Word) : Assertion :=
  ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
    (regIs .x5 listBase) ** (regIs .x12 (listBase + 1)) **
    (regIs .x10 (listBase + 1)) ** (regIs .x11 endPtr) **
    (regIs .x2 sp) ** (regIs .x0 (0 : Word)) **
    validateCallerSlack sp_v **
    bytesRegion base bytes **
    ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
    sharedValidateCallerRest sp raVal cursor outerNext outerStatus
      outerLen depth)

/-! ## Inhabitant attempt for the amended short-arm goal (GH #12457)

The amended `SharedListArmsFromValidateGoal` short-arm conclusion, chained
end-to-end at the intended exit `raVal &&& ~~~1`: goal precondition →
`shared_short_arm_validate_call` (composition check) → the callee residual →
depth+status continuation.  The three hypotheses `hval`, `hsucc`, `hfail`
are the *named residuals*: `hval` is the callee-side obligation the
`hchild`-to-triple adapter must deliver (a `validateCR` triple whose
dependent post is exactly `sharedAfterValidatePre` at the child fuel
`cycleFuel payloadStart payloadEnd`), and `hsucc`/`hfail` are the two
status-post implications the caller's post `R` must satisfy.  The theorem
proves the amended conclusion is *inhabitable modulo precisely those
names* — the anti-vacuity rubric's conclusion-side oracle at the intended
instantiation.  The long arm additionally needs the prefix-loop chain and
is not part of this check. -/

theorem shared_list_arm_goal_short_full_chain
    {bytes : List (BitVec 8)} {base : Word} {floor parentFuel : Nat}
    {cursorOff endOff : Nat}
    {spV sp raVal exit_ endPtr pfx listBase depth : Word}
    {oldPayload old10 oldOut old7 oldRem old13 old29 oldAcc : Word}
    {cursor outerNext outerStatus outerLen : Word}
    {P R : Assertion} {nVal : Nat}
    (h : SharedListArmInputs bytes base floor parentFuel cursorOff endOff spV sp
      raVal exit_ endPtr pfx listBase depth oldPayload old10 oldOut old7
      oldRem old13 old29 oldAcc P)
    (hval : cpsTripleWithin nVal (GuestAddrs.rlp_validate_payload : Word)
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
        (regIs .x5 listBase) ** (regIs .x12 (listBase + 1)) **
        (regIs .x10 (listBase + 1)) **
        sharedValidateCallRemainder spV sp endPtr **
        ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
          h.selector.payloadEnd) h.selector.payloadStart
          h.selector.payloadEnd⌝ ** P)
      (cpsDepPost (sharedAfterValidatePre (bytes := bytes) (base := base)
        (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
        (fuel := cycleFuel h.selector.payloadStart h.selector.payloadEnd)
        endPtr sp raVal cursor outerNext outerStatus outerLen depth)))
    (hsucc : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := cycleFuel h.selector.payloadStart h.selector.payloadEnd)
          endPtr sp raVal cursor outerNext outerStatus outerLen r) hp →
      R hp)
    (hfail : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := cycleFuel h.selector.payloadStart h.selector.payloadEnd)
          endPtr sp raVal cursor outerNext outerStatus outerLen r) hp →
      R hp) :
    cpsTripleWithin (2 + (1 + nVal) + 15) (RlpWalkNextStrictTie.S + 148)
      (raVal &&& ~~~(1 : Word))
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      (((regIs .x5 listBase) ** (regIs .x12 oldPayload) **
        (regIs .x10 old10) ** (regIs .x1 raVal) **
        ⌜sharedPrefixByteAt bytes cursorOff pfx⌝ **
        ⌜¬ BitVec.ult pfx (192 : Word)⌝ **
        ⌜BitVec.ult depth (rlpRecursiveDecodeDepthCap : Word)⌝ **
        ⌜cursorOff < h.selector.payloadStart⌝ **
        ⌜h.selector.payloadStart ≤ h.selector.payloadEnd⌝ **
        ⌜BitVec.ult pfx (248 : Word)⌝ **
        sharedValidateCallRemainder spV sp endPtr **
        ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
          h.selector.payloadEnd) h.selector.payloadStart
          h.selector.payloadEnd⌝) ** P)
      R :=
  cpsTripleWithin_seq_dep_post_same_cr
    (shared_list_arm_goal_short_compose h hval)
    (shared_after_validate_cont_family endPtr sp raVal cursor outerNext
      outerStatus outerLen depth hsucc hfail)

/-! The long LIST arm has the same status continuation as the short arm, but
the validator call receives the prefix-decoder scratch that the long-header
loop publishes.  Keep this as a family theorem rather than hiding the
long-header facts in an arbitrary callee frame: the selector's concrete `n`
and the three owned scratch registers are the resources consumed at the
`S+160` seam. -/

theorem shared_list_arm_goal_long_full_chain
    {bytes : List (BitVec 8)} {base : Word} {floor parentFuel : Nat}
    {cursorOff endOff : Nat}
    {spV sp raVal exit_ endPtr pfx listBase depth : Word}
    {oldPayload old10 oldOut old7 oldRem old13 old29 oldAcc : Word}
    {cursor outerNext outerStatus outerLen : Word}
    {P R : Assertion} {nVal : Nat}
    (h : SharedListArmInputs bytes base floor parentFuel cursorOff endOff spV sp
      raVal exit_ endPtr pfx listBase depth oldPayload old10 oldOut old7
      oldRem old13 old29 oldAcc P)
    (hlong : ¬ BitVec.ult pfx (248 : Word))
    (hval : ∀ n, n ≤ 8 →
      cpsTripleWithin nVal (GuestAddrs.rlp_validate_payload : Word)
        ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
        ((regIs .x1 (RlpWalkNextStrictTie.S + 160)) **
          (regIs .x12 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x5 listBase) ** (regIs .x13 (BitVec.ofNat 64 n)) **
          (regIs .x10 (listBase + BitVec.ofNat 64 n + 1)) **
          (regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
          (regIs .x28 (0 : Word)) ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (regIs .x0 (0 : Word)) **
          bytesRegion base bytes ** sharedValidateCallRemainder spV sp endPtr **
          ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
            h.selector.payloadEnd) h.selector.payloadStart
            h.selector.payloadEnd⌝ ** P)
        (cpsDepPost (sharedAfterValidatePre (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := cycleFuel h.selector.payloadStart h.selector.payloadEnd)
          endPtr sp raVal cursor outerNext outerStatus outerLen depth)))
    (hsucc : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusSuccessPost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := cycleFuel h.selector.payloadStart h.selector.payloadEnd)
          endPtr sp raVal cursor outerNext outerStatus outerLen r) hp →
      R hp)
    (hfail : ∀ r hp,
      ((regIs .x9 (depth - 1)) **
        sharedValidateStatusFailurePost (bytes := bytes) (base := base)
          (floor := floor) (cursorOff := cursorOff) (endOff := endOff)
          (fuel := cycleFuel h.selector.payloadStart h.selector.payloadEnd)
          endPtr sp raVal cursor outerNext outerStatus outerLen r) hp →
      R hp) :
    ∃ nLong, cpsTripleWithin nLong (RlpWalkNextStrictTie.S + 88)
      (raVal &&& ~~~(1 : Word))
      (RlpWalkNextStrictTie.sharedCode.union validateCR)
      (((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        regOwn .x30 ** regOwn .x31 ** (regIs .x12 oldOut) **
        (regIs .x10 old10) ** (regIs .x1 raVal) **
        (regIs .x0 (0 : Word)) ** bytesRegion base bytes **
        ⌜sharedPrefixByteAt bytes cursorOff pfx⌝ **
        ⌜¬ BitVec.ult pfx (192 : Word)⌝ **
        ⌜BitVec.ult depth (rlpRecursiveDecodeDepthCap : Word)⌝ **
        ⌜cursorOff < h.selector.payloadStart⌝ **
        ⌜h.selector.payloadStart ≤ h.selector.payloadEnd⌝ **
        ⌜¬ BitVec.ult pfx (248 : Word)⌝ **
        sharedValidateCallRemainder spV sp endPtr **
        ⌜ValidateFuel bytes (cycleFuel h.selector.payloadStart
          h.selector.payloadEnd) h.selector.payloadStart
          h.selector.payloadEnd⌝) ** P) R := by
  obtain ⟨nLong, hArm⟩ := shared_list_arm_goal_long_compose
    (h := h) (hlong := hlong) (hval := hval)
  have hcont := shared_after_validate_cont_family endPtr sp raVal cursor
    outerNext outerStatus outerLen depth hsucc hfail
  refine ⟨nLong + 15, ?_⟩
  exact cpsTripleWithin_seq_dep_post_same_cr hArm hcont

/-! The nested caller returns at `V+40`, while the long-arm validator return
seam is named relative to `S+160`.  In the linked image the continuation
address is exactly 0x58 (88 bytes) above that seam; keep the conversion
kernel-checked instead of copying either absolute address into a caller. -/
theorem shared_s160_plus_88_eq_validate_v40 :
    RlpWalkNextStrictTie.S + 160 + 88 = validateEntry + 40 := by
  decide

theorem shared_long_arm_to_validate_v40
    {nLong : Nat} {P R : Assertion}
    (h : cpsTripleWithin nLong (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 160 + 88)
      (RlpWalkNextStrictTie.sharedCode.union validateCR) P R) :
    cpsTripleWithin nLong (RlpWalkNextStrictTie.S + 88)
      (validateEntry + 40)
      (RlpWalkNextStrictTie.sharedCode.union validateCR) P R := by
  rw [shared_s160_plus_88_eq_validate_v40] at h
  exact h

end EvmAsm.Codegen.RlpWalkNextStrictFuel
