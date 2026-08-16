/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachineKnot

  Knot-continuation for #12419 (split from MachineCont at the Programs
  1500-line cap).  Strengthens the Shared post at `V+40` to a
  frame-preserving walk-next ABI (coord: strengthening a too-thin post is
  the right repair; result-only / epilogue-shaped posts were statement defects).
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachineCont

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-! ## Entry frame vs loop-back frame (split-`callRa`)

`validateKnotFrame` is the *entry* landing at `V+36`: `x1 = raVal` and
`memIs sp = raVal`.  After a successful sibling Cont, the loop re-enters
`V+16 → V+36` with a different shape: `x1 = V+40` (Cont return address) while
`memIs sp` still holds the outer `raVal`.  That is not three coincidences —
ZeroToReload, `validate_success_tail_cps` (`x1Old`), and the nonempty
ZeroReload prefix all rediscovered it — it is a structural property of the
routine: **the loop re-entry state is not the entry state**.  Any lemma
written against the entry frame is wrong at every loop-back site (#12419).

`validateKnotLoopBackFrame` names that distinction once so the IH and its
downstream uses refer to it instead of re-deriving the split. -/

/-- Loop-back knot landing at `V+36`.  Differs from `validateKnotFrame` in
exactly one register: `x1` holds `validateEntry + 40` rather than the outer
`raVal`; the outer return address remains spilled at `memIs sp`. -/
def validateKnotLoopBackFrame
    (sp raVal cursor endPtr : Word) : Assertion :=
  ((regIs .x1 (validateEntry + 40)) **
    validateKnotFrameRest sp raVal cursor endPtr)

theorem validateKnotLoopBackFrame_of_rest
    (sp raVal cursor endPtr : Word) :
    ∀ hp,
      ((regIs .x1 (validateEntry + 40)) **
        validateKnotFrameRest sp raVal cursor endPtr) hp →
      validateKnotLoopBackFrame sp raVal cursor endPtr hp := by
  intro hp h
  simpa [validateKnotLoopBackFrame] using h

/-! ## Strengthened Shared post at `V+40`

After the nested Shared call returns, the machine is in *walk-next* ABI
(`x10` = advanced cursor, `x11` = status, `x12` = len) with the validate
frame slots still owned.  That is **not** `validateResultDependentPost`
(epilogue ABI: `x10` = status).  Using the epilogue post at `V+40` was a
statement defect: too thin to feed
`rlp_validate_payload_nested_nonzero_status_cps` /
`validate_nested_success_zero_loop_indexed`. -/

/-- Validate frame slots preserved across nested Shared (no data regs that
the nested return overwrites). `raVal` is the outer return address spilled
at `sp`; `frameCursor` / `endPtr` are the saved cursor/end. -/
def validateKnotFrameSlots
    (sp raVal frameCursor endPtr : Word) : Assertion :=
  ((regIs .x2 sp) **
    (memIs sp raVal) ** (memIs (sp + 8) frameCursor) **
    (memIs (sp + 16) endPtr))

/-- Honest Shared post at `V+40` when called from the validate knot.

Success-only cursor pin (#12419 (c)): on `r.status = 0` the live cursor in
`x10` (= `r.cursor`) is the semantic item boundary `base + r.next`.  This is
what positions the zero-loop's stored frame cursor; it is NOT put in
`validateResultFacts` (that shared def also indexes the outer result, where
success may choose `r.cursor := endPtr`).  Nested and outer are different
`r`'s — pinning the nested cursor cannot re-break outer `x11`.

⚠️ OPEN PRODUCER OBLIGATION (#12419, 12464-class vacuity risk).  The cursor
pin STRENGTHENS this post.  Consumers (`validateKnotCont_zero_to_reload`) now
peel it, so ContGoal is derived — BUT nothing in-tree yet PRODUCES a Shared
proof whose post is this strengthened shape.  Every `hshared` fed to
`validate_knot_body_under_shared_framed` must inhabit it including the pin.
Until a concrete Shared machine proof posts the pin, that framed theorem is
dischargeable only from an as-yet-unbuilt `hshared`; if the pin turns out
NOT to hold on the nested success path, the framed knot body becomes VACUOUS
(kernel-clean, green build, proving nothing — the exact 12464 class).  The pin
is BELIEVED dischargeable (the nested success path leaves `x10 = item end`),
NOT yet SHOWN.  Do not count the producer as done until a real `hshared`
inhabits this post. -/
def validateKnotSharedPost
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal : Word) (P : Assertion) (r : ValidateResult) : Assertion :=
  ((regIs .x1 (validateEntry + 40)) **
    (regIs .x10 r.cursor) ** (regIs .x11 r.status) ** (regIs .x12 r.len) **
    (regIs .x0 (0 : Word)) ** regOwn .x5 **
    validateKnotFrameSlots sp raVal
      (base + BitVec.ofNat 64 cursorOff)
      (base + BitVec.ofNat 64 endOff) **
    bytesRegion base bytes **
    ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P **
    ⌜validateResultFacts bytes base floor cursorOff endOff fuel
      (base + BitVec.ofNat 64 endOff) r⌝ **
    ⌜r.status = 0 → r.cursor = base + BitVec.ofNat 64 r.next⌝)

/-- `hcont` under the strengthened post. -/
def ValidateKnotContGoal
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal exit_ : Word) (contCode : CodeReq) (P : Assertion)
    (nCont : Nat) : Prop :=
  ∀ r, cpsTripleWithin nCont (validateEntry + 40) exit_ contCode
    (validateKnotSharedPost bytes base floor fuel cursorOff endOff
      sp raVal P r)
    (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)

/-- Reload pre at `V+16` after a successful nested item.

Carries the outer `ValidateFuel` / first-item `validateResultFacts` / `x12`
through so empty-remaining success can reassemble `validateCyclePost` without
re-deriving the item decode.  `ValidateK` is the REMAINING window at
`r.next` with fuel `endOff - r.next` (#12419 fuel split). -/
def validateKnotZeroReloadPre
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal : Word) (P : Assertion) (r : ValidateResult) : Assertion :=
  ((regIs .x2 sp) ** (regIs .x10 r.cursor) ** (regIs .x11 (0 : Word)) **
    (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
    (regIs .x5 (base + BitVec.ofNat 64 endOff)) **
    (regIs .x12 r.len) **
    (memIs sp raVal) ** (memIs (sp + 8) r.cursor) **
    (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
    ⌜ValidateK bytes base floor r.cursor
      (base + BitVec.ofNat 64 endOff) r.next endOff (endOff - r.next)⌝ **
    ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
    ⌜validateResultFacts bytes base floor cursorOff endOff fuel
      (base + BitVec.ofNat 64 endOff) r⌝ **
    bytesRegion base bytes ** P)

/-- Zero-status Cont residual: `V+16` → `validateCyclePost` (induction edge). -/
def ValidateKnotContZeroReloadGoal
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal exit_ : Word) (contCode : CodeReq) (P : Assertion)
    (nReload : Nat) : Prop :=
  ∀ r, r.status = 0 →
    cpsTripleWithin nReload (validateEntry + 16) exit_ contCode
      (validateKnotZeroReloadPre bytes base floor fuel cursorOff endOff
        sp raVal P r)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)

/-- Knot body under Shared with the strengthened frame-preserving post.

⚠️ OPEN PRODUCER OBLIGATION (#12419 hand-off): the `hshared` hypothesis below
now demands the STRENGTHENED `validateKnotSharedPost` (with the success-only
cursor pin).  No caller yet supplies such an `hshared`.  Discharging it — a real
Shared machine proof whose dependent post includes
`r.status = 0 → r.cursor = base + r.next` — is the FIRST task of the next
session.  Until then this theorem is not vacuous by itself, but any downstream
use is only as strong as the `hshared` it is fed; do NOT mark the producer done
on a green build alone (12464 class — see the note on `validateKnotSharedPost`).

`x1Old` is the incoming `x1` value: the `JAL .x1` at `V+36` OVERWRITES it with
`V+40` before anything reads it, so the body is parametric over the incoming
`ra` register (only OWNERSHIP of `x1` is required, not a specific value).  This
is the FRAME-LEVEL instance of the entry-vs-loop-back split (#12419): the
prologue lands here with `x1 = raVal`, the sibling loop-back with `x1 = V+40`,
and both weaken to `regIs .x1 x1Old ** validateKnotFrameRest`.  `raVal` (the
outer return address spilled at `memIs sp`) is unchanged. -/
theorem validate_knot_body_under_shared_framed
    {nShared nCont : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {contCode wholeCode : CodeReq}
    (sp raVal exit_ x1Old : Word) (offset : BitVec 21)
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
        (validateKnotFrameRest sp raVal
          (base + BitVec.ofNat 64 cursorOff)
          (base + BitVec.ofNat 64 endOff) **
          (regIs .x0 (0 : Word)) ** regOwn .x12 **
          bytesRegion base bytes **
          ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P))
      (cpsDepPost (validateKnotSharedPost bytes base floor fuel cursorOff endOff
        sp raVal P)))
    (hcont : ValidateKnotContGoal bytes base floor fuel cursorOff endOff
      sp raVal exit_ contCode P nCont) :
    cpsTripleWithin (1 + (1 + nShared) + nCont) (validateEntry + 36) exit_ wholeCode
      (((regIs .x1 x1Old) **
        validateKnotFrameRest sp raVal
          (base + BitVec.ofNat 64 cursorOff)
          (base + BitVec.ofNat 64 endOff)) **
        (regIs .x0 (0 : Word)) ** regOwn .x12 **
        bytesRegion base bytes **
        ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  let cursor := base + BitVec.ofNat 64 cursorOff
  let endPtr := base + BitVec.ofNat 64 endOff
  let ambient : Assertion :=
    ((regIs .x0 (0 : Word)) ** regOwn .x12 ** bytesRegion base bytes **
      ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
  let bodyP : Assertion :=
    validateKnotFrameRest sp raVal cursor endPtr ** ambient
  have hbodyP : bodyP.pcFree := by
    simp only [bodyP, validateKnotFrameRest, ambient]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_regOwn
      | exact pcFree_pure
      | exact hP
      | exact bytesRegion_pcFree _ _
  have hshared' :
      cpsTripleWithin nShared
        (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
        RlpWalkNextStrictTie.sharedCode
        ((regIs .x1 (validateEntry + 40)) ** bodyP)
        (cpsDepPost (validateKnotSharedPost bytes base floor fuel cursorOff
          endOff sp raVal P)) := by
    simpa [bodyP, cursor, endPtr, ambient] using hshared
  have hbody0 := rlp_validate_payload_nonempty_cps_under_shared
    (P := bodyP)
    (R := validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)
    (post := validateKnotSharedPost bytes base floor fuel cursorOff endOff
      sp raVal P)
    (contCode := contCode)
    x1Old exit_ offset hoffset halign hbodyP hcallCode hsharedDisj houterDisj
    hshared' hcont
  have hbody := cpsTripleWithin_extend_code hbodySub hbody0
  refine cpsTripleWithin_weaken ?_ (fun _ hp => hp) hbody
  intro hp h
  simp only [bodyP, validateKnotFrameRest, ambient, cursor,
    endPtr] at h ⊢
  xperm_chunked h

/-- Package entry-level proof from a framed knot body. -/
def ValidateEntryFromKnotGoal
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal exit_ : Word) (wholeCode : CodeReq) (P : Assertion) : Prop :=
  exit_ = raVal &&& ~~~(1 : Word) →
  P.pcFree →
  (∀ a i, validateCR a = some i → wholeCode a = some i) →
  (base + BitVec.ofNat 64 cursorOff ≠ base + BitVec.ofNat 64 endOff) →
  ((base + BitVec.ofNat 64 endOff).ult
    (base + BitVec.ofNat 64 cursorOff) ≠ true) →
  (∃ nKnot, cpsTripleWithin nKnot (validateEntry + 36) exit_ wholeCode
    (validateKnotFrame sp raVal
      (base + BitVec.ofNat 64 cursorOff)
      (base + BitVec.ofNat 64 endOff) **
      (regIs .x0 (0 : Word)) ** regOwn .x12 **
      bytesRegion base bytes **
      ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
    (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)) →
  (∃ steps, cpsTripleWithin steps validateEntry exit_ wholeCode
    (validateCyclePre bytes base fuel cursorOff endOff sp raVal P)
    (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P))

theorem validateEntryFromKnotGoal_discharge
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal exit_ : Word) (wholeCode : CodeReq) (P : Assertion) :
    ValidateEntryFromKnotGoal bytes base floor fuel cursorOff endOff
      sp raVal exit_ wholeCode P := by
  intro _hexit hP hvalidateSub hne horder ⟨nKnot, hknot⟩
  exact validate_machine_proof_of_knot (nKnot := nKnot) (bytes := bytes)
    (base := base) (floor := floor) (fuel := fuel) (cursorOff := cursorOff)
    (endOff := endOff) (P := P) (wholeCode := wholeCode)
    sp raVal exit_ hne horder hP hvalidateSub hknot

/-! ## Nonzero arm of `ValidateKnotContGoal`

Packages `rlp_validate_payload_nested_nonzero_status_cps` (now with honest
`frameCursor` / `endPtr` spills) into `validateCyclePost`, framing the
ambient bytes/fuel/`x12`/`P` through the failure return. -/

/-- Failure return witness: status 7, `x11` still holds the nested nonzero status. -/
def validateKnotFailureResult (r : ValidateResult) : ValidateResult where
  next := r.next
  cursor := r.status
  status := (7 : Word)
  len := r.len

theorem validateKnotFailureResult_facts
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (r : ValidateResult) (_hstatus : r.status ≠ 0) :
    validateResultFacts bytes base floor cursorOff endOff fuel
      (base + BitVec.ofNat 64 endOff) (validateKnotFailureResult r) :=
  Or.inr (by
    change (7 : Word) ≠ 0
    decide)

theorem validateKnotCont_nonzero
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursorOff endOff : Nat}
    {P : Assertion}
    (sp raVal : Word) (r : ValidateResult)
    (hstatus : r.status ≠ 0)
    (hP : P.pcFree) :
    cpsTripleWithin 5 (validateEntry + 40) (raVal &&& ~~~1) validateCR
      (validateKnotSharedPost bytes base floor fuel cursorOff endOff
        sp raVal P r)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  let frameCursor := base + BitVec.ofNat 64 cursorOff
  let endPtr := base + BitVec.ofNat 64 endOff
  -- Rest of the pre without x5 / entry-facts (facts unused on the failure arm).
  let preRest : Assertion :=
    ((regIs .x1 (validateEntry + 40)) **
      (regIs .x10 r.cursor) ** (regIs .x11 r.status) **
      (regIs .x12 r.len) ** (regIs .x0 (0 : Word)) **
      validateKnotFrameSlots sp raVal frameCursor endPtr **
      bytesRegion base bytes **
      ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
  have hforall : ∀ x5Old,
      cpsTripleWithin 5 (validateEntry + 40) (raVal &&& ~~~1) validateCR
        (preRest ** (regIs .x5 x5Old))
        (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal
          P) := by
    intro x5Old
    have hcore0 := rlp_validate_payload_nested_nonzero_status_cps
      sp raVal r.cursor r.status endPtr frameCursor x5Old hstatus
    have hcore := cpsTripleWithin_frameR
      ((regIs .x12 r.len) ** bytesRegion base bytes **
        ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
      (by
        repeat first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_pure
          | exact hP
          | exact bytesRegion_pcFree _ _)
      hcore0
    refine cpsTripleWithin_weaken ?_ ?_ hcore
    · intro hp h
      simp only [preRest, validateKnotFrameSlots, frameCursor, endPtr] at h ⊢
      xperm_chunked h
    · intro hp h
      refine ⟨validateKnotFailureResult r, ?_⟩
      have hf := validateKnotFailureResult_facts bytes base floor fuel
        cursorOff endOff r hstatus
      simp only [validateResultPost, validateKnotFailureResult,
        frameCursor, endPtr] at h ⊢
      -- Move x5 to the right, convert to ownership, attach failure facts, permute.
      have h1 :
          (((regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) **
            (regIs .x11 r.status) ** (regIs .x0 (0 : Word)) **
            (regIs .x1 raVal) **
            (memIs sp raVal) ** (memIs (sp + 8) frameCursor) **
            (memIs (sp + 16) endPtr) ** (regIs .x12 r.len) **
            bytesRegion base bytes **
            ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P) **
            (regIs .x5 x5Old)) hp := by
        xperm_chunked h
      have h2 := sepConj_mono_right (regIs_to_regOwn .x5 x5Old) hp h1
      have hadd : ∀ hq,
          (regOwn .x5) hq →
          (regOwn .x5 **
            ⌜validateResultFacts bytes base floor cursorOff endOff fuel
              endPtr (validateKnotFailureResult r)⌝) hq :=
        fun hq how => (sepConj_pure_right _).2 ⟨how, hf⟩
      have hpure := sepConj_mono_right hadd hp h2
      simp only [validateKnotFailureResult, frameCursor, endPtr] at hpure ⊢
      -- The `sp+8` slot is a dead frame slot after return (unobservable: in-degree
      -- 1 + SP restored before ret), so `validateCyclePost` now holds it as
      -- `memOwn`.  Likewise `x12` is `regOwn` in the (corrected) cycle post — the
      -- nested call's `x12` (last child's len) is dead, unobservable.  Weaken the
      -- machine's concrete `regIs x12 r.len` and `memIs(sp+8)` to ownership before
      -- permuting to the (weakened) cycle post (#12419).
      have hhead :
          ((regIs .x12 r.len) **
            ((memIs (sp + 8) (base + BitVec.ofNat 64 cursorOff)) **
              (regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) **
              (regIs .x11 r.status) ** (regIs .x0 (0 : Word)) **
              (regIs .x1 raVal) ** (memIs sp raVal) **
              (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
              bytesRegion base bytes **
              ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
              regOwn .x5 **
              ⌜validateResultFacts bytes base floor cursorOff endOff fuel
                  (base + BitVec.ofNat 64 endOff)
                  { next := r.next, cursor := r.status, status := 7,
                    len := r.len }⌝ ** P)) hp := by
        xperm_chunked hpure
      have hown12 := sepConj_mono_left (regIs_to_regOwn .x12 r.len) hp hhead
      have hhead2 :
          ((memIs (sp + 8) (base + BitVec.ofNat 64 cursorOff)) **
            ((regOwn .x12) **
              (regIs .x2 (sp + 32)) ** (regIs .x10 (7 : Word)) **
              (regIs .x11 r.status) ** (regIs .x0 (0 : Word)) **
              (regIs .x1 raVal) ** (memIs sp raVal) **
              (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
              bytesRegion base bytes **
              ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
              regOwn .x5 **
              ⌜validateResultFacts bytes base floor cursorOff endOff fuel
                  (base + BitVec.ofNat 64 endOff)
                  { next := r.next, cursor := r.status, status := 7,
                    len := r.len }⌝ ** P)) hp := by
        xperm_chunked hown12
      have hown8 := sepConj_mono_left memIs_implies_memOwn hp hhead2
      xperm_chunked hown8
  have hown :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) hforall
  refine cpsTripleWithin_weaken ?_ (fun _ hp => hp) hown
  intro hp h
  -- Drop the trailing nested-entry facts + success-only cursor pin (failure
  -- arm does not use either; the cursor pin is guarded on status = 0).
  simp only [validateKnotSharedPost] at h
  have h1 :
      (((preRest ** regOwn .x5) **
        ⌜validateResultFacts bytes base floor cursorOff endOff fuel
          (base + BitVec.ofNat 64 endOff) r⌝) **
        ⌜r.status = 0 → r.cursor = base + BitVec.ofNat 64 r.next⌝) hp := by
    simp only [preRest, validateKnotFrameSlots, frameCursor, endPtr] at h ⊢
    xperm_chunked h
  exact ((sepConj_pure_right _).1 ((sepConj_pure_right _).1 h1).1).1

/-! ## Zero arm of `ValidateKnotContGoal`

`V+40` → `V+16` via `validate_nested_success_zero_loop_indexed`, then the
reload Goal (induction edge) finishes to `validateCyclePost`. -/

theorem PayloadStrictFuel.fuel_eq
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursor endOff : Nat}
    (h : PayloadStrictFuel bytes base floor fuel cursor endOff) :
    fuel = endOff - cursor := by
  cases h <;> rfl

theorem validateLoopContinuation_inhabited
    (bytes : List (BitVec 8)) (base : Word) (floor nextOff endOff fuel : Nat) :
    ValidateLoopContinuation bytes base floor nextOff endOff fuel := by
  intro sp x1Val spVal cursorPtr frameCursorPtr endPtr hcross
  have hown : cpsTripleWithin 4 (validateEntry + 44) (validateEntry + 16)
      validateCR
      (((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 x1Val) **
        (regIs .x11 (0 : Word)) ** (memIs sp spVal) **
        (memIs (sp + 8) frameCursorPtr) ** (memIs (sp + 16) endPtr) **
        ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝) **
       regOwn .x5)
      ((regIs .x2 sp) ** (regIs .x10 cursorPtr) ** (regIs .x1 x1Val) **
       (regIs .x5 endPtr) ** (regIs .x11 (0 : Word)) **
       (memIs sp spVal) ** (memIs (sp + 8) cursorPtr) **
       (memIs (sp + 16) endPtr) **
       ⌜ValidateK bytes base floor cursorPtr endPtr nextOff endOff fuel⌝) := by
    apply cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
    intro x5Old
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (validate_nested_zero_loop_cps (bytes := bytes) (base := base)
        (floor := floor) (nextOff := nextOff) (endOff := endOff) (fuel := fuel)
        sp x1Val spVal cursorPtr frameCursorPtr endPtr x5Old hcross)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hown

/-- `V+40` → `V+16` under status-0 Shared post.  Semantic hyps (`ValidateK`,
register-form decode) are DERIVED from the Shared post: `validateResultFacts`
(semantic boundary) + the success-only cursor pin
`r.cursor = base + r.next` (#12419 (c)). -/
def ValidateKnotContZeroToReloadGoal
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal : Word) (P : Assertion) (r : ValidateResult) : Prop :=
  r.status = 0 →
  base.toNat + bytes.length < 2 ^ 64 →
  base.toNat + endOff + 9 < 2 ^ 64 →
  P.pcFree →
  cpsTripleWithin 5 (validateEntry + 40) (validateEntry + 16) validateCR
    (validateKnotSharedPost bytes base floor fuel cursorOff endOff
      sp raVal P r)
    (validateKnotZeroReloadPre bytes base floor fuel cursorOff endOff
      sp raVal P r)

/-- Small `PayloadStrictFuel` window/cursor extractors used by the zero-arm
derivation.  Both are single `cases` — no induction, so they cannot smuggle in
the recursive fact the outer induction must establish. -/
theorem payloadStrictFuel_window
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursor endOff : Nat}
    (h : PayloadStrictFuel bytes base floor fuel cursor endOff) :
    endOff ≤ bytes.length := by
  cases h with
  | empty _ hend => exact hend
  | item _ _ hbytes _ _ => exact hbytes

theorem payloadStrictFuel_cursor_le
    {bytes : List (BitVec 8)} {base : Word} {floor fuel cursor endOff : Nat}
    (h : PayloadStrictFuel bytes base floor fuel cursor endOff) :
    cursor ≤ endOff := by
  cases h with
  | empty heq _ => omega
  | item hcursor hend _ _ _ => omega

/-- Peel a leading pure from a CPS pre (local copy of `StmtSoundCall`'s lemma;
avoids importing the SAsm soundness stack into this Programs file). -/
private theorem cpsTripleWithin_pure_pre_left {n : Nat} {entry exit_ : Word}
    {cr : CodeReq} {fact : Prop} {H Q : Assertion}
    (h : fact → cpsTripleWithin n entry exit_ cr H Q) :
    cpsTripleWithin n entry exit_ cr (⌜fact⌝ ** H) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨h0, hcompat, hh⟩ := hPR
  rw [sepConj_assoc', sepConj_pure_left] at hh
  exact h hh.1 R hR s hcr ⟨h0, hcompat, hh.2⟩ hpc

/-- DERIVED discharge of `ValidateKnotContZeroToReloadGoal`.  Peels
`validateResultFacts` + the success-only cursor pin from the Shared post,
rebuilds register-form `ValidateK` / decode, then runs the split-ra zero-loop. -/
theorem validateKnotCont_zero_to_reload
    {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    (sp raVal : Word) (r : ValidateResult) :
    ValidateKnotContZeroToReloadGoal bytes base floor fuel cursorOff
      endOff sp raVal P r := by
  intro hstatus hover _hnowrap hP
  -- SharedPost with the two trailing pures leading, for peeling.
  let H : Assertion :=
    ((regIs .x1 (validateEntry + 40)) **
      (regIs .x10 r.cursor) ** (regIs .x11 r.status) ** (regIs .x12 r.len) **
      (regIs .x0 (0 : Word)) ** regOwn .x5 **
      validateKnotFrameSlots sp raVal
        (base + BitVec.ofNat 64 cursorOff)
        (base + BitVec.ofNat 64 endOff) **
      bytesRegion base bytes **
      ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
  let peeled : Assertion :=
    (⌜validateResultFacts bytes base floor cursorOff endOff fuel
        (base + BitVec.ofNat 64 endOff) r⌝ **
      ⌜r.status = 0 → r.cursor = base + BitVec.ofNat 64 r.next⌝ ** H)
  let Pre : Assertion :=
    validateKnotSharedPost bytes base floor fuel cursorOff endOff sp raVal P r
  let Post : Assertion :=
    validateKnotZeroReloadPre bytes base floor fuel cursorOff endOff sp raVal P r
  refine @cpsTripleWithin_weaken 5 (validateEntry + 40) (validateEntry + 16)
    validateCR peeled Pre Post Post ?hpre (fun _ h => h) ?hinner
  case hpre =>
    intro hp h
    simp only [Pre, validateKnotSharedPost, peeled, H, validateKnotFrameSlots] at h ⊢
    xperm_chunked h
  case hinner =>
    refine cpsTripleWithin_pure_pre_left (fun hRF =>
      cpsTripleWithin_pure_pre_left (fun hpin => ?_))
    -- Success facts at the semantic boundary.
    have hfacts : ValidateK bytes base floor
        (base + BitVec.ofNat 64 r.next)
        (base + BitVec.ofNat 64 endOff) r.next endOff (endOff - r.next) ∧
      rlpItemDecodeStrictW bytes base cursorOff
        r.next ((base + BitVec.ofNat 64 endOff) - base).toNat r.len (floor + 1) := by
      rcases hRF with hOK | hbad
      · exact ⟨hOK.2.1, hOK.2.2⟩
      · exact absurd hstatus hbad
    have hKnext := hfacts.1
    have hitem0 := hfacts.2
    have hcur : r.cursor = base + BitVec.ofNat 64 r.next := hpin hstatus
    have hpay : PayloadStrictFuel bytes base floor (endOff - r.next) r.next endOff :=
      hKnext.2.2
    have hwin : endOff ≤ bytes.length := payloadStrictFuel_window hpay
    have hnext_le : r.next ≤ endOff := payloadStrictFuel_cursor_le hpay
    have hoverEnd : base.toNat + endOff < 2 ^ 64 := by omega
    have hcursub : (r.cursor - base).toNat = r.next := by
      rw [hcur]; exact sub_base_of_base_add hnext_le hoverEnd
    have hendsub : ((base + BitVec.ofNat 64 endOff) - base).toNat = endOff :=
      sub_base_of_base_add (le_refl endOff) hoverEnd
    have hitem : rlpItemDecodeStrictW bytes base cursorOff r.next endOff r.len
        (floor + 1) := by
      simpa [hendsub] using hitem0
    -- Register-form ValidateK / decode (what the zero-loop consumes).
    have hK : ValidateK bytes base floor r.cursor
        (base + BitVec.ofNat 64 endOff) r.next endOff (endOff - r.next) := by
      rw [hcur]; exact hKnext
    have hdecode : rlpItemDecodeStrictW bytes base cursorOff
        (r.cursor - base).toNat
        ((base + BitVec.ofNat 64 endOff) - base).toNat r.len (floor + 1) := by
      simpa [hcursub, hendsub] using hitem
    have hloop := validateLoopContinuation_inhabited bytes base floor r.next endOff
      (endOff - r.next)
    have hzero := validate_nested_success_zero_loop_indexed
      (bytes := bytes) (base := base) (floor := floor) (cursor := cursorOff)
      (next := r.next) (endOff := endOff) (a0 := r.cursor)
      (endPtr := base + BitVec.ofNat 64 endOff) (a2 := r.len) (status := r.status)
      hnext_le hwin hitem hKnext hloop hover rfl hdecode hstatus
      sp (validateEntry + 40) raVal (base + BitVec.ofNat 64 cursorOff)
    have hframed := cpsTripleWithin_frameR
      ((regIs .x12 r.len) ** bytesRegion base bytes **
        ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
        ⌜validateResultFacts bytes base floor cursorOff endOff fuel
          (base + BitVec.ofNat 64 endOff) r⌝ ** P)
      (by
        repeat first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_pure
          | exact hP
          | exact bytesRegion_pcFree _ _)
      hzero
    -- H (bare Shared resources) → zero-loop pre ** frame:
    -- re-inject hK and the already-peeled hRF.
    refine @cpsTripleWithin_weaken 5 (validateEntry + 40) (validateEntry + 16)
      validateCR
      (((regIs .x2 sp) ** (regIs .x10 r.cursor) ** (regIs .x11 r.status) **
        (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
        regOwn .x5 **
        (memIs sp raVal) **
        (memIs (sp + 8) (base + BitVec.ofNat 64 cursorOff)) **
        (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
        ⌜ValidateK bytes base floor r.cursor
          (base + BitVec.ofNat 64 endOff) r.next endOff (endOff - r.next)⌝) **
        ((regIs .x12 r.len) ** bytesRegion base bytes **
          ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
          ⌜validateResultFacts bytes base floor cursorOff endOff fuel
            (base + BitVec.ofNat 64 endOff) r⌝ ** P))
      H Post Post ?hre (fun _ h => h) ?hcore
    case hre =>
      intro hp h
      simp only [H, validateKnotFrameSlots] at h
      -- Inject ValidateK then validateResultFacts as leading pures, then permute.
      have h1 := (sepConj_pure_left hp).2 ⟨hK, h⟩
      have h2 := (sepConj_pure_left hp).2 ⟨hRF, h1⟩
      xperm_chunked h2
    case hcore =>
      refine cpsTripleWithin_weaken (fun _ h => h) ?_ hframed
      intro hp h
      simp only [Post, validateKnotZeroReloadPre]
      xperm_chunked h

/-- From remaining-empty `ValidateK`, the live cursor pointer equals `endPtr`. -/
theorem validateK_of_empty_next
    {bytes : List (BitVec 8)} {base : Word} {floor : Nat}
    {cursorPtr endPtr : Word} {next endOff fuel : Nat}
    (hK : ValidateK bytes base floor cursorPtr endPtr next endOff fuel)
    (heq : next = endOff) :
    cursorPtr = endPtr := by
  rcases hK with ⟨hcur, hend, _⟩
  subst heq
  rw [hcur, hend]

/-- Machine core of the empty-remaining ZeroReload, `hcur` explicit.
`V+16` loads → equality branch taken (cursor = endPtr) → success epilogue.
`x1 = V+40` incoming is dead (epilogue reloads `ra` from `sp+0` before `JALR`),
so the return still lands at outer `raVal` (#12419). -/
theorem validateKnotCont_zero_reload_empty_core
    (sp raVal r_cursor r_len endPtr : Word)
    (hcur : r_cursor = endPtr) :
    cpsTripleWithin 8 (validateEntry + 16) (raVal &&& ~~~1) validateCR
      ((regIs .x2 sp) ** (regIs .x10 r_cursor) ** (regIs .x11 (0 : Word)) **
        (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
        (regIs .x5 endPtr) ** (regIs .x12 r_len) **
        (memIs sp raVal) ** (memIs (sp + 8) r_cursor) **
        (memIs (sp + 16) endPtr))
      ((regIs .x2 (sp + 32)) ** (regIs .x10 (0 : Word)) **
        (regIs .x1 raVal) ** (regIs .x5 endPtr) ** (regIs .x11 endPtr) **
        (regIs .x12 r_len) ** (regIs .x0 (0 : Word)) **
        (memIs sp raVal) ** (memIs (sp + 8) r_cursor) **
        (memIs (sp + 16) endPtr)) := by
  have hload0 := validate_loads_cps sp r_cursor endPtr endPtr (0 : Word)
  have hload := cpsTripleWithin_frameR
    ((regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
      (regIs .x12 r_len) ** (memIs sp raVal))
    (by pcf_validate_cps) hload0
  have hbr := validate_empty_branch_cps r_cursor endPtr
  have htaken0 := cpsBranchWithin_takenStripPure2 hbr (by
    intro hp hq
    have hleft := (sepConj_assoc hp).mpr hq
    obtain ⟨_, _, _, _, _, hpure⟩ := hleft
    exact hpure.2 hcur)
  have htaken := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x11 endPtr) **
      (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
      (regIs .x12 r_len) ** (memIs sp raVal) **
      (memIs (sp + 8) r_cursor) ** (memIs (sp + 16) endPtr))
    (by pcf_validate_cps) htaken0
  have htail0 :=
    validate_success_tail_cps sp (validateEntry + 40) raVal r_cursor endPtr
  have htail := cpsTripleWithin_frameR
    ((regIs .x12 r_len) ** (regIs .x0 (0 : Word)))
    (by pcf_validate_cps) htail0
  have h1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hload htaken
  have h2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h1 htail
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) h2)

/-- Machine core of the nonempty-remaining ZeroReload prefix: `V+16` loads →
equality branch NOT taken (`cursor ≠ endPtr`) → precheck NOT taken
(`¬ endPtr.ult cursor`) → knot entry `V+36`.

Lands on `validateKnotLoopBackFrame` (not the entry-shaped `validateKnotFrame`):
`x1 = V+40` while `memIs sp` holds the outer `raVal`.  The nested JAL at
`V+36` rewrites `x1` to `V+40` anyway, so the incoming `x1 = V+40` is live
only as ownership of the register until the JAL (#12419). -/
theorem validateKnotCont_zero_reload_nonempty_to_knot_core
    (sp raVal r_cursor r_len endPtr : Word)
    (hne : r_cursor ≠ endPtr)
    (horder : endPtr.ult r_cursor ≠ true) :
    cpsTripleWithin 5 (validateEntry + 16) (validateEntry + 36) validateCR
      ((regIs .x2 sp) ** (regIs .x10 r_cursor) ** (regIs .x11 (0 : Word)) **
        (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
        (regIs .x5 endPtr) ** (regIs .x12 r_len) **
        (memIs sp raVal) ** (memIs (sp + 8) r_cursor) **
        (memIs (sp + 16) endPtr))
      (validateKnotLoopBackFrame sp raVal r_cursor endPtr **
        (regIs .x0 (0 : Word)) ** (regIs .x12 r_len)) := by
  have hload0 := validate_loads_cps sp r_cursor endPtr endPtr (0 : Word)
  have hload := cpsTripleWithin_frameR
    ((regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
      (regIs .x12 r_len) ** (memIs sp raVal))
    (by pcf_validate_cps) hload0
  have hempty := validate_empty_branch_cps r_cursor endPtr
  have hntakenEmpty0 := cpsBranchWithin_ntakenStripPure2 hempty (by
    intro _ hQt
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
    exact absurd ((sepConj_pure_right _).mp h_rest).2 hne)
  have hntakenEmpty := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x11 endPtr) **
      (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
      (regIs .x12 r_len) ** (memIs sp raVal) **
      (memIs (sp + 8) r_cursor) ** (memIs (sp + 16) endPtr))
    (by pcf_validate_cps) hntakenEmpty0
  have hpre := validate_precheck_branch_cps r_cursor endPtr
  have hntakenPre0 := cpsBranchWithin_ntakenStripPure2 hpre (by
    intro _ hQt
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
    exact absurd ((sepConj_pure_right _).mp h_rest).2 horder)
  have hntakenPre := cpsTripleWithin_frameR
    ((regIs .x2 sp) ** (regIs .x11 endPtr) **
      (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
      (regIs .x12 r_len) ** (memIs sp raVal) **
      (memIs (sp + 8) r_cursor) ** (memIs (sp + 16) endPtr))
    (by pcf_validate_cps) hntakenPre0
  have s1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hload hntakenEmpty
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s1 hntakenPre
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by
        simp only [validateKnotLoopBackFrame, validateKnotFrameRest]
        xperm_hyp hp) s2)

/-- Empty-remaining discharge of `ValidateKnotContZeroReloadGoal` (no IH). -/
theorem validateKnotCont_zero_reload_empty
    {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {contCode : CodeReq}
    (sp raVal exit_ : Word) (r : ValidateResult)
    (hstatus : r.status = 0)
    (heq : r.next = endOff)
    (hK : ValidateK bytes base floor r.cursor
      (base + BitVec.ofNat 64 endOff) r.next endOff (endOff - r.next))
    (hP : P.pcFree)
    (hexit : exit_ = raVal &&& ~~~(1 : Word))
    (hsub : ∀ a i, validateCR a = some i → contCode a = some i) :
    cpsTripleWithin 8 (validateEntry + 16) exit_ contCode
      (validateKnotZeroReloadPre bytes base floor fuel cursorOff endOff
        sp raVal P r)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  have hcur : r.cursor = base + BitVec.ofNat 64 endOff :=
    validateK_of_empty_next hK heq
  have hcore := validateKnotCont_zero_reload_empty_core sp raVal r.cursor r.len
    (base + BitVec.ofNat 64 endOff) hcur
  have hpcP :
      (⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
        ⌜validateResultFacts bytes base floor cursorOff endOff fuel
          (base + BitVec.ofNat 64 endOff) r⌝ **
        bytesRegion base bytes ** P).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_pure
      | exact hP
      | exact bytesRegion_pcFree _ _
  have hframed := cpsTripleWithin_frameR _ hpcP hcore
  have hres :
      cpsTripleWithin 8 (validateEntry + 16) (raVal &&& ~~~1) validateCR
        (validateKnotZeroReloadPre bytes base floor fuel cursorOff endOff
          sp raVal P r)
        (validateCyclePost bytes base floor fuel cursorOff endOff
          sp raVal P) := by
    refine cpsTripleWithin_weaken ?_ ?_ hframed
    · intro hp h
      simp only [validateKnotZeroReloadPre] at h
      extract_pure_deep h
      obtain ⟨⟨⟨_hVK, hVF⟩, hRF⟩, hres⟩ := h
      xperm_pure hres
    · intro hp h
      refine ⟨r, ?_⟩
      simp only [validateResultPost, hstatus, hcur] at h ⊢
      simp only [sepConj_assoc] at h
      have h5 := sepConj_mono_left (regIs_to_regOwn .x5
          (base + BitVec.ofNat 64 endOff)) hp
        (show ((regIs .x5 (base + BitVec.ofNat 64 endOff)) **
            ((regIs .x2 (sp + 32)) ** (regIs .x10 (0 : Word)) **
              (regIs .x1 raVal) ** (regIs .x11 (base + BitVec.ofNat 64 endOff)) **
              (regIs .x12 r.len) ** (regIs .x0 (0 : Word)) **
              (memIs sp raVal) ** (memIs (sp + 8) (base + BitVec.ofNat 64 endOff)) **
              (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
              ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
              ⌜validateResultFacts bytes base floor cursorOff endOff fuel
                (base + BitVec.ofNat 64 endOff) r⌝ **
              bytesRegion base bytes ** P)) hp from by xperm_chunked h)
      have h6 := sepConj_mono_left memIs_implies_memOwn hp
        (show ((memIs (sp + 8) (base + BitVec.ofNat 64 endOff)) **
            ((regOwn .x5) ** (regIs .x2 (sp + 32)) ** (regIs .x10 (0 : Word)) **
              (regIs .x1 raVal) ** (regIs .x11 (base + BitVec.ofNat 64 endOff)) **
              (regIs .x12 r.len) ** (regIs .x0 (0 : Word)) **
              (memIs sp raVal) **
              (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
              ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
              ⌜validateResultFacts bytes base floor cursorOff endOff fuel
                (base + BitVec.ofNat 64 endOff) r⌝ **
              bytesRegion base bytes ** P)) hp from by xperm_chunked h5)
      -- `x12` (nested call's last-child len) is dead: weaken to `regOwn` for the
      -- corrected `validateResultPost` (#12419).
      have h7 := sepConj_mono_left (regIs_to_regOwn .x12 r.len) hp
        (show ((regIs .x12 r.len) **
            ((memOwn (sp + 8)) **
              (regOwn .x5) ** (regIs .x2 (sp + 32)) ** (regIs .x10 (0 : Word)) **
              (regIs .x1 raVal) ** (regIs .x11 (base + BitVec.ofNat 64 endOff)) **
              (regIs .x0 (0 : Word)) **
              (memIs sp raVal) **
              (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
              ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
              ⌜validateResultFacts bytes base floor cursorOff endOff fuel
                (base + BitVec.ofNat 64 endOff) r⌝ **
              bytesRegion base bytes ** P)) hp from by xperm_chunked h6)
      xperm_chunked h7
  simpa [hexit] using cpsTripleWithin_extend_code hsub hres

/-- Empty-remaining ZeroReload as a goal alias. -/
def ValidateKnotContZeroReloadEmptyGoal
    (bytes : List (BitVec 8)) (base : Word) (floor fuel cursorOff endOff : Nat)
    (sp raVal exit_ : Word) (contCode : CodeReq) (P : Assertion) : Prop :=
  ∀ r, r.status = 0 → r.next = endOff →
    ValidateK bytes base floor r.cursor
      (base + BitVec.ofNat 64 endOff) r.next endOff (endOff - r.next) →
    P.pcFree → exit_ = raVal &&& ~~~(1 : Word) →
    (∀ a i, validateCR a = some i → contCode a = some i) →
    cpsTripleWithin 8 (validateEntry + 16) exit_ contCode
      (validateKnotZeroReloadPre bytes base floor fuel cursorOff endOff
        sp raVal P r)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)

theorem validateKnotCont_zero
    {nReload : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {contCode : CodeReq}
    (sp raVal exit_ : Word) (r : ValidateResult)
    (hstatus : r.status = 0)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64)
    (hP : P.pcFree)
    (hsub : ∀ a i, validateCR a = some i → contCode a = some i)
    (hreload : ValidateKnotContZeroReloadGoal bytes base floor fuel cursorOff
      endOff sp raVal exit_ contCode P nReload) :
    cpsTripleWithin (5 + nReload) (validateEntry + 40) exit_ contCode
      (validateKnotSharedPost bytes base floor fuel cursorOff endOff
        sp raVal P r)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  have hto : ValidateKnotContZeroToReloadGoal bytes base floor fuel cursorOff
      endOff sp raVal P r := validateKnotCont_zero_to_reload sp raVal r
  have hto' := cpsTripleWithin_extend_code hsub
    (hto hstatus hover hnowrap hP)
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hto' (hreload r hstatus)

theorem validateKnotContGoal_of_status
    {nZero : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {contCode : CodeReq}
    (sp raVal exit_ : Word)
    (hnz : ∀ r, r.status ≠ 0 →
      cpsTripleWithin 5 (validateEntry + 40) exit_ contCode
        (validateKnotSharedPost bytes base floor fuel cursorOff endOff
          sp raVal P r)
        (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P))
    (hz : ∀ r, r.status = 0 →
      cpsTripleWithin nZero (validateEntry + 40) exit_ contCode
        (validateKnotSharedPost bytes base floor fuel cursorOff endOff
          sp raVal P r)
        (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)) :
    ValidateKnotContGoal bytes base floor fuel cursorOff endOff
      sp raVal exit_ contCode P (Nat.max 5 nZero) := by
  intro r
  by_cases h : r.status = 0
  · exact cpsTripleWithin_mono_nSteps (Nat.le_max_right _ _) (hz r h)
  · exact cpsTripleWithin_mono_nSteps (Nat.le_max_left _ _) (hnz r h)

/-! ## Remaining-window → outer `validateCyclePost` bridge (DERIVED)

`ValidateKnotContZeroReloadGoal` at window `(cursorOff, endOff)` posts the
OUTER `validateCyclePost`.  Nonempty remaining re-enters the knot at
`(nextOff, endOff)` whose standard body posts the REMAINING cycle post.
The two `validateCyclePost` bodies are IDENTICAL except for two pure
sub-assertions — `⌜ValidateFuel ..⌝` and the `⌜validateResultFacts ..⌝` inside
`validateResultPost` — and the choice of the existential result `r`.  Every
resource atom (registers `x2/x1/x0`, `memIs sp`, `memOwn (sp+8)`,
`memIs (sp+16)`, `regOwn .x5`, `bytesRegion`, `regOwn .x12`, and the tail `P`)
coincides.

FINDING probed before baking, then RESOLVED: coord's hypothesis was that an
unconditioned bridge is only false because a later-sibling failure leaves
`x10 = 7` while the first-item-success shape wants `x10 = 0`; and that because
`validateCyclePost` is existential in `r`, the outer post may simply CHOOSE the
outcome the machine actually produced.  Confirmed, AND it generalises: since
`validateResultFacts` was decoupled to `r.next` (it never reads `r.cursor`),
the outer existential can reuse the destructed remaining witness's own
`status`/`cursor` verbatim — so `regIs x10 r.status` and `regIs x11 r.cursor`
transfer with NO rewrite, on BOTH arms:

* remaining SUCCESS (`r.status = 0`): pick `rOut` with the FIRST item's
  `next`/`len` (from ZeroReloadPre `rOuter`) but `r`'s own `status`/`cursor`.
  `validateResultFacts` reads only `.status`/`.next`/`.len`, so the outer facts
  come straight from `hRFo`.  `x11 = r.cursor` is left as whatever the machine
  produced (endPtr on full success) — the decouple means we need not prove it
  equals endPtr, which is why the earlier `rRem.cursor = endPtr` hypothesis was
  spurious.
* remaining FAILURE (`r.status ≠ 0`): pick `rOut := r`; outer
  `validateResultFacts` is the right disjunct `r.status ≠ 0`, trivially true.

So there is NO failure-only residual and NO post change: the whole bridge is a
window re-index witnessed by `hVF` (outer `ValidateFuel`, from ZeroReloadPre)
plus per-outcome result selection.  This is a strengthening-free indexing
correction, not a weaken (#12419). -/
theorem validateCyclePost_reindex_window
    {bytes : List (BitVec 8)} {base : Word}
    {floor fuel fuel' cursorOff nextOff endOff : Nat}
    {sp raVal : Word} {P : Assertion} (rOuter : ValidateResult)
    (hstatusO : rOuter.status = 0)
    (hVF : ValidateFuel bytes fuel cursorOff endOff)
    (hRFo : validateResultFacts bytes base floor cursorOff endOff fuel
      (base + BitVec.ofNat 64 endOff) rOuter) :
    ∀ hp, (validateCyclePost bytes base floor fuel' nextOff endOff sp raVal P) hp →
          (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) hp := by
  intro hp hrem
  simp only [validateCyclePost, validateResultPost] at hrem ⊢
  obtain ⟨r, hb⟩ := hrem
  by_cases hs : r.status = 0
  · -- SUCCESS: first-item next/len, r's own status/cursor
    refine ⟨{ next := rOuter.next, cursor := r.cursor,
              status := r.status, len := rOuter.len }, ?_⟩
    have hRFout : validateResultFacts bytes base floor cursorOff endOff fuel
        (base + BitVec.ofNat 64 endOff)
        { next := rOuter.next, cursor := r.cursor,
          status := r.status, len := rOuter.len } := by
      simp only [validateResultFacts] at hRFo ⊢
      rcases hRFo with ⟨_, hvk, hdec⟩ | hne
      · exact Or.inl ⟨hs, hvk, hdec⟩
      · exact absurd hstatusO hne
    exact
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (fun _ hx => ⟨hx.1, hVF⟩)
              (sepConj_mono_left
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (fun _ hx => ⟨hx.1, hRFout⟩)))))))))))))) hp hb
  · -- FAILURE: reuse remaining witness; facts are the trivial right disjunct
    refine ⟨r, ?_⟩
    have hRFout : validateResultFacts bytes base floor cursorOff endOff fuel
        (base + BitVec.ofNat 64 endOff) r := by
      simp only [validateResultFacts]; exact Or.inr hs
    exact
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (fun _ hx => ⟨hx.1, hVF⟩)
              (sepConj_mono_left
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (fun _ hx => ⟨hx.1, hRFout⟩)))))))))))))) hp hb

/-! ## Own `ValidateKnotContZeroReloadGoal` from a knot-body IH

The loop-back lands at `V+36` with `validateKnotLoopBackFrame` (`x1 = V+40`).
The induction family's recursive surface must therefore be a knot-body contract
at that altitude — not the full-entry `ValidateMachineContract` (#12419
IH-altitude finding).  `ValidateKnotBodyRemainingGoal` is that surface for one
remaining window.  Owning ZeroReload = empty arm (banked) ∪ nonempty
(nonempty_to_knot ∘ body-IH ∘ reindex); the nonempty composition is the named
residual below, with the IH premise EXPLICIT. -/

/-- Knot-body triple at the REMAINING window `(nextOff, endOff)`, with incoming
`x1 = validateEntry + 40` (loop-back).  This is the IH surface ZeroReload's
nonempty arm consumes — same altitude as `validateKnotLoopBackFrame`.
`regOwn .x12` is required in the pre: the body writes `x12`, and a CPS post
cannot manufacture a register the pre never owned (#12419 / #12464). -/
def ValidateKnotBodyRemainingGoal
    (bytes : List (BitVec 8)) (base : Word)
    (floor fuel' nextOff endOff : Nat)
    (sp raVal exit_ : Word) (contCode : CodeReq) (P : Assertion)
    (nKnot : Nat) : Prop :=
  ValidateFuel bytes fuel' nextOff endOff →
  P.pcFree →
  exit_ = raVal &&& ~~~(1 : Word) →
  (∀ a i, validateCR a = some i → contCode a = some i) →
  cpsTripleWithin nKnot (validateEntry + 36) exit_ contCode
    (((regIs .x1 (validateEntry + 40)) **
      validateKnotFrameRest sp raVal
        (base + BitVec.ofNat 64 nextOff)
        (base + BitVec.ofNat 64 endOff)) **
      (regIs .x0 (0 : Word)) ** regOwn .x12 **
      bytesRegion base bytes **
      ⌜ValidateFuel bytes fuel' nextOff endOff⌝ ** P)
    (validateCyclePost bytes base floor fuel' nextOff endOff sp raVal P)

/-- Nonempty ZeroReload composition residual: `V+16 → V+36` (banked
`nonempty_to_knot_core`) ∘ knot-body IH at remaining fuel ∘
`validateCyclePost_reindex_window`.  IH premise is EXPLICIT
(`ValidateKnotBodyRemainingGoal`). -/
def ValidateKnotContZeroReloadNonemptyOfBodyGoal
    (bytes : List (BitVec 8)) (base : Word)
    (floor fuel cursorOff endOff : Nat)
    (sp raVal exit_ : Word) (contCode : CodeReq) (P : Assertion)
    (nKnot : Nat) (r : ValidateResult) : Prop :=
  r.status = 0 →
  r.next < endOff →
  ValidateK bytes base floor r.cursor
    (base + BitVec.ofNat 64 endOff) r.next endOff (endOff - r.next) →
  ValidateFuel bytes fuel cursorOff endOff →
  validateResultFacts bytes base floor cursorOff endOff fuel
    (base + BitVec.ofNat 64 endOff) r →
  ValidateFuel bytes (cycleFuel r.next endOff) r.next endOff →
  base.toNat + bytes.length < 2 ^ 64 →
  P.pcFree →
  exit_ = raVal &&& ~~~(1 : Word) →
  (∀ a i, validateCR a = some i → contCode a = some i) →
  ValidateKnotBodyRemainingGoal bytes base floor
    (cycleFuel r.next endOff) r.next endOff sp raVal exit_ contCode P nKnot →
  cpsTripleWithin (5 + nKnot) (validateEntry + 16) exit_ contCode
    (validateKnotZeroReloadPre bytes base floor fuel cursorOff endOff
      sp raVal P r)
    (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)

/-- DERIVED discharge of `ValidateKnotContZeroReloadNonemptyOfBodyGoal`. -/
theorem validateKnotCont_zero_reload_nonempty_of_body
    {nKnot : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {contCode : CodeReq}
    (sp raVal exit_ : Word) (r : ValidateResult) :
    ValidateKnotContZeroReloadNonemptyOfBodyGoal bytes base floor fuel
      cursorOff endOff sp raVal exit_ contCode P nKnot r := by
  intro hstatus hlt hK hVF hRF hVFrem hover hP hexit hsub hbodyG
  have hcur : r.cursor = base + BitVec.ofNat 64 r.next := hK.1
  have hwin : endOff ≤ bytes.length := payloadStrictFuel_window hK.2.2
  have hnext_le : r.next ≤ endOff := Nat.le_of_lt hlt
  have hoverEnd : base.toNat + endOff < 2 ^ 64 := by omega
  have hne : r.cursor ≠ base + BitVec.ofNat 64 endOff := by
    rw [hcur]; intro heq
    have hn : (base + BitVec.ofNat 64 r.next - base).toNat =
        (base + BitVec.ofNat 64 endOff - base).toNat := by
      simp only [heq]
    rw [sub_base_of_base_add hnext_le hoverEnd,
      sub_base_of_base_add (le_refl endOff) hoverEnd] at hn
    exact Nat.ne_of_lt hlt hn
  have horder : (base + BitVec.ofNat 64 endOff).ult r.cursor ≠ true := by
    rw [hcur]
    intro hult
    exact absurd
      ((ult_base_add_ofNat (bound := bytes.length) hwin
        (le_trans hnext_le hwin) hover).mp hult)
      (Nat.not_lt_of_ge hnext_le)
  have hcore0 := validateKnotCont_zero_reload_nonempty_to_knot_core
    sp raVal r.cursor r.len (base + BitVec.ofNat 64 endOff) hne horder
  -- Ambient carried through the core into the body: remaining VF (body needs
  -- it), outer VF+RF (reindex needs them), bytes, P.
  let remFuel : Nat := cycleFuel r.next endOff
  let ambient : Assertion :=
    (bytesRegion base bytes **
      ⌜ValidateFuel bytes remFuel r.next endOff⌝ **
      ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
      ⌜validateResultFacts bytes base floor cursorOff endOff fuel
        (base + BitVec.ofNat 64 endOff) r⌝ ** P)
  have hpcA : ambient.pcFree := by
    simp only [ambient]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_pure
      | exact hP
      | exact bytesRegion_pcFree _ _
  have hcore := cpsTripleWithin_frameR ambient hpcA hcore0
  -- Body pre (loop-back at remaining window) ** outer pures for reindex.
  let bodyPre : Assertion :=
    (((regIs .x1 (validateEntry + 40)) **
      validateKnotFrameRest sp raVal
        (base + BitVec.ofNat 64 r.next)
        (base + BitVec.ofNat 64 endOff)) **
      (regIs .x0 (0 : Word)) ** regOwn .x12 **
      bytesRegion base bytes **
      ⌜ValidateFuel bytes remFuel r.next endOff⌝ ** P)
  let outerPures : Assertion :=
    (⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
      ⌜validateResultFacts bytes base floor cursorOff endOff fuel
        (base + BitVec.ofNat 64 endOff) r⌝)
  have htoBody : cpsTripleWithin 5 (validateEntry + 16) (validateEntry + 36)
      validateCR
      (((regIs .x2 sp) ** (regIs .x10 r.cursor) ** (regIs .x11 (0 : Word)) **
        (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
        (regIs .x5 (base + BitVec.ofNat 64 endOff)) **
        (regIs .x12 r.len) **
        (memIs sp raVal) ** (memIs (sp + 8) r.cursor) **
        (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) ** ambient))
      (bodyPre ** outerPures) := by
    refine cpsTripleWithin_weaken ?_ ?_ hcore
    · intro hp h; simp only [ambient] at h ⊢; xperm_chunked h
    · intro hp h
      simp only [validateKnotLoopBackFrame, validateKnotFrameRest, ambient,
        bodyPre, outerPures, hcur] at h ⊢
      have h1 :
          ((regIs .x12 r.len) **
            ((regIs .x1 (validateEntry + 40)) **
              (regIs .x2 sp) **
              (regIs .x10 (base + BitVec.ofNat 64 r.next)) **
              (regIs .x5 (base + BitVec.ofNat 64 endOff)) **
              (regIs .x11 (base + BitVec.ofNat 64 endOff)) **
              (memIs sp raVal) **
              (memIs (sp + 8) (base + BitVec.ofNat 64 r.next)) **
              (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
              (regIs .x0 (0 : Word)) ** bytesRegion base bytes **
              ⌜ValidateFuel bytes remFuel r.next endOff⌝ **
              ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
              ⌜validateResultFacts bytes base floor cursorOff endOff fuel
                (base + BitVec.ofNat 64 endOff) r⌝ ** P)) hp := by
        xperm_chunked h
      have h2 := sepConj_mono_left (regIs_to_regOwn .x12 r.len) hp h1
      xperm_chunked h2
  have htoBodyCode := cpsTripleWithin_extend_code hsub htoBody
  -- Body IH at remaining window (ValidateFuel / cyclePost at `cycleFuel`).
  have hbodyT : cpsTripleWithin nKnot (validateEntry + 36) exit_ contCode
      bodyPre
      (validateCyclePost bytes base floor remFuel r.next endOff
        sp raVal P) := by
    simpa [bodyPre, remFuel] using hbodyG hVFrem hP hexit hsub
  have hbodyFramed := cpsTripleWithin_frameR outerPures
    (by simp only [outerPures]; apply pcFree_sepConj <;> exact pcFree_pure)
    hbodyT
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) htoBodyCode hbodyFramed
  -- Reindex remaining → outer under the framed outer pures.
  have hreindex :=
    @validateCyclePost_reindex_window bytes base floor fuel
      remFuel cursorOff r.next endOff sp raVal P r
      hstatus hVF hRF
  refine cpsTripleWithin_weaken ?_ ?_ hseq
  · -- ZeroReloadPre → core resource pre ** ambient (inject remaining VF).
    intro hp h
    simp only [validateKnotZeroReloadPre, ambient] at h ⊢
    extract_pure_deep h
    obtain ⟨⟨⟨_hVK, hVF⟩, hRF⟩, hres⟩ := h
    -- `hVFrem`/`hVF`/`hRF` are ambient; `xperm_pure` reinserts them into the
    -- target (same pattern as empty ZeroReload, plus remaining-fuel pure).
    xperm_pure hres
  · -- remaining cyclePost ** outerPures → outer cyclePost.
    intro hp h
    simp only [outerPures] at h
    -- `**` is right-assoc: cyclePost ** (⌜VF⌝ ** ⌜RF⌝); assoc.mpr then peel.
    have h1 := (sepConj_assoc hp).2 h
    have hmid := ((sepConj_pure_right _).1 h1).1
    exact hreindex hp ((sepConj_pure_right _).1 hmid).1

/-! ## Own `ValidateKnotContZeroReloadGoal` (empty ∪ nonempty)

`ValidateKnotContZeroReloadGoal` is `∀ r, status=0 → triple(ZeroReloadPre,…)`.
The Pre embeds `ValidateK` / outer `ValidateFuel` / `validateResultFacts` as
pures; a local `cpsTripleWithin_pure_pre` peels them so the banked empty and
nonempty dischargers apply.  Remaining-window `ValidateFuel` is NOT in
ZeroReloadPre — it is an explicit induction-side premise (same altitude as the
knot-body IH), discharged by the fuel family at `cycleFuel nextOff endOff`. -/

/-- Own ZeroReload from empty ∪ nonempty_of_body.  IH + remaining VF are EXPLICIT.

NOTE: the induction builder must only instantiate these at *advancing*
`nextOff` (`cursorOff < nextOff`), which is what `cycleFuel_strict_of_advance`
requires.  The Prop quantifies `nextOff < endOff` for statement simplicity;
non-advancing instantiations are not usable at smaller fuel (and success
decode forces advance — lemma residual `validateResultFacts_success_advances`). -/
def ValidateKnotContZeroReloadOfBodyGoal
    (bytes : List (BitVec 8)) (base : Word)
    (floor fuel cursorOff endOff : Nat)
    (sp raVal exit_ : Word) (contCode : CodeReq) (P : Assertion)
    (nKnot : Nat) : Prop :=
  (∀ nextOff, nextOff < endOff →
    ValidateFuel bytes (cycleFuel nextOff endOff) nextOff endOff) →
  (∀ nextOff, nextOff < endOff →
    ValidateKnotBodyRemainingGoal bytes base floor
      (cycleFuel nextOff endOff) nextOff endOff sp raVal exit_ contCode P nKnot) →
  base.toNat + bytes.length < 2 ^ 64 →
  P.pcFree →
  exit_ = raVal &&& ~~~(1 : Word) →
  (∀ a i, validateCR a = some i → contCode a = some i) →
  ValidateKnotContZeroReloadGoal bytes base floor fuel cursorOff endOff
    sp raVal exit_ contCode P (Nat.max 8 (5 + nKnot))

/-- DERIVED: empty ∪ `nonempty_of_body` ⇒ `ValidateKnotContZeroReloadGoal`. -/
theorem validateKnotCont_zero_reload_of_body
    {nKnot : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {contCode : CodeReq}
    (sp raVal exit_ : Word) :
    ValidateKnotContZeroReloadOfBodyGoal bytes base floor fuel cursorOff endOff
      sp raVal exit_ contCode P nKnot := by
  intro hVFremAll hbodyAll hover hP hexit hsub r hstatus
  let H : Assertion :=
    ((regIs .x2 sp) ** (regIs .x10 r.cursor) ** (regIs .x11 (0 : Word)) **
      (regIs .x0 (0 : Word)) ** (regIs .x1 (validateEntry + 40)) **
      (regIs .x5 (base + BitVec.ofNat 64 endOff)) **
      (regIs .x12 r.len) **
      (memIs sp raVal) ** (memIs (sp + 8) r.cursor) **
      (memIs (sp + 16) (base + BitVec.ofNat 64 endOff)) **
      bytesRegion base bytes ** P)
  let peeled : Assertion :=
    (⌜ValidateK bytes base floor r.cursor
        (base + BitVec.ofNat 64 endOff) r.next endOff (endOff - r.next)⌝ **
      ⌜ValidateFuel bytes fuel cursorOff endOff⌝ **
      ⌜validateResultFacts bytes base floor cursorOff endOff fuel
        (base + BitVec.ofNat 64 endOff) r⌝ ** H)
  let nReload : Nat := Nat.max 8 (5 + nKnot)
  let Pre : Assertion :=
    validateKnotZeroReloadPre bytes base floor fuel cursorOff endOff
      sp raVal P r
  let Post : Assertion :=
    validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P
  -- Permute ZeroReloadPre so the three pures are leading, then peel.
  refine @cpsTripleWithin_weaken nReload (validateEntry + 16) exit_ contCode
    peeled Pre Post Post ?hpre (fun _ h => h) ?hinner
  case hpre =>
    intro hp h
    simp only [Pre, validateKnotZeroReloadPre, peeled, H] at h ⊢
    xperm_chunked h
  case hinner =>
    refine cpsTripleWithin_pure_pre_left (fun hVK =>
      cpsTripleWithin_pure_pre_left (fun hVF =>
        cpsTripleWithin_pure_pre_left (fun hRF => ?_)))
    have hfull : cpsTripleWithin nReload (validateEntry + 16) exit_ contCode
        Pre Post := by
      by_cases hlt : r.next < endOff
      · have hVFrem := hVFremAll r.next hlt
        have hbodyG := hbodyAll r.next hlt
        have hne := validateKnotCont_zero_reload_nonempty_of_body
          (nKnot := nKnot) (bytes := bytes) (base := base)
          (floor := floor) (fuel := fuel) (cursorOff := cursorOff)
          (endOff := endOff) (P := P) (contCode := contCode)
          sp raVal exit_ r
        have ht := hne hstatus hlt hVK hVF hRF hVFrem hover hP hexit hsub hbodyG
        exact cpsTripleWithin_mono_nSteps (Nat.le_max_right _ _) ht
      · have hnext_le : r.next ≤ endOff :=
          payloadStrictFuel_cursor_le hVK.2.2
        have heq : r.next = endOff :=
          Nat.le_antisymm hnext_le (Nat.not_lt.mp hlt)
        have ht := validateKnotCont_zero_reload_empty
          (bytes := bytes) (base := base) (floor := floor) (fuel := fuel)
          (cursorOff := cursorOff) (endOff := endOff) (P := P)
          (contCode := contCode) sp raVal exit_ r
          hstatus heq hVK hP hexit hsub
        exact cpsTripleWithin_mono_nSteps (Nat.le_max_left _ _) ht
    -- Bare resources H → ZeroReloadPre by re-injecting peeled pures.
    refine @cpsTripleWithin_weaken nReload (validateEntry + 16) exit_ contCode
      Pre H Post Post ?hre (fun _ h => h) hfull
    case hre =>
      intro hp h
      simp only [Pre, validateKnotZeroReloadPre]
      xperm_pure h

/-! ## Third decrease confirmation + full-entry from knot-body

After the residual `ValidateFuel` index rewrite to `cycleFuel`: sibling advance
still strictly decreases the family index.  Confirmation only — not a new
decrease argument. -/

theorem zeroReload_remaining_cycleFuel_lt
    {cursor next endOff : Nat}
    (hcursor : cursor < next) (hend : next ≤ endOff) :
    cycleFuel next endOff < cycleFuel cursor endOff :=
  cycleFuel_strict_of_advance hcursor hend

/-- `ValidateKnotBodyRemainingGoal` is the loop-back instance (`x1 = V+40`) of
`validateKnotBodyPre`. -/
theorem validateKnotBodyRemainingGoal_of_contract
    {nKnot : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel' nextOff endOff : Nat} {P : Assertion}
    {contCode : CodeReq}
    (sp raVal exit_ : Word)
    (C : ValidateKnotBodyContract bytes base floor fuel' nextOff endOff
      sp raVal exit_ contCode P)
    (hsteps : C.steps = nKnot) :
    ValidateKnotBodyRemainingGoal bytes base floor fuel' nextOff endOff
      sp raVal exit_ contCode P nKnot := by
  intro _hVF _hP _hexit _hsub
  simpa [validateKnotBodyPre, validateKnotFrameRest, hsteps] using
    C.proof (validateEntry + 40)

/-- Derive full-entry `ValidateMachineContract.proof` from a knot-body contract
(once; not a parallel family). -/
theorem validateMachineContract_proof_of_knotBody
    {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {wholeCode : CodeReq}
    (sp raVal exit_ : Word)
    (hne : (base + BitVec.ofNat 64 cursorOff) ≠
      (base + BitVec.ofNat 64 endOff))
    (horder : (base + BitVec.ofNat 64 endOff).ult
      (base + BitVec.ofNat 64 cursorOff) ≠ true)
    (C : ValidateKnotBodyContract bytes base floor fuel cursorOff endOff
      sp raVal exit_ wholeCode P) :
    ∃ steps, cpsTripleWithin steps validateEntry exit_ wholeCode
      (validateCyclePre bytes base fuel cursorOff endOff sp raVal P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
  have hknot : cpsTripleWithin C.steps (validateEntry + 36) exit_ wholeCode
      (validateKnotFrame sp raVal
        (base + BitVec.ofNat 64 cursorOff)
        (base + BitVec.ofNat 64 endOff) **
        (regIs .x0 (0 : Word)) ** regOwn .x12 **
        bytesRegion base bytes **
        ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P) := by
    have hbody := C.proof raVal
    refine cpsTripleWithin_weaken ?_ (fun _ h => h) hbody
    · intro hp h
      simp only [validateKnotBodyPre, validateKnotFrame] at h ⊢
      xperm_chunked h
  exact validate_machine_proof_of_knot (nKnot := C.steps) (bytes := bytes)
    (base := base) (floor := floor) (fuel := fuel) (cursorOff := cursorOff)
    (endOff := endOff) (P := P) (wholeCode := wholeCode)
    sp raVal exit_ hne horder C.hP C.hvalidateSub hknot

/-! ## Fuel-indexed step budget at the knot altitudes (option 3, #12419)

The builder wall was ContGoal's UNIFORM `nCont` against a per-window recursive
`steps`.  With a monotone `KnotStepBudget` the uniformity is recovered without
weakening any statement: every child window at index `k ≤ fuel` lifts to the
single bound `bud.B fuel` (`knotBody_proof_at_bound`), so

* `of_body`'s single `nKnot` for ALL remaining windows  := `bud.B fuel`;
* ZeroReload's `nReload`                                := `max 8 (5 + bud.B fuel)`;
* ContGoal's `nCont`                                    := `max 5 (5 + nReload)`.

No asymmetry between the two altitudes (coord's question): both need exactly the
same fact — child index ≤ parent index ⇒ `B` child ≤ `B` parent ⇒
`cpsTripleWithin_mono_nSteps`.  `B` is a parameter exhibited by the builder, so
the budget stays derived bottom-up and composes upward. -/

/-- Uniform-bound instance of `validateKnotBodyRemainingGoal_of_contract`: a
bounded contract at ANY index `k ≤ fuel` discharges the IH surface at the single
bound `bud.B fuel`. -/
theorem validateKnotBodyRemainingGoal_of_bounded
    {bytes : List (BitVec 8)} {base : Word}
    {floor k fuel nextOff endOff : Nat} {P : Assertion}
    {contCode : CodeReq} {bud : KnotStepBudget}
    (sp raVal exit_ : Word)
    (C : ValidateKnotBodyContract bytes base floor k nextOff endOff
      sp raVal exit_ contCode P)
    (hsteps : C.steps ≤ bud.B k) (hk : k ≤ fuel) :
    ValidateKnotBodyRemainingGoal bytes base floor k nextOff endOff
      sp raVal exit_ contCode P (bud.B fuel) := by
  intro _hVF _hP _hexit _hsub
  simpa [validateKnotBodyPre, validateKnotFrameRest] using
    knotBody_proof_at_bound (bud := bud) C hsteps hk (validateEntry + 40)

/-- The IH surface for one *advancing* remaining window, at the uniform bound
`bud.B fuel`, taken from a bounded family below `fuel`.  `hadv` is where the
non-circularity lives: `cycleFuel_strict_of_advance` puts the child strictly
below the parent index. -/
theorem validateKnotBodyRemainingGoal_uniform_of_boundedFamily
    {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff nextOff endOff : Nat} {P : Assertion}
    {contCode : CodeReq} {bud : KnotStepBudget}
    (sp raVal exit_ : Word)
    (hfam : ∀ k, k < fuel →
      knotBodyBoundedFamily bytes base floor sp raVal exit_ contCode P bud k)
    (hfuel : fuel = cycleFuel cursorOff endOff)
    (hadv : cursorOff < nextOff) (hnext : nextOff ≤ endOff)
    (hwindow : endOff ≤ bytes.length)
    (hal : base.toNat % 8 = 0)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64)
    (hvalid : ∀ off, off < endOff →
      isValidByteAccess (base + BitVec.ofNat 64 off) = true)
    (hexit : exit_ = raVal &&& ~~~(1 : Word)) (hP : P.pcFree)
    (hsub : ∀ a i, validateCR a = some i → contCode a = some i) :
    ValidateKnotBodyRemainingGoal bytes base floor
      (cycleFuel nextOff endOff) nextOff endOff sp raVal exit_ contCode P
      (bud.B fuel) := by
  have hlt : cycleFuel nextOff endOff < fuel := by
    rw [hfuel]; exact cycleFuel_strict_of_advance hadv hnext
  obtain ⟨C, hsteps⟩ := hfam (cycleFuel nextOff endOff) hlt rfl hnext hwindow
    hal hover hnowrap hvalid hexit hP hsub
  exact validateKnotBodyRemainingGoal_of_bounded (bud := bud) sp raVal exit_ C
    hsteps (Nat.le_of_lt hlt)

/-- ContGoal at the CLOSED bound `max 5 (5 + max 8 (5 + bud.B fuel))`: uniform
in `r`.  Zero-arm `ValidateK`/decode are no longer inputs — they peel from the
Shared post's `validateResultFacts` + success-only cursor pin (#12419 (c)). -/
theorem validateKnotContGoal_of_bound
    {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat} {P : Assertion}
    {bud : KnotStepBudget}
    (sp raVal : Word)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64)
    (hP : P.pcFree)
    (hreload : ValidateKnotContZeroReloadGoal bytes base floor fuel cursorOff
      endOff sp raVal (raVal &&& ~~~(1 : Word)) validateCR P
      (Nat.max 8 (5 + bud.B fuel))) :
    ValidateKnotContGoal bytes base floor fuel cursorOff endOff
      sp raVal (raVal &&& ~~~(1 : Word)) validateCR P
      (Nat.max 5 (5 + Nat.max 8 (5 + bud.B fuel))) :=
  validateKnotContGoal_of_status sp raVal (raVal &&& ~~~(1 : Word))
    (fun r hnz => validateKnotCont_nonzero sp raVal r hnz hP)
    (fun r hz => validateKnotCont_zero sp raVal (raVal &&& ~~~(1 : Word)) r hz
      hover hnowrap hP (fun _ _ h => h) hreload)

/-! Classical-only axiom audit. -/
#print axioms validateKnotCont_zero_reload_empty
#print axioms validateKnotCont_zero_reload_nonempty_to_knot_core
#print axioms validateCyclePost_reindex_window
#print axioms validateKnotCont_zero_reload_nonempty_of_body
#print axioms validateKnotCont_zero_reload_of_body
#print axioms zeroReload_remaining_cycleFuel_lt
#print axioms validateKnotBodyRemainingGoal_of_contract
#print axioms validateKnotCont_nonzero
#print axioms validateLoopContinuation_inhabited
#print axioms validateKnotCont_zero_to_reload
#print axioms validateKnotCont_zero
#print axioms validateKnotContGoal_of_status
#print axioms validateMachineContract_proof_of_knotBody
#print axioms validateKnotBodyRemainingGoal_of_bounded
#print axioms validateKnotBodyRemainingGoal_uniform_of_boundedFamily
#print axioms validateKnotContGoal_of_bound

end EvmAsm.Codegen.RlpWalkNextStrictFuel
