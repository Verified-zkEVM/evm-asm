/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachineAltitude

  Altitude adapters for the repaired Shared/Validate knot.  The knot-body
  contract owns the nested Shared frame explicitly; this file lifts its
  bounded V+36 proof through the Validate entry while consuming that frame,
  and then packages the result for the caller-side ambient post.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachineCont

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-! A direct post bridge for the pinned Validate-entry precondition.  The
    existing bridge is intentionally generic over the two scratch registers;
    this copy keeps the pin visible at the producer boundary instead of
    weakening it back to `regOwn` before the caller sees it. -/
theorem validate_machine_proof_pinned_post_to_ambient
    {n : Nat} {bytes : List (BitVec 8)} {base : Word}
    {floor fuel cursorOff endOff : Nat}
    (spV sp raVal cursor outerNext outerStatus outerLen depth endPtr : Word)
    (x5Val x12Val : Word)
    (hsp : sp = spV + 32)
    (hra : raVal = RlpWalkNextStrictTie.S + 160)
    (hend : endPtr = base + BitVec.ofNat 64 endOff)
    (hproof : cpsTripleWithin n validateEntry
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      (validateCyclePrePinned bytes base fuel cursorOff endOff
        spV raVal x5Val x12Val
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth))
      (validateCyclePost bytes base floor fuel cursorOff endOff spV raVal
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth))) :
    cpsTripleWithin n validateEntry
      ((RlpWalkNextStrictTie.S + 160) &&& ~~~(1 : Word)) validateCR
      (validateCyclePrePinned bytes base fuel cursorOff endOff
        spV raVal x5Val x12Val
        (sharedValidateCallerRest sp raVal cursor outerNext outerStatus
          outerLen depth))
      (cpsDepPost (fun r =>
        sharedValidateCallerAmbient sp raVal cursor outerNext outerStatus
          outerLen depth **
          validateResultPost bytes base floor cursorOff endOff fuel endPtr r **
          validateCallerSlack spV **
          validatePreservedResources bytes base fuel cursorOff endOff)) := by
  have hpost := validateCyclePost_to_callerAmbient
    bytes base floor fuel cursorOff endOff spV sp raVal cursor outerNext
    outerStatus outerLen depth hsp hra
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ hproof
  intro hp h
  have h' := hpost hp h
  simpa [hend] using h'

/-! `knotBody_proof_at_bound` supplies one uniform V+36 bound for a child
    window.  The entry prologue is then sequenced around it with the
    repaired knot frame as an explicit ambient that is consumed by the body.
    The result is pinned at `x5`/`x12`, which is the form needed at the
    Shared→Validate call site. -/
theorem validate_machine_proof_pinned_of_bounded_knot_body
    {bytes : List (BitVec 8)} {base : Word}
    {floor k fuel cursorOff endOff : Nat} {P : Assertion}
    {wholeCode : CodeReq} {spV raVal exit_ : Word}
    {bud : KnotStepBudget}
    (C : ValidateKnotBodyContract bytes base floor k cursorOff endOff
      spV raVal exit_ wholeCode P)
    (hsteps : C.steps ≤ bud.B k) (hk : k ≤ fuel)
    (hne : (base + BitVec.ofNat 64 cursorOff) ≠
      (base + BitVec.ofNat 64 endOff))
    (horder : (base + BitVec.ofNat 64 endOff).ult
      (base + BitVec.ofNat 64 cursorOff) ≠ true)
    (hvalidateSub : ∀ a i, validateCR a = some i → wholeCode a = some i)
    (x5Val x12Val : Word) :
    ∃ steps, cpsTripleWithin steps validateEntry exit_ wholeCode
      (validateCyclePrePinned bytes base k cursorOff endOff
        spV raVal x5Val x12Val
        (validateKnotSharedFrame spV ** P))
      (validateCyclePost bytes base floor k cursorOff endOff spV raVal P) := by
  let cursor := base + BitVec.ofNat 64 cursorOff
  let endPtr := base + BitVec.ofNat 64 endOff
  let ambient : Assertion :=
    ((regIs .x0 (0 : Word)) ** regOwn .x12 **
      validateKnotSharedFrame spV ** bytesRegion base bytes **
      ⌜ValidateFuel bytes k cursorOff endOff⌝ ** P)
  have hAmbientPc : ambient.pcFree := by
    simp only [ambient]
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memOwn
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact C.hP
  have hbody := knotBody_proof_at_bound
    (bud := bud) C hsteps hk raVal
  have hknot : cpsTripleWithin (bud.B fuel) (validateEntry + 36)
      exit_ wholeCode
      (validateKnotFrame spV raVal cursor endPtr ** ambient)
      (validateCyclePost bytes base floor k cursorOff endOff spV raVal P) := by
    refine cpsTripleWithin_weaken ?_ (fun _ hp => hp) hbody
    intro hp h
    simp only [validateKnotBodyPre, validateKnotFrame, ambient, cursor, endPtr]
      at h ⊢
    xperm_chunked h
  let postDep : Unit → Assertion := fun _ =>
    validateCyclePost bytes base floor k cursorOff endOff spV raVal P
  have hknotDep : cpsTripleWithin (bud.B fuel) (validateEntry + 36)
      exit_ wholeCode
      (validateKnotFrame spV raVal cursor endPtr ** ambient)
      (cpsDepPost postDep) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hp => ⟨(), hp⟩) hknot
  have hentry := validate_entry_then_knot_dep_extend
    (P := ambient) (post := postDep)
    spV raVal cursor endPtr x5Val exit_ hne horder hAmbientPc
    hvalidateSub hknotDep
  refine ⟨9 + bud.B fuel, ?_⟩
  refine cpsTripleWithin_weaken ?_ ?_ hentry
  · intro hp h
    simp only [validateCyclePrePinned, ambient]
      at h ⊢
    let pinnedBody : Assertion :=
      ((regIs .x2 (spV + 32)) ** (regIs .x1 raVal) **
        (regIs .x0 (0 : Word)) **
        (regIs .x10 (base + BitVec.ofNat 64 cursorOff)) **
        (regIs .x11 (base + BitVec.ofNat 64 endOff)) **
        (regIs .x5 x5Val) ** (regIs .x12 x12Val) **
        memOwn spV ** memOwn (spV + 8) ** memOwn (spV + 16) **
        bytesRegion base bytes ** ⌜ValidateFuel bytes k cursorOff endOff⌝)
    let ownedBody : Assertion :=
      ((regIs .x2 (spV + 32)) ** (regIs .x1 raVal) **
        (regIs .x0 (0 : Word)) **
        (regIs .x10 (base + BitVec.ofNat 64 cursorOff)) **
        (regIs .x11 (base + BitVec.ofNat 64 endOff)) **
        (regIs .x5 x5Val) ** regOwn .x12 **
        memOwn spV ** memOwn (spV + 8) ** memOwn (spV + 16) **
        bytesRegion base bytes ** ⌜ValidateFuel bytes k cursorOff endOff⌝)
    have hbody : ∀ h, pinnedBody h → ownedBody h := by
      intro h hp
      simp only [pinnedBody, ownedBody] at hp ⊢
      exact sepConj_mono (fun _ h => h)
        (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => h)
            (sepConj_mono (fun _ h => h)
              (sepConj_mono (fun _ h => h)
                (sepConj_mono (fun _ h => h)
                  (sepConj_mono (regIs_implies_regOwn .x12)
                    (fun _ h => h))))))) h hp
    have h' := sepConj_mono_left hbody hp h
    xperm_chunked h'
  · intro hp h
    rcases h with ⟨u, hu⟩
    exact hu

end EvmAsm.Codegen.RlpWalkNextStrictFuel
