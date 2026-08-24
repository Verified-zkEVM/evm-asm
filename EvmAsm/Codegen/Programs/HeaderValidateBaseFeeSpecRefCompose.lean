/-
  EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecRefCompose

  The attribution increment on #12762's machine-layer spec of K74
  `header_validate_base_fee` (issue #12346).  #12762's
  `header_validate_base_fee_spec_within` concludes a bare status disjunction
  (`hvbfFinalAny`: `a0 ∈ {2, 0, 1}` plus regions) over free byte-list
  parameters — it says nothing about *why* each status arises.  This file
  adds the SpecRef-semantic layer on top, without re-proving any machine
  step:

  * `k73RouteBArmPost` / `k73RouteBPost` — the Route-B K73 callee contract
    shape (issue #12346 item 10): an UNCONDITIONAL whole-routine triple over
    the linked K73 entry (`GuestAddrs.eip1559_calc_base_fee_per_gas`)
    returning to the caller's `ra`, whose post is an ARM-INDEXED disjunction
    over the equal / increase / decrease recurrence arms (each asserting the
    output scratch holds `hvbfExpectedBytes`, the recurrence encoding for
    that arm) plus a failure arm (status ≠ 0, with the actual scratch bytes).
    This is
    the premise codex2's forthcoming whole-routine K73 theorem discharges.
  * `k73RouteB_adapt` — the adapter at the heart of the increment: at the
    wrapper's call site (`ra = H + 40`, initial scratch already the
    recurrence encoding, as #12762's `hk73` shape requires), every Route-B
    arm collapses onto #12762's `k73PostOwn`.
  * `header_validate_base_fee_specref_within` — applies #12762's theorem as
    the machine layer and concludes the ATTRIBUTED post
    (`hvbfSpecRefRetPost`): status 0 carries the reference-acceptance
    reading, status 1 the `.invalidBlock "base fee mismatch"` attribution
    (explicitly never "gas limit out of bounds" — see
    `hvbfSpecRef_baseFeeMismatch_ne_gasLimit`), status 2 the guest-internal
    K73 failure.

  Honest-domain notes.  (1) #12762's `hk73` shares the scratch byte list
  across the K73 call boundary, so discharging it forces the entry
  precondition `bytesRegion hvbf_expected (hvbfExpectedBytes …)`: the
  theorem is stated for entry states whose scratch already holds the
  recurrence encoding.  That restriction is inherited from the machine
  layer's shape, not from the routine (which overwrites the scratch); it
  lifts once the machine layer separates pre/post scratch content.
  (2) #12762's post does not expose the `u256_eq` byte-relation (which
  status corresponds to which byte outcome), so the status-0/1 pure
  conjuncts are implications indexed by that relation — the relation itself
  is the `heq` premise's semantic content.  Both implications are proved
  here from `hvbfSpecRefBaseFeeCheck_ok` / `_mismatch`, so the attribution
  content is fully carried.
-/

import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpec
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecRef
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeWitness

namespace EvmAsm.Codegen.HeaderValidateBaseFeeSpecRef

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Stateless.SpecRef

/-- Strip a trailing pure conjunct (the Route-B arm guards). -/
theorem hvbfSpecRef_strip_guard {A : Assertion} {P : Prop} :
    ∀ h, (A ** ⌜P⌝) h → A h :=
  fun h hp => ((sepConj_pure_right h).1 hp).1

/-! ## §1  The Route-B K73 contract shape (issue #12346 item 10) -/

/-- One arm of the Route-B K73 post: the machine state at the K73 return,
    status pinned in `a0`, the scratch holding `scratchOutBytes`, and the
    arm's guard as a trailing pure conjunct.  The register and frame
    inventory matches #12762's `k73PostOwn` atom-for-atom (with `a0` pinned
    rather than owned, the K73 frame's saved link register parameterized by
    the caller's `raRet` instead of the baked-in `H + 40`, and `x13` owned —
    K73's mul callee clobbers it without restoring, per #12762's x13
    repair), so at `raRet := H + 40` each arm collapses onto `k73PostOwn`
    once the guard is stripped (`k73RouteB_adapt`). -/
def k73RouteBArmPost (spH spK raRet raIn old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 status : Word)
    (parentBytes scratchOutBytes headerBytes : List (BitVec 8))
    (armGuard : Prop) (F : Assertion) : Assertion :=
  ((.x1 ↦ᵣ raRet) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ status) **
    regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
    frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
    (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
    regOwn .x12 ** regOwn .x13 **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 **
    frameSlotsSaved k73Frame spK (k73Saved raRet headerPtr v9 old18 v19 v20) **
    bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
    bytesRegion Expected scratchOutBytes ** F) ** ⌜armGuard⌝

/-- The Route-B whole-routine K73 post: an arm-indexed disjunction (NOT a
    single existential, per the #12346 item 10 coordination ruling).  The
    three success arms correspond to the reference recurrence's equal /
    increase / decrease cases; each pins status 0, asserts the scratch holds
    the recurrence encoding `hvbfExpectedBytes` (the recurrence value of
    that arm), and carries the arm's gas guard.  The failure arm carries an
    arbitrary nonzero status and the bytes actually left in the scratch
    region. -/
def k73RouteBPost (spH spK raRet raIn old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes _initBytes headerBytes : List (BitVec 8)) (F : Assertion) :
    Assertion := fun h =>
  (k73RouteBArmPost spH spK raRet raIn old8 headerPtr gasLimit gasUsed parentPtr
      v9 old18 v19 v20 (0 : Word) parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes)
      headerBytes (gasUsed.toNat = gasLimit.toNat / 2) F) h ∨
  (k73RouteBArmPost spH spK raRet raIn old8 headerPtr gasLimit gasUsed parentPtr
      v9 old18 v19 v20 (0 : Word) parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes)
      headerBytes (gasLimit.toNat / 2 < gasUsed.toNat) F) h ∨
  (k73RouteBArmPost spH spK raRet raIn old8 headerPtr gasLimit gasUsed parentPtr
      v9 old18 v19 v20 (0 : Word) parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes)
      headerBytes (gasUsed.toNat < gasLimit.toNat / 2) F) h ∨
  ∃ (status : Word) (scratchOutBytes : List (BitVec 8)),
    status ≠ (0 : Word) ∧
    (k73RouteBArmPost spH spK raRet raIn old8 headerPtr gasLimit gasUsed parentPtr
      v9 old18 v19 v20 status parentBytes scratchOutBytes headerBytes
      (status ≠ (0 : Word)) F) h

/-! ## §2  The adapter: Route-B arms collapse onto #12762's `k73PostOwn` -/

/-- The adapter at the heart of the increment.  At the wrapper's call site
    (`raRet := H + 40`, initial scratch instantiated to the recurrence
    encoding — the shape #12762's `hk73` premise requires), every Route-B
    arm implies the normalized `k73CallPost` at
    `expectedBytes := hvbfExpectedBytes`: the success arms assert exactly that
    scratch content, while the failure arm carries the bytes actually left in
    the scratch region.  The pinned success status is dropped into
    `k73PostOwn`'s owned `a0`; a failure status remains explicit. -/
theorem k73RouteB_adapt
    {k73Code : CodeReq} {n73 : Nat}
    (spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes headerBytes : List (BitVec 8)) (F : Assertion)
    (hk73RouteB : ∀ (raRet : Word) (initBytes : List (BitVec 8)),
      initBytes.length = 32 →
      (raRet &&& ~~~(1 : Word)) = raRet →
      parentBytes.length = 32 →
      cpsTripleWithin n73 K73 raRet k73Code
        ((.x1 ↦ᵣ raRet) **
          k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
            parentBytes initBytes headerBytes raIn old8 (k74FlatFrame F))
        (k73RouteBPost spH spK raRet raIn old8 headerPtr gasLimit gasUsed parentPtr
          v9 old18 v19 v20 parentBytes initBytes headerBytes (k74FlatFrame F))) :
    parentBytes.length = 32 →
    cpsTripleWithin n73 K73 (H + 40) k73Code
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes) headerBytes
          raIn old8 (k74FlatFrame F))
      ((.x1 ↦ᵣ (H + 40)) **
        k73CallPost spH spK raIn old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
          parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes) headerBytes
          (k74FlatFrame F)) := by
  intro hsrc
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_)
    (hk73RouteB (H + 40) (hvbfExpectedBytes gasLimit gasUsed parentBytes) (by
      simp [hvbfExpectedBytes]) (by decide) hsrc)
  have arm_to_own : ∀ (status : Word) (armGuard : Prop),
      (((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** (.x10 ↦ᵣ status) **
        regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        regOwn .x12 ** regOwn .x13 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        frameSlotsSaved k73Frame spK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
        bytesRegion Expected (hvbfExpectedBytes gasLimit gasUsed parentBytes) **
          (k74FlatFrame F)) **
        ⌜armGuard⌝) h →
      ((.x1 ↦ᵣ (H + 40)) **
        k73PostOwn spH spK headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
          parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes) headerBytes
          raIn old8 (k74FlatFrame F)) h := by
    intro status armGuard hq
    have h1 := hvbfSpecRef_strip_guard h hq
    have h2 : ((.x10 ↦ᵣ status) **
        ((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
        regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        regOwn .x12 ** regOwn .x13 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        frameSlotsSaved k73Frame spK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
        bytesRegion Expected (hvbfExpectedBytes gasLimit gasUsed parentBytes) **
          (k74FlatFrame F))) h := by
      xperm_hyp h1
    have h3 := sepConj_mono_left (regIs_implies_regOwn (r := .x10) (v := status)) h h2
    unfold k73PostOwn tailRest tailRestCore
    xperm_hyp h3
  have arm_to_failure : ∀ (status : Word) (scratchOutBytes : List (BitVec 8))
      (armGuard : Prop),
      (((.x1 ↦ᵣ (H + 40)) ** (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
        (.x10 ↦ᵣ status) ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        regOwn .x12 ** regOwn .x13 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        frameSlotsSaved k73Frame spK (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
        bytesRegion Expected scratchOutBytes ** (k74FlatFrame F)) **
        ⌜armGuard⌝) h →
      ((.x1 ↦ᵣ (H + 40)) **
        k73FailurePost spH spK headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
          status parentBytes scratchOutBytes headerBytes raIn old8 (k74FlatFrame F)) h := by
    intro status scratchOutBytes armGuard hq
    have h1 := hvbfSpecRef_strip_guard h hq
    have h2 : ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ status) **
        ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** regOwn .x11 **
        (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsSaved hvbfFrame spH (hvbfSaved raIn old8) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) ** regOwn .x12 ** regOwn .x13 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        frameSlotsSaved k73Frame spK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
        bytesRegion Expected scratchOutBytes ** (k74FlatFrame F))) h := by
      xperm_hyp h1
    unfold k73FailurePost tailRestScratch tailRestCore
    xperm_hyp h2
  unfold k73RouteBPost k73RouteBArmPost at hq
  rcases hq with h_arm | h_arm | h_arm | ⟨status, scratchOutBytes, hstatus, h_arm⟩
  · unfold k73CallPost
    exact sepConj_mono_right (fun _ h => Or.inl h) h
      (arm_to_own (0 : Word) _ h_arm)
  · unfold k73CallPost
    exact sepConj_mono_right (fun _ h => Or.inl h) h
      (arm_to_own (0 : Word) _ h_arm)
  · unfold k73CallPost
    exact sepConj_mono_right (fun _ h => Or.inl h) h
      (arm_to_own (0 : Word) _ h_arm)
  · unfold k73CallPost
    exact sepConj_mono_right
      (fun _ h => Or.inr ⟨status, scratchOutBytes, hstatus, h⟩) h
      (arm_to_failure status scratchOutBytes _ h_arm)

/-! ## §3  The attributed whole-routine post and theorem -/

/-- The attributed whole-routine return postcondition: #12762's three-way
    status disjunction, each outcome carrying its reference-level reading.

    * status 2 — the K73 compute step failed.  Guest-internal: the
      reference's unbounded arithmetic never fails here (the only
      `calculate_base_fee_per_gas` throw is the gas-limit check, which is a
      different guest routine's status), so this outcome has no reference
      counterpart.
    * status 0 — match: if the header fee bytes ARE the recurrence encoding
      (the `u256_eq` outcome the status selects, per the `heq` premise's
      semantics), then under a passing gas-limit check the reference's
      isolated base-fee check `hvbfSpecRefBaseFeeCheck` accepts — i.e.
      `validate_header`'s `calculate_base_fee_per_gas`-equality test passes.
    * status 1 — mismatch: if the header fee bytes differ from the
      recurrence encoding, then under a passing gas-limit check the
      reference raises `.invalidBlock "base fee mismatch"` — explicitly
      NEVER "gas limit out of bounds" (that raise comes from the reference's
      earlier `check_gas_limit`, a different routine's status; see
      `hvbfSpecRef_baseFeeMismatch_ne_gasLimit`). -/
def hvbfSpecRefRetPost (sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes headerBytes : List (BitVec 8)) (F : Assertion) : Assertion := fun h =>
  (∃ scratchBytes,
    hvbfFinalScratch sp0 spH spK raIn old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed
      parentPtr (2 : Word) gasUsed parentBytes scratchBytes headerBytes F h) ∨
  ((hvbfFinal sp0 spH spK raIn old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
      (0 : Word) Expected parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes)
      headerBytes F) **
    ⌜headerBytes = hvbfExpectedBytes gasLimit gasUsed parentBytes →
      ∀ blockGasLimit : Nat, check_gas_limit blockGasLimit gasLimit.toNat = true →
        hvbfSpecRefBaseFeeCheck blockGasLimit gasLimit gasUsed parentBytes headerBytes =
          .ok ()⌝) h ∨
  ((hvbfFinal sp0 spH spK raIn old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
      (1 : Word) Expected parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes)
      headerBytes F) **
    ⌜headerBytes ≠ hvbfExpectedBytes gasLimit gasUsed parentBytes →
      ∀ blockGasLimit : Nat, check_gas_limit blockGasLimit gasLimit.toNat = true →
        hvbfSpecRefBaseFeeCheck blockGasLimit gasLimit gasUsed parentBytes headerBytes =
          .error (.invalidBlock "base fee mismatch")⌝) h

/-- The K74 `header_validate_base_fee` wrapper with the SpecRef attribution
    layer: #12762's machine-layer theorem applied as-is, its K73 premise
    discharged from the Route-B contract, its post lifted to
    `hvbfSpecRefRetPost`.

    The `hk73RouteB` premise IS the Route-B contract of issue #12346 item
    10: an unconditional whole-routine triple over the linked K73 entry
    (`GuestAddrs.eip1559_calc_base_fee_per_gas`) returning to an arbitrary
    caller `ra`, with the arm-indexed post `k73RouteBPost` (equal / increase
    / decrease arms each asserting the scratch holds `hvbfExpectedBytes`,
    plus a failure arm).  codex2's forthcoming whole-routine K73 theorem
    discharges this hypothesis directly.  The `heq` premise is #12762's
    `u256_eq` call contract verbatim (at the recurrence-encoding scratch
    content), kept as a named premise because the existing general
    `u256Eq_spec` does not expose the `x12`/`x13` preservation
    #12762's `eqPostOwn` requires. -/
theorem header_validate_base_fee_specref_within
    {cr k73Code eqCode : CodeReq} {n73 nEq : Nat}
    (sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes headerBytes : List (BitVec 8)) (F : Assertion)
    (hspH : spH = sp0 + signExtend12 (-16 : BitVec 12))
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hF : F.pcFree)
    (hcode : ∀ a i, hvbfCode a = some i → cr a = some i)
    (hk73Mono : ∀ a i, k73Code a = some i → cr a = some i)
    (hk73RouteB : ∀ (raRet : Word) (initBytes : List (BitVec 8)),
      initBytes.length = 32 →
      (raRet &&& ~~~(1 : Word)) = raRet →
      parentBytes.length = 32 →
      cpsTripleWithin n73 K73 raRet k73Code
        ((.x1 ↦ᵣ raRet) **
          k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
            parentBytes initBytes headerBytes raIn old8 (k74FlatFrame F))
        (k73RouteBPost spH spK raRet raIn old8 headerPtr gasLimit gasUsed parentPtr
          v9 old18 v19 v20 parentBytes initBytes headerBytes (k74FlatFrame F)))
    (heqMono : ∀ a i, eqCode a = some i → cr a = some i)
    (heq : cpsTripleWithin nEq EqK (H + 60) eqCode
      ((.x1 ↦ᵣ (H + 60)) **
        eqPre spH spK raIn old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
          parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes) headerBytes
            (k74FlatFrame F))
      ((.x1 ↦ᵣ (H + 60)) **
        eqPostOwn spH spK raIn old8 headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed parentPtr
          parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes) headerBytes
            (k74FlatFrame F))) :
    parentBytes.length = 32 →
    cpsTripleWithin (27 + n73 + nEq) H raIn cr
      (hvbfPre sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
        v9 old18 v19 v20
        parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes) headerBytes
          (k74FlatFrame F))
      (hvbfSpecRefRetPost sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
        v9 old18 v19 v20 parentBytes headerBytes (k74FlatFrame F)) := by
  intro hsrc
  have hk73 := k73RouteB_adapt spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
    v9 old18 v19 v20 parentBytes headerBytes F hk73RouteB hsrc
  have hmachine := HeaderValidateBaseFeeSpec.header_validate_base_fee_spec_within
    sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr v9 old18 v19 v20
    parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes) headerBytes F
    hspH hspK hret hF hcode hk73Mono hk73 heqMono heq
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hmachine
  unfold hvbfFinalAny at hq
  rcases hq with h2 | h0 | h1
  · exact Or.inl h2
  · refine Or.inr (Or.inl ?_)
    exact (sepConj_pure_right h).2 ⟨h0, fun hmatch bl hb =>
      hvbfSpecRefBaseFeeCheck_ok bl gasLimit gasUsed parentBytes headerBytes hb hmatch⟩
  · refine Or.inr (Or.inr ?_)
    exact (sepConj_pure_right h).2 ⟨h1, fun hne bl hb =>
      hvbfSpecRefBaseFeeCheck_mismatch bl gasLimit gasUsed parentBytes headerBytes hb hne⟩

/-! ## §4  Non-vacuity: a concrete inhabitant of the static premise set -/

/-- The whole-routine theorem's static premise set is inhabited: at the
    caller-shaped addresses of #12762's own witness family, with the trivial
    code choice `cr = k73Code = eqCode = hvbfCode` (which makes the three
    code-subsumption premises reflexivity), every static premise holds and
    the entry assertion is pc-free.  The two callee contracts (`hk73RouteB`,
    `heq`) remain named hypotheses of the main theorem — the K73 family's
    remaining work and the `u256_eq` whole-routine gap — exactly like
    `hcore` in `validate_header_cps_compose`. -/
theorem header_validate_base_fee_specref_within_inhabitable :
    ∃ (cr k73Code eqCode : CodeReq) (sp0 spH spK raIn old8 headerPtr gasLimit gasUsed
        parentPtr : Word) (v9 old18 v19 v20 : Word)
      (parentBytes headerBytes : List (BitVec 8)) (F : Assertion),
      F.pcFree ∧
      (spH = sp0 + signExtend12 (-16 : BitVec 12)) ∧
      (spK = spH + signExtend12 (-56 : BitVec 12)) ∧
      (raIn &&& ~~~(1 : Word) = raIn) ∧
      (parentBytes.length = 32) ∧
      (∀ a i, hvbfCode a = some i → cr a = some i) ∧
      (∀ a i, k73Code a = some i → cr a = some i) ∧
      (∀ a i, eqCode a = some i → cr a = some i) ∧
        (hvbfPre sp0 spH spK raIn old8 headerPtr gasLimit gasUsed parentPtr
        v9 old18 v19 v20
        parentBytes (hvbfExpectedBytes gasLimit gasUsed parentBytes) headerBytes
          (k74FlatFrame F)).pcFree := by
  refine ⟨hvbfCode, hvbfCode, hvbfCode,
    (0x100000 : Word), (0x0ffff0 : Word), (0x0fffb8 : Word),
    (0x12340000 : Word), (0x56780000 : Word), (0x200000 : Word),
    (100000 : Word), (50000 : Word), (0x200100 : Word),
    1, 2, 3, 4,
    List.replicate 32 (0 : BitVec 8), List.replicate 32 (0 : BitVec 8),
    empAssertion, pcFree_emp, by decide, by decide, by decide, by decide,
    fun a i h => h, fun a i h => h, fun a i h => h, ?_⟩
  unfold hvbfPre
  dsimp [k74FlatFrame]
  pcf

#print axioms header_validate_base_fee_specref_within
#print axioms k73RouteB_adapt
#print axioms header_validate_base_fee_specref_within_inhabitable

end EvmAsm.Codegen.HeaderValidateBaseFeeSpecRef
