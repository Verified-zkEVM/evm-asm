/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelMachine

  Option-2 machine-indexed families for #12419.  The structural
  `cycleFuel_mutual_strong_induction` stays the index eliminator; these
  families carry `sharedCyclePre` / `validateCyclePre`, concrete `CodeReq`,
  and the #12408 continuation-output anti-vacuity witness — content that
  `sharedIndexedFamily` / `validateIndexedFamily` deliberately omitted.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuel
import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelContracts
import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelModel
import EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelStatus
import EvmAsm.Codegen.Programs.RlpWalkNextStrictTie

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-! ## Machine-indexed families (option 2)

Each family is quantified like `SharedFuelFamily` / `ValidateFuelFamily`: at a
fixed `fuel` index, every cursor window whose `cycleFuel` equals that index
must supply a real machine contract.  The ambient `P` remains a static frame
fragment; the fuel-dependent pure (`SharedFuel` / `ValidateFuel`) lives inside
`sharedCyclePre` / `validateCyclePre`, so the induction cannot instantiate at
`P = ⌜False⌝` and claim success without a concrete pre/post relation. -/

def sharedMachineIndexedFamily
    {α : Type} (bytes : List (BitVec 8)) (base : Word) (floor : Nat)
    (sp budget a2 : Word) (P : Assertion) (post : α → Assertion)
    (exit_ : Word) (contCode : CodeReq) (R : Assertion)
    (fuel : Nat) : Prop :=
  ∀ {cursorOff endOff : Nat},
    fuel = cycleFuel cursorOff endOff →
    cursorOff ≤ endOff →
    endOff ≤ bytes.length →
    base.toNat % 8 = 0 →
    base.toNat + bytes.length < 2 ^ 64 →
    base.toNat + endOff + 9 < 2 ^ 64 →
    (∀ off, off < endOff →
      isValidByteAccess (base + BitVec.ofNat 64 off) = true) →
    P.pcFree →
    Nonempty (SharedMachineContract bytes base floor fuel cursorOff endOff
      sp budget a2 P post exit_ contCode R)

def validateMachineIndexedFamily
    (bytes : List (BitVec 8)) (base : Word) (floor : Nat)
    (sp raVal exit_ : Word) (wholeCode : CodeReq) (P : Assertion)
    (fuel : Nat) : Prop :=
  ∀ {cursorOff endOff : Nat},
    fuel = cycleFuel cursorOff endOff →
    cursorOff ≤ endOff →
    endOff ≤ bytes.length →
    base.toNat % 8 = 0 →
    base.toNat + bytes.length < 2 ^ 64 →
    base.toNat + endOff + 9 < 2 ^ 64 →
    (∀ off, off < endOff →
      isValidByteAccess (base + BitVec.ofNat 64 off) = true) →
    exit_ = raVal &&& ~~~(1 : Word) →
    P.pcFree →
    (∀ a i, validateCR a = some i → wholeCode a = some i) →
    Nonempty (ValidateMachineContract bytes base floor fuel cursorOff endOff
      sp raVal exit_ wholeCode P)

/-! ## Knot-body family (recursive Validate surface, #12419)

Full-entry `validateMachineIndexedFamily` is derived ONCE from this family via
`validate_machine_proof_of_knot` (in Cont/Knot).  The recursive induction edge
is the V+36 knot body: loop-back lands here with `x1 = V+40`; entry prologue
lands with `x1 = raVal`.  Both are instances of the `x1Old`-parametric pre.
`validateKnotFrameRest` in Cont is the named twin of the inlined frame atoms
below — inlined here so Machine does not import Cont (Cont imports Machine). -/

/-- Knot-body pre at `V+36`: parametric `x1Old` + frame rest + `x0`/`x12`/bytes/fuel. -/
def validateKnotBodyPre
    (bytes : List (BitVec 8)) (base : Word)
    (fuel cursorOff endOff : Nat) (sp raVal x1Old : Word) (P : Assertion) :
    Assertion :=
  (((regIs .x1 x1Old) **
    (regIs .x2 sp) **
    (regIs .x10 (base + BitVec.ofNat 64 cursorOff)) **
    (regIs .x5 (base + BitVec.ofNat 64 endOff)) **
    (regIs .x11 (base + BitVec.ofNat 64 endOff)) **
    (memIs sp raVal) **
    (memIs (sp + 8) (base + BitVec.ofNat 64 cursorOff)) **
    (memIs (sp + 16) (base + BitVec.ofNat 64 endOff))) **
    (regIs .x0 (0 : Word)) ** regOwn .x12 **
    bytesRegion base bytes **
    ⌜ValidateFuel bytes fuel cursorOff endOff⌝ ** P)

/-- Machine contract at knot-body altitude (`V+36` → `validateCyclePost`). -/
structure ValidateKnotBodyContract
    (bytes : List (BitVec 8)) (base : Word)
    (floor fuel cursorOff endOff : Nat) (sp raVal exit_ : Word)
    (wholeCode : CodeReq) (P : Assertion) : Type where
  hbase_aligned : base.toNat % 8 = 0
  hcursor : cursorOff ≤ endOff
  hwindow : endOff ≤ bytes.length
  hover : base.toNat + bytes.length < 2 ^ 64
  hnowrap : base.toNat + endOff + 9 < 2 ^ 64
  hvalid : ∀ off, off < endOff →
    isValidByteAccess (base + BitVec.ofNat 64 off) = true
  hexit : exit_ = raVal &&& ~~~(1 : Word)
  hP : P.pcFree
  hvalidateSub : ∀ a i, validateCR a = some i → wholeCode a = some i
  steps : Nat
  /-- Parametric in incoming `x1` (entry `raVal` or loop-back `V+40`). -/
  proof : ∀ x1Old,
    cpsTripleWithin steps (validateEntry + 36) exit_ wholeCode
      (validateKnotBodyPre bytes base fuel cursorOff endOff sp raVal x1Old P)
      (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)

/-- Recursive Validate family: every window at this `cycleFuel` supplies a
knot-body contract. -/
def knotBodyMachineIndexedFamily
    (bytes : List (BitVec 8)) (base : Word) (floor : Nat)
    (sp raVal exit_ : Word) (wholeCode : CodeReq) (P : Assertion)
    (fuel : Nat) : Prop :=
  ∀ {cursorOff endOff : Nat},
    fuel = cycleFuel cursorOff endOff →
    cursorOff ≤ endOff →
    endOff ≤ bytes.length →
    base.toNat % 8 = 0 →
    base.toNat + bytes.length < 2 ^ 64 →
    base.toNat + endOff + 9 < 2 ^ 64 →
    (∀ off, off < endOff →
      isValidByteAccess (base + BitVec.ofNat 64 off) = true) →
    exit_ = raVal &&& ~~~(1 : Word) →
    P.pcFree →
    (∀ a i, validateCR a = some i → wholeCode a = some i) →
    Nonempty (ValidateKnotBodyContract bytes base floor fuel cursorOff endOff
      sp raVal exit_ wholeCode P)

/-! ## Fuel-indexed step budget `B(fuel)` (option 3, #12419)

`ValidateKnotContGoal`'s `nCont` is UNIFORM over `ValidateResult`, while a
knot-body contract's `steps` is per-window and recursively
`1 + (1 + nShared) + nCont_child` at strictly smaller child fuels.  There is no
closed uniform bound on the raw family surface (the named builder wall).

The fix that keeps budgets DERIVED and BOTTOM-UP rather than capped top-down is
a *bound as a function of the fuel index*: a monotone `B : Nat → Nat` such that
every window at index `fuel` runs within `B fuel`.  Monotonicity is the whole
point — a child window at `k < fuel` satisfies `B k ≤ B fuel`, so
`cpsTripleWithin_mono_nSteps` lifts every child triple to the SAME bound
`B fuel`, which is exactly the uniformity ContGoal asks for.  `B` is never
chosen here: it is a parameter the builder must exhibit, so the budget still
composes upward from per-routine step counts. -/
structure KnotStepBudget where
  /-- Step bound as a function of the `cycleFuel` index. -/
  B : Nat → Nat
  /-- Monotone in the fuel index: child windows fit inside the parent's bound. -/
  hmono : ∀ {a b : Nat}, a ≤ b → B a ≤ B b

/-- Knot-body family with a fuel-indexed step bound.  Same content as
`knotBodyMachineIndexedFamily` plus `steps ≤ bud.B fuel`. -/
def knotBodyBoundedFamily
    (bytes : List (BitVec 8)) (base : Word) (floor : Nat)
    (sp raVal exit_ : Word) (wholeCode : CodeReq) (P : Assertion)
    (bud : KnotStepBudget) (fuel : Nat) : Prop :=
  ∀ {cursorOff endOff : Nat},
    fuel = cycleFuel cursorOff endOff →
    cursorOff ≤ endOff →
    endOff ≤ bytes.length →
    base.toNat % 8 = 0 →
    base.toNat + bytes.length < 2 ^ 64 →
    base.toNat + endOff + 9 < 2 ^ 64 →
    (∀ off, off < endOff →
      isValidByteAccess (base + BitVec.ofNat 64 off) = true) →
    exit_ = raVal &&& ~~~(1 : Word) →
    P.pcFree →
    (∀ a i, validateCR a = some i → wholeCode a = some i) →
    ∃ C : ValidateKnotBodyContract bytes base floor fuel cursorOff endOff
      sp raVal exit_ wholeCode P, C.steps ≤ bud.B fuel

/-- A bounded family is in particular a family (bound forgotten). -/
theorem knotBodyMachineIndexedFamily_of_bounded
    {bytes : List (BitVec 8)} {base : Word} {floor : Nat}
    {sp raVal exit_ : Word} {wholeCode : CodeReq} {P : Assertion}
    {bud : KnotStepBudget} {fuel : Nat}
    (h : knotBodyBoundedFamily bytes base floor sp raVal exit_ wholeCode P
      bud fuel) :
    knotBodyMachineIndexedFamily bytes base floor sp raVal exit_ wholeCode P
      fuel := by
  intro cursorOff endOff hfuel hcursor hwindow hal hover hnowrap hvalid hexit
    hP hsub
  obtain ⟨C, _⟩ := h hfuel hcursor hwindow hal hover hnowrap hvalid hexit hP hsub
  exact ⟨C⟩

/-- The uniformity lemma: a bounded contract at ANY index `k ≤ fuel` yields a
knot-body triple at the single bound `bud.B fuel`.  This is what makes a
uniform `nCont` / `nKnot` available at the parent altitude. -/
theorem knotBody_proof_at_bound
    {bytes : List (BitVec 8)} {base : Word}
    {floor k fuel cursorOff endOff : Nat} {P : Assertion}
    {wholeCode : CodeReq} {sp raVal exit_ : Word}
    {bud : KnotStepBudget}
    (C : ValidateKnotBodyContract bytes base floor k cursorOff endOff
      sp raVal exit_ wholeCode P)
    (hsteps : C.steps ≤ bud.B k) (hk : k ≤ fuel) (x1Old : Word) :
    cpsTripleWithin (bud.B fuel) (validateEntry + 36) exit_ wholeCode
      (validateKnotBodyPre bytes base k cursorOff endOff sp raVal x1Old P)
      (validateCyclePost bytes base floor k cursorOff endOff sp raVal P) :=
  cpsTripleWithin_mono_nSteps (le_trans hsteps (bud.hmono hk)) (C.proof x1Old)

/-! The option-2 eliminator: `cycleFuel` strong induction over Shared +
**knot-body** Validate (not full-entry).  Full-entry is derived once outside. -/
theorem actual_strict_walk_machine_induction
    {α : Type} {bytes : List (BitVec 8)} {base : Word} {floor : Nat}
    {sp budget a2 raVal exit_ : Word} {P : Assertion} {post : α → Assertion}
    {contCode wholeCode : CodeReq} {R : Assertion}
    (hshared : ∀ fuel,
      (∀ k, k < fuel →
        sharedMachineIndexedFamily bytes base floor sp budget a2 P post
          exit_ contCode R k ∧
        knotBodyMachineIndexedFamily bytes base floor sp raVal exit_
          wholeCode P k) →
      sharedMachineIndexedFamily bytes base floor sp budget a2 P post
        exit_ contCode R fuel)
    (hknot : ∀ fuel,
      (∀ k, k < fuel →
        sharedMachineIndexedFamily bytes base floor sp budget a2 P post
          exit_ contCode R k ∧
        knotBodyMachineIndexedFamily bytes base floor sp raVal exit_
          wholeCode P k) →
      knotBodyMachineIndexedFamily bytes base floor sp raVal exit_
        wholeCode P fuel) :
    ∀ fuel,
      sharedMachineIndexedFamily bytes base floor sp budget a2 P post
        exit_ contCode R fuel ∧
      knotBodyMachineIndexedFamily bytes base floor sp raVal exit_
        wholeCode P fuel := by
  apply cycleFuel_mutual_strong_induction
  intro fuel ih
  exact ⟨hshared fuel ih, hknot fuel ih⟩

/-! ## Degenerate-window facts

`cycleFuel c e = 0` forces `c = e`.  These lemmas pin the empty-window
boundary the base cases must inhabit. -/
theorem cycleFuel_eq_zero_iff
    {cursor endOff : Nat} :
    cycleFuel cursor endOff = 0 ↔ cursor = endOff ∨ endOff < cursor := by
  unfold cycleFuel remainingBytes
  constructor
  · intro h
    omega
  · intro h
    omega

theorem cycleFuel_eq_zero_of_eq
    {cursor endOff : Nat} (heq : cursor = endOff) :
    cycleFuel cursor endOff = 0 := by
  subst endOff
  unfold cycleFuel remainingBytes
  omega

/-! ## Closed: anti-vacuity shape for the enriched Shared family

`SharedMachineContract` already requires `sharedDependentContinuation`, which
includes `sharedContinuationOutput`.  The two elim lemmas below reuse the
#12408 guards so a "success" that packages `Empty` / `⌜False⌝` posts cannot
inhabit the enriched family. -/
theorem sharedMachineIndexedFamily_empty_post_elim
    {bytes : List (BitVec 8)} {base : Word} {floor : Nat}
    {sp budget a2 : Word} {P : Assertion} {exit_ : Word}
    {contCode : CodeReq} {R : Assertion} {fuel : Nat}
    (h : sharedMachineIndexedFamily (α := Empty) bytes base floor
      sp budget a2 P (fun _ => ⌜True⌝) exit_ contCode R fuel)
    {cursorOff endOff : Nat}
    (hfuel : fuel = cycleFuel cursorOff endOff)
    (hcursor : cursorOff ≤ endOff) (hwindow : endOff ≤ bytes.length)
    (hbase_aligned : base.toNat % 8 = 0)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64)
    (hvalid : ∀ off, off < endOff →
      isValidByteAccess (base + BitVec.ofNat 64 off) = true)
    (hP : P.pcFree) :
    False := by
  rcases h hfuel hcursor hwindow hbase_aligned hover hnowrap hvalid hP with ⟨C⟩
  exact sharedDependentContinuation_empty_elim C.hcontinuation

theorem sharedMachineIndexedFamily_false_post_elim
    {bytes : List (BitVec 8)} {base : Word} {floor : Nat}
    {sp budget a2 : Word} {P : Assertion} {exit_ : Word}
    {contCode : CodeReq} {R : Assertion} {fuel : Nat}
    (h : sharedMachineIndexedFamily (α := Unit) bytes base floor
      sp budget a2 P (fun _ => ⌜False⌝) exit_ contCode R fuel)
    {cursorOff endOff : Nat}
    (hfuel : fuel = cycleFuel cursorOff endOff)
    (hcursor : cursorOff ≤ endOff) (hwindow : endOff ≤ bytes.length)
    (hbase_aligned : base.toNat % 8 = 0)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hnowrap : base.toNat + endOff + 9 < 2 ^ 64)
    (hvalid : ∀ off, off < endOff →
      isValidByteAccess (base + BitVec.ofNat 64 off) = true)
    (hP : P.pcFree) :
    False := by
  rcases h hfuel hcursor hwindow hbase_aligned hover hnowrap hvalid hP with ⟨C⟩
  exact sharedDependentContinuation_false_post_elim C.hcontinuation

/-! ## Open obligations (named; not discharged)

Each residual is stated as the exact Prop the induction step must prove.
Leaving them as `theorem ... := by sorry` would expand the axiom baseline;
instead they are `def` aliases of the goal types so the report can quote them
without introducing `sorryAx`. -/

/-- Shared-side residual: under a strictly smaller Validate-family witness,
merge short `S+148` and long `S+88` arms via `shared_list_arm_cps_under_validator`.
Closed: long-prefix loop; preamble→payload (`*_preamble_zero_to_payload`,
`*_preamble_n_iter_to_payload`); short/long validate_call adapters;
`*_validate_then_cont`; depth+status `hcont` (`shared_after_validate_*`);
result→pre bridge; `*_validate_then_status`.
Still open: (1) inhabit full `ValidateKnotContGoal` — nonzero arm closed
(`validateKnotCont_nonzero`); zero arm's `V+40 → V+16` edge now DERIVED
(`validateKnotCont_zero_to_reload`, via the split-`callRa` zero-loop so
`x1 = V+40` and `memIs sp = raVal` hold together); `validateKnotCont_zero`
no longer takes `ValidateKnotContZeroToReloadGoal` as an input.  Remaining:
`ValidateKnotContZeroReloadGoal` (`V+16` → cycle post) is now OWNED under an
explicit knot-body IH: `validateKnotCont_zero_reload_of_body` (classical-clean)
discharges empty ∪ `nonempty_of_body` after peeling Pre pures.  Premises the
induction builder must still supply: (i) remaining-window `ValidateFuel` at
`cycleFuel nextOff endOff` for every `nextOff < endOff`, (ii) `ValidateKnotBodyRemainingGoal`
at that same window.  `validateKnotCont_zero` still TAKES the Goal as input —
but the Goal is no longer an unowned packaging hole; its owner is
`ValidateKnotContZeroReloadOfBodyGoal` once the builder wires those two
premises.

IH-ALTITUDE FINDING (#12419): remaining→outer bridge DERIVED
(`validateCyclePost_reindex_window`); nonempty composition DERIVED
(`validateKnotCont_zero_reload_nonempty_of_body`).  Loop-back lands at `V+36`
with `validateKnotLoopBackFrame`.  DONE: `actual_strict_walk_machine_induction`
now inducts on `knotBodyMachineIndexedFamily` (V+36, `x1Old`-parametric);
full-entry `validateMachineIndexedFamily` is derived once via
`validate_machine_proof_of_knot` (Cont/Knot), not a parallel recursive family.
FUEL-INDEX CORRECTION: BodyRemainingGoal / of_body index `ValidateFuel` and
remaining `validateCyclePost` at `cycleFuel next endOff` (what
`ValidateFuel`'s constructors inhabit), not `endOff - next` (that slot belongs
to `PayloadStrictFuel` / `ValidateK` only).  Decrease unchanged:
`cursor < next ≤ endOff` ⇒ `cycleFuel next endOff < cycleFuel cursor endOff`
(`cycleFuel_strict_of_advance`); equivalent to `endOff - next < endOff - cursor`
by the factor-of-two definition.
OPEN: wire knot-body builder to discharge `ValidateKnotContZeroReloadOfBodyGoal`
(BodyRemainingGoal at `x1Old = V+40` + rem VF from family), then ContGoal.

FINDING — ContGoal UNIFORM STEP BOUND (#12419 builder wall):
`ValidateKnotContGoal` / `cpsTripleWithin_seq_dep_post`'s `hcont` require a
*uniform* `nCont` across every `ValidateResult`.  `ValidateKnotBodyContract.steps`
is per-window and recursively `1+(1+nShared)+nCont_child` at child fuels — no
closed uniform bound exists on the current Prop surface.  Therefore the
knot-body builder cannot INHABIT `ValidateKnotContGoal` (as stated) from
`knotBodyMachineIndexedFamily` without one of:
  (1) restating ContGoal / dep-bind `hcont` as `∀ r, ∃ n, cpsTripleWithin n`
      (alters the claimed API — stop and ask),
  (2) taking an unowned uniform step bound (RELABELLING — refuse),
  (3) proving a fuel-indexed step bound `∀ windows at fuel, steps ≤ B(fuel)`
      (new lemma; not yet attempted).
`actual_strict_walk_machine_induction` itself (Shared ∧ knotBody on cycleFuel)
is not the obstruction — ContGoal's uniform-`nCont` statement is.

RESOLVED by (3), no statement change: `KnotStepBudget` + `knotBodyBoundedFamily`
above, and in `…MachineKnot.lean`
`validateKnotBodyRemainingGoal_of_bounded` /
`validateKnotBodyRemainingGoal_uniform_of_boundedFamily` /
`validateKnotContGoal_of_bound`.  Monotone `B` makes every child window at
index `k ≤ fuel` lift to the single bound `B fuel`, so the uniform indices are
the closed chain `nKnot = B fuel`, `nReload = max 8 (5 + B fuel)`,
`nCont = max 5 (5 + nReload)`.  `of_body`'s single `nKnot` for all remaining
windows is the SAME construction (no asymmetry between the altitudes): both
need only child-index ≤ parent-index ⇒ `B` mono ⇒ `cpsTripleWithin_mono_nSteps`.
`B` is exhibited by the builder, never capped here.

STILL UNOWNED at ContGoal (labelled, not counted as derived): none — ContGoal
consumer is DERIVED.  `validateKnotContGoal_of_bound` takes only statics +
ZeroReload; `hK`/`hdecode` peel from SharedPost via `validateResultFacts` + the
success-only cursor pin `r.status = 0 → r.cursor = base + r.next` added to
`validateKnotSharedPost` (#12419 (c); NOT in `validateResultFacts`).

OPEN residual (producer, not ContGoal): `hshared` in
`validate_knot_body_under_shared_framed` must inhabit the strengthened
`validateKnotSharedPost` (including the cursor pin).  No concrete Shared proof
posts that shape yet — the pin is what the nested success path establishes and
must publish.  If that obligation cannot be discharged, bank there; do not
re-introduce hK/hdecode as ContGoal inputs. -/
def SharedListArmsFromValidateGoal
    (bytes : List (BitVec 8)) (base : Word) (floor parentFuel childFuel : Nat)
    (_cursorOff _endOff : Nat) (pfx exit_ : Word) (P R : Assertion) : Prop :=
  childFuel < parentFuel →
  validateMachineIndexedFamily bytes base floor
    (0 : Word) (0 : Word) exit_ validateCR P childFuel →
  ∃ nShort nLong,
    cpsTripleWithin nShort (RlpWalkNextStrictTie.S + 148) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
          pure (BitVec.ult pfx (248 : Word))) ** P) R ∧
    cpsTripleWithin nLong (RlpWalkNextStrictTie.S + 88) exit_
      RlpWalkNextStrictTie.sharedCode
      (((regIs .x6 pfx) ** (regIs .x7 (248 : Word)) **
          pure (¬ BitVec.ult pfx (248 : Word))) ** P) R

/-- Validate-side residual: from a strictly smaller Shared-family witness,
plus static window/code facts and an entry-level CPS proof (via
`validate_machine_proof_of_knot` / `rlp_validate_payload_cps_under_shared`),
obtain `ValidateMachineContract`. -/
def ValidateFromSharedGoal
    (bytes : List (BitVec 8)) (base : Word) (floor fuel : Nat)
    (cursorOff endOff : Nat) (sp raVal exit_ : Word)
    (wholeCode : CodeReq) (P : Assertion) : Prop :=
  exit_ = raVal &&& ~~~(1 : Word) →
  P.pcFree →
  (∀ a i, validateCR a = some i → wholeCode a = some i) →
  base.toNat % 8 = 0 →
  cursorOff ≤ endOff →
  endOff ≤ bytes.length →
  base.toNat + bytes.length < 2 ^ 64 →
  base.toNat + endOff + 9 < 2 ^ 64 →
  (∀ off, off < endOff →
    isValidByteAccess (base + BitVec.ofNat 64 off) = true) →
  (∀ {cursor next len}, cursor < next → next ≤ endOff →
    endOff ≤ bytes.length →
    rlpItemDecodeStrictW bytes base cursor next endOff len (floor + 1)) →
  (∀ {next}, next ≤ endOff →
    ValidateK bytes base floor
      (base + BitVec.ofNat 64 next)
      (base + BitVec.ofNat 64 endOff)
      next endOff (endOff - next)) →
  (∀ k, k < fuel →
    Nonempty (IndexedCpsContract k
      (GuestAddrs.rlp_walk_next_shared : Word) (validateEntry + 40)
      RlpWalkNextStrictTie.sharedCode
      ((regIs .x1 (validateEntry + 40)) ** P)
      (cpsDepPost (validateResultDependentPost bytes base floor
        cursorOff endOff fuel)))) →
  (∃ steps, cpsTripleWithin steps validateEntry exit_ wholeCode
    (validateCyclePre bytes base fuel cursorOff endOff sp raVal P)
    (validateCyclePost bytes base floor fuel cursorOff endOff sp raVal P)) →
  Nonempty (ValidateMachineContract bytes base floor fuel cursorOff endOff
    sp raVal exit_ wholeCode P)

/-- Top-level residual: the two builders that `actual_strict_walk_machine_induction`
still needs (Shared + **knot-body** Validate), with `cycleFuel` decrease at each
recursive edge.  Full-entry `validateMachineIndexedFamily` is derived once from
the knot-body family, not inducted in parallel. -/
def MachineInductionBuildersGoal
    {α : Type} (bytes : List (BitVec 8)) (base : Word) (floor : Nat)
    (sp budget a2 raVal exit_ : Word) (P : Assertion) (post : α → Assertion)
    (contCode wholeCode : CodeReq) (R : Assertion) : Prop :=
  (∀ fuel,
    (∀ k, k < fuel →
      sharedMachineIndexedFamily bytes base floor sp budget a2 P post
        exit_ contCode R k ∧
      knotBodyMachineIndexedFamily bytes base floor sp raVal exit_
        wholeCode P k) →
    sharedMachineIndexedFamily bytes base floor sp budget a2 P post
      exit_ contCode R fuel) ∧
  (∀ fuel,
    (∀ k, k < fuel →
      sharedMachineIndexedFamily bytes base floor sp budget a2 P post
        exit_ contCode R k ∧
      knotBodyMachineIndexedFamily bytes base floor sp raVal exit_
        wholeCode P k) →
    knotBodyMachineIndexedFamily bytes base floor sp raVal exit_
      wholeCode P fuel)

/-! ## Degenerate inhabitant (anti-vacuity): empty ValidateFuel structural side

Structural empty windows are inhabited for every `bytes` (fuel model).  The
machine contract at `validateEntry+36` is a *nonempty* knot entry — empty
payloads exit before that PC — so the Validate machine family at fuel 0 is
not discharged by `rlp_validate_payload_empty_cursor_cps` alone.  Record the
structural half here as a positive inhabitant; the machine half remains open
under `ValidateFromSharedGoal`. -/
theorem validateFuel_empty_window_inhabited
    (bytes : List (BitVec 8)) {cursorOff endOff : Nat}
    (heq : cursorOff = endOff) (hend : endOff ≤ bytes.length) :
    ValidateFuel bytes (cycleFuel cursorOff endOff) cursorOff endOff := by
  simpa [cycleFuel_eq_zero_of_eq heq] using
    (ValidateFuel.empty (bytes := bytes) (cursor := cursorOff) (endOff := endOff)
      ⟨heq, hend⟩)

theorem sharedFuel_empty_window_inhabited
    (bytes : List (BitVec 8)) {cursorOff endOff : Nat}
    (heq : cursorOff = endOff) (hend : endOff ≤ bytes.length) :
    SharedFuel bytes (cycleFuel cursorOff endOff) cursorOff endOff := by
  have hwindow : cursorOff ≤ endOff ∧ endOff ≤ bytes.length := ⟨le_of_eq heq, hend⟩
  simpa [cycleFuel_eq_zero_of_eq heq] using
    (SharedFuel.nonList (bytes := bytes) (cursor := cursorOff) (endOff := endOff)
      hwindow)

/-! ## Closed slice of the long-prefix residual

Zero-remaining exit from the length-decoder header (`S+104` init + taken
`BEQ` at `S+108`) lands at the payload-base setup (`S+136`).  This is the
loop-exit edge; the nonzero body (shift/LBU/OR/cursor/remaining/backedge)
and the Validate handoff after `S+136` remain open under
`SharedListArmsFromValidateGoal`. -/
theorem shared_long_prefix_zero_remaining_to_payload_base
    (oldAcc : Word) :
    cpsTripleWithin 2 (RlpWalkNextStrictTie.S + 104)
      (RlpWalkNextStrictTie.S + 136) RlpWalkNextStrictTie.sharedCode
      ((regIs .x30 oldAcc) ** (regIs .x28 (0 : Word)) ** (regIs .x0 (0 : Word)))
      ((regIs .x30 (0 : Word)) ** (regIs .x28 (0 : Word)) **
        (regIs .x0 (0 : Word))) := by
  have hinit0 := shared_long_prefix_init_acc oldAcc
  have hinit := cpsTripleWithin_frameR
    ((regIs .x28 (0 : Word)) ** (regIs .x0 (0 : Word)))
    (by apply pcFree_sepConj <;> exact pcFree_regIs) hinit0
  have hbr0 := shared_long_prefix_branch (0 : Word)
  have htaken0 := cpsBranchWithin_takenStripPure2 hbr0 (by
    intro _ hQf
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).mp h_rest).2)
  have htaken := cpsTripleWithin_frameR (regIs .x30 (0 : Word))
    (by exact pcFree_regIs) htaken0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hinit htaken
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hseq

/-! Zero-length long-prefix payload setup: after the length loop exits with
`acc = 0`, compute `payload = cursor + pfx + 1` and fall through to the
validator handoff at `S+152`.  Does not yet include the Validate call or the
status continuation (`SharedListArmsFromValidateGoal`). -/
theorem shared_long_prefix_zero_payload_setup
    (cursor pfx oldOut : Word) :
    cpsTripleWithin 3 (RlpWalkNextStrictTie.S + 136)
      (RlpWalkNextStrictTie.S + 152) RlpWalkNextStrictTie.sharedCode
      ((regIs .x12 oldOut) ** (regIs .x5 cursor) ** (regIs .x13 pfx))
      ((regIs .x12 (cursor + pfx + 1)) ** (regIs .x5 cursor) **
        (regIs .x13 pfx)) := by
  have hbase := shared_long_prefix_payload_base cursor pfx oldOut
  have hstart := shared_long_prefix_payload_start cursor pfx
  have hto0 := shared_long_prefix_to_validator (cursor + pfx + 1)
  have hto := cpsTripleWithin_frameR
    ((regIs .x5 cursor) ** (regIs .x13 pfx))
    (by apply pcFree_sepConj <;> exact pcFree_regIs) hto0
  have h1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hbase hstart
  have h2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h1 hto
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) h2

/-! One nonzero long-prefix iteration body: shift → LBU → OR → cursor++ →
remaining-- → backedge to `S+108`.  Pattern mirrors
`rlp_phase2_long_loop_succ_spec_within`, specialised to the shared-walker
register assignment (`x30` acc, `x29` cursor, `x28` remaining). -/
theorem shared_long_prefix_one_iter
    (acc cursor remaining oldByte dwordAddr wordVal : Word)
    (hne : remaining ≠ 0)
    (halign : alignToDword cursor = dwordAddr)
    (hvalid : isValidByteAccess cursor = true) :
    cpsTripleWithin 7 (RlpWalkNextStrictTie.S + 108)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x30 acc) ** (regIs .x29 cursor) ** (regIs .x28 remaining) **
        (regIs .x31 oldByte) ** (regIs .x0 (0 : Word)) **
        (dwordAddr ↦ₘ wordVal))
      ((regIs .x30
          ((acc <<< 8) |||
            (extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
        (regIs .x29 (cursor + 1)) ** (regIs .x28 (remaining - 1)) **
        (regIs .x31 ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  have hbr0 := shared_long_prefix_branch remaining
  have hntaken0 := cpsBranchWithin_ntakenStripPure2 hbr0 (by
    intro _ hQt
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
    exact absurd ((sepConj_pure_right _).mp h_rest).2 hne)
  have hntaken := cpsTripleWithin_frameR
    ((regIs .x30 acc) ** (regIs .x29 cursor) ** (regIs .x31 oldByte) **
      (dwordAddr ↦ₘ wordVal))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs)
    hntaken0
  have hshift0 := shared_long_prefix_shift acc
  have hshift := cpsTripleWithin_frameR
    ((regIs .x29 cursor) ** (regIs .x28 remaining) ** (regIs .x31 oldByte) **
      (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs)
    hshift0
  have hload0 := shared_long_prefix_load_byte cursor oldByte dwordAddr wordVal
    halign hvalid
  have hload := cpsTripleWithin_frameR
    ((regIs .x30 (acc <<< 8)) ** (regIs .x28 remaining) **
      (regIs .x0 (0 : Word)))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hload0
  have hacc0 := shared_long_prefix_accumulate_byte (acc <<< 8)
    ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)
  have hacc := cpsTripleWithin_frameR
    ((regIs .x29 cursor) ** (regIs .x28 remaining) **
      (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs)
    hacc0
  have hcur0 := shared_long_prefix_cursor_increment cursor remaining
  have hcur := cpsTripleWithin_frameR
    ((regIs .x30
        ((acc <<< 8) |||
          (extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
      (regIs .x31 ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
      (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs)
    hcur0
  have hdec0 := shared_long_prefix_decrement remaining (cursor + 1)
  have hdec := cpsTripleWithin_frameR
    ((regIs .x30
        ((acc <<< 8) |||
          (extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
      (regIs .x31 ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
      (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs)
    hdec0
  have hback0 := shared_long_prefix_loop_backedge (cursor + 1) (remaining - 1)
  have hback := cpsTripleWithin_frameR
    ((regIs .x30
        ((acc <<< 8) |||
          (extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
      (regIs .x31 ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
      (dwordAddr ↦ₘ wordVal))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs)
    hback0
  have s1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hntaken hshift
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s1 hload
  have s3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s2 hacc
  have s4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s3 hcur
  have s5 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s4 hdec
  have s6 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s5 hback
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) s6

/-! One-byte long-prefix decode: one nonzero iteration then the zero-remaining
exit to `S+136`.  Entry is the loop header at `S+108` with `remaining = 1`. -/
theorem shared_long_prefix_one_byte_to_payload_base
    (acc cursor oldByte dwordAddr wordVal : Word)
    (halign : alignToDword cursor = dwordAddr)
    (hvalid : isValidByteAccess cursor = true) :
    cpsTripleWithin 8 (RlpWalkNextStrictTie.S + 108)
      (RlpWalkNextStrictTie.S + 136) RlpWalkNextStrictTie.sharedCode
      ((regIs .x30 acc) ** (regIs .x29 cursor) ** (regIs .x28 (1 : Word)) **
        (regIs .x31 oldByte) ** (regIs .x0 (0 : Word)) **
        (dwordAddr ↦ₘ wordVal))
      ((regIs .x30
          ((acc <<< 8) |||
            (extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
        (regIs .x29 (cursor + 1)) ** (regIs .x28 (0 : Word)) **
        (regIs .x31 ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  have hne : (1 : Word) ≠ 0 := by decide
  have hiter := shared_long_prefix_one_iter acc cursor (1 : Word) oldByte
    dwordAddr wordVal hne halign hvalid
  -- After one iter: remaining = 0, at S+108; take the zero exit.
  have hbr0 := shared_long_prefix_branch (0 : Word)
  have htaken0 := cpsBranchWithin_takenStripPure2 hbr0 (by
    intro _ hQf
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).mp h_rest).2)
  have htaken := cpsTripleWithin_frameR
    ((regIs .x30
        ((acc <<< 8) |||
          (extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
      (regIs .x29 (cursor + 1)) **
      (regIs .x31 ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
      (dwordAddr ↦ₘ wordVal))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs)
    htaken0
  -- `one_iter` leaves remaining-1 = 0 definitionally for remaining=1.
  have hiter' : cpsTripleWithin 7 (RlpWalkNextStrictTie.S + 108)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x30 acc) ** (regIs .x29 cursor) ** (regIs .x28 (1 : Word)) **
        (regIs .x31 oldByte) ** (regIs .x0 (0 : Word)) **
        (dwordAddr ↦ₘ wordVal))
      ((regIs .x30
          ((acc <<< 8) |||
            (extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
        (regIs .x29 (cursor + 1)) ** (regIs .x28 (0 : Word)) **
        (regIs .x31 ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
    simpa using hiter
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hiter' htaken
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp) hseq)

/-! ## Long-prefix preamble `S+88` → `S+108`

Index 22–26 of `rlpWalkNextShared_prog`: compute `remaining = pfx - 247`,
stash it in `x13`, set the length-cursor to `listBase + 1`, and clear the
accumulator before the loop header. -/
theorem shared_long_prefix_li247 (old7 : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 92) RlpWalkNextStrictTie.sharedCode
      (regIs .x7 old7) (regIs .x7 (247 : Word)) := by
  have h := li_spec_gen_within .x7 old7 (247 : Word)
    (RlpWalkNextStrictTie.S + 88) (by decide)
  rw [show RlpWalkNextStrictTie.S + 88 + 4 = RlpWalkNextStrictTie.S + 92 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 88)
      (.LI .x7 (247 : Word)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 22 (RlpWalkNextStrictTie.S + 88)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_remaining (pfx oldRem : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 92)
      (RlpWalkNextStrictTie.S + 96) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) ** (regIs .x28 oldRem))
      ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (pfx - 247))) := by
  have h := sub_spec_gen_within .x28 .x6 .x7 pfx (247 : Word) oldRem
    (RlpWalkNextStrictTie.S + 92) (by decide)
  rw [show RlpWalkNextStrictTie.S + 92 + 4 = RlpWalkNextStrictTie.S + 96 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 92)
      (.SUB .x28 .x6 .x7) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 23 (RlpWalkNextStrictTie.S + 92)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_stash_len (remaining old13 : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 96)
      (RlpWalkNextStrictTie.S + 100) RlpWalkNextStrictTie.sharedCode
      ((regIs .x28 remaining) ** (regIs .x13 old13))
      ((regIs .x28 remaining) ** (regIs .x13 remaining)) := by
  have h := mv_spec_gen_within .x13 .x28 remaining old13
    (RlpWalkNextStrictTie.S + 96) (by decide)
  rw [show RlpWalkNextStrictTie.S + 96 + 4 = RlpWalkNextStrictTie.S + 100 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 96)
      (.MV .x13 .x28) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 24 (RlpWalkNextStrictTie.S + 96)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

theorem shared_long_prefix_len_cursor (listBase old29 : Word) :
    cpsTripleWithin 1 (RlpWalkNextStrictTie.S + 100)
      (RlpWalkNextStrictTie.S + 104) RlpWalkNextStrictTie.sharedCode
      ((regIs .x5 listBase) ** (regIs .x29 old29))
      ((regIs .x5 listBase) ** (regIs .x29 (listBase + 1))) := by
  have h := addi_spec_gen_within .x29 .x5 old29 listBase (1 : BitVec 12)
    (RlpWalkNextStrictTie.S + 100) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    show listBase + (1 : Word) = listBase + 1 by bv_omega,
    show RlpWalkNextStrictTie.S + 100 + 4 = RlpWalkNextStrictTie.S + 104 by bv_omega] at h
  have hmono : ∀ a i, CodeReq.singleton (RlpWalkNextStrictTie.S + 100)
      (.ADDI .x29 .x5 (1 : BitVec 12)) a = some i →
      CodeReq.ofProg RlpWalkNextStrictTie.S rlpWalkNextShared_prog a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr RlpWalkNextStrictTie.S
      rlpWalkNextShared_prog 25 (RlpWalkNextStrictTie.S + 100)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num)
      (by rw [RlpWalkNextStrictTie.shared_length]; norm_num) (by bv_omega))
  have hcode := cpsTripleWithin_extend_code hmono h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hcode

/-- Preamble from the long-arm entry through accumulator init, landing on the
loop header with `remaining = pfx - 247`, `x13 = remaining`, `x29 = listBase+1`,
`x30 = 0`. -/
theorem shared_long_prefix_preamble
    (pfx listBase old7 oldRem old13 old29 oldAcc : Word) :
    cpsTripleWithin 5 (RlpWalkNextStrictTie.S + 88)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x6 pfx) ** (regIs .x7 old7) ** (regIs .x28 oldRem) **
        (regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
        (regIs .x30 oldAcc))
      ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
        (regIs .x28 (pfx - 247)) ** (regIs .x13 (pfx - 247)) **
        (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)) **
        (regIs .x30 (0 : Word))) := by
  have hli0 := shared_long_prefix_li247 old7
  have hli := cpsTripleWithin_frameR
    ((regIs .x6 pfx) ** (regIs .x28 oldRem) ** (regIs .x13 old13) **
      (regIs .x5 listBase) ** (regIs .x29 old29) ** (regIs .x30 oldAcc))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hli0
  have hrem0 := shared_long_prefix_remaining pfx oldRem
  have hrem := cpsTripleWithin_frameR
    ((regIs .x13 old13) ** (regIs .x5 listBase) ** (regIs .x29 old29) **
      (regIs .x30 oldAcc))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hrem0
  have hstash0 := shared_long_prefix_stash_len (pfx - 247) old13
  have hstash := cpsTripleWithin_frameR
    ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) ** (regIs .x5 listBase) **
      (regIs .x29 old29) ** (regIs .x30 oldAcc))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hstash0
  have hcur0 := shared_long_prefix_len_cursor listBase old29
  have hcur := cpsTripleWithin_frameR
    ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
      (regIs .x28 (pfx - 247)) ** (regIs .x13 (pfx - 247)) **
      (regIs .x30 oldAcc))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hcur0
  have hacc0 := shared_long_prefix_init_acc oldAcc
  have hacc := cpsTripleWithin_frameR
    ((regIs .x6 pfx) ** (regIs .x7 (247 : Word)) **
      (regIs .x28 (pfx - 247)) ** (regIs .x13 (pfx - 247)) **
      (regIs .x5 listBase) ** (regIs .x29 (listBase + 1)))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs)
    hacc0
  have s1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hli hrem
  have s2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s1 hstash
  have s3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s2 hcur
  have s4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) s3 hacc
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) s4

/-! ## n-iteration long-prefix loop

Parametric over a concrete `Nat` count `n = remaining`.  The inductive step
reuses `shared_long_prefix_one_iter`.  Window hypotheses require every loaded
byte to share one dword (same shape as Phase2). -/
def sharedLongAcc (wordVal : Word) (acc ptr : Word) : Nat → Word
  | 0 => acc
  | k + 1 =>
      sharedLongAcc wordVal
        ((acc <<< 8) |||
          (extractByte wordVal (byteOffset ptr)).zeroExtend 64)
        (ptr + 1) k

def sharedLongLastByte (wordVal : Word) (cursor oldByte : Word) : Nat → Word
  | 0 => oldByte
  | n + 1 =>
      (extractByte wordVal (byteOffset (cursor + BitVec.ofNat 64 n))).zeroExtend 64

theorem sharedLongAcc_zero (wordVal acc ptr : Word) :
    sharedLongAcc wordVal acc ptr 0 = acc := rfl

theorem sharedLongAcc_succ (wordVal acc ptr : Word) (k : Nat) :
    sharedLongAcc wordVal acc ptr (k + 1) =
      sharedLongAcc wordVal
        ((acc <<< 8) |||
          (extractByte wordVal (byteOffset ptr)).zeroExtend 64)
        (ptr + 1) k := rfl

theorem sharedLongLastByte_zero (wordVal cursor oldByte : Word) :
    sharedLongLastByte wordVal cursor oldByte 0 = oldByte := rfl

theorem sharedLongLastByte_succ (wordVal cursor oldByte : Word) (n : Nat) :
    sharedLongLastByte wordVal cursor oldByte (n + 1) =
      (extractByte wordVal (byteOffset (cursor + BitVec.ofNat 64 n))).zeroExtend 64 :=
  rfl

theorem cursor_add_ofNat_succ (cursor : Word) (i : Nat) :
    cursor + BitVec.ofNat 64 (i + 1) = (cursor + 1) + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sharedLongLastByte_succ_step (wordVal cursor oldByte : Word) (k : Nat) :
    sharedLongLastByte wordVal cursor oldByte (k + 1) =
      sharedLongLastByte wordVal (cursor + 1)
        ((extractByte wordVal (byteOffset cursor)).zeroExtend 64) k := by
  cases k with
  | zero =>
      simp [sharedLongLastByte_succ, sharedLongLastByte_zero,
        show cursor + BitVec.ofNat 64 0 = cursor by simp]
  | succ k' =>
      simp only [sharedLongLastByte_succ]
      rw [cursor_add_ofNat_succ]

theorem word_ofNat_succ_sub_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) - (1 : Word) = BitVec.ofNat 64 k := by
  have hsign : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hsub : BitVec.ofNat 64 (k + 1) - (1 : Word) =
      BitVec.ofNat 64 (k + 1) + signExtend12 (-1 : BitVec 12) := by
    rw [hsign]
    bv_omega
  have hdec : BitVec.ofNat 64 (k + 1) + signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat =
        18446744073709551615 := by decide
    rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hsub, hdec]

theorem word_ofNat_succ_ne_zero' (k : Nat) (hk : k + 1 ≤ 8) :
    BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
  | n + 8 => omega

/-- Run `n` loop iterations, staying at the header with `remaining = 0`. -/
theorem shared_long_prefix_loop_to_zero
    (n : Nat) (hn : n ≤ 8)
    (acc cursor oldByte dwordAddr wordVal : Word)
    (hwin : ∀ i, i < n →
      alignToDword (cursor + BitVec.ofNat 64 i) = dwordAddr ∧
      isValidByteAccess (cursor + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (7 * n) (RlpWalkNextStrictTie.S + 108)
      (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
      ((regIs .x30 acc) ** (regIs .x29 cursor) **
        (regIs .x28 (BitVec.ofNat 64 n)) ** (regIs .x31 oldByte) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
      ((regIs .x30 (sharedLongAcc wordVal acc cursor n)) **
        (regIs .x29 (cursor + BitVec.ofNat 64 n)) **
        (regIs .x28 (0 : Word)) **
        (regIs .x31 (sharedLongLastByte wordVal cursor oldByte n)) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  induction n generalizing acc cursor oldByte with
  | zero =>
      have hrefl :=
        cpsTripleWithin_refl (addr := RlpWalkNextStrictTie.S + 108)
          (P :=
            ((regIs .x30 acc) ** (regIs .x29 cursor) **
              (regIs .x28 (0 : Word)) ** (regIs .x31 oldByte) **
              (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)))
          (fun _ hp => hp)
      have hcode := cpsTripleWithin_extend_code
        (cr := CodeReq.empty) (cr' := RlpWalkNextStrictTie.sharedCode)
        (fun _ _ h => nomatch h) hrefl
      have hpre :
          ((regIs .x30 acc) ** (regIs .x29 cursor) **
            (regIs .x28 (BitVec.ofNat 64 0)) ** (regIs .x31 oldByte) **
            (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) =
          ((regIs .x30 acc) ** (regIs .x29 cursor) **
            (regIs .x28 (0 : Word)) ** (regIs .x31 oldByte) **
            (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
        simp only [show (BitVec.ofNat 64 0 : Word) = 0 from rfl]
      have hpost :
          ((regIs .x30 (sharedLongAcc wordVal acc cursor 0)) **
            (regIs .x29 (cursor + BitVec.ofNat 64 0)) **
            (regIs .x28 (0 : Word)) **
            (regIs .x31 (sharedLongLastByte wordVal cursor oldByte 0)) **
            (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) =
          ((regIs .x30 acc) ** (regIs .x29 cursor) **
            (regIs .x28 (0 : Word)) ** (regIs .x31 oldByte) **
            (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
        simp only [sharedLongAcc_zero, sharedLongLastByte_zero,
          show cursor + (0 : Word) = cursor by bv_omega,
          show (BitVec.ofNat 64 0 : Word) = 0 from rfl]
      simpa [hpre, hpost] using hcode
  | succ k ih =>
      have hne := word_ofNat_succ_ne_zero' k (by omega)
      obtain ⟨ha0, hv0⟩ := hwin 0 (by omega)
      rw [show cursor + BitVec.ofNat 64 0 = cursor by simp] at ha0 hv0
      have hiter := shared_long_prefix_one_iter acc cursor
        (BitVec.ofNat 64 (k + 1)) oldByte dwordAddr wordVal hne ha0 hv0
      have hwin' : ∀ i, i < k →
          alignToDword ((cursor + 1) + BitVec.ofNat 64 i) = dwordAddr ∧
          isValidByteAccess ((cursor + 1) + BitVec.ofNat 64 i) = true := by
        intro i hi
        have h := hwin (i + 1) (by omega)
        rwa [cursor_add_ofNat_succ cursor i] at h
      have hrem := word_ofNat_succ_sub_one k
      have hiter' : cpsTripleWithin 7 (RlpWalkNextStrictTie.S + 108)
          (RlpWalkNextStrictTie.S + 108) RlpWalkNextStrictTie.sharedCode
          ((regIs .x30 acc) ** (regIs .x29 cursor) **
            (regIs .x28 (BitVec.ofNat 64 (k + 1))) ** (regIs .x31 oldByte) **
            (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
          ((regIs .x30
              ((acc <<< 8) |||
                (extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
            (regIs .x29 (cursor + 1)) ** (regIs .x28 (BitVec.ofNat 64 k)) **
            (regIs .x31
              ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)) **
            (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
        rw [← hrem]; exact hiter
      have ihspec := ih (by omega)
        ((acc <<< 8) |||
          (extractByte wordVal (byteOffset cursor)).zeroExtend 64)
        (cursor + 1)
        ((extractByte wordVal (byteOffset cursor)).zeroExtend 64)
        hwin'
      have composed := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hiter' ihspec
      have hsteps : 7 * (k + 1) = 7 + 7 * k := by omega
      rw [hsteps, sharedLongAcc_succ, sharedLongLastByte_succ_step,
        cursor_add_ofNat_succ]
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by xperm_hyp hp) composed

/-- Full n-byte long-prefix decode: `n` iterations then the zero-remaining exit
to `S+136`. -/
theorem shared_long_prefix_n_iter
    (n : Nat) (hn : n ≤ 8)
    (acc cursor oldByte dwordAddr wordVal : Word)
    (hwin : ∀ i, i < n →
      alignToDword (cursor + BitVec.ofNat 64 i) = dwordAddr ∧
      isValidByteAccess (cursor + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (7 * n + 1) (RlpWalkNextStrictTie.S + 108)
      (RlpWalkNextStrictTie.S + 136) RlpWalkNextStrictTie.sharedCode
      ((regIs .x30 acc) ** (regIs .x29 cursor) **
        (regIs .x28 (BitVec.ofNat 64 n)) ** (regIs .x31 oldByte) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal))
      ((regIs .x30 (sharedLongAcc wordVal acc cursor n)) **
        (regIs .x29 (cursor + BitVec.ofNat 64 n)) **
        (regIs .x28 (0 : Word)) **
        (regIs .x31 (sharedLongLastByte wordVal cursor oldByte n)) **
        (regIs .x0 (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  have hloop := shared_long_prefix_loop_to_zero n hn acc cursor oldByte
    dwordAddr wordVal hwin
  have hbr0 := shared_long_prefix_branch (0 : Word)
  have htaken0 := cpsBranchWithin_takenStripPure2 hbr0 (by
    intro _ hQf
    obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).mp h_rest).2)
  have htaken := cpsTripleWithin_frameR
    ((regIs .x30 (sharedLongAcc wordVal acc cursor n)) **
      (regIs .x29 (cursor + BitVec.ofNat 64 n)) **
      (regIs .x31 (sharedLongLastByte wordVal cursor oldByte n)) **
      (dwordAddr ↦ₘ wordVal))
    (by
      repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs)
    htaken0
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hloop htaken
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) hseq

end EvmAsm.Codegen.RlpWalkNextStrictFuel
