/-
 Route-indexed whole-routine contract for K73 (#12346 item 10).

  The four completed route adapters do not share one ambient assertion:
  equal and zero preserve a flat frame, while increase and decrease leave the
  multiply frame and accumulator image in the caller-visible ambient.  This
  file therefore joins the already-proved route triples without pretending
  that those ambients are interchangeable.
-/

import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionEqualDecrease
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeCompositionIncreaseRoute

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionRouteFamily

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionEqualRoute
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionIncreaseRoute
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute
open EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseZero

/-! ## The honest replacement for the retired single-post shape -/

/-- One already-dischargeable K73 route contract.  The pre/post assertions are
    fields rather than re-created here so a route may retain its own ambient
    transition.  In particular, this type cannot silently turn an increase or
    decrease post into the equal-route flat frame. -/
structure K73RouteCase (cr : CodeReq) where
  nSteps : Nat
  pre : Assertion
  post : Assertion
  sound : cpsTripleWithin nSteps K73 (H + 40) cr pre post

/-- The four route cases, in emitted control-flow order: equal, increase,
    nonzero decrease, and zero-gas decrease. -/
structure K73RouteFamily (cr : CodeReq) where
  equal : K73RouteCase cr
  increase : K73RouteCase cr
  decrease : K73RouteCase cr
  zeroDecrease : K73RouteCase cr

/-- A family bound large enough for every route. -/
def k73RouteFamilySteps {cr : CodeReq} (f : K73RouteFamily cr) : Nat :=
  max f.equal.nSteps
    (max f.increase.nSteps (max f.decrease.nSteps f.zeroDecrease.nSteps))

/-- The route-indexed precondition.  It is deliberately a disjunction: a
    caller supplies exactly the static precondition belonging to the route
    whose arithmetic guard holds.  Route-specific scratch/ownership facts are
    not intersected, which would make the composed pre unsatisfiable. -/
def k73RouteFamilyPre {cr : CodeReq} (f : K73RouteFamily cr) : Assertion :=
  fun h =>
    ((f.equal.pre h ∨ f.increase.pre h) ∨ f.decrease.pre h) ∨
      f.zeroDecrease.pre h

/-- The route-indexed postcondition.  Each branch preserves the exact
    route-specific ambient and output relation supplied by its case. -/
def k73RouteFamilyPost {cr : CodeReq} (f : K73RouteFamily cr) : Assertion :=
  fun h =>
    ((f.equal.post h ∨ f.increase.post h) ∨ f.decrease.post h) ∨
      f.zeroDecrease.post h

private theorem k73RouteCase_pad {cr : CodeReq} (f : K73RouteFamily cr)
    (c : K73RouteCase cr) (hle : c.nSteps ≤ k73RouteFamilySteps f) :
    cpsTripleWithin (k73RouteFamilySteps f) K73 (H + 40) cr c.pre c.post :=
  cpsTripleWithin_mono_nSteps hle c.sound

/-- Join the four completed, route-specific K73 triples into one
    whole-routine family contract.  This is a junction, not a fresh callee
    premise: every `K73RouteCase.sound` field is an already-proved triple.
    The resulting contract is intentionally tagged by a disjunction, because
    the route ambients are not definitionally equal and no sound weakening
    identifies them. -/
theorem k73_route_family_spec_within {cr : CodeReq}
    (f : K73RouteFamily cr) :
    cpsTripleWithin (k73RouteFamilySteps f) K73 (H + 40) cr
      (k73RouteFamilyPre f) (k73RouteFamilyPost f) := by
  have heq : cpsTripleWithin (k73RouteFamilySteps f) K73 (H + 40) cr
      f.equal.pre (fun h =>
        ((f.equal.post h ∨ f.increase.post h) ∨ f.decrease.post h) ∨
          f.zeroDecrease.post h) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => Or.inl (Or.inl (Or.inl hq)))
      (k73RouteCase_pad f f.equal (by
        dsimp [k73RouteFamilySteps]
        exact Nat.le_max_left _ _))
  have hincr : cpsTripleWithin (k73RouteFamilySteps f) K73 (H + 40) cr
      f.increase.pre (fun h =>
        ((f.equal.post h ∨ f.increase.post h) ∨ f.decrease.post h) ∨
          f.zeroDecrease.post h) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => Or.inl (Or.inl (Or.inr hq)))
      (k73RouteCase_pad f f.increase (by
        dsimp [k73RouteFamilySteps]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
  have hdecr : cpsTripleWithin (k73RouteFamilySteps f) K73 (H + 40) cr
      f.decrease.pre (fun h =>
        ((f.equal.post h ∨ f.increase.post h) ∨ f.decrease.post h) ∨
          f.zeroDecrease.post h) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => Or.inl (Or.inr hq))
      (k73RouteCase_pad f f.decrease (by
        dsimp [k73RouteFamilySteps]
        exact Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (Nat.le_max_right _ _)
            (Nat.le_max_right _ _))))
  have hzero : cpsTripleWithin (k73RouteFamilySteps f) K73 (H + 40) cr
      f.zeroDecrease.pre (fun h =>
        ((f.equal.post h ∨ f.increase.post h) ∨ f.decrease.post h) ∨
          f.zeroDecrease.post h) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => Or.inr hq)
      (k73RouteCase_pad f f.zeroDecrease (by
        dsimp [k73RouteFamilySteps]
        exact Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (Nat.le_max_right _ _)
            (Nat.le_max_right _ _))))
  have hei := cpsTripleWithin_pre_or heq hincr
  have heid := cpsTripleWithin_pre_or hei hdecr
  have heidz := cpsTripleWithin_pre_or heid hzero
  change cpsTripleWithin (k73RouteFamilySteps f) K73 (H + 40) cr
    (fun h => ((f.equal.pre h ∨ f.increase.pre h) ∨ f.decrease.pre h) ∨
      f.zeroDecrease.pre h)
    (fun h => ((f.equal.post h ∨ f.increase.post h) ∨ f.decrease.post h) ∨
      f.zeroDecrease.post h)
  exact heidz

/-! ## Non-vacuity of the four-case interface

The individual route adapters already carry closed concrete inhabitants.  A
small packaging theorem keeps those witnesses visible at the family boundary;
it does not claim that one concrete test state is a proof of the universal
route family. -/

private noncomputable def k73ConcreteRouteFamily :
    K73RouteFamily EvmAsm.Codegen.HeaderBaseFeeSpec.wholeCode :=
  { equal :=
      { nSteps := _
        pre := _
        post := _
        sound := by
          exact k73_equal_route_adapter_inhabited }
    increase :=
      { nSteps := _
        pre := _
        post := _
        sound := by
          exact k73_incr_route_adapter_inhabited }
    decrease :=
      { nSteps := _
        pre := _
        post := _
        sound := by
          exact k73_decr_route_adapter_inhabited }
    zeroDecrease :=
      { nSteps := _
        pre := _
        post := _
        sound := by
          exact k73_zero_route_adapter_inhabited } }

theorem k73_route_family_cases_inhabited :
    ∃ _f : K73RouteFamily EvmAsm.Codegen.HeaderBaseFeeSpec.wholeCode, True := by
  exact ⟨k73ConcreteRouteFamily, trivial⟩

/-- The packaged current-route family has a closed whole-routine proof.  Its
    pre/post are the four concrete route cases above; this theorem is a
    non-vacuity and junction check, not a claim that those four sample states
    replace the parameterized route adapters. -/
theorem k73_route_family_cases_spec_within :
    cpsTripleWithin (k73RouteFamilySteps k73ConcreteRouteFamily) K73 (H + 40)
      (EvmAsm.Codegen.HeaderBaseFeeSpec.wholeCode)
      (k73RouteFamilyPre k73ConcreteRouteFamily)
      (k73RouteFamilyPost k73ConcreteRouteFamily) :=
  k73_route_family_spec_within k73ConcreteRouteFamily

/-! The fields above retain the exact route-specific proofs rather than a
    premise-free placeholder. -/

/-! The concrete family below is constructed from the four closed route
    inhabitants, not from premise-free placeholders. -/

#print axioms k73_route_family_spec_within
#print axioms k73_route_family_cases_inhabited
#print axioms k73_route_family_cases_spec_within

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionRouteFamily
