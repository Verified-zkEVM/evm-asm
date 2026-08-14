/-
  EvmAsm.Codegen.Programs.RlpWalkNextStrictFuelModel

  Structural fuel model for #12300.  The strict LIST path is one mutual
  recursion, not three independent calls:

      shared -> validate_payload -> nested -> shared

  The index carried here is twice the number of bytes remaining in the current
  cursor window.  The constructors deliberately expose the three back-edges
  and require a cursor advance before each one.  The semantic postconditions
  are intentionally not in this checkpoint; this file establishes the
  well-founded shape that the eventual machine triple will consume.
-/

import EvmAsm.Codegen.Programs.RlpWalkNextStrictTie
import EvmAsm.Rv64.RLP.WalkItemDeterminism
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.Tactics.XPermPure
import EvmAsm.Rv64.Tactics.DropPure

namespace EvmAsm.Codegen.RlpWalkNextStrictFuel

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP

/-- Remaining input bytes in a cursor window.  The end is exclusive. -/
def remainingBytes (cursor endOff : Nat) : Nat := endOff - cursor

/-- The wrapper's two-fuel-per-byte budget for a cursor window.

The factor `2` is load-bearing rather than slack: the mutual knot alternates
`Shared → Validate → Nested → Shared`, and both the outer list edge and the
inner item edge must consume a strict index.  A one-fuel-per-byte index would
be enough for one of those legs in isolation but does not expose the strict
decrease at both legs of the `S → V → S` cycle. -/
def cycleFuel (cursor endOff : Nat) : Nat := 2 * remainingBytes cursor endOff

/-- Consuming at least one byte strictly decreases the two-fuel budget, even
    when the recursive call keeps the same enclosing end pointer. -/
theorem cycleFuel_strict_of_advance
    {cursor next endOff : Nat}
    (hcursor : cursor < next) (hend : next ≤ endOff) :
    cycleFuel next endOff < cycleFuel cursor endOff := by
  unfold cycleFuel remainingBytes
  omega

/-! The three call contracts are mutually recursive.  They are a structural
    skeleton, not the final machine postcondition: each list/item arm records
    the exact byte-window facts needed by the eventual CPS composition. -/

mutual

  /-- `rlp_walk_next_shared`: a list arm enters payload validation. -/
  inductive SharedFuel (bytes : List Byte) : Nat → Nat → Nat → Prop where
    | nonList {cursor endOff}
        (hwindow : cursor ≤ endOff ∧ endOff ≤ bytes.length) :
        SharedFuel bytes (cycleFuel cursor endOff) cursor endOff
    | list {cursor outerEnd payloadStart payloadEnd}
        (hcursor : cursor < payloadStart)
        (hpayload : payloadStart ≤ payloadEnd)
        (hpayloadEnd : payloadEnd ≤ outerEnd)
        (houter : outerEnd ≤ bytes.length)
        (hvalidate : ValidateFuel bytes (cycleFuel payloadStart payloadEnd)
          payloadStart payloadEnd) :
        SharedFuel bytes (cycleFuel cursor outerEnd) cursor outerEnd

  /-- `rlp_validate_payload`: either the payload is empty or one item is
      decoded and the cursor advances before the next nested call. -/
  inductive ValidateFuel (bytes : List Byte) : Nat → Nat → Nat → Prop where
    | empty {cursor endOff}
        (hwindow : cursor = endOff ∧ endOff ≤ bytes.length) :
        ValidateFuel bytes (cycleFuel cursor endOff) cursor endOff
    | item {cursor next endOff}
        (hcursor : cursor < next)
        (hend : next ≤ endOff)
        (hwindow : endOff ≤ bytes.length)
        (hnested : NestedFuel bytes (cycleFuel next endOff) next endOff) :
        ValidateFuel bytes (cycleFuel cursor endOff) cursor endOff

  /-- `rlp_walk_next_nested`: one nested item returns to the shared walker at
      the advanced cursor. -/
  inductive NestedFuel (bytes : List Byte) : Nat → Nat → Nat → Prop where
    /-- The nested wrapper may enter the shared walker at the exact payload
        end.  The shared core's `BGEU cursor,end` then returns success without
        consuming another item; this is the terminal case for a one-item
        payload, not an omitted recursive step. -/
    | done {cursor endOff}
        (heq : cursor = endOff)
        (hwindow : endOff ≤ bytes.length) :
        NestedFuel bytes (cycleFuel cursor endOff) cursor endOff
    | descend {cursor next endOff}
        (hcursor : cursor < next)
        (hend : next ≤ endOff)
        (hwindow : endOff ≤ bytes.length)
        (hshared : SharedFuel bytes (cycleFuel next endOff) next endOff) :
        NestedFuel bytes (cycleFuel cursor endOff) cursor endOff

end

/-! The three edge lemmas are the checkpoint's key obligation.  The LIST arm
    may also shrink the enclosing end pointer, so retain that stronger form in
    addition to the same-window cursor lemma above. -/

theorem cycleFuel_strict_of_window
    {cursor payloadStart payloadEnd outerEnd : Nat}
    (hcursor : cursor < payloadStart)
    (hpayload : payloadStart ≤ payloadEnd)
    (hpayloadEnd : payloadEnd ≤ outerEnd) :
    cycleFuel payloadStart payloadEnd < cycleFuel cursor outerEnd := by
  unfold cycleFuel remainingBytes
  omega

theorem shared_list_edge_decreases
    {cursor outerEnd payloadStart payloadEnd : Nat}
    (hcursor : cursor < payloadStart)
    (hpayload : payloadStart ≤ payloadEnd)
    (hpayloadEnd : payloadEnd ≤ outerEnd) :
    cycleFuel payloadStart payloadEnd < cycleFuel cursor outerEnd := by
  exact cycleFuel_strict_of_window hcursor hpayload hpayloadEnd

/-! Named boundary lemmas keep the zero-length and last-item cases explicit.
These are the two degenerate list shapes where both payload bounds can
coincide; proving them once avoids hiding the strictness argument in an
inline arithmetic simplification at a recursive call site. -/

theorem shared_list_edge_decreases_zero_payload
    {cursor payloadStart outerEnd : Nat}
    (hcursor : cursor < payloadStart)
    (hpayloadEnd : payloadStart ≤ outerEnd) :
    cycleFuel payloadStart payloadStart < cycleFuel cursor outerEnd := by
  exact cycleFuel_strict_of_window hcursor le_rfl hpayloadEnd

theorem shared_list_edge_decreases_last_item
    {cursor payloadStart payloadEnd : Nat}
    (hcursor : cursor < payloadStart)
    (hpayload : payloadStart ≤ payloadEnd) :
    cycleFuel payloadStart payloadEnd < cycleFuel cursor payloadEnd := by
  exact cycleFuel_strict_of_window hcursor hpayload le_rfl

theorem shared_list_edge_decreases_zero_last
    {cursor payloadStart : Nat}
    (hcursor : cursor < payloadStart) :
    cycleFuel payloadStart payloadStart < cycleFuel cursor payloadStart := by
  exact shared_list_edge_decreases_zero_payload hcursor le_rfl

theorem validate_item_edge_decreases
    {cursor next endOff : Nat}
    (hcursor : cursor < next) (hend : next ≤ endOff) :
    cycleFuel next endOff < cycleFuel cursor endOff := by
  exact cycleFuel_strict_of_advance hcursor hend

theorem nested_shared_edge_decreases
    {cursor next endOff : Nat}
    (hcursor : cursor < next) (hend : next ≤ endOff) :
    cycleFuel next endOff < cycleFuel cursor endOff := by
  exact cycleFuel_strict_of_advance hcursor hend

/-! A small reusable knot eliminator.  The two machine contract families must
be indexed by the *same* `cycleFuel`; a family quantified at a raw
`endOff-cursor` or at an unrelated fixed CPS bound cannot be supplied by this
induction hypothesis.  The step receives both contracts at every strictly
smaller index, so `Shared → Validate → Nested → Shared` can consume whichever
side the current arm enters. -/
theorem cycleFuel_mutual_strong_induction
    {Shared Validate : Nat → Prop}
    (hstep : ∀ fuel,
      (∀ k, k < fuel → Shared k ∧ Validate k) →
        Shared fuel ∧ Validate fuel) :
    ∀ fuel, Shared fuel ∧ Validate fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      exact hstep fuel ih

/-! The CPS proof has three mutually recursive contract families, not merely a
Shared/Validate pair: the validator's item arm enters the nested wrapper, and
the nested wrapper re-enters the shared walker after advancing the cursor.
Keep that third family explicit in the eliminator so the induction hypothesis
cannot hide the `Validate → Nested → Shared` edge in a constructor proof. -/
theorem cycleFuel_mutual_strong_induction3
    {Shared Validate Nested : Nat → Prop}
    (hstep : ∀ fuel,
      (∀ k, k < fuel → Shared k ∧ Validate k ∧ Nested k) →
        Shared fuel ∧ Validate fuel ∧ Nested fuel) :
    ∀ fuel, Shared fuel ∧ Validate fuel ∧ Nested fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      exact hstep fuel ih

/-! The real semantic families now instantiate the strong-induction helper.
The terminal `NestedFuel.done` case is essential: a one-item payload advances
the nested call to `endOff`, where the shared core's empty-window check returns
success without another cursor advance. -/
def SharedFuelFamily (bytes : List Byte) (fuel : Nat) : Prop :=
  ∀ {cursor endOff}, fuel = cycleFuel cursor endOff →
    cursor ≤ endOff → endOff ≤ bytes.length →
      SharedFuel bytes fuel cursor endOff

def ValidateFuelFamily (bytes : List Byte) (fuel : Nat) : Prop :=
  ∀ {cursor endOff}, fuel = cycleFuel cursor endOff →
    cursor ≤ endOff → endOff ≤ bytes.length →
      ValidateFuel bytes fuel cursor endOff

def NestedFuelFamily (bytes : List Byte) (fuel : Nat) : Prop :=
  ∀ {cursor endOff}, fuel = cycleFuel cursor endOff →
    cursor ≤ endOff → endOff ≤ bytes.length →
      NestedFuel bytes fuel cursor endOff

/-! A first consumer of the three-family eliminator.  This witness intentionally
uses the abstract constructors rather than machine contracts, but it exercises
all three strict edges: a non-empty shared window enters validation, validation
enters the nested wrapper, and nested descent re-enters shared at a smaller
cycleFuel index.  The terminal nested case closes the one-item boundary. -/
theorem mutual_fuel_witness_all (bytes : List Byte) :
    ∀ fuel, SharedFuelFamily bytes fuel ∧
      ValidateFuelFamily bytes fuel ∧ NestedFuelFamily bytes fuel := by
  intro fuel
  apply cycleFuel_mutual_strong_induction3
  intro fuel ih
  constructor
  · intro cursor endOff hfuel hcursor hend
    by_cases heq : cursor = endOff
    · simpa [hfuel] using (SharedFuel.nonList (bytes := bytes)
        (cursor := cursor) (endOff := endOff) ⟨hcursor, hend⟩)
    · have hlt : cursor < endOff := Nat.lt_of_le_of_ne hcursor heq
      let payloadStart := cursor + 1
      have hpayloadStart : cursor < payloadStart := by
        dsimp [payloadStart]
        omega
      have hpayloadEnd : payloadStart ≤ endOff := by
        dsimp [payloadStart]
        omega
      have hchild : cycleFuel payloadStart endOff < fuel := by
        rw [hfuel]
        exact cycleFuel_strict_of_window hpayloadStart hpayloadEnd le_rfl
      have hvalidate := (ih (cycleFuel payloadStart endOff) hchild).2.1
        (cursor := payloadStart) (endOff := endOff) rfl hpayloadEnd hend
      simpa [hfuel] using (SharedFuel.list (bytes := bytes)
        hpayloadStart hpayloadEnd le_rfl hend hvalidate)
  · constructor
    · intro cursor endOff hfuel hcursor hend
      by_cases heq : cursor = endOff
      · subst endOff
        simpa [hfuel] using (ValidateFuel.empty (bytes := bytes) ⟨rfl, hend⟩)
      · have hlt : cursor < endOff := Nat.lt_of_le_of_ne hcursor heq
        let next := cursor + 1
        have hnext : next ≤ endOff := by
          dsimp [next]
          omega
        have hitem : cursor < next := by
          dsimp [next]
          omega
        have hchild : cycleFuel next endOff < fuel := by
          rw [hfuel]
          exact cycleFuel_strict_of_advance hitem hnext
        have hnested := (ih (cycleFuel next endOff) hchild).2.2
          (cursor := next) (endOff := endOff) rfl hnext hend
        simpa [hfuel] using (ValidateFuel.item (bytes := bytes)
          hitem hnext hend hnested)
    · intro cursor endOff hfuel hcursor hend
      by_cases heq : cursor = endOff
      · simpa [hfuel] using (NestedFuel.done (bytes := bytes) heq hend)
      · have hlt : cursor < endOff := Nat.lt_of_le_of_ne hcursor heq
        let next := cursor + 1
        have hnext : next ≤ endOff := by
          dsimp [next]
          omega
        have hcursorNext : cursor < next := by
          dsimp [next]
          omega
        have hchild : cycleFuel next endOff < fuel := by
          rw [hfuel]
          exact cycleFuel_strict_of_advance hcursorNext hnext
        have hshared := (ih (cycleFuel next endOff) hchild).1
          (cursor := next) (endOff := endOff) rfl hnext hend
        simpa [hfuel] using (NestedFuel.descend (bytes := bytes)
          hcursorNext hnext hend hshared)

theorem mutual_fuel_witness (bytes : List Byte) :
    ∀ fuel, SharedFuelFamily bytes fuel ∧ ValidateFuelFamily bytes fuel := by
  intro fuel
  rcases mutual_fuel_witness_all bytes fuel with ⟨hshared, hvalidate, _⟩
  exact ⟨hshared, hvalidate⟩

end EvmAsm.Codegen.RlpWalkNextStrictFuel
