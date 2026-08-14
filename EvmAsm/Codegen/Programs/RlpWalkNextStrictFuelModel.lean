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

theorem mutual_fuel_witness (bytes : List Byte) :
    ∀ fuel, SharedFuelFamily bytes fuel ∧ ValidateFuelFamily bytes fuel := by
  intro fuel
  apply cycleFuel_mutual_strong_induction
    (Shared := SharedFuelFamily bytes) (Validate := ValidateFuelFamily bytes)
  intro fuel ih
  constructor
  · intro cursor endOff hfuel hcursor hend
    simpa [hfuel] using (SharedFuel.nonList (bytes := bytes)
      (cursor := cursor) (endOff := endOff) ⟨hcursor, hend⟩)
  · intro cursor endOff hfuel hcursor hend
    by_cases heq : cursor = endOff
    · subst endOff
      simpa [hfuel] using (ValidateFuel.empty (bytes := bytes)
        (cursor := cursor) (endOff := cursor) ⟨rfl, hend⟩)
    · have hlt : cursor < endOff := Nat.lt_of_le_of_ne hcursor heq
      let next := cursor + 1
      have hnext : next ≤ endOff := by omega
      have hitem : cursor < next := by dsimp [next]; omega
      have hnested : NestedFuel bytes (cycleFuel next endOff) next endOff := by
        by_cases hlast : next = endOff
        · subst endOff
          exact NestedFuel.done (bytes := bytes) rfl hend
        · have hnextlt : next < endOff := lt_of_le_of_ne hnext hlast
          let next₂ := next + 1
          have hnext₂ : next₂ ≤ endOff := by dsimp [next₂]; omega
          have hchild : cycleFuel next₂ endOff < fuel := by
            rw [hfuel]
            exact cycleFuel_strict_of_advance (by dsimp [next₂]; omega) hnext₂
          have hih := ih (cycleFuel next₂ endOff) hchild
          have hshared := hih.1 (cursor := next₂) (endOff := endOff)
            rfl hnext₂ hend
          exact NestedFuel.descend (bytes := bytes)
            (cursor := next) (next := next₂) (endOff := endOff)
            (by dsimp [next₂]; omega) hnext₂ hend hshared
      simpa [hfuel] using (ValidateFuel.item (bytes := bytes)
        (cursor := cursor) (next := next) (endOff := endOff)
        hitem hnext hend hnested)

end EvmAsm.Codegen.RlpWalkNextStrictFuel
