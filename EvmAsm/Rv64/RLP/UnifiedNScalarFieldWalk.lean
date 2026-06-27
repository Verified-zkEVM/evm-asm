/-
  EvmAsm.Rv64.RLP.UnifiedNScalarFieldWalk

  EL.3 / Phase 5 — the recursive N-field scalar walk. The keystone for fixed-schema
  STF decoders: decode-and-store a whole LIST of consecutive scalar fields, each to its
  own output slot, through one output base pointer `rOut`.

  Generalizes `unified_three_scalar_field_walk` from a hand-unrolled 3 to an arbitrary
  list `fields : List (BitVec 12 × List Byte)` (output offset, field data) by recursion:
  the inductive step runs the `regOwn`+`memOwn` unit on the head field, then the IH on
  the tail, framing the tail's output cells (a `memOwn` fold) through the head unit and
  the head's written cell through the tail walk. Disjointness of the head unit's CodeReq
  from the rest-of-walk is the step-13 `scalarFieldUnitCR_disjoint_walkCR` lemma. The
  whole program is `nFieldWalkCR` (unit `i` at `base + 184*i`).

  Output slots: pre = a fold of `memOwn` cells (each holds some old value, overwritten);
  post = a fold of `↦ₘ` cells holding the decoded field values.
-/

import EvmAsm.Rv64.RLP.ScalarFieldWalkInfra

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- Total step count of the N-field walk: `Σ (64 + 6 * len_i)`. -/
def nFieldSteps : List (BitVec 12 × List Byte) → Nat
  | [] => 0
  | (_, data) :: rest => (64 + 6 * data.length) + nFieldSteps rest

/-- The output cells of an N-field walk BEFORE the walk: a `**`-fold of `memOwn` slots
    (each holds an unknown old value, to be overwritten). -/
def nFieldOutOwn (outBase : Word) : List (BitVec 12 × List Byte) → Assertion
  | [] => empAssertion
  | (off, _) :: rest => memOwn (outBase + signExtend12 off) ** nFieldOutOwn outBase rest

/-- The output cells AFTER the walk: a `**`-fold of `↦ₘ` slots holding the decoded
    field values. -/
def nFieldOutVal (outBase : Word) : List (BitVec 12 × List Byte) → Assertion
  | [] => empAssertion
  | (off, data) :: rest =>
      ((outBase + signExtend12 off) ↦ₘ BitVec.ofNat 64 (Nat.fromBytesBE data)) **
        nFieldOutVal outBase rest

theorem nFieldOutOwn_pcFree (outBase : Word) (fields : List (BitVec 12 × List Byte)) :
    (nFieldOutOwn outBase fields).pcFree := by
  induction fields with
  | nil => exact pcFree_emp
  | cons f rest ih => exact pcFree_sepConj pcFree_memOwn ih

theorem nFieldOutVal_pcFree (outBase : Word) (fields : List (BitVec 12 × List Byte)) :
    (nFieldOutVal outBase fields).pcFree := by
  induction fields with
  | nil => exact pcFree_emp
  | cons f rest ih => exact pcFree_sepConj pcFree_memIs ih

end EvmAsm.Rv64.RLP
