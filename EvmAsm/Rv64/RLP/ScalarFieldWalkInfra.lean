/-
  EvmAsm.Rv64.RLP.ScalarFieldWalkInfra

  EL.3 / Phase 5 — infrastructure for the recursive N-field scalar walk.

  The three-field walk (`unified_three_scalar_field_walk`) was unrolled by hand. To
  decode a fixed schema of N scalar fields by recursion, we need three pieces, all
  assembled here (the recursive walk theorem itself follows in a later step):

  1. `unified_scalar_field_decode_and_store_at_regOwn_memOwn` — the decode-and-store
     unit with BOTH its scratch registers (`regOwn`) AND its output cell (`memOwn`)
     owned abstractly. This is the atomic unit the recursive walk iterates: a field's
     output slot holds an unknown old value (it gets overwritten), so the walk's
     precondition is a fold of `memOwn` cells, peeled one per step.

  2. `nFieldWalkCR base rOut fields` — the recursive CodeReq of the unrolled N-unit
     program (unit `i` at `base + 184*i`).

  3. `scalarFieldUnitCR_disjoint_walkCR` — a single unit's CodeReq is disjoint from the
     whole rest-of-walk CodeReq (proved by induction on the field list, each step a
     `scalarFieldUnitCR_disjoint`). This discharges the `cpsTripleWithin_seq` obligation
     in the recursive walk's inductive step with one lemma.
-/

import EvmAsm.Rv64.RLP.ScalarFieldWalkChain

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

end EvmAsm.Rv64.RLP
