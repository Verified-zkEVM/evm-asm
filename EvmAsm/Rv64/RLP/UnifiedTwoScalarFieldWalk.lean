/-
  EvmAsm.Rv64.RLP.UnifiedTwoScalarFieldWalk

  EL.3 / Phase 5 — the first end-to-end MULTI-FIELD walk. Two contributions:

  1. `unified_scalar_field_decode_and_store_at_regOwn` — a `regOwn`-precondition
     variant of `unified_scalar_field_decode_and_store`. The decode clobbers its
     scratch registers (`x5, x10, x12, x14`) and so RELEASES them as `regOwn` in its
     post; the concrete unit, however, REQUIRES them concrete in its pre, so a second
     field's unit cannot consume the first's output. Peeling those four scratch
     registers to `regOwn` (via `cpsTripleWithin_of_forall_regIs_to_regOwn`) makes the
     unit callable after a prior field has run.

  2. `unified_two_scalar_field_walk` — decode-and-store field A → output slot `offA`,
     then field B → slot `offB`, through one output base pointer `rOut` (the STF
     calling convention: output struct base in `a2`, one slot offset per field). The
     concrete unit handles field A; the `regOwn` variant handles field B (its scratch
     is `regOwn` after A). The first unit's `x13` (advanced to the next field) feeds
     the second's payload pointer with no glue code, exactly as the sibling-descent
     walk (`unified_list_descend_two_siblings_bridge`) chains two descents.

  Layout (program base `base`; aligned `regionBase`, buffer `bs`, field-A offset `OA`):
      base       < unified_scalar_field_decode_and_store : field A >   (base .. base+184)
      base+184   < unified_scalar_field_decode_and_store : field B >   (base+184 .. base+368)
      base+368   (exit)
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldStore

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

end EvmAsm.Rv64.RLP
