/-
  EvmAsm.Rv64.RLP.SchemaListDecodeExample

  EL.3 / Phase 5 — concrete end-to-end cross-check of the RLP list decoder. Decodes the short
  RLP list `[0xc4, 0x2a, 0x82, 0x01, 0x02]` — i.e. `RLP.list [bytes [0x2a], bytes [0x01, 0x02]]`
  — at region `0x2000` into a 24-byte output struct at `0x3000` via `x18`, treating the two
  elements as a scalar field (→ 8 bytes at output offset 0) and a 2-byte array field (→ output
  offset 8). The whole pipeline runs: list-header descend ⨾ N-field fold, with `SchemaValid`
  discharged from the single concatenation fact by `schemaValid_of_concat` and the list
  window/pointer discharged by `short_list_schema_walk`. Demonstrates the generic decoder applies
  to a concrete RLP list with zero bespoke proof.
-/

import EvmAsm.Rv64.RLP.SchemaListWalkShort
import EvmAsm.Rv64.RLP.SchemaFoldConcat

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

end EvmAsm.Rv64.RLP
