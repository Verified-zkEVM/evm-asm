/-
  EvmAsm.Rv64.RLP.SchemaListWalk

  EL.3 / Phase 5 — the RLP-LIST schema decoder: descend one list level to its payload, then run
  the N-field fold over the element fields. This is the shape every real STF structure takes —
  a transaction / block header is an RLP list whose elements are the fields.

  `unified_list_header_descend` (the "descend one list level to its payload" primitive) leaves
  `x13` at the payload pointer and clobbers the scratch registers; its post has exactly the same
  atom order as `schema_walk`'s `schemaINV` precondition, so bridging it is a positional
  scratch weaken (concrete → `regOwn`) plus an `x13`-pointer rewrite (`hptr` gives the payload
  offset from the list prefix). The output region is framed through the descend. The result:
  decode a list-structured schema into one shared output `bytesRegion`, coinciding field-by-field
  with the RLP spec (`schemaDecodes`).
-/

import EvmAsm.Rv64.RLP.SchemaFold
import EvmAsm.Rv64.RLP.UnifiedListDescendConcrete

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

end EvmAsm.Rv64.RLP
