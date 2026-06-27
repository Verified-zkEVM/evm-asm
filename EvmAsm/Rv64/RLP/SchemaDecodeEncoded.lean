/-
  EvmAsm.Rv64.RLP.SchemaDecodeEncoded

  EL.3 / Phase 5 — the end-user decode API. Given that the input buffer (from offset `O`) is the
  genuine RLP encoding of the field record — `encode (.list (schemaItems specs)) ++ tail`, with a
  short-list-sized payload — this runs the whole decoder and yields the field-by-field result,
  deriving BOTH the prefix-class fact and `SchemaValid` from the encoding (via the encode bridge
  and `schemaValid_of_concat`). The caller supplies only the encoding fact, per-field core
  validity, and the region/output well-formedness — no RLP-internal proof obligations.
-/

import EvmAsm.Rv64.RLP.SchemaListWalkShort
import EvmAsm.Rv64.RLP.SchemaListEncode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

end EvmAsm.Rv64.RLP
