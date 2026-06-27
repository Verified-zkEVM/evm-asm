/-
  EvmAsm.Rv64.RLP.SchemaDecodeValues

  EL.3 / Phase 5 — end-user decode-to-FIELD-VALUES API. The `decode_encoded_{short,long}_list_schema`
  theorems take RLP-encoded list bytes and yield the operational decode triple plus the per-field
  `schemaDecodes` coincidence (each field decodes as a scalar or a byte array). A real STF consumer
  wants the numeric VALUE of every field uniformly — and (per `UnifiedWideScalarField`) a transaction's
  `u256` fields ride the byte-array path, so the fold reports them via `decode`/`.bytes`.

  This file packages the final step: combine the encoded-list decoders with
  `schemaDecodes_imp_scalarValues` (`SchemaScalarValues`) so the conclusion is `schemaScalarValues` —
  every field's big-endian value at its input offset. The result is the one-shot API behind the
  concrete tx/header decoders: RLP bytes in → operational decode + all field values out, verified.
-/

import EvmAsm.Rv64.RLP.SchemaDecodeEncoded
import EvmAsm.Rv64.RLP.SchemaDecodeEncodedLong
import EvmAsm.Rv64.RLP.SchemaScalarValues

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

end EvmAsm.Rv64.RLP
