/-
  EvmAsm.Rv64.RLP.SchemaDecodeEncodedLong

  EL.3 / Phase 5 — long-list end-user decode API. The long-list counterpart of
  `decode_encoded_short_list_schema`: when the input buffer (from `O`) is the genuine RLP
  encoding of the field record as a LONG list (payload `> 55`, the real tx/header case), the
  decoder runs and yields the field-by-field result. The `longList` prefix fact, the
  length-bytes-fit bound, and `SchemaValid` are all derived from the encoding — using the
  `Nat.toBytesBE` length bounds (`1 ≤ lenOfLen ≤ 8`) for the prefix range.
-/

import EvmAsm.Rv64.RLP.SchemaListWalkLong
import EvmAsm.Rv64.RLP.SchemaListEncodeLong

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

end EvmAsm.Rv64.RLP
