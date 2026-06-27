/-
  EvmAsm.Rv64.RLP.SchemaDecodeEncodedExample

  EL.3 / Phase 5 — concrete cross-check of the end-user decode API
  (`decode_encoded_short_list_schema`). Starting from the GENUINE RLP encoding of a two-field
  record — `encode (.list [.bytes [0x2a], .bytes [0x01, 0x02]])` = `[0xc4, 0x2a, 0x82, 0x01, 0x02]`
  — the whole decoder runs into a 24-byte output struct, with the prefix-class fact and
  `SchemaValid` BOTH derived from the encoding. The caller supplies only the encoding equation
  (`by decide`), per-field core validity, and region/output well-formedness — demonstrating the
  "RLP bytes in → verified decode out" path with zero RLP-internal proof obligations.
-/

import EvmAsm.Rv64.RLP.SchemaDecodeEncoded

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

end EvmAsm.Rv64.RLP
