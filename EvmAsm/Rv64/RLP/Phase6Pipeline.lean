/-
  EvmAsm.Rv64.RLP.Phase6Pipeline

  EL.3 / Phase 6 — the **complete top-level RLP pipeline**: `read_input ⨾ decode ⨾ write_output`.
  Composes the read⨾decode unit (`rlp_phase6_read_and_decode`) with the `write_output` wrapper
  (`rlp_phase6_write_output_spec_regOwn`): the host `read_input` syscall hands the RLP buffer to
  the schema decoder, which decodes the record into the output `bytesRegion`, and `write_output`
  commits that region to the host public-values stream.

  From the host-ABI input contract (`inputBufBaseIs buf_base`, `privateInputIs input`,
  `bytesRegion buf_base input` with `input = encode (.list (schemaItems specs)) ++ tail`), the whole
  program runs end to end in `(5 + (61 + schemaSteps specs)) + 4` steps, leaving
  `publicValues = old ++ schemaOut out specs` and recovering every field value
  (`schemaScalarValues`). This closes the RLP arc: RLP bytes in → decode → committed output, with a
  kernel-checkable round-trip proof against the pure RLP spec.
-/

import EvmAsm.Rv64.RLP.Phase6ReadDecode
import EvmAsm.Rv64.RLP.Phase6DecodeWrite

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

end EvmAsm.Rv64.RLP
