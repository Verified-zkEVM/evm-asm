/-
  EvmAsm.Rv64.RLP.UnifiedScalarFieldRegionRegOwn

  EL.3 / Phase 5 — `regOwn`-precondition variant of `unified_scalar_field_decode_and_store_region`.
  The decode clobbers its scratch registers (`x5, x10, x11, x12`) and releases them as `regOwn`
  in its post; so to chain a scalar field AFTER another field (which left those `regOwn`), the
  scalar-into-region unit must accept `regOwn` scratch in its precondition. Peeling those four via
  `cpsTripleWithin_of_forall_regIs_to_regOwn` (à la the byte-array
  `unified_bytes_field_decode_and_copy_at_regOwn`) makes it chainable. `x14`/`x15` stay concrete
  (the prior field supplies them: `x14` is overwritten by the unit's `ADDI x14, rOut, fieldImm`,
  `x15` is framed through untouched). The scalar mirror of the byte-array `…_at_regOwn`.
-/

import EvmAsm.Rv64.RLP.UnifiedScalarFieldRegion

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

end EvmAsm.Rv64.RLP
