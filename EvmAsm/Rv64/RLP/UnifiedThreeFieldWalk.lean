/-
  EvmAsm.Rv64.RLP.UnifiedThreeFieldWalk

  EL.3 / Phase 5 — a THREE-field heterogeneous walk: scalar ⨾ scalar ⨾ byte-array, all
  decoded into one shared output `bytesRegion`. The integration test that exercises BOTH new
  composition pieces together: the scalar-into-region `regOwn` re-entry variant
  (`unified_scalar_field_decode_and_store_region_at_regOwn`, the middle field, callable after a
  prior field clobbered the scratch) and the reusable code-range disjointness
  (`codeReq_disjoint_of_ranges` + the per-unit `…_none_above/_below` lemmas). It demonstrates the
  path scales — disjointness is two `codeReq_disjoint_of_ranges` calls, no per-leaf product — and
  is the direct precursor to the concrete legacy-tx / block-header decoders (fixed unit sequences).

  Layout (program base `base`; field-A offset `OA`):
      base       < scalar A : decode + spill into region >   (base     .. base+280)
      base+280   < scalar B : decode + spill into region >   (base+280 .. base+560)
      base+560   < byte   C : decode + copy  into region >   (base+560 .. base+712+20·|dataC|)
-/

import EvmAsm.Rv64.RLP.FieldUnitDisjoint
import EvmAsm.Rv64.RLP.UnifiedScalarFieldRegionRegOwn
import EvmAsm.Rv64.RLP.UnifiedHeteroFieldWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

end EvmAsm.Rv64.RLP
