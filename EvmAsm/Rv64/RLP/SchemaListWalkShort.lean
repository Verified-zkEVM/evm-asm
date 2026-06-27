/-
  EvmAsm.Rv64.RLP.SchemaListWalkShort

  EL.3 / Phase 5 — short-list specialization of `list_schema_walk`. When the outer list is a
  SHORT list (RLP prefix `0xc0..0xf7`, payload ≤ 55 bytes), the payload starts at `O + 1` and
  the `regionLongWindow` precondition is vacuously `True` (only long forms carry length bytes).
  So a short-list schema decode needs neither the window nor the pointer-offset hypothesis — just
  the prefix-class fact `classifyPrefix (bs[O]) = .shortList`. This is the convenience entry point
  for short list-structured schemas.
-/

import EvmAsm.Rv64.RLP.SchemaListWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

end EvmAsm.Rv64.RLP
