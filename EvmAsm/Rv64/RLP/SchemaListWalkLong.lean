/-
  EvmAsm.Rv64.RLP.SchemaListWalkLong

  EL.3 / Phase 5 — long-list specialization of `list_schema_walk`. Real STF structures
  (transactions, block headers) exceed 55 bytes, so they are encoded as LONG lists (RLP prefix
  `0xf8..0xff`): the prefix is followed by `lenOfLen` big-endian length bytes, then the payload.
  The payload therefore starts at `(O + 1) + lenOfLen`, and `regionLongWindow` requires those
  `lenOfLen` length bytes to be in-region — which follows from the global byte-access validity
  (`hwin`) plus a single "the length bytes fit in the buffer" bound. This discharges both, so a
  long-list schema decode needs only the prefix-class fact and that bound.
-/

import EvmAsm.Rv64.RLP.SchemaListWalk

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

end EvmAsm.Rv64.RLP
