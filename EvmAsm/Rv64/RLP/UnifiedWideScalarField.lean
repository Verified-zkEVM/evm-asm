/-
  EvmAsm.Rv64.RLP.UnifiedWideScalarField

  EL.3 / Phase 5 — the WIDE (`u256`) scalar field. The single-word scalar unit
  (`unified_scalar_field_decode_and_store`) reads the payload big-endian into one
  64-bit register, so it caps at `data.length ≤ 8`. But a legacy transaction's
  `nonce, gas_price, gas, value, v, r, s` are `u256` — `r`/`s` are essentially
  always the full 32 bytes — which that unit cannot decode.

  The fix needs no multi-limb big-endian arithmetic. A `u256` scalar's payload is
  ≤ 32 bytes, so it fits the byte-array copy unit
  (`unified_bytes_field_decode_and_copy`, proven for `≤ 55` bytes): copy the raw
  big-endian payload into the output region (contiguous, advancing the output
  cursor `x14`), exactly as the schema fold lays fields out. The scalar VALUE
  coincidence is then free: `decodeScalar` is defined as "decode the item, read its
  bytes as a big-endian natural" with no minimality check, so from the copy unit's
  `decode (bs.drop O) = some (.bytes data, tail)` we get
  `decodeScalar (bs.drop O) = some (Nat.fromBytesBE data, tail)` directly.

  This lifts the scalar field ceiling from 8 to 32 bytes. The output holds the
  field's minimal big-endian bytes (`data.length` of them); fixed-width 32-byte
  zero-padding, if a target struct wants it, is a presentation step layered on at
  schema-assembly time.
-/

import EvmAsm.Rv64.RLP.UnifiedBytesFieldDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

end EvmAsm.Rv64.RLP
