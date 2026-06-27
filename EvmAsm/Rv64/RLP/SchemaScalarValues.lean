/-
  EvmAsm.Rv64.RLP.SchemaScalarValues

  EL.3 / Phase 5 — reading a schema decode as FIELD VALUES. The N-field fold
  (`schema_walk`) proves a per-field decode coincidence (`schemaDecodes`): each field
  decodes either as a scalar (`decodeScalar … = some (value, …)`) or as a byte array
  (`decode … = some (.bytes data, …)`). For the concrete tx/header decoders we want
  the numeric VALUE of every field uniformly — a legacy transaction's `nonce, value,
  v, r, s` are `u256` scalars, and (per `UnifiedWideScalarField`) they ride the
  byte-array machine path, so the fold reports them via the `.bytes` coincidence.

  This file supplies the missing forward bridge `decodeScalar_of_decode_bytes`
  (a byte-string decode determines its payload's big-endian value, since `decodeScalar`
  applies no minimality check) and lifts it over a whole schema: `schemaDecodes` ⇒
  `schemaScalarValues`, recovering every field's value regardless of which machine path
  decoded it. This is the spec keystone that lets the all-byte-array `schema_walk` act
  as a `u256`-field decoder.
-/

import EvmAsm.Rv64.RLP.SchemaFold

namespace EvmAsm.Rv64.RLP

open EvmAsm.EL.RLP

/-- Every field of a schema read as a scalar VALUE: its big-endian natural at its input
    offset, consuming the field's encoding length. -/
def schemaScalarValues (bs : List Byte) : Nat → List FieldSpec → Prop
  | _, [] => True
  | O, f :: rest =>
    decodeScalar (bs.drop O) = some (Nat.fromBytesBE f.data, bs.drop (O + fieldEnc f)) ∧
    schemaScalarValues bs (O + fieldEnc f) rest

end EvmAsm.Rv64.RLP
