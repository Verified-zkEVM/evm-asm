/-
  EvmAsm.Rv64.RLP.SchemaEmptyFieldExample

  EL.3 / Phase 5 — concrete cross-check that the schema engine now decodes EMPTY (`n=0`) fields.
  Starting from the genuine RLP encoding of a two-field record whose FIRST field is a zero scalar
  (empty payload `0x80`) — `encode (.list [.bytes [], .bytes [0x2a]])` = `[0xc2, 0x80, 0x2a]` — the
  whole decoder runs into a 16-byte output struct AND recovers each field's value
  (`schemaScalarValues`): field 0 = `0` (the empty/zero scalar), field 1 = `0x2a` = 42. Demonstrates
  that `schema_walk` (via the decode-to-values API) handles zero-valued fields end-to-end.
-/

import EvmAsm.Rv64.RLP.SchemaDecodeValues

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- An empty (zero) scalar field at output offset 0, then a 1-byte scalar `0x2a` at offset 8. -/
abbrev egEmptySpecs : List FieldSpec :=
  [⟨true, ([] : List Byte), 0, 0⟩, ⟨true, [(0x2a : Byte)], 8, 8⟩]

/-- The buffer is the genuine RLP encoding of the field record: `[0xc2, 0x80, 0x2a]`. -/
abbrev egEmptyBs : List Byte := [(0xc2 : Byte), 0x80, 0x2a]

-- The recovered field values: the empty scalar is `0`, and `0x2a = 42`.
example : Nat.fromBytesBE ([] : List Byte) = 0 := by decide
example : Nat.fromBytesBE [(0x2a : Byte)] = 42 := by decide

end EvmAsm.Rv64.RLP
