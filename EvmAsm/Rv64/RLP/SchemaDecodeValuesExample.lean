/-
  EvmAsm.Rv64.RLP.SchemaDecodeValuesExample

  EL.3 / Phase 5 — concrete cross-check of the decode-to-field-VALUES API
  (`decode_encoded_short_list_schema_values`). Starting from the GENUINE RLP encoding of a
  two-field record — `encode (.list [.bytes [0x2a], .bytes [0x01,0x02]])` =
  `[0xc4, 0x2a, 0x82, 0x01, 0x02]` — the whole decoder runs into a 24-byte output struct AND
  the per-field scalar VALUES are recovered (`schemaScalarValues`): field 0 = `0x2a` = 42,
  field 1 = `fromBytesBE [0x01,0x02]` = 258. Demonstrates the end-to-end "RLP bytes in → field
  values out" path with zero RLP-internal proof obligations.
-/

import EvmAsm.Rv64.RLP.SchemaDecodeValues

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- A scalar field (`0x2a`) at output offset 0 and a 2-byte array (`[0x01,0x02]`) at offset 8. -/
abbrev egValSpecs : List FieldSpec :=
  [⟨true, [(0x2a : Byte)], 0, 0⟩, ⟨false, [(0x01 : Byte), (0x02 : Byte)], 8, 8⟩]

/-- The buffer is the genuine RLP encoding of the field record: `[0xc4, 0x2a, 0x82, 0x01, 0x02]`. -/
abbrev egValBs : List Byte := [(0xc4 : Byte), 0x2a, 0x82, 0x01, 0x02]

set_option maxRecDepth 8000 in
/-- **End-to-end field-value recovery.** Decoding the encoded record recovers each field's
    big-endian value at its input offset (`schemaScalarValues`). -/
theorem egTxFieldValues : schemaScalarValues egValBs 1 egValSpecs :=
  (decode_encoded_short_list_schema_values (0x1000 : Word) (0x2000 : Word) (0x3000 : Word) .x18
    egValBs 0 egValSpecs (List.replicate 24 (0 : Byte)) 24 [] 0 0 0 0 0 0 (by decide) (by decide)
    (by intro f hf; fin_cases hf <;> exact ⟨by decide, by decide, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by simp) (by decide) (by decide) (by decide)).2

-- The recovered field values are the expected naturals: `0x2a = 42` and `[0x01,0x02] = 258`.
example : Nat.fromBytesBE [(0x2a : Byte)] = 42 := by decide
example : Nat.fromBytesBE [(0x01 : Byte), (0x02 : Byte)] = 258 := by decide

end EvmAsm.Rv64.RLP
