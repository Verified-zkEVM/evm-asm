/-
  EvmAsm.Rv64.RLP.SchemaListDecodeCoincidence

  EL.3 / Phase 5 — list-LEVEL decode coincidence for the schema decoders. The N-field fold
  yields per-field `schemaDecodes` (each element decodes to its `.bytes` item). This file adds
  the complementary WHOLE-LIST fact: when the input from `O` is the RLP encoding of the field
  record, `decode (bs.drop O) = some (.list (schemaItems specs), tail)` — i.e. the buffer the
  decoder consumes IS, per the pure RLP spec, the encoding of the list of field items. It follows
  directly from the spec's `decode ∘ encode` round-trip (no fuel / `decodeListPayload` reasoning),
  and ties the operational decoder's input to the spec at the list level.
-/

import EvmAsm.Rv64.RLP.SchemaListEncode

namespace EvmAsm.Rv64.RLP

open EvmAsm.EL.RLP

/-- **List-level decode coincidence.** If the buffer from `O` is the RLP encoding of the field
    record, the pure spec decodes it to the list of field items with the same `tail`. -/
theorem decode_list_of_encoded (bs : List Byte) (specs : List FieldSpec) (O : Nat) (tail : List Byte)
    (hsize : (encode (.list (schemaItems specs))).length < 256 ^ 8)
    (hbs : bs.drop O = encode (.list (schemaItems specs)) ++ tail) :
    decode (bs.drop O) = some (.list (schemaItems specs), tail) := by
  rw [hbs]
  exact decode_encode_append (.list (schemaItems specs)) tail hsize

end EvmAsm.Rv64.RLP
