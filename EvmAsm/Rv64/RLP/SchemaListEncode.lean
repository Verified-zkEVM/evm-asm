/-
  EvmAsm.Rv64.RLP.SchemaListEncode

  EL.3 / Phase 5 — spec-side bridge connecting a field schema to its RLP LIST encoding. The
  decoder's instantiation helper (`schemaValid_of_concat`) wants the input buffer to be
  `schemaEncBytes specs ++ tail`. This file shows that string IS the payload of the RLP list
  encoding of the fields (`encode (.list (schemaItems specs))`): the list payload `encodeItems`
  is exactly the per-field-encoding concatenation `schemaEncBytes`. So a caller whose input is a
  genuine `encode (.list …)` of the field items can discharge the decoder's concat hypothesis
  structurally — closing the gap between "input is the RLP encoding of these fields" and "the
  decoder runs."
-/

import EvmAsm.Rv64.RLP.SchemaFoldConcat

namespace EvmAsm.Rv64.RLP

open EvmAsm.EL.RLP

/-- The RLP items a schema's fields encode to (each field is a byte string). -/
def schemaItems (specs : List FieldSpec) : List RLPItem :=
  specs.map (fun f => RLPItem.bytes f.data)

/-- **Schema payload = list payload.** The RLP list payload (`encodeItems`) of the field items
    is exactly the decoder's expected `schemaEncBytes`. -/
theorem encodeItems_schemaItems (specs : List FieldSpec) :
    encode.encodeItems (schemaItems specs) = schemaEncBytes specs := by
  induction specs with
  | nil => rfl
  | cons f rest ih =>
    simp only [schemaItems, List.map_cons, encode.encodeItems, schemaEncBytes] at *
    rw [ih]

/-- **Short-list encoding of a field schema.** When the schema's payload fits in a short list
    (`≤ 55` bytes), the RLP encoding of the field items is the 1-byte header `0xC0 + len`
    followed by `schemaEncBytes`. -/
theorem encode_list_schemaItems_short (specs : List FieldSpec)
    (hlen : (schemaEncBytes specs).length ≤ 55) :
    encode (.list (schemaItems specs))
      = [BitVec.ofNat 8 (0xC0 + (schemaEncBytes specs).length)] ++ schemaEncBytes specs := by
  simp only [encode, encodeItems_schemaItems]
  rw [if_pos hlen]

/-- **Concat hypothesis from a short-list-encoded input.** If the buffer from `O` is the RLP
    short-list encoding of the field items followed by `tail`, then the payload at `O+1` is
    `schemaEncBytes specs ++ tail` — exactly `schemaValid_of_concat`'s concatenation premise
    (and the short-list payload starts at `O+1`). -/
theorem schemaConcat_of_encode_list_short (bs : List Byte) (specs : List FieldSpec)
    (O : Nat) (tail : List Byte) (hlen : (schemaEncBytes specs).length ≤ 55)
    (hbs : bs.drop O = encode (.list (schemaItems specs)) ++ tail) :
    bs.drop (O + 1) = schemaEncBytes specs ++ tail := by
  rw [← List.drop_drop, hbs, encode_list_schemaItems_short specs hlen]
  simp

/-- **Payload slice from a complete short-list input.** A caller carrying the full
    encoded-list equality can expose the schema payload at offset `1` without
    manually inventing a concat witness. -/
theorem schemaConcat_of_encoded_list_short (bs : List Byte) (specs : List FieldSpec)
    (hlen : (schemaEncBytes specs).length ≤ 55)
    (hinput : bs = encode (.list (schemaItems specs))) :
    bs.drop 1 = schemaEncBytes specs ++ ([] : List Byte) := by
  have hbs : bs.drop 0 = encode (.list (schemaItems specs)) ++ ([] : List Byte) := by
    rw [hinput]
    simp
  simpa using schemaConcat_of_encode_list_short bs specs 0 ([] : List Byte) hlen hbs

end EvmAsm.Rv64.RLP
