/-
  EvmAsm.Rv64.RLP.SchemaListEncodeLong

  EL.3 / Phase 5 — long-list counterpart of `SchemaListEncode`. Real STF records (transactions,
  block headers) exceed 55 bytes, so their RLP encoding is a LONG list: a `0xF7 + lenOfLen`
  prefix, then `lenOfLen` big-endian length bytes, then the payload. This shows the payload is
  again exactly `schemaEncBytes`, and that dropping the `1 + lenOfLen` header bytes from a
  long-list-encoded input yields `schemaEncBytes specs ++ tail` — the concat premise the long
  decoder (`long_list_schema_walk`) consumes, at offset `O + 1 + lenOfLen`.
-/

import EvmAsm.Rv64.RLP.SchemaListEncode

namespace EvmAsm.Rv64.RLP

open EvmAsm.EL.RLP

/-- **Long-list encoding of a field schema.** When the payload exceeds 55 bytes, the RLP
    encoding of the field items is the `0xF7 + lenOfLen` header, the big-endian length bytes,
    then `schemaEncBytes`. -/
theorem encode_list_schemaItems_long (specs : List FieldSpec)
    (hlen : ¬ (schemaEncBytes specs).length ≤ 55) :
    encode (.list (schemaItems specs))
      = [BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (schemaEncBytes specs).length).length)]
        ++ Nat.toBytesBE (schemaEncBytes specs).length ++ schemaEncBytes specs := by
  simp only [encode, encodeItems_schemaItems]
  rw [if_neg hlen]

/-- **Concat hypothesis from a long-list-encoded input.** If the buffer from `O` is the RLP
    long-list encoding of the field items followed by `tail`, then the payload at
    `O + 1 + lenOfLen` is `schemaEncBytes specs ++ tail`. -/
theorem schemaConcat_of_encode_list_long (bs : List Byte) (specs : List FieldSpec)
    (O : Nat) (tail : List Byte) (hlen : ¬ (schemaEncBytes specs).length ≤ 55)
    (hbs : bs.drop O = encode (.list (schemaItems specs)) ++ tail) :
    bs.drop (O + (1 + (Nat.toBytesBE (schemaEncBytes specs).length).length))
      = schemaEncBytes specs ++ tail := by
  rw [← List.drop_drop, hbs, encode_list_schemaItems_long specs hlen, List.append_assoc,
      show 1 + (Nat.toBytesBE (schemaEncBytes specs).length).length
        = ([BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (schemaEncBytes specs).length).length)]
            ++ Nat.toBytesBE (schemaEncBytes specs).length).length from by simp [Nat.add_comm]]
  rw [List.drop_append_length]

end EvmAsm.Rv64.RLP
