/-
  EvmAsm.Rv64.RLP.SchemaFoldConcat

  EL.3 / Phase 5 — instantiation helper for the N-field fold (`SchemaFold`). `schema_walk`
  requires a per-field drop hypothesis (`SchemaValid`). For a real decoder the input buffer is
  exactly the concatenation of the fields' RLP encodings followed by a tail; this file derives
  the whole `SchemaValid` from that single fact (`schemaValid_of_concat`) plus a per-field
  "core" validity (length / immediate / output-bound, no drop bookkeeping). It makes applying
  the fold to a concrete schema a one-liner.
-/

import EvmAsm.Rv64.RLP.SchemaFold

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- The byte string a schema decodes: the concatenation of its fields' RLP encodings. -/
def schemaEncBytes : List FieldSpec → List Byte
  | [] => []
  | f :: rest => encode (.bytes f.data) ++ schemaEncBytes rest

/-- Per-field validity WITHOUT the drop bookkeeping (length / immediate / output bound). -/
def fieldCoreValid (outLen : Nat) (f : FieldSpec) : Prop :=
  (if f.isScalar then f.data.length ≤ 8
   else (encode (.bytes f.data)).length < 256 ^ 8) ∧
  signExtend12 f.imm = BitVec.ofNat 64 f.di ∧
  f.di + fieldWriteLen f ≤ outLen

/-- **`SchemaValid` from a single concatenation fact.** If the input buffer from offset `O` is
    exactly the schema's encodings followed by `tail`, and every field is core-valid, then the
    full `SchemaValid` (with its per-field drop conditions) holds. -/
theorem schemaValid_of_concat (bs : List Byte) (outLen : Nat) (tail : List Byte) :
    ∀ (specs : List FieldSpec) (O : Nat),
      (∀ f, f ∈ specs → fieldCoreValid outLen f) →
      bs.drop O = schemaEncBytes specs ++ tail →
      SchemaValid bs outLen O specs := by
  intro specs
  induction specs with
  | nil => intro O _ _; exact trivial
  | cons f rest ih =>
    intro O hcore hconcat
    obtain ⟨hk, hi, hd⟩ := hcore f (by simp)
    have hdrop_tail : bs.drop (O + fieldEnc f) = schemaEncBytes rest ++ tail := by
      rw [← List.drop_drop, hconcat]
      simp only [schemaEncBytes, fieldEnc, List.append_assoc, List.drop_append_length]
    have hhead : bs.drop O = encode (.bytes f.data) ++ bs.drop (O + fieldEnc f) := by
      rw [hdrop_tail, hconcat]; simp only [schemaEncBytes, List.append_assoc]
    exact ⟨hk, hi, hd, hhead,
      ih (O + fieldEnc f) (fun g hg => hcore g (by simp [hg])) hdrop_tail⟩

end EvmAsm.Rv64.RLP
