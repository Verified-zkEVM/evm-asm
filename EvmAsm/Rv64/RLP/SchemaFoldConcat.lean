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
  1 ≤ f.data.length ∧
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
    obtain ⟨h1, hk, hi, hd⟩ := hcore f (by simp)
    have hdrop_tail : bs.drop (O + fieldEnc f) = schemaEncBytes rest ++ tail := by
      rw [← List.drop_drop, hconcat]
      simp only [schemaEncBytes, fieldEnc, List.append_assoc, List.drop_append_length]
    have hhead : bs.drop O = encode (.bytes f.data) ++ bs.drop (O + fieldEnc f) := by
      rw [hdrop_tail, hconcat]; simp only [schemaEncBytes, List.append_assoc]
    exact ⟨h1, hk, hi, hd, hhead,
      ih (O + fieldEnc f) (fun g hg => hcore g (by simp [hg])) hdrop_tail⟩

-- Concrete cross-check: decode a 3-field mixed schema — scalar `0x2a` (→ 42 at byte 0), the
-- 2-byte array `[0x01, 0x02]` (→ bytes 8..10), scalar `0x07` (→ 7 at byte 16) — from the buffer
-- `[0x2a, 0x82, 0x01, 0x02, 0x07]` at region `0x2000` into the 24-byte output region at `0x3000`
-- via `x18`. `SchemaValid` is discharged from the single concatenation fact by
-- `schemaValid_of_concat`, showing the generic fold applies to a concrete heterogeneous schema.
example :=
  schema_walk (0x2000 : Word) (0x3000 : Word) .x18
    [(0x2a : Byte), (0x82 : Byte), (0x01 : Byte), (0x02 : Byte), (0x07 : Byte)]
    (by decide) (by decide) (by decide) (by decide) 24 (by decide) (by decide)
    [⟨true, [(0x2a : Byte)], 0, 0⟩, ⟨false, [(0x01 : Byte), (0x02 : Byte)], 8, 8⟩,
      ⟨true, [(0x07 : Byte)], 16, 16⟩]
    (0x1000 : Word) 0 (List.replicate 24 (0 : Byte)) (by simp)
    (schemaValid_of_concat _ 24 []
      [⟨true, [(0x2a : Byte)], 0, 0⟩, ⟨false, [(0x01 : Byte), (0x02 : Byte)], 8, 8⟩,
        ⟨true, [(0x07 : Byte)], 16, 16⟩] 0
      (by intro f hf; fin_cases hf <;> exact ⟨by decide, by decide, by decide, by decide⟩)
      (by decide))
    (by decide)

end EvmAsm.Rv64.RLP
