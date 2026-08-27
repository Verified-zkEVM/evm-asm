/-
  EvmAsm.Codegen.Programs.RlpItemSizeGateCover

  **The three `rlp_item_size` rows' gates partition the head byte** — coverage
  evidence for the one row of the three that carried none.

  `rlp_item_size` appears in the registry three times, each `.conditional` on a
  restriction of the head byte `p`:

  | row | gate | coverRef before this module |
  |---|---|---|
  | `rlp_item_size_spec_within` | `SpanForm p` | **none** |
  | `…_long_string_pinned_spec_within` | `0xb8 ≤ p < 0xc0` | `longStringSample_reachable` |
  | `…_long_list_pinned_spec_within` | `0xf8 ≤ p` | `longListSample_reachable` |

  The two long-form rows each exhibit a reachable sample.  The `SpanForm` row —
  the one covering the *common* path — cited nothing at all, which is what put
  it on #12867.

  ## What is worth proving here is not another sample

  A single satisfying byte would tick the box and say very little: `SpanForm` is
  a range predicate, and nobody doubts a range is inhabited.  The question a
  reader of these three rows actually has is whether the three gates, taken
  together, leave anything out.

  They do not.  `head_byte_forms_partition` shows every `b : BitVec 8` lands in
  exactly one of the three, and `head_byte_forms_disjoint` shows no byte lands
  in two.  So the three rows are a *complete case split on the head byte*: the
  routine is total, and `.conditional` here records which arm proves which case
  rather than an uncovered region of the input space.

  That is a materially different claim from "the gate is satisfiable", and it is
  the one the row should have been making.

  ⚠️ Scope.  This is about the **head byte** only.  `rlp_item_size` computes a
  span from the prefix; nothing here says the rest of the buffer is well-formed,
  that the item's payload is present, or that the span is in bounds.  The
  long-list row's own note makes the same point ("the payload's own
  well-formedness is NOT part of the gate").

  Issue: #12867.
-/
import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec

namespace EvmAsm.Codegen.RlpItemSizeGateCover

open EvmAsm.Codegen.RlpSpliceHelperSpec

/-- The long-string arm's gate, as the sibling row states it. -/
def LongStringForm (b : BitVec 8) : Prop := 0xb8 ≤ b.toNat ∧ b.toNat < 0xc0

/-- The long-list arm's gate, as the sibling row states it. -/
def LongListForm (b : BitVec 8) : Prop := 0xf8 ≤ b.toNat

/-- **The three gates cover every head byte.**  Not a sample — the statement the
    `SpanForm` row should have carried: taken together the three `rlp_item_size`
    rows are a complete case split, so `.conditional` records which arm proves
    which case rather than a hole in the input space. -/
theorem head_byte_forms_partition (b : BitVec 8) :
    SpanForm b ∨ LongStringForm b ∨ LongListForm b := by
  have := b.isLt
  unfold SpanForm LongStringForm LongListForm
  omega

/-- …and no head byte is covered twice, so the three rows do not overlap and a
    reader can pick the arm from the prefix alone. -/
theorem head_byte_forms_disjoint (b : BitVec 8) :
    ¬ (SpanForm b ∧ LongStringForm b) ∧
    ¬ (SpanForm b ∧ LongListForm b) ∧
    ¬ (LongStringForm b ∧ LongListForm b) := by
  unfold SpanForm LongStringForm LongListForm
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ### The gate admits each of its three forms, not just one

    `SpanForm` is a union of two ranges spanning three RLP forms.  A single
    witness would leave open whether the other two are reachable inside it, so
    there is one per form, each paired with the span the guest computes — which
    makes the witness a claim about *behaviour* rather than about a range. -/

/-- Single byte: `0x2a < 0x80`, span 1. -/
theorem spanForm_admits_singleByte :
    SpanForm (0x2a : BitVec 8) ∧ risSpan (0x2a : BitVec 8) = 1 := by
  refine ⟨by unfold SpanForm; decide, by decide⟩

/-- Short string: `0x83` is a 3-byte string, span 4 = 1 header + 3. -/
theorem spanForm_admits_shortString :
    SpanForm (0x83 : BitVec 8) ∧ risSpan (0x83 : BitVec 8) = 4 := by
  refine ⟨by unfold SpanForm; decide, by decide⟩

/-- Short list: `0xc3` is a 3-byte payload list, span 4. -/
theorem spanForm_admits_shortList :
    SpanForm (0xc3 : BitVec 8) ∧ risSpan (0xc3 : BitVec 8) = 4 := by
  refine ⟨by unfold SpanForm; decide, by decide⟩

/-! ### ⛔ Negative controls — the gate really does exclude something

    Without these the coverage above would be consistent with `SpanForm` being
    trivially true, in which case the row would not be `.conditional` at all. -/

/-- `0xb8`, the smallest long-string prefix, is excluded — and is exactly the
    byte the long-string row's own `longStringSample_reachable` covers. -/
theorem spanForm_excludes_longString :
    ¬ SpanForm (0xb8 : BitVec 8) ∧ LongStringForm (0xb8 : BitVec 8) := by
  refine ⟨by unfold SpanForm; decide, by unfold LongStringForm; decide⟩

/-- `0xf8`, the smallest long-list prefix, is excluded — the arm every block
    header RLP takes. -/
theorem spanForm_excludes_longList :
    ¬ SpanForm (0xf8 : BitVec 8) ∧ LongListForm (0xf8 : BitVec 8) := by
  refine ⟨by unfold SpanForm; decide, by unfold LongListForm; decide⟩

/-- The four edges, pinned.  A range gate is most likely to be wrong by one at
    its boundaries, and these are the four places `SpanForm` turns over. -/
theorem spanForm_boundaries :
    SpanForm (0xb7 : BitVec 8) ∧ ¬ SpanForm (0xb8 : BitVec 8) ∧
    ¬ SpanForm (0xbf : BitVec 8) ∧ SpanForm (0xc0 : BitVec 8) ∧
    SpanForm (0xf7 : BitVec 8) ∧ ¬ SpanForm (0xf8 : BitVec 8) := by
  unfold SpanForm
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end EvmAsm.Codegen.RlpItemSizeGateCover
