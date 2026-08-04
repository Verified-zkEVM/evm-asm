/-
  EvmAsm.Codegen.Programs.RlpWalkDeterminism

  The `Codegen`-layer half of the walk determinism story: `StrictListPayload`,
  `StrictNthItem` and `Success` are **functions** of the bytes they read.

  The core-layer half — `rlpItemDecode_deterministic` — lives in
  `EvmAsm/Rv64/RLP/WalkItemDeterminism.lean`, because it is about a predicate the
  verified core owns. The predicates below are defined under `Codegen`
  (`RlpListNthItemSAsmBase.lean`, `RlpListNthItemStrictList.lean`), so their determinism
  has to be stated here; `check-layering.sh` L1 forbids the other direction.

  WHAT THIS UNBLOCKS. Every walk-family postcondition is existential —
  `∃ offset len, Success bytes base listLen index offset len ∧ <outputs from offset/len>`.
  Those existentials are whatever the *routine* found. A caller holding a **known**
  encoding (an `AccountRecord`'s four fields, a header's field 8) cannot conclude the
  outputs denote that value without knowing the found offsets are the right ones. That
  step is exactly `success_deterministic`, and it was missing — which is the actual
  content of #11345 and #11346, both of which sit on this tower.

  ⚠️ This module is deliberately consumer-free: it is a prerequisite landed on its own so
  it can be reviewed as one idea. The consumers arrive with #11345/#11346. That is not the
  "availability is not use" failure — no registry row claims a grade on the strength of
  these lemmas.
-/

import EvmAsm.Rv64.RLP.WalkItemDeterminism
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase

namespace EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP

/-- The list header determines both the payload cursor and the exclusive end.

    `endPtr` is forced by the `listLen` index alone (both constructors conclude
    `base + BitVec.ofNat 64 listLen`), so the content is the cursor: the `short` arm
    yields `1` and the `long` arm `1 + lenOfLen`, and the two are separated by the
    `ult B 0xf8` guard. -/
theorem strictListPayload_deterministic {bytes : List (BitVec 8)} {base : Word}
    {listLen c₁ c₂ : Nat} {e₁ e₂ : Word}
    (h₁ : StrictListPayload bytes base listLen c₁ e₁)
    (h₂ : StrictListPayload bytes base listLen c₂ e₂) :
    c₁ = c₂ ∧ e₁ = e₂ := by
  cases h₁ with
  | short b hb hlist hshort hcur hlen =>
    cases h₂ with
    | short b' hb' _ _ hcur' _ =>
      exact ⟨hcur.trans hcur'.symm, rfl⟩
    | long b' first' hb' hlong' _ _ _ _ _ =>
      obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
      exact absurd hshort hlong'
  | long b first hb hlong hfirst hnz hmin hcur hlen =>
    cases h₂ with
    | short b' hb' _ hshort' _ _ =>
      obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
      exact absurd hshort' hlong
    | long b' first' hb' _ _ _ _ hcur' _ =>
      obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
      exact ⟨hcur.trans hcur'.symm, rfl⟩

/-- Walking to the `index`-th item is deterministic: same window and same start offset
    give the same final cursor and length. Induction on the index; each step is pinned by
    `rlpItemDecode_deterministic`, which also forces the offset handed to the next step. -/
theorem strictNthItem_deterministic {bytes : List (BitVec 8)} {base endPtr : Word}
    {index off : Nat} {n₁ l₁ n₂ l₂ : Word}
    (h₁ : StrictNthItem bytes base endPtr index off n₁ l₁)
    (h₂ : StrictNthItem bytes base endPtr index off n₂ l₂) :
    n₁ = n₂ ∧ l₁ = l₂ := by
  induction h₁ generalizing n₂ l₂ with
  | zero off n l hitem =>
    cases h₂ with
    | zero _ n' l' hitem' => exact rlpItemDecode_deterministic hitem hitem'
  | succ index off n l fn fl hitem hrest ih =>
    cases h₂ with
    | succ _ _ n' l' fn' fl' hitem' hrest' =>
      obtain ⟨rfl, -⟩ := rlpItemDecode_deterministic hitem hitem'
      exact ih hrest'

/-- ⭐ **`Success` is deterministic.** The offset and length a walk routine reports for
    item `index` are functions of the bytes, the base, the declared list length and the
    index — nothing else.

    This is the lemma callers need to identify an existentially-quantified postcondition
    with a known encoding's field offsets. -/
theorem success_deterministic {bytes : List (BitVec 8)} {base : Word}
    {listLen index : Nat} {o₁ l₁ o₂ l₂ : Word}
    (h₁ : Success bytes base listLen index o₁ l₁)
    (h₂ : Success bytes base listLen index o₂ l₂) :
    o₁ = o₂ ∧ l₁ = l₂ := by
  obtain ⟨c₁, e₁, n₁, hlist₁, hnth₁, hoff₁⟩ := h₁
  obtain ⟨c₂, e₂, n₂, hlist₂, hnth₂, hoff₂⟩ := h₂
  obtain ⟨rfl, rfl⟩ := strictListPayload_deterministic hlist₁ hlist₂
  obtain ⟨rfl, rfl⟩ := strictNthItem_deterministic hnth₁ hnth₂
  exact ⟨hoff₁.trans hoff₂.symm, rfl⟩

end EvmAsm.Codegen.RlpListNthItemSAsm
