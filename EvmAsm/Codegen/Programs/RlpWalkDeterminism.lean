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
import EvmAsm.Rv64.RLP.ItemDecodeForward
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


/-! ## Success excludes Failure

`rlp_list_nth_item` reports exactly one of `Success` and `Failure`, but nothing
in the tree said so; every existing use *constructs* a `Failure`. The model →
guest direction needs the exclusion, in order to rule out `Result.listFailure`
once the model has already established `Success`. -/

/-- Any chain, of any arity, starts with a decode at its own cursor. -/
theorem strictNthItem_head {bytes : List (BitVec 8)} {base endPtr : Word}
    {index off : Nat} {next len : Word}
    (h : StrictNthItem bytes base endPtr index off next len) :
    ∃ n l, rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr n l := by
  cases h
  · exact ⟨_, _, by assumption⟩
  · exact ⟨_, _, by assumption⟩

/-- A walked prefix of `count ≤ index` steps lands on the `StrictNthItem`
    chain: what remains at that cursor is a chain of arity `index - count`.

    Induction is on the `StrictPrefix` derivation, identifying the prefix's
    decode with the chain's at each cursor via `rlpItemDecode_deterministic`. -/
theorem strictNthItem_extends_prefix {bytes : List (BitVec 8)} {base endPtr : Word}
    {cursorOff : Nat} {index : Nat} {next len : Word}
    (hnth : StrictNthItem bytes base endPtr index cursorOff next len) :
    ∀ {count off : Nat}, StrictPrefix bytes base endPtr cursorOff count off →
      count ≤ index →
      ∃ next' len', StrictNthItem bytes base endPtr (index - count) off next' len' := by
  intro count off hprefix
  induction hprefix with
  | zero => intro _; exact ⟨next, len, by simpa using hnth⟩
  | succ count off0 n0 l0 hprefix hitem ih =>
      intro hle
      obtain ⟨n', l', hrest⟩ := ih (by omega)
      obtain ⟨k, hk⟩ : ∃ k, index - count = k + 1 := ⟨index - count - 1, by omega⟩
      rw [hk] at hrest
      cases hrest
      rename_i nn ll hitem' hrec
      obtain ⟨rfl, -⟩ := rlpItemDecode_deterministic hitem hitem'
      exact ⟨n', l', by rw [show index - (count + 1) = k from by omega]; exact hrec⟩

/-- A walked prefix never runs past the list's declared end. -/
theorem strictPrefix_le {bytes : List (BitVec 8)} {base : Word} {endOff cursorOff : Nat}
    (hover : base.toNat + endOff + 9 < 2 ^ 64) (hstart : cursorOff ≤ endOff) :
    ∀ {count off : Nat},
      StrictPrefix bytes base (base + BitVec.ofNat 64 endOff) cursorOff count off →
      off ≤ endOff := by
  intro count off h
  induction h with
  | zero => exact hstart
  | succ count off0 n0 l0 hprefix hitem ih =>
      exact (BalAccountNonstorageFinalsSpec.rlpItemDecode_advance hitem ih hover).2.2

/-- `Success` and `Failure` are mutually exclusive. -/
theorem success_not_failure {bytes : List (BitVec 8)} {base : Word}
    {listLen index : Nat} {offset len : Word}
    (hover : base.toNat + listLen + 9 < 2 ^ 64)
    (hsucc : Success bytes base listLen index offset len)
    (hfail : Failure bytes base listLen index) : False := by
  obtain ⟨cursorOff, ep, nxt, hlist, hnth, -⟩ := hsucc
  cases hfail with
  | init hno => exact hno ⟨cursorOff, ep, hlist⟩
  | walk cursorOff' count off ep' hlist' hcount hprefix hfail =>
      obtain ⟨rfl, rfl⟩ := strictListPayload_deterministic hlist' hlist
      obtain ⟨n', l', hrest⟩ := strictNthItem_extends_prefix hnth hprefix hcount
      obtain ⟨n, l, hdec⟩ := strictNthItem_head hrest
      have hend : ep' = base + BitVec.ofNat 64 listLen := hlist'.end_eq
      rw [hend] at hdec hfail
      -- a decode exists at `off`, which refutes the "no item decodes" disjunct
      -- outright and, via the advance bound, the "cursor past end" one too
      have hstart : cursorOff' ≤ listLen := hlist'.cursor_le
      rw [hend] at hprefix
      have hoffle : off ≤ listLen := strictPrefix_le (by omega) hstart hprefix
      obtain ⟨-, hlt, hle⟩ :=
        BalAccountNonstorageFinalsSpec.rlpItemDecode_advance hdec hoffle (by omega)
      rcases hfail with hbound | hnodec
      · exact hbound ((ult_base_add_ofNat (bound := listLen) hoffle (le_refl _)
          (by omega)).mpr (by omega))
      · exact hnodec ⟨n, l, hdec⟩

end EvmAsm.Codegen.RlpListNthItemSAsm
