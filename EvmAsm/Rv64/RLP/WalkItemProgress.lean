/-
  EvmAsm.Rv64.RLP.WalkItemProgress

  **Boundedness for one walked RLP item** — part of the site-*i* → site-*i+1*
  derivation named on #12799 as the single obligation standing between the
  header-decoder tranche and whole-routine triples.

  A loop that walks items calls `rlp_walk_next_leaf` once per iteration and must
  re-establish that callee's entry premises at the *new* cursor from the *old*
  iteration's postcondition.  Two facts about the accept relation would give
  them:

      next  ≤u endPtr  (boundedness — the walk cannot overrun)   ← proved here
      cursor <u next   (strict progress — the walk cannot stall) ← see below

  `rlpItemDecode_bounded` proves the first, uniformly over all five prefix
  forms.

  ## ⛔ Why strict progress is NOT proved here

  It is not true of this relation.  Both long-form arms establish only
  `¬ult endPtr (cursor + hdrDelta)`, i.e. the header end is at or below
  `endPtr`.  **If `cursor + hdrDelta` wraps**, it lands below `cursor` and still
  satisfies that conjunct, so `next` can be *less* than `cursor`.  Nothing in
  `rlpItemDecode` excludes it — the definition's comment describes the long-form
  fit as "overflow-free", and it is overflow-free only in the sense that it
  never subtracts below zero, not in the sense that the sum cannot wrap.

  ⇒ Progress on the long arms needs a no-wrap premise the relation does not
  carry.  It belongs in whichever lemma consumes the address bound, not here;
  claiming it here would make this theorem's name write a cheque its hypotheses
  cannot cash.  Progress *is* available on the three short arms.

  **Where the missing premise comes from, stated precisely** (the first version
  of this paragraph overclaimed, #12903 review).  Every `rlp_walk_next*` entry
  contract *takes* `hvalid : isValidByteAccess (srcBase + …) = true` as a
  premise — 23 occurrences in `WalkNext.lean`, 6 in `RlpWalkNextLeafTie.lean`,
  1 in `RlpWalkNextEntryTie.lean` — and `toNat_le_of_validByte`
  (`Rv64/MemSat.lean`) turns that into `addr ≤ 0xc0000000`, roughly
  `1.8 × 10 ^ 19` below `2 ^ 64`.  A call site cannot apply any of these
  contracts without supplying `hvalid`, so the bound is available **by
  construction at the point the contract is instantiated**, which is exactly
  where the residual would be discharged.

  ⛔ That is a claim about the CONTRACT, not about call sites.  It says nothing
  about the 303 direct `jal` sites to `rlp_walk_next`, most of which have no
  discharged contract — for those the bound is not established by anything.
  The earlier wording here ("call sites have it") read as a universal over
  those 303 and was not checked against them.

  ## Why `hlt` is a premise and not a conclusion

  `BitVec.ult cursor endPtr` is required, and it is **not** redundant: the
  short-list arm's fit conjunct is `¬ult (endPtr - cursor) ((p - 0xc0) + 1)`,
  which bounds `next - cursor` but says nothing about the *direction* of
  `endPtr - cursor`.  Under wraparound that difference can be enormous while
  `endPtr <u cursor`.  The single-byte arm carries `ult cursor endPtr`
  internally and the two long arms carry the stronger `¬ult endPtr (header
  end)`, but neither short arm does, so the premise has to come from the caller.
  It does: every `rlp_walk_next*` entry contract already carries it as `hlt`.

  `rlpItemDecode_bounded_needs_hlt` is the negative control — a concrete wrapped
  state satisfying the short-list arm where the conclusion is false.
-/

import EvmAsm.Rv64.RLP.WalkNext

namespace EvmAsm.Rv64.RLP

-- `Nat.fromBytesBE` resolves only under this open, as in `WalkNext.lean`.
open EvmAsm.EL.RLP

/-- The shape both long-form arms need: a header end at or below `endPtr`, and a
    payload length fitting in what remains, put the payload end at or below
    `endPtr`.  Stated over an abstract `hdr` because `bv_omega` does not see
    through the compound header expression when it is inlined. -/
private theorem ule_add_of_ule_sub {hdr endPtr L : Word}
    (hhdr : ¬ BitVec.ult endPtr hdr = true)
    (hfit : ¬ BitVec.ult (endPtr - hdr) L = true) :
    ¬ BitVec.ult endPtr (hdr + L) = true := by
  simp only [BitVec.ult, decide_eq_true_eq] at hhdr hfit ⊢
  bv_omega

/-! ### A note on `bv_omega` cost

    `ule_add_of_ule_sub` is stated over an abstract `hdr`/`L` for a measured
    reason, not a stylistic one.  With the long form's compound length term
    `BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop (off+1)).take …))` in scope,
    `bv_omega` ran for **18m35s of CPU without finishing** on this goal.  Over
    an atom the same fact closes in under a second.  When a `bv_omega` goal is
    slow here, the cause is term size rather than difficulty: state the
    arithmetic over a variable and apply it. -/

/-- **One walked item never advances the cursor past `endPtr`.**

    Uniform over all five prefix forms.  This is half of what a walking loop
    needs to re-establish its callee's entry premises for the next iteration:
    the new cursor is still inside the walked region.

    ⚠️ The other half — **strict progress**, `cursor <u next` — is deliberately
    NOT claimed here, because it is not true of this relation.  See the module
    docstring. -/
theorem rlpItemDecode_bounded {bytes : List (BitVec 8)} {off : Nat}
    {cursor endPtr next len : Word}
    (h : rlpItemDecode bytes off cursor endPtr next len)
    (hlt : BitVec.ult cursor endPtr = true) :
    ¬ BitVec.ult endPtr next = true := by
  obtain ⟨b, _, harm⟩ := h
  rcases harm with ⟨h1, h2, h3, _⟩ | ⟨h1, h2, _, h4, h5, _⟩ |
      ⟨h1, h2, _, _, h5, h6, h7, _⟩ | ⟨h1, h2, h3, h4, _⟩ | ⟨h1, _, _, h4, h5, h6, _⟩
  -- single byte: `next = cursor + 1`, and `cursor <u endPtr` bounds it
  · subst h3
    simp only [signExtend12_1, BitVec.ult, decide_eq_true_eq] at hlt h2 ⊢
    bv_omega
  -- short string: content length `<u endPtr - cursor`
  · subst h5
    simp only [signExtend12_1, BitVec.ult, decide_eq_true_eq] at hlt h1 h2 h4 ⊢
    bv_omega
  -- long string: header end `≤u endPtr`, payload fits in the remainder
  · subst h7
    -- `next` is already `(cursor + hdrDelta) + L`; hand it to the abstract
    -- helper so `bv_omega` never sees the `Nat.fromBytesBE` term.
    exact ule_add_of_ule_sub h5 h6
  -- short list: span `≤u endPtr - cursor`
  · subst h4
    simp only [signExtend12_1, BitVec.ult, decide_eq_true_eq] at hlt h1 h2 h3 ⊢
    bv_omega
  -- long list: same as the long string, modulo where the `+ 1` sits
  · subst h6
    -- Here the `+ 1` sits inside the payload sum, so reassociate first — over
    -- the abstract length that is a one-line `BitVec` identity.
    have hassoc : ∀ L : Word,
        cursor + ((b.zeroExtend 64 - (0xf7 : Word)) + L + signExtend12 (1 : BitVec 12)) =
        (cursor + ((b.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) + L := by
      intro L; bv_omega
    rw [hassoc]
    exact ule_add_of_ule_sub h4 h5

/-- **Negative control for `hlt`.** A concrete wrapped state satisfying the
    short-list arm where boundedness is FALSE, so the premise is load-bearing
    rather than an ABI formality that could be dropped.

    `cursor = 5`, `endPtr = 3`, prefix `0xc0`: the fit conjunct reads
    `¬ult (endPtr - cursor) 1`, and `3 - 5` wraps to `2^64 - 2`, so it holds.
    `next = 6`, and `6 ≤u 3` is false — so boundedness fails outright without
    `hlt`. Exactly the situation the docstring above argues the short arms
    cannot rule out on their own. -/
theorem rlpItemDecode_bounded_needs_hlt :
    rlpItemDecode [(0xc0 : BitVec 8)] 0 (5 : Word) (3 : Word) (6 : Word) (1 : Word) ∧
      BitVec.ult (5 : Word) (3 : Word) = false ∧
      BitVec.ult (3 : Word) (6 : Word) = true := by
  refine ⟨⟨(0xc0 : BitVec 8), rfl, ?_⟩, by decide, by decide⟩
  refine Or.inr (Or.inr (Or.inr (Or.inl ⟨by decide, by decide, by decide, by decide,
    by decide⟩)))

end EvmAsm.Rv64.RLP
