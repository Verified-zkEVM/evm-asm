/-
  EvmAsm.Rv64.RLP.WalkItemDeterminism

  **`rlpItemDecode` is a function**, not merely a relation — and so are the walk
  predicates built on it.

  WHY THIS IS NEEDED, and why it lives here rather than beside a consumer. Every
  whole-routine spec in the RLP walk family states its outcome existentially: the
  `rlp_list_nth_item` / `account_decode` / `account_is_eip161_empty` posts all read
  `∃ offset len, … Success bytes base listLen index offset len ∧ <outputs written from
  offset/len>`. Those existentials are *whatever the routine found*. To conclude that the
  outputs denote a **known** value — the four fields of an `AccountRecord`, say — a caller
  must know the found offsets ARE the offsets of that value's encoding. That is exactly a
  determinism statement, and nothing in the tree had one.

  So this is not an `account_decode` lemma; it is shared infrastructure. #11345 and #11346
  sit on the identical `StrictListPayload`/`StrictNthItem`/`rlpItemDecode` tower, and
  #11351 reaches it through `rlp_field_to_u64`. Putting it under `Rv64/RLP/` rather than
  `Codegen/Programs/` is deliberate: the `Codegen` consumers sit on the other side of the
  layering boundary, so core-layer walk facts (determinism, content-span) live here.

  ⭐ WHY IT IS TRUE. `rlpItemDecode` (`WalkNext.lean:3649`) is
  `∃ b, bytes[off]? = some b ∧ (five disjuncts)`. The head byte is shared — `Option.some`
  is injective — and the five disjuncts are guarded by **range-disjoint** tests on
  `B := b.zeroExtend 64`:

      1  ult B 0x80                    2  ¬ult B 0x80 ∧ ult B 0xb8
      3  ¬ult B 0xb8 ∧ ult B 0xc0      4  ¬ult B 0xc0 ∧ ult B 0xf8
      5  ¬ult B 0xf8

  so at most one arm applies. Within each arm `next` and `len` are pinned by explicit
  equations in `b`, `cursor`, `endPtr`, `bytes` and `off` — there is no further choice.
  Hence 25 cases: 5 diagonal ones close by `rfl` after substitution, and the 20
  off-diagonal ones are guard contradictions, discharged uniformly by pushing every `ult`
  through to `Nat` and calling `omega`.

  ⚠️ NOT claimed here: that a decode *exists*, or that it agrees with `EL.RLP.decodeAux`.
  The latter is **false** for the nested-list arms — see the `c3 c2 81 00` counterexample
  on #11341 — and is a separate question about the verdict column, not this one.
-/

import EvmAsm.Rv64.RLP.WalkNext

namespace EvmAsm.Rv64.RLP

/-- Widening the bound of an unsigned comparison. The workhorse for the 20
    off-diagonal cases: a byte below `0x80` is below `0xb8`, and so on. -/
private theorem ult_mono {x c1 c2 : Word}
    (h : BitVec.ult x c1 = true) (hc : c1.toNat ≤ c2.toNat) :
    BitVec.ult x c2 = true := by
  rw [BitVec.ult_iff_toNat_lt] at h ⊢
  omega

/-- The head-byte literals, as naturals — supplied to `omega`, which cannot evaluate
    `BitVec.toNat` of a numeral on its own. -/
private theorem prefix_literals :
    ((0x80 : Word)).toNat = 128 ∧ ((0xb8 : Word)).toNat = 184 ∧
    ((0xc0 : Word)).toNat = 192 ∧ ((0xf8 : Word)).toNat = 248 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- ⭐ **`rlpItemDecode` is deterministic.** Two canonical decodes at the same offset,
    cursor and window agree on both the advanced cursor and the item length.

    This is what lets a caller identify the existentially-quantified offsets in a walk
    routine's postcondition with the offsets of a *known* encoding. -/
theorem rlpItemDecode_deterministic {bytes : List (BitVec 8)} {off : Nat}
    {cursor endPtr next₁ len₁ next₂ len₂ : Word}
    (h₁ : rlpItemDecode bytes off cursor endPtr next₁ len₁)
    (h₂ : rlpItemDecode bytes off cursor endPtr next₂ len₂) :
    next₁ = next₂ ∧ len₁ = len₂ := by
  obtain ⟨b, hb, hc₁⟩ := h₁
  obtain ⟨b', hb', hc₂⟩ := h₂
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨p80, pb8, pc0, pf8⟩ := prefix_literals
  rcases hc₁ with ⟨g, -, hn₁, hl₁⟩ | ⟨g, g', -, -, hn₁, hl₁⟩ |
      ⟨g, g', -, -, -, -, hn₁, hl₁⟩ | ⟨g, g', -, hn₁, hl₁⟩ | ⟨g, -, -, -, -, hn₁, hl₁⟩ <;>
    rcases hc₂ with ⟨f, -, hn₂, hl₂⟩ | ⟨f, f', -, -, hn₂, hl₂⟩ |
        ⟨f, f', -, -, -, -, hn₂, hl₂⟩ | ⟨f, f', -, hn₂, hl₂⟩ | ⟨f, -, -, -, -, hn₂, hl₂⟩ <;>
    subst hn₁ <;> subst hl₁ <;> subst hn₂ <;> subst hl₂ <;>
    first
      | exact ⟨rfl, rfl⟩
      | (exfalso
         simp only [BitVec.ult_eq_decide, decide_eq_true_eq, Nat.not_lt,
           p80, pb8, pc0, pf8] at *
         omega)

/-! ## Content-span bridge

    Pure window facts for an accepted `rlpItemDecode`: the content pointer
    recovered as `next - len` lies inside `[off, endOff]`. Lived briefly beside
    the retired experimental `rlp_field0_to_u64` wrapper (#12437); kept under the
    historical name `rlpItemDecode_field0_content_span` so Account/Withdrawal
    callers need no rename. -/

private theorem decode_ult_lt {a b : Word} (h : BitVec.ult a b = true) :
    a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem decode_not_ult_le {a b : Word} (h : ¬ BitVec.ult a b = true) :
    b.toNat ≤ a.toNat := by
  simp [BitVec.ult] at h
  exact h

private theorem decode_spanStart_longString {base : Word} {off endOff : Nat}
    {next header payload len : Word}
    (hheader1 : 1 ≤ header.toNat) (hheader9 : header.toNat ≤ 9)
    (hfit1 : ¬ BitVec.ult (base + BitVec.ofNat 64 endOff)
      ((base + BitVec.ofNat 64 off) + header) = true)
    (hfit2 : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff) -
      ((base + BitVec.ofNat 64 off) + header)) payload = true)
    (hnext : next = ((base + BitVec.ofNat 64 off) + header) + payload)
    (hlen : len = payload) (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    off ≤ (next - len - base).toNat ∧
      (next - len - base).toNat + len.toNat ≤ endOff := by
  have hfit1' := decode_not_ult_le hfit1
  have hfit2' := decode_not_ult_le hfit2
  constructor <;> bv_omega

private theorem decode_spanStart_shortList {base : Word} {off endOff : Nat}
    {next span len : Word}
    (hspan1 : 1 ≤ span.toNat) (hspan56 : span.toNat ≤ 56)
    (hfit : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff) -
      (base + BitVec.ofNat 64 off)) span = true)
    (hnext : next = (base + BitVec.ofNat 64 off) + span)
    (hlen : len = span) (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    off ≤ (next - len - base).toNat ∧
      (next - len - base).toNat + len.toNat ≤ endOff := by
  have hfit' := decode_not_ult_le hfit
  constructor <;> bv_omega

private theorem decode_spanStart_longList {base : Word} {off endOff : Nat}
    {next header payload len : Word}
    (hheader1 : 1 ≤ header.toNat) (hheader9 : header.toNat ≤ 9)
    (hfit1 : ¬ BitVec.ult (base + BitVec.ofNat 64 endOff)
      ((base + BitVec.ofNat 64 off) + header) = true)
    (hfit2 : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff) -
      ((base + BitVec.ofNat 64 off) + header)) payload = true)
    (hnext : next = ((base + BitVec.ofNat 64 off) + header) + payload)
    (hlen : len = header + payload) (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    off ≤ (next - len - base).toNat ∧
      (next - len - base).toNat + len.toNat ≤ endOff := by
  have hfit1' := decode_not_ult_le hfit1
  have hfit2' := decode_not_ult_le hfit2
  constructor <;> bv_omega

private theorem decode_reassocLongList (cursor header payload : Word) :
    cursor + (header + payload + 1) = (cursor + (header + 1)) + payload := by
  bv_omega

private theorem decode_addRotate (header payload : Word) :
    header + payload + 1 = (header + 1) + payload := by
  bv_omega

/-- Core-layer content-window bridge for an accepted walk item. -/
theorem rlpItemDecode_field0_content_span {bytes : List (BitVec 8)} {base : Word}
    {off endOff : Nat} {next len : Word}
    (h : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff) next len)
    (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    next - len = base + BitVec.ofNat 64 ((next - len - base).toNat) ∧
    off ≤ (next - len - base).toNat ∧
    (next - len - base).toNat + len.toNat ≤ endOff := by
  have hrep : next - len = base + BitVec.ofNat 64 ((next - len - base).toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  refine ⟨hrep, ?_⟩
  obtain ⟨b, _hb, hd⟩ := h
  have hb256 : (b.zeroExtend 64).toNat < 256 := by bv_omega
  rcases hd with ⟨_hp80, hin, hnext, hlen⟩ |
      ⟨hge80, _hltb8, _hcanon, hfit, hnext, hlen⟩ |
      ⟨hgeb8, hltc0, _hlead, _hmin, hfit1, hfit2, hnext, hlen⟩ |
      ⟨hgec0, hltf8, hfit, hnext, hlen⟩ |
      ⟨hgef8, _hlead, _hmin, hfit1, hfit2, hnext, hlen⟩
  · have hin' := decode_ult_lt hin
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hnext
    subst hlen
    constructor <;> bv_omega
  · have hfit' := decode_ult_lt hfit
    have hge' := decode_not_ult_le hge80
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hnext
    subst hlen
    constructor <;> bv_omega
  · have hge' := decode_not_ult_le hgeb8
    have hlt' := decode_ult_lt hltc0
    have hheader1 : 1 ≤ ((b.zeroExtend 64 - (0xb7 : Word)) +
        signExtend12 (1 : BitVec 12)).toNat := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
    have hheader9 : ((b.zeroExtend 64 - (0xb7 : Word)) +
        signExtend12 (1 : BitVec 12)).toNat ≤ 9 := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
    exact decode_spanStart_longString hheader1 hheader9 hfit1 hfit2 hnext hlen hoffle hover
  · have hge' := decode_not_ult_le hgec0
    have hlt' := decode_ult_lt hltf8
    have hspan1 : 1 ≤ ((b.zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)).toNat := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
    have hspan56 : ((b.zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)).toNat ≤ 56 := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega
    exact decode_spanStart_shortList hspan1 hspan56 hfit hnext hlen hoffle hover
  · have hge' := decode_not_ult_le hgef8
    have hheader1 : 1 ≤ ((b.zeroExtend 64 - (0xf7 : Word)) + (1 : Word)).toNat := by
      bv_omega
    have hheader9 : ((b.zeroExtend 64 - (0xf7 : Word)) + (1 : Word)).toNat ≤ 9 := by
      bv_omega
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hnext hlen hfit1 hfit2
    rw [decode_reassocLongList] at hnext
    rw [decode_addRotate] at hlen
    exact decode_spanStart_longList hheader1 hheader9 hfit1 hfit2 hnext hlen hoffle hover

end EvmAsm.Rv64.RLP
