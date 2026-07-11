/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsWalk

  Walk-semantics layer for the `bal_account_nonstorage_finals` find-last
  loops (bead evm-asm-4ch8f.43.5, slice 2a) — the pure lemmas that let the
  `MeasureLoop` fold consume the verified `rlp_walk_next` contract:

  * `rlpItemDecode_advance` — every accepted decode strictly advances the
    cursor and stays inside the window (the strictly-decreasing measure for
    `measureTwoExitLoop_spec`).  The no-overflow side condition carries a
    9-byte slack (`base + endOff + 9 < 2^64`): a long-form header can be up
    to 9 bytes, and a window flush against the top of the address space
    could otherwise wrap mid-header (the routine-level pre supplies the
    slack from the region bounds, where it is trivially satisfiable);
  * `WalkPrefix` — the "walked so far, last span = (next, len)" chain the
    loop invariant carries, with `WalkPrefix.snoc` (one more iteration) and
    `WalkPrefix.toLastItemAt` (the head-exit conversion into the §2
    `LastItemAt` semantics of the spec file).
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsSpec
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SAsm.AbiFrameOwn

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-! ## §1  Cursor advance -/

private theorem se1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide

theorem ult_lt {a b : Word} (h : BitVec.ult a b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem not_ult_le {a b : Word} (h : ¬ BitVec.ult a b = true) : b.toNat ≤ a.toNat := by
  simp [BitVec.ult] at h
  exact h

/-- Shared long-form advance core: with an in-window cursor, a 1–9 byte
    header that fits (`hfit1`) and a payload that fits the remaining gap
    (`hfit2`), the advanced cursor `(cursor + hdr) + L` lands strictly past
    `off` and inside the window.  `L` is opaque (the callers pass the
    `fromBytesBE` payload length as an atom). -/
private theorem advance_longform {base : Word} {off endOff : Nat}
    {next hdrW L : Word}
    (hhdr1 : 1 ≤ hdrW.toNat) (hhdr9 : hdrW.toNat ≤ 9)
    (hfit1 : ¬ BitVec.ult (base + BitVec.ofNat 64 endOff)
      ((base + BitVec.ofNat 64 off) + hdrW) = true)
    (hfit2 : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff)
      - ((base + BitVec.ofNat 64 off) + hdrW)) L = true)
    (hnext : next = ((base + BitVec.ofNat 64 off) + hdrW) + L)
    (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    off < (next - base).toNat ∧ (next - base).toNat ≤ endOff := by
  have hfit1' := not_ult_le hfit1
  have hfit2' := not_ult_le hfit2
  bv_omega

private theorem reassoc_longlist (c h l : Word) :
    c + (h + l + 1) = (c + (h + 1)) + l := by
  bv_omega

/-- Every accepted `rlpItemDecode` strictly advances the cursor and stays
    inside the window: with the cursor at `base + off` and the window end at
    `base + endOff` (no wrap), the advanced cursor `next` is `base + off'`
    with `off < off' ≤ endOff`.  This is the strictly-decreasing measure the
    find-last loops fold by. -/
theorem rlpItemDecode_advance {bytes : List (BitVec 8)} {base : Word}
    {off endOff : Nat} {next len : Word}
    (h : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff) next len)
    (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    next = base + BitVec.ofNat 64 ((next - base).toNat) ∧
    off < (next - base).toNat ∧ (next - base).toNat ≤ endOff := by
  have hrep : next = base + BitVec.ofNat 64 ((next - base).toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  refine ⟨hrep, ?_⟩
  obtain ⟨b, hb, hdisj⟩ := h
  rcases hdisj with ⟨hp80, hin, hnext, hlen⟩ | ⟨hge80, hltb8, hcanon, hfit, hnext, hlen⟩ |
    ⟨hgeb8, hltc0, hlead, hmin, hfit1, hfit2, hnext, hlen⟩ |
    ⟨hgec0, hltf8, hfit, hnext, hlen⟩ | ⟨hgef8, hlead, hmin, hfit1, hfit2, hnext, hlen⟩
  · -- single byte: next = cursor + 1, cursor < endPtr
    have hin' := ult_lt hin
    rw [se1] at hnext
    bv_omega
  · -- short string: len = b - 0x80 < endPtr - cursor, next = (cursor + 1) + len
    have hfit' := ult_lt hfit
    have hge' := not_ult_le hge80
    rw [se1] at hnext
    bv_omega
  · -- long string: hdr = (b - 0xb7) + se1 fits, L ≤ end - (cursor + hdr)
    have hge' := not_ult_le hgeb8
    have hlt' := ult_lt hltc0
    have hhdr1 : 1 ≤ ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12)).toNat := by
      rw [se1]; bv_omega
    have hhdr9 : ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12)).toNat ≤ 9 := by
      rw [se1]; bv_omega
    exact advance_longform hhdr1 hhdr9 hfit1 hfit2 hnext hoffle hover
  · -- short list: span = (b - 0xc0) + 1 ≤ endPtr - cursor
    have hge' := not_ult_le hgec0
    have hlt' := ult_lt hltf8
    have hfit' := not_ult_le hfit
    rw [se1] at hnext hfit'
    bv_omega
  · -- long list: hdr = (b - 0xf7) + se1 fits, L ≤ end - (cursor + hdr)
    have hge' := not_ult_le hgef8
    have hhdr1 : 1 ≤ ((b.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)).toNat := by
      rw [se1]; bv_omega
    have hhdr9 : ((b.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)).toNat ≤ 9 := by
      rw [se1]; bv_omega
    rw [se1] at hnext hfit1 hfit2
    rw [reassoc_longlist] at hnext
    exact advance_longform hhdr1 hhdr9 hfit1 hfit2 hnext hoffle hover

#print axioms rlpItemDecode_advance

/-- Word rotation for the long-list span shape: `h + l + 1 = (h + 1) + l`. -/
private theorem add_rot (h l : Word) : h + l + 1 = (h + 1) + l := by
  bv_omega

/-- Short-list span-start core (`span` opaque small). -/
private theorem spanStart_shortlist {base : Word} {off endOff : Nat}
    {next span len : Word}
    (hspan1 : 1 ≤ span.toNat) (hspan56 : span.toNat ≤ 56)
    (hfit : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff)
      - (base + BitVec.ofNat 64 off)) span = true)
    (hnext : next = (base + BitVec.ofNat 64 off) + span)
    (hlen : len = span)
    (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    off ≤ (next - len - base).toNat ∧
    (next - len - base).toNat + len.toNat ≤ endOff := by
  have hfit' := not_ult_le hfit
  constructor <;> bv_omega

/-- Long-string span-start core (`L` opaque). -/
private theorem spanStart_longstring {base : Word} {off endOff : Nat}
    {next hdrW L len : Word}
    (hhdr1 : 1 ≤ hdrW.toNat) (hhdr9 : hdrW.toNat ≤ 9)
    (hfit1 : ¬ BitVec.ult (base + BitVec.ofNat 64 endOff)
      ((base + BitVec.ofNat 64 off) + hdrW) = true)
    (hfit2 : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff)
      - ((base + BitVec.ofNat 64 off) + hdrW)) L = true)
    (hnext : next = ((base + BitVec.ofNat 64 off) + hdrW) + L)
    (hlen : len = L)
    (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    off ≤ (next - len - base).toNat ∧
    (next - len - base).toNat + len.toNat ≤ endOff := by
  have hfit1' := not_ult_le hfit1
  have hfit2' := not_ult_le hfit2
  constructor <;> bv_omega

/-- Long-list span-start core (`L` opaque; the span is header + payload). -/
private theorem spanStart_longlist {base : Word} {off endOff : Nat}
    {next hdrW L len : Word}
    (hhdr1 : 1 ≤ hdrW.toNat) (hhdr9 : hdrW.toNat ≤ 9)
    (hfit1 : ¬ BitVec.ult (base + BitVec.ofNat 64 endOff)
      ((base + BitVec.ofNat 64 off) + hdrW) = true)
    (hfit2 : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff)
      - ((base + BitVec.ofNat 64 off) + hdrW)) L = true)
    (hnext : next = ((base + BitVec.ofNat 64 off) + hdrW) + L)
    (hlen : len = hdrW + L)
    (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    off ≤ (next - len - base).toNat ∧
    (next - len - base).toNat + len.toNat ≤ endOff := by
  have hfit1' := not_ult_le hfit1
  have hfit2' := not_ult_le hfit2
  constructor <;> bv_omega

/-- The span-start of an accepted decode (`next - len`, the routine's
    `s3 := a0 - a2` capture) lies inside the window: at or past the item's
    own cursor, and (with the span) at or before the window end.  Feeds the
    field-station `rlp_walk_init` side conditions. -/
theorem rlpItemDecode_spanStart {bytes : List (BitVec 8)} {base : Word}
    {off endOff : Nat} {next len : Word}
    (h : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff) next len)
    (hoffle : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    next - len = base + BitVec.ofNat 64 ((next - len - base).toNat) ∧
    off ≤ (next - len - base).toNat ∧
    (next - len - base).toNat + len.toNat ≤ endOff := by
  have hrepS : next - len = base + BitVec.ofNat 64 ((next - len - base).toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  refine ⟨hrepS, ?_⟩
  clear hrepS
  obtain ⟨hrep', hlt, hle⟩ := rlpItemDecode_advance h hoffle hover
  obtain ⟨b, hb, hdisj⟩ := h
  clear hrep'
  have hb256 : (b.zeroExtend 64).toNat < 256 := by bv_omega
  rcases hdisj with ⟨hp80, hin, hnext, hlen⟩ | ⟨hge80, hltb8, hcanon, hfit, hnext, hlen⟩ |
    ⟨hgeb8, hltc0, hlead, hmin, hfit1, hfit2, hnext, hlen⟩ |
    ⟨hgec0, hltf8, hfit, hnext, hlen⟩ | ⟨hgef8, hlead, hmin, hfit1, hfit2, hnext, hlen⟩
  · -- single byte: start = cursor, len = 1
    have hin' := ult_lt hin
    subst hlen
    rw [se1] at hnext
    refine ⟨?_, ?_⟩ <;> bv_omega
  · -- short string: start = cursor + 1
    have hfit' := ult_lt hfit
    have hge' := not_ult_le hge80
    subst hlen
    rw [se1] at hnext
    refine ⟨?_, ?_⟩ <;> bv_omega
  · -- long string: start = cursor + 1 + lenlen
    have hge' := not_ult_le hgeb8
    have hlt' := ult_lt hltc0
    have hhdr1 : 1 ≤ ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12)).toNat := by
      rw [se1]; bv_omega
    have hhdr9 : ((b.zeroExtend 64 - (0xb7 : Word)) + signExtend12 (1 : BitVec 12)).toNat ≤ 9 := by
      rw [se1]; bv_omega
    exact spanStart_longstring hhdr1 hhdr9 hfit1 hfit2 hnext hlen hoffle hover
  · -- short list: start = cursor, len = span
    have hge' := not_ult_le hgec0
    have hlt' := ult_lt hltf8
    have hspan1 : 1 ≤ ((b.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)).toNat := by
      rw [se1]; bv_omega
    have hspan56 : ((b.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)).toNat ≤ 56 := by
      rw [se1]; bv_omega
    exact spanStart_shortlist hspan1 hspan56 hfit hnext hlen hoffle hover
  · -- long list: start = cursor, len = span
    have hge' := not_ult_le hgef8
    have hhdr1 : 1 ≤ ((b.zeroExtend 64 - (0xf7 : Word)) + (1 : Word)).toNat := by
      have hb3 := (b.zeroExtend 64).isLt
      bv_omega
    have hhdr9 : ((b.zeroExtend 64 - (0xf7 : Word)) + (1 : Word)).toNat ≤ 9 := by
      have hb3 : (b.zeroExtend 64).toNat < 256 := by bv_omega
      bv_omega
    rw [se1] at hnext hlen
    rw [reassoc_longlist] at hnext
    rw [add_rot] at hlen
    have hfit1' : ¬ BitVec.ult (base + BitVec.ofNat 64 endOff)
        ((base + BitVec.ofNat 64 off) + ((b.zeroExtend 64 - (0xf7 : Word)) + (1 : Word)))
        = true := by
      rw [show ((b.zeroExtend 64 - (0xf7 : Word)) + (1 : Word))
          = ((b.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) from by
        rw [se1]]
      exact hfit1
    have hfit2' : ¬ BitVec.ult ((base + BitVec.ofNat 64 endOff)
        - ((base + BitVec.ofNat 64 off) + ((b.zeroExtend 64 - (0xf7 : Word)) + (1 : Word))))
        (BitVec.ofNat 64 (EL.RLP.Nat.fromBytesBE
          ((bytes.drop (off + 1)).take (b.zeroExtend 64 - (0xf7 : Word)).toNat))) = true := by
      rw [show ((b.zeroExtend 64 - (0xf7 : Word)) + (1 : Word))
          = ((b.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) from by
        rw [se1]]
      exact hfit2
    exact spanStart_longlist hhdr1 hhdr9 hfit1' hfit2' hnext hlen hoffle hover

#print axioms rlpItemDecode_spanStart


/-! ## §2  The walked-so-far chain -/

/-- The loop invariant's chain: from offset `off0`, one or more accepted
    decodes whose every non-final step advanced past a NON-end cursor
    (the loop only re-enters when the head test finds cursor ≠ end), the
    LAST decode being `(next, len)` and ending at offset `off`. -/
inductive WalkPrefix (bytes : List (BitVec 8)) (base endPtr : Word) :
    Nat → Nat → Word → Word → Prop
  | one (off : Nat) (next len : Word)
      (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len) :
      WalkPrefix bytes base endPtr off ((next - base).toNat) next len
  | cons (off off' : Nat) (next len next' len' : Word)
      (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len)
      (hne : next ≠ endPtr)
      (hrest : WalkPrefix bytes base endPtr ((next - base).toNat) off' next' len') :
      WalkPrefix bytes base endPtr off off' next' len'

/-- Append one more iteration to the chain: the loop re-entered (so the
    previous last cursor was not the end) and decoded one more item. -/
theorem WalkPrefix.snoc {bytes : List (BitVec 8)} {base endPtr : Word}
    {off0 off : Nat} {next len next' len' : Word}
    (h : WalkPrefix bytes base endPtr off0 off next len)
    (hne : next ≠ endPtr)
    (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next' len') :
    WalkPrefix bytes base endPtr off0 ((next' - base).toNat) next' len' := by
  induction h with
  | one o n l hi =>
      exact .cons o _ n l next' len' hi hne (.one _ next' len' hitem)
  | cons o o' n l n' l' hi hne0 hrest ih =>
      exact .cons o _ n l next' len' hi hne0 (ih hne hitem)

/-- Head-exit conversion: a chain whose last decode reached the window end
    IS a `LastItemAt` derivation (the §2 semantics of the spec file). -/
theorem WalkPrefix.toLastItemAt {bytes : List (BitVec 8)} {base endPtr : Word}
    {off0 off : Nat} {next len : Word}
    (h : WalkPrefix bytes base endPtr off0 off next len)
    (hend : next = endPtr) :
    LastItemAt bytes base endPtr off0 next len := by
  induction h with
  | one o n l hi => exact .last o n l hi hend
  | cons o o' n l n' l' hi hne hrest ih =>
      exact .step o n l n' l' hi hne (ih hend)

#print axioms WalkPrefix.snoc
#print axioms WalkPrefix.toLastItemAt

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
