/-
  EvmAsm.Codegen.Programs.HeaderExtendedDecodeWalkChain

  **Site *i* → site *i + 1*: the derivation #12799 named as the single
  obligation between the walk-site tranche and a whole-routine triple.**

  `HeaderExtendedDecodeWalkSite` proves nineteen `rlp_walk_next` call sites,
  each under a `WalkPre srcBase endPtr srcBytes srcOff` bundle.  Chaining them
  means producing site *i + 1*'s bundle from site *i*'s post, whose only
  description of the new cursor is the `rlpItemDecodeStrictW` conjunct of
  `RlpWalkNextEntryTie.entryPost`.

  ## ⭐ The shape: nine per-site premises become one per-REGION premise

  The obvious reading of "chain nineteen sites" is nineteen derivations, one
  per hop, each re-deriving nine fields.  That is not what is needed.

  Seven of `WalkPre`'s nine fields — `salign`, `off`, `over`, `valid`, `ss`,
  `ls`, `endValid` — say nothing about *which* offset the cursor is at.  They
  say the **source region is readable**: aligned base, offsets inside the byte
  list, no wraparound, valid guest byte access, and enough bytes left for a
  short-string or long-string payload the header announces.  All seven follow
  from one off-independent fact, `WalkRegion`, plus the offset being inside the
  span.

  Only two fields are genuinely per-site:

  * `lt`  — `cursor <u endPtr`, which is the decoder's **loop guard**.  The
    machine tests it; it is a hypothesis here because site *i + 1* runs exactly
    when it holds.
  * `notlist` — the INHERITED `.conditional` gate (prefix `< 0xc0`).  It is not
    derivable and is not derived; see `HeaderExtendedDecodeWalkSite`'s module
    docstring for why no instruction of `header_extended_decode` can establish
    it.

  So the chain is `walkPre_of_region` applied at the new offset, and the
  nineteen hops cost nineteen instances of one lemma rather than nineteen
  proofs.  Compare `reshape the goal, not N cases` — the same move that
  collapsed the eight `lenlen` widths in #12777.

  ## What makes the new offset legitimate

  `walkPre_chain` needs the new cursor to be a real offset into the same
  region.  That is exactly the pair of facts `Rv64.RLP.WalkItemProgress`
  provides:

      rlpItemDecode_bounded  : next ≤u endPtr    (the walk cannot overrun)
      rlpItemDecode_progress : cursor <u next    (the walk cannot stall)

  Progress is what makes `off < off'` and hence rules out site *i + 1* being
  site *i* replayed; boundedness keeps `off'` inside the span.  `progress`
  needs `isValidByteAccess endPtr`, which `WalkRegion.endValid` supplies.

  ## ⛔ What this file does NOT do

  It does not state a whole-routine triple for `header_extended_decode`, add a
  registry row, or discharge the non-LIST gate.  It closes the *derivation*
  that was missing; the loop invariant that consumes it is separate work.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodeWalkSite
import EvmAsm.Rv64.RLP.WalkItemProgress
import EvmAsm.Rv64.MemSat

namespace EvmAsm.Codegen.HeaderExtendedDecodeWalkChain

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP
open EvmAsm.Codegen.HeaderExtendedDecodeWalkSite

/-- **The off-independent half of `WalkPre`.**

    Everything the walked source region must satisfy once, as opposed to once
    per call site: the base is doubleword-aligned, the whole byte list fits
    below `2 ^ 64`, every offset in it is a valid guest byte access, the end
    pointer is valid, and the end pointer lies at or before the end of the
    list.

    `endFits` is what turns "the header says `n` more bytes and they fit before
    `endPtr`" into "there are `n` more bytes in `srcBytes`", which is how the
    `ss` and `ls` readability fields of `WalkPre` get discharged. -/
structure WalkRegion (srcBase endPtr : Word) (srcBytes : List (BitVec 8)) : Prop where
  salign   : srcBase.toNat % 8 = 0
  noWrap   : srcBase.toNat + srcBytes.length ≤ 2 ^ 64
  allValid : ∀ k, k < srcBytes.length →
                isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true
  endValid : isValidByteAccess endPtr = true
  endFits  : endPtr.toNat ≤ srcBase.toNat + srcBytes.length

/-- The cursor at offset `off` has the `toNat` you expect, and `off` is inside
    the byte list.  Both follow from the region facts plus the loop guard. -/
theorem cursor_toNat_and_lt {srcBase endPtr : Word} {srcBytes : List (BitVec 8)}
    {off : Nat} (hR : WalkRegion srcBase endPtr srcBytes)
    (hover : srcBase.toNat + off < 2 ^ 64)
    (hlt : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true) :
    (srcBase + BitVec.ofNat 64 off).toNat = srcBase.toNat + off ∧ off < srcBytes.length := by
  have hcur : (srcBase + BitVec.ofNat 64 off).toNat = srcBase.toNat + off :=
    toNat_add_ofNat_of_le hover
  refine ⟨hcur, ?_⟩
  simp only [BitVec.ult, decide_eq_true_eq] at hlt
  have := hR.endFits
  omega

/-- **The whole of `WalkPre`, from one region fact and two per-site facts.**

    `hlt` is the decoder's loop guard and `hnotlist` is the inherited
    `.conditional` gate; everything else comes out of `WalkRegion`.

    `hnotlist` is quantified over the `off < srcBytes.length` proof because
    `WalkPre.notlist` mentions `srcBytes[off]'off` — the *value* does not depend
    on which proof is supplied, so this form is no stronger than pinning one. -/
theorem walkPre_of_region {srcBase endPtr : Word} {srcBytes : List (BitVec 8)}
    (hR : WalkRegion srcBase endPtr srcBytes) (off : Nat)
    (hover : srcBase.toNat + off < 2 ^ 64)
    (hlt : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true)
    (hnotlist : ∀ h : off < srcBytes.length,
      BitVec.ult ((srcBytes[off]'h).zeroExtend 64) (0xc0 : Word) = true) :
    WalkPre srcBase endPtr srcBytes off := by
  obtain ⟨hcur, hoff⟩ := cursor_toNat_and_lt hR hover hlt
  have hltN : srcBase.toNat + off < endPtr.toNat := by
    simp only [BitVec.ult, decide_eq_true_eq] at hlt; omega
  have hfits := hR.endFits
  have hnw := hR.noWrap
  refine
    { salign := hR.salign
      off := hoff
      over := hover
      valid := hR.allValid off hoff
      endValid := hR.endValid
      lt := hlt
      notlist := hnotlist hoff
      ss := ?_
      ls := ?_ }
  -- short string of length 1: one more byte must be readable
  · intro _ _ h3 h4
    rw [h4] at h3
    simp only [BitVec.ult, decide_eq_true_eq] at h3
    have hsub : (endPtr - (srcBase + BitVec.ofNat 64 off)).toNat
        = endPtr.toNat - (srcBase.toNat + off) := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; omega), hcur]
    rw [hsub] at h3
    have hone : (1 : Word).toNat = 1 := by decide
    rw [hone] at h3
    have hlen : off + 1 < srcBytes.length := by omega
    exact ⟨hlen, by omega, hR.allValid (off + 1) hlen⟩
  -- long string: the announced length-of-length bytes must be readable
  · intro h1 h2 h3
    have hb : 1 ≤ ((srcBytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat ∧
        ((srcBytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat ≤ 8 := by
      simp only [BitVec.ult, decide_eq_true_eq] at h1 h2
      constructor <;> bv_omega
    obtain ⟨hb1, hb8⟩ := hb
    have hone : (1 : Word).toNat = 1 := by decide
    have hend : endPtr.toNat ≤ 0xc0000000 := toNat_le_of_validByte hR.endValid
    have hhdr : ((srcBase + BitVec.ofNat 64 off) +
        (((srcBytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)) +
          signExtend12 (1 : BitVec 12))).toNat
        = srcBase.toNat + off
            + ((srcBytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat + 1 := by
      rw [BitVec.toNat_add, hcur, signExtend12_1, BitVec.toNat_add, hone]
      omega
    simp only [BitVec.ult, decide_eq_true_eq] at h3
    rw [hhdr] at h3
    have hlen : off + 1
        + ((srcBytes[off]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
        ≤ srcBytes.length := by omega
    refine ⟨hlen, by omega, ?_⟩
    intro k hk
    exact hR.allValid (off + 1 + k) (by omega)

/-- **The chaining derivation, closed.**

    From site *i*'s `WalkPre`, the `rlpItemDecodeStrictW` conjunct of its post,
    the loop guard at the new cursor and the inherited gate there, produce site
    *i + 1*'s `WalkPre` — and, as a separate conjunct, the fact that the offset
    strictly increased, which is what a loop measure needs.

    `hbase` says the walk never runs below its own base.  It is not a new
    assumption about the machine: `srcBase` is the region base and every cursor
    the walk produces is `srcBase + <offset>`. -/
theorem walkPre_chain {srcBase endPtr a0 a2 : Word} {srcBytes : List (BitVec 8)}
    {off floor : Nat}
    (hR : WalkRegion srcBase endPtr srcBytes)
    (hover : srcBase.toNat + off < 2 ^ 64)
    (hlt : BitVec.ult (srcBase + BitVec.ofNat 64 off) endPtr = true)
    (hdec : rlpItemDecodeStrictW srcBytes srcBase off (a0 - srcBase).toNat
              (endPtr - srcBase).toNat a2 floor)
    (hbase : srcBase.toNat ≤ a0.toNat)
    (hlt' : BitVec.ult a0 endPtr = true)
    (hnotlist' : ∀ h : (a0 - srcBase).toNat < srcBytes.length,
      BitVec.ult ((srcBytes[(a0 - srcBase).toNat]'h).zeroExtend 64) (0xc0 : Word) = true) :
    WalkPre srcBase endPtr srcBytes (a0 - srcBase).toNat ∧
      off < (a0 - srcBase).toNat := by
  have hoff' : (a0 - srcBase).toNat = a0.toNat - srcBase.toNat := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; omega)]
  have hbe : srcBase.toNat ≤ endPtr.toNat := by
    simp only [BitVec.ult, decide_eq_true_eq] at hlt'; omega
  have hendOff : srcBase + BitVec.ofNat 64 (endPtr - srcBase).toNat = endPtr := by
    have : (endPtr - srcBase).toNat = endPtr.toNat - srcBase.toNat := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, this]
    have := endPtr.isLt
    omega
  have hnextOff : srcBase + BitVec.ofNat 64 (a0 - srcBase).toNat = a0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hoff']
    have := a0.isLt
    omega
  obtain ⟨hdecode, _⟩ := hdec
  rw [hendOff, hnextOff] at hdecode
  have hprog : BitVec.ult (srcBase + BitVec.ofNat 64 off) a0 = true :=
    rlpItemDecode_progress hdecode hlt hR.endValid
  have hcur : (srcBase + BitVec.ofNat 64 off).toNat = srcBase.toNat + off :=
    toNat_add_ofNat_of_le hover
  have hstrict : off < (a0 - srcBase).toNat := by
    simp only [BitVec.ult, decide_eq_true_eq] at hprog
    omega
  refine ⟨walkPre_of_region hR _ ?_ ?_ hnotlist', hstrict⟩
  · have := a0.isLt; omega
  · rw [hnextOff]; exact hlt'

/-! ## Non-vacuity -/

/-- **`WalkRegion` is satisfiable**, on the same input-memory span the walk-site
    instances use. -/
theorem walkRegion_instance :
    WalkRegion (0x40000000 : Word) ((0x40000000 : Word) + 4)
      [0x83, 0x01, 0x02, 0x03] where
  salign   := by decide
  noWrap   := by decide
  allValid := by
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with h | h | h | h <;> subst h <;> decide
  endValid := by decide
  endFits  := by decide

/-- **`walkPre_of_region` really produces the bundle the sites consume**, with
    no hypothesis left over: the same `WalkPre` that `walkPre_instance`
    exhibits by hand is here derived from the region fact instead. -/
theorem walkPre_of_region_instance :
    WalkPre (0x40000000 : Word) ((0x40000000 : Word) + 4) [0x83, 0x01, 0x02, 0x03] 0 :=
  walkPre_of_region walkRegion_instance 0 (by decide) (by decide) (fun h => by
    have hb : (([0x83, 0x01, 0x02, 0x03] : List (BitVec 8))[0]'h) = 0x83 := rfl
    rw [hb]
    decide)

/-- **NEGATIVE CONTROL — `WalkRegion` excludes something.**  A region whose end
    pointer lies past the end of the byte list fails `endFits`, which is the
    field that carries the whole readability argument: without it the header
    could announce a payload that fits before `endPtr` and still run off the
    end of `srcBytes`. -/
theorem walkRegion_refutable_on_short_list :
    ¬ WalkRegion (0x40000000 : Word) ((0x40000000 : Word) + 64)
        [0x83, 0x01, 0x02, 0x03] := by
  intro h
  exact absurd h.endFits (by decide)

end EvmAsm.Codegen.HeaderExtendedDecodeWalkChain
