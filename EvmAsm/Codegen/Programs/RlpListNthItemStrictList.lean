/-
  EvmAsm.Codegen.Programs.RlpListNthItemStrictList

  Layout-independent strict-list payload type and its structural lemmas,
  split out of `RlpListNthItemSAsmBase` so guest-layout changes do not rebuild
  these facts.  Keep this module free of `GuestAddrs`, `RegionMap`, and
  emitted-program imports.  The declarations live in the same namespace
  `EvmAsm.Codegen.RlpListNthItemSAsm` as the parent so all fully-qualified
  references resolve unchanged.
-/

import EvmAsm.Rv64.Instructions
import EvmAsm.EL.RLP.Basic
import Mathlib.Data.Nat.Basic

namespace EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- A strict successful outer-list decode.  `cursorOff` is the first child
    offset and `endPtr` is the exclusive end of the complete encoded list.
    The two constructors mirror the only status-zero arms of
    `rlp_walk_init`: exact short-list length and canonical exact long-list
    length. -/
inductive StrictListPayload (bytes : List (BitVec 8)) (base : Word) :
    Nat → Nat → Word → Prop
  | short (listLen cursorOff : Nat) (b : BitVec 8)
      (hbyte : bytes[0]? = some b)
      (hlist : ¬ BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true)
      (hshort : BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true)
      (hcursor : cursorOff = 1)
      (hlen : (b.zeroExtend 64 - (0xc0 : Word)).toNat + 1 = listLen) :
      StrictListPayload bytes base listLen cursorOff
        (base + BitVec.ofNat 64 listLen)

  | long (listLen cursorOff : Nat) (b first : BitVec 8)
      (hbyte : bytes[0]? = some b)
      (hlong : ¬ BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true)
      (hfirst : bytes[1]? = some first)
      (hnz : first ≠ 0)
      (hminimal : 56 ≤ Nat.fromBytesBE
        ((bytes.drop 1).take (b.zeroExtend 64 - (0xf7 : Word)).toNat))
      (hcursor : cursorOff = 1 + (b.zeroExtend 64 - (0xf7 : Word)).toNat)
      (hlen : cursorOff + Nat.fromBytesBE
        ((bytes.drop 1).take (b.zeroExtend 64 - (0xf7 : Word)).toNat) = listLen) :
      StrictListPayload bytes base listLen cursorOff
        (base + BitVec.ofNat 64 listLen)

theorem StrictListPayload.end_eq {bytes : List (BitVec 8)} {base endPtr : Word}
    {listLen cursorOff : Nat}
    (h : StrictListPayload bytes base listLen cursorOff endPtr) :
    endPtr = base + BitVec.ofNat 64 listLen := by
  cases h <;> rfl

theorem StrictListPayload.cursor_pos {bytes : List (BitVec 8)} {base endPtr : Word}
    {listLen cursorOff : Nat}
    (h : StrictListPayload bytes base listLen cursorOff endPtr) :
    1 ≤ cursorOff := by
  cases h with
  | short _ _ _ _ hc _ => omega
  | long _ _ _ _ _ _ _ hc _ => omega

theorem StrictListPayload.cursor_le {bytes : List (BitVec 8)} {base endPtr : Word}
    {listLen cursorOff : Nat}
    (h : StrictListPayload bytes base listLen cursorOff endPtr) :
    cursorOff ≤ listLen := by
  cases h with
  | short b _ _ _ hc hl =>
      subst hc
      have hb := b.isLt
      simp only [BitVec.toNat_sub] at hl
      omega
  | long _ _ _ _ _ _ _ hc hl => omega

theorem StrictListPayload.listLen_pos {bytes : List (BitVec 8)} {base endPtr : Word}
    {listLen cursorOff : Nat}
    (h : StrictListPayload bytes base listLen cursorOff endPtr) :
    0 < listLen := by
  exact lt_of_lt_of_le h.cursor_pos h.cursor_le

theorem StrictListPayload.prefix_not_lt_c0 {bytes : List (BitVec 8)}
    {base endPtr : Word} {listLen cursorOff : Nat}
    (h : StrictListPayload bytes base listLen cursorOff endPtr) (hoff : 0 < bytes.length) :
    ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
  cases h with
  | short b hbyte hnot _ _ _ =>
      rw [List.getElem?_eq_getElem hoff] at hbyte
      have hb : bytes[0]'hoff = b := Option.some.inj hbyte
      subst b
      exact hnot
  | long b first hbyte hlong _ _ _ _ _ =>
      rw [List.getElem?_eq_getElem hoff] at hbyte
      have hb : bytes[0]'hoff = b := Option.some.inj hbyte
      subst b
      intro hlt
      have hlt' := BitVec.ult_iff_lt.mp hlt
      have hlong' : ¬ ((bytes[0]'hoff).zeroExtend 64) < (0xf8 : Word) := by
        intro hx
        exact hlong (BitVec.ult_iff_lt.mpr hx)
      change (bytes[0]'hoff).toNat < 192 at hlt'
      change ¬ (bytes[0]'hoff).toNat < 248 at hlong'
      omega

theorem StrictListPayload.long_view {bytes : List (BitVec 8)}
    {base endPtr : Word} {listLen cursorOff : Nat}
    (h : StrictListPayload bytes base listLen cursorOff endPtr)
    (hoff : 0 < bytes.length)
    (hlong : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true) :
    ∃ first : BitVec 8,
      bytes[1]? = some first ∧ first ≠ 0 ∧
      56 ≤ Nat.fromBytesBE ((bytes.drop 1).take
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ∧
      cursorOff = 1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ∧
      cursorOff + Nat.fromBytesBE ((bytes.drop 1).take
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) = listLen := by
  cases h with
  | short b hbyte _ hshort _ _ =>
      rw [List.getElem?_eq_getElem hoff] at hbyte
      have hb : bytes[0]'hoff = b := Option.some.inj hbyte
      subst b
      exact False.elim (hlong hshort)
  | long b first hbyte _ hfirst hnz hminimal hcursor hlen =>
      rw [List.getElem?_eq_getElem hoff] at hbyte
      have hb : bytes[0]'hoff = b := Option.some.inj hbyte
      subst b
      exact ⟨first, hfirst, hnz, hminimal, hcursor, hlen⟩

end EvmAsm.Codegen.RlpListNthItemSAsm
