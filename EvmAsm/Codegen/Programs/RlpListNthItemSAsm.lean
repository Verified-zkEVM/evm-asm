/-
  EvmAsm.Codegen.Programs.RlpListNthItemSAsm

  Genuine semantics and proof layer for the strict K20 `rlp_list_nth_item`
  replacement.  The emitted routine embeds the already-verified strict
  `rlp_walk_init` and `rlp_walk_next` programs behind a framed index loop.
-/

import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsWalk
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.Tactics.DropPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

/-! ## Pure strict semantics -/

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

theorem noStrictList_of_empty (bytes : List (BitVec 8)) (base : Word) :
    ¬ ∃ cursorOff endPtr, StrictListPayload bytes base 0 cursorOff endPtr := by
  rintro ⟨cursorOff, endPtr, h⟩
  exact (Nat.not_lt_zero _ h.listLen_pos)

theorem noStrictList_of_notlist (bytes : List (BitVec 8)) (base : Word)
    (listLen : Nat) (hoff : 0 < bytes.length)
    (hnotlist : BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    ¬ ∃ cursorOff endPtr,
      StrictListPayload bytes base listLen cursorOff endPtr := by
  rintro ⟨cursorOff, endPtr, h⟩
  exact h.prefix_not_lt_c0 hoff hnotlist

theorem noStrictList_of_short_mismatch (bytes : List (BitVec 8)) (base : Word)
    (listLen : Nat) (hoff : 0 < bytes.length)
    (h_len : listLen < 2 ^ 64)
    (hshort : BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hmismatch : base +
      (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)) ≠ base + BitVec.ofNat 64 listLen) :
    ¬ ∃ cursorOff endPtr,
      StrictListPayload bytes base listLen cursorOff endPtr := by
  rintro ⟨cursorOff, endPtr, h⟩
  cases h with
  | short b hbyte _ _ _ hnat =>
      rw [List.getElem?_eq_getElem hoff] at hbyte
      have hb : bytes[0]'hoff = b := Option.some.inj hbyte
      subst b
      apply hmismatch
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
      congr 1
      have hsmall :
          ((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)).toNat + 1 < 2 ^ 64 := by
        have hb := (bytes[0]'hoff).isLt
        bv_omega
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, show BitVec.toNat (1 : Word) = 1 by decide,
        BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt h_len]
      exact hnat
  | long b first hbyte hlong _ _ _ _ _ =>
      rw [List.getElem?_eq_getElem hoff] at hbyte
      have hb : bytes[0]'hoff = b := Option.some.inj hbyte
      subst b
      exact hlong hshort

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

theorem noStrictList_of_long_leading_zero (bytes : List (BitVec 8))
    (base : Word) (listLen : Nat) (hoff : 0 < bytes.length)
    (hlong : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hzero : bytes[1]? = some (0 : BitVec 8)) :
    ¬ ∃ cursorOff endPtr,
      StrictListPayload bytes base listLen cursorOff endPtr := by
  rintro ⟨cursorOff, endPtr, h⟩
  obtain ⟨first, hfirst, hnz, _⟩ := h.long_view hoff hlong
  have : first = 0 := Option.some.inj (hfirst.symm.trans hzero)
  exact hnz this

theorem noStrictList_of_long_nonminimal (bytes : List (BitVec 8))
    (base : Word) (listLen : Nat) (hoff : 0 < bytes.length)
    (hlong : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hnonminimal : BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
      ((bytes.drop 1).take
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
      (56 : Word) = true) :
    ¬ ∃ cursorOff endPtr,
      StrictListPayload bytes base listLen cursorOff endPtr := by
  rintro ⟨cursorOff, endPtr, h⟩
  obtain ⟨first, hfirst, hnz, hminimal, _⟩ := h.long_view hoff hlong
  have hlt := BitVec.ult_iff_lt.mp hnonminimal
  have hdec : Nat.fromBytesBE ((bytes.drop 1).take
      ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) < 2 ^ 64 := by
    have hn : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
      have hb := (bytes[0]'hoff).isLt
      have hge := BalAccountNonstorageFinalsSpec.not_ult_le hlong
      bv_omega
    have hp := Nat.fromBytesBE_lt ((bytes.drop 1).take
      ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)
    have htake : ((bytes.drop 1).take
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat).length ≤ 8 := by
      exact le_trans (List.length_take_le _ _) hn
    calc
      _ < 256 ^ ((bytes.drop 1).take
          ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat).length := hp
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by omega) htake
      _ = 2 ^ 64 := by norm_num
  change (BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop 1).take
    ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))).toNat < 56 at hlt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdec] at hlt
  omega

theorem noStrictList_of_long_header_truncated (bytes : List (BitVec 8))
    (base : Word) (listLen : Nat) (hoff : 0 < bytes.length)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hlong : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (htrunc : BitVec.ult (base + BitVec.ofNat 64 listLen)
      (base + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true) :
    ¬ ∃ cursorOff endPtr,
      StrictListPayload bytes base listLen cursorOff endPtr := by
  rintro ⟨cursorOff, endPtr, h⟩
  obtain ⟨first, hfirst, hnz, hminimal, hcursor, hlen⟩ :=
    h.long_view hoff hlong
  have hn : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
    have hb := (bytes[0]'hoff).isLt
    have hge := BalAccountNonstorageFinalsSpec.not_ult_le hlong
    bv_omega
  have hhead :
      ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 cursorOff := by
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
    subst cursorOff
    bv_omega
  rw [hhead] at htrunc
  have hcursorLe : cursorOff ≤ listLen := by omega
  have hbaseEnd : base.toNat + listLen < 2 ^ 64 := by omega
  have hbaseCursor : base.toNat + cursorOff < 2 ^ 64 := by omega
  have hlt := BitVec.ult_iff_lt.mp htrunc
  change (base + BitVec.ofNat 64 listLen).toNat <
    (base + BitVec.ofNat 64 cursorOff).toNat at hlt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hlt
  have hlmod : listLen % 2 ^ 64 = listLen := Nat.mod_eq_of_lt (by omega)
  have hcmod : cursorOff % 2 ^ 64 = cursorOff := Nat.mod_eq_of_lt (by omega)
  rw [hlmod, hcmod, Nat.mod_eq_of_lt hbaseCursor] at hlt
  omega

theorem noStrictList_of_long_mismatch (bytes : List (BitVec 8))
    (base : Word) (listLen : Nat) (hoff : 0 < bytes.length)
    (hlong : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hmismatch : base +
        (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop 1).take
          ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) ≠
      base + BitVec.ofNat 64 listLen) :
    ¬ ∃ cursorOff endPtr,
      StrictListPayload bytes base listLen cursorOff endPtr := by
  rintro ⟨cursorOff, endPtr, h⟩
  obtain ⟨first, hfirst, hnz, hminimal, hcursor, hlen⟩ :=
    h.long_view hoff hlong
  apply hmismatch
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
  have hhead :
      ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + (1 : Word) =
        BitVec.ofNat 64 cursorOff := by
    rw [hcursor]
    bv_omega
  rw [hhead, BitVec.add_assoc, ← BitVec.ofNat_add, hlen]

/-- Convert WalkInit's short-list success facts at offset zero into the
    wrapper's strict outer-list relation. -/
theorem shortInit_to_strict (bytes : List (BitVec 8)) (base : Word)
    (listLen : Nat) (hoff : 0 < bytes.length)
    (h_len : listLen < 2 ^ 64)
    (hnotlist : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (hshort : BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hend : base +
      (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)) = base + BitVec.ofNat 64 listLen) :
    StrictListPayload bytes base listLen 1 (base + BitVec.ofNat 64 listLen) := by
  have hword :
      ((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 listLen := by
    bv_omega
  have hnat :
      (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)).toNat + 1) = listLen := by
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide] at hword
    have hge := BalAccountNonstorageFinalsSpec.not_ult_le hnotlist
    have hsmall :
        ((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)).toNat + 1 < 2 ^ 64 := by
      have hb := (bytes[0]'hoff).isLt
      bv_omega
    have hof : BitVec.ofNat 64
        (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)).toNat + 1) =
        BitVec.ofNat 64 listLen := by
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat]
      exact hword
    have hw := congrArg BitVec.toNat hof
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall,
      Nat.mod_eq_of_lt h_len] using hw
  exact .short listLen 1 (bytes[0]'hoff) (by simp) hnotlist hshort rfl hnat

/-- Convert WalkInit's canonical long-list success facts at offset zero into
    the wrapper's strict outer-list relation. -/
theorem longInit_to_strict (bytes : List (BitVec 8)) (base : Word)
    (listLen : Nat) (hoff : 0 < bytes.length)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64)
    (hlong : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hfit : ¬ BitVec.ult (base + BitVec.ofNat 64 listLen)
      (base + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12))) = true)
    (hfirst : bytes[1]? = some (bytes[1]'(by omega)))
    (hnz : bytes[1]'(by omega) ≠ 0)
    (hminimal : 56 ≤ Nat.fromBytesBE
      ((bytes.drop 1).take
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
    (hend : base +
        (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop 1).take
          ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) =
      base + BitVec.ofNat 64 listLen) :
    StrictListPayload bytes base listLen
      (1 + ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)
      (base + BitVec.ofNat 64 listLen) := by
  let n := ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
  let dec := Nat.fromBytesBE ((bytes.drop 1).take n)
  have hn : n ≤ 8 := by
    have hb := (bytes[0]'hoff).isLt
    have hge := BalAccountNonstorageFinalsSpec.not_ult_le hlong
    dsimp [n]
    bv_omega
  have hdec : dec < 2 ^ 64 := by
    have hp := Nat.fromBytesBE_lt ((bytes.drop 1).take n)
    have htake : ((bytes.drop 1).take n).length ≤ 8 := by simp [hn]
    dsimp [dec]
    calc
      Nat.fromBytesBE ((bytes.drop 1).take n) <
          256 ^ ((bytes.drop 1).take n).length := hp
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by omega) htake
      _ = 2 ^ 64 := by norm_num
  have hnat : 1 + n + dec = listLen := by
    have hbaseEnd : base.toNat + listLen < 2 ^ 64 := by omega
    have hbaseCursor : base.toNat + (1 + n) < 2 ^ 64 := by omega
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide] at hend hfit
    have hhead :
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) + (1 : Word) =
          BitVec.ofNat 64 (1 + n) := by
      dsimp [n] at hn ⊢
      bv_omega
    rw [hhead] at hend hfit
    change base + BitVec.ofNat 64 (1 + n) + BitVec.ofNat 64 dec =
      base + BitVec.ofNat 64 listLen at hend
    have hcursorEnd := BalAccountNonstorageFinalsSpec.not_ult_le hfit
    have heq := congrArg BitVec.toNat hend
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hdec] at heq
    have hcursorNat :
        (base.toNat + (1 + n) % 2 ^ 64) % 2 ^ 64 =
          base.toNat + (1 + n) := by
      have hm : (1 + n) % 2 ^ 64 = 1 + n := Nat.mod_eq_of_lt (by omega)
      omega
    have hendNat :
        (base.toNat + listLen % 2 ^ 64) % 2 ^ 64 =
          base.toNat + listLen := by
      have hm : listLen % 2 ^ 64 = listLen := Nat.mod_eq_of_lt (by omega)
      omega
    rw [hcursorNat, hendNat] at heq
    have hcursorLe : base.toNat + (1 + n) ≤ base.toNat + listLen := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hcursorEnd
      have hnmod : (1 + n) % 2 ^ 64 = 1 + n := Nat.mod_eq_of_lt (by omega)
      have hlmod : listLen % 2 ^ 64 = listLen := Nat.mod_eq_of_lt (by omega)
      rw [hnmod, hlmod, Nat.mod_eq_of_lt hbaseCursor,
        Nat.mod_eq_of_lt hbaseEnd] at hcursorEnd
      exact hcursorEnd
    by_cases hsum : base.toNat + (1 + n) + dec < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hsum] at heq
      omega
    · have hsum2 : base.toNat + (1 + n) + dec < 2 * 2 ^ 64 := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at heq
      omega
  exact .long listLen _ (bytes[0]'hoff) (bytes[1]'(by omega)) (by simp)
    hlong hfirst hnz hminimal rfl hnat

/-- Exactly `index + 1` successful strict `rlp_walk_next` decodes, starting
    at `off`.  The final `(next,len)` is the selected item's advanced cursor
    and reported content length.  Every step uses `rlpItemDecode`, so bounds
    and all structural canonicality rules are part of the relation. -/
inductive StrictNthItem (bytes : List (BitVec 8)) (base endPtr : Word) :
    Nat → Nat → Word → Word → Prop
  | zero (off : Nat) (next len : Word)
      (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
        endPtr next len) :
      StrictNthItem bytes base endPtr 0 off next len
  | succ (index off : Nat) (next len finalNext finalLen : Word)
      (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
        endPtr next len)
      (hrest : StrictNthItem bytes base endPtr index
        (next - base).toNat finalNext finalLen) :
      StrictNthItem bytes base endPtr (index + 1) off finalNext finalLen

/-- The loop's walked-so-far chain.  A prefix of length zero leaves the
    cursor at `startOff`; a successor records one canonical decode and the
    exact cursor handed to the next iteration. -/
inductive StrictPrefix (bytes : List (BitVec 8)) (base endPtr : Word)
    (startOff : Nat) : Nat → Nat → Prop
  | zero : StrictPrefix bytes base endPtr startOff 0 startOff
  | succ (count off : Nat) (next len : Word)
      (hprefix : StrictPrefix bytes base endPtr startOff count off)
      (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
        endPtr next len) :
      StrictPrefix bytes base endPtr startOff (count + 1) (next - base).toNat

/-- Append one decode after an already-selected chain. -/
theorem StrictNthItem.snoc {bytes : List (BitVec 8)} {base endPtr : Word}
    {index startOff : Nat} {lastNext lastLen next len : Word}
    (h : StrictNthItem bytes base endPtr index startOff lastNext lastLen)
    (hitem : rlpItemDecode bytes (lastNext - base).toNat
      (base + BitVec.ofNat 64 (lastNext - base).toNat) endPtr next len) :
    StrictNthItem bytes base endPtr (index + 1) startOff next len := by
  induction h with
  | zero off n l hi => exact .succ 0 off n l next len hi (.zero _ _ _ hitem)
  | succ i off n l fn fl hi hr ih =>
      exact .succ (i + 1) off n l next len hi (ih hitem)

/-- Appending the currently decoded item to a `count`-item prefix identifies
    that item as the zero-based `count`th child. -/
theorem StrictPrefix.select {bytes : List (BitVec 8)} {base endPtr : Word}
    {startOff count off : Nat} {next len : Word}
    (hprefix : StrictPrefix bytes base endPtr startOff count off)
    (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      endPtr next len) :
    StrictNthItem bytes base endPtr count startOff next len := by
  induction hprefix generalizing next len with
  | zero => exact .zero _ _ _ hitem
  | succ count off next0 len0 hprefix hitem0 ih =>
      exact StrictNthItem.snoc (ih hitem0) hitem

/-- A successful non-selected iteration extends the walked prefix by one. -/
theorem StrictPrefix.step {bytes : List (BitVec 8)} {base endPtr : Word}
    {startOff count off : Nat} {next len : Word}
    (hprefix : StrictPrefix bytes base endPtr startOff count off)
    (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      endPtr next len) :
    StrictPrefix bytes base endPtr startOff (count + 1) (next - base).toNat :=
  .succ count off next len hprefix hitem

/-- The exact next offset used to re-enter the loop is strictly advanced and
    remains within the declared list window. -/
theorem StrictPrefix.step_bounds {bytes : List (BitVec 8)} {base : Word}
    {endOff startOff count off : Nat} {next len : Word}
    (hprefix : StrictPrefix bytes base (base + BitVec.ofNat 64 endOff)
      startOff count off)
    (hitem : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 endOff) next len)
    (hoff : off ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    next = base + BitVec.ofNat 64 (next - base).toNat ∧
      off < (next - base).toNat ∧ (next - base).toNat ≤ endOff ∧
      StrictPrefix bytes base (base + BitVec.ofNat 64 endOff)
        startOff (count + 1) (next - base).toNat := by
  have ha := BalAccountNonstorageFinalsSpec.rlpItemDecode_advance hitem hoff hover
  exact ⟨ha.1, ha.2.1, ha.2.2, StrictPrefix.step hprefix hitem⟩

/-- Successful K20 meaning: the complete input is one strict list and its
    zero-based `index` child exists.  The ABI outputs are the selected content
    offset and length (`next - len - base`, `len`). -/
def Success (bytes : List (BitVec 8)) (base : Word) (listLen index : Nat)
    (offset len : Word) : Prop :=
  ∃ cursorOff endPtr next,
    StrictListPayload bytes base listLen cursorOff endPtr ∧
    StrictNthItem bytes base endPtr index cursorOff next len ∧
    offset = next - len - base

/-- The complete failure information exposed by the unified WalkNext theorem:
    status 2 proves the cursor is at/past the exclusive end; statuses 3--6
    prove that no strict item decodes at the cursor. -/
def WalkFailure (bytes : List (BitVec 8)) (off : Nat)
    (cursor endPtr : Word) : Prop :=
  (¬ BitVec.ult cursor endPtr = true) ∨
  (¬ ∃ next len, rlpItemDecode bytes off cursor endPtr next len)

/-- A concrete strict traversal failure.  Either the outer list itself has no
    strict payload, or a canonical prefix of `count ≤ index` children reaches
    a cursor at which no strict next item exists.  The latter uniformly covers
    end/OOB, bounds, and structural non-canonicality. -/
inductive Failure (bytes : List (BitVec 8)) (base : Word)
    (listLen index : Nat) : Prop
  | init (h : ¬ ∃ cursorOff endPtr,
      StrictListPayload bytes base listLen cursorOff endPtr) :
      Failure bytes base listLen index
  | walk (cursorOff count off : Nat) (endPtr : Word)
      (hlist : StrictListPayload bytes base listLen cursorOff endPtr)
      (hcount : count ≤ index)
      (hprefix : StrictPrefix bytes base endPtr cursorOff count off)
      (hfail : WalkFailure bytes off (base + BitVec.ofNat 64 off) endPtr) :
      Failure bytes base listLen index

/-- Unified semantic result, including the ABI's precise failure behavior:
    output cells are unchanged on failure. -/
inductive Result (bytes : List (BitVec 8)) (base : Word)
    (listLen index : Nat) (oldOffset oldLen : Word) : Word → Word → Word → Prop
  | ok (offset len : Word) (h : Success bytes base listLen index offset len) :
      Result bytes base listLen index oldOffset oldLen 0 offset len
  | fail (h : Failure bytes base listLen index) :
      Result bytes base listLen index oldOffset oldLen 1 oldOffset oldLen

/-! ## Emitted-byte ties -/

theorem wrapper_length : rlpListNthItemWrapper_prog.length = 38 := by decide
theorem total_length : rlpListNthItem_prog.length = 194 := by
  simp only [rlpListNthItem_prog, List.length_append, wrapper_length,
    rlp_walk_init_prog_length, rlp_walk_next_prog_length]

theorem embedded_walk_init :
    (rlpListNthItem_prog.drop rlpListNthItemWrapper_prog.length).take
      rlp_walk_init_prog.length = rlp_walk_init_prog := by decide

theorem embedded_walk_next :
    rlpListNthItem_prog.drop
      (rlpListNthItemWrapper_prog.length + rlp_walk_init_prog.length) =
      rlp_walk_next_prog := by decide

theorem reemit_byte_tie :
    rlpListNthItem_prog =
      (show List Instr from rlpListNthItemWrapper_prog) ++
        (show List Instr from rlp_walk_init_prog) ++ rlp_walk_next_prog := by rfl

#print axioms reemit_byte_tie

/-! ## Concrete embedded code and call-site adapters -/

abbrev B : Word := (GuestAddrs.rlp_list_nth_item : Word)
abbrev WI : Word := B + 152
abbrev WN : Word := B + 364

def code : CodeReq := CodeReq.ofProg B rlpListNthItem_prog

theorem walkInit_sub : ∀ a i, rlp_walk_init_code WI a = some i → code a = some i := by
  intro a i h
  exact CodeReq.ofProg_mono_sub B WI rlpListNthItem_prog rlp_walk_init_prog
    38 (by simp [WI]) (by simpa [wrapper_length] using embedded_walk_init)
    (by rw [total_length, rlp_walk_init_prog_length]; omega)
    (by rw [total_length]; norm_num) a i h

theorem walkNext_sub : ∀ a i, rlp_walk_next_code WN a = some i → code a = some i := by
  intro a i h
  exact CodeReq.ofProg_mono_sub B WN rlpListNthItem_prog rlp_walk_next_prog
    91 (by simp [WN]) (by simpa [wrapper_length, rlp_walk_init_prog_length]
      using embedded_walk_next)
    (by rw [total_length, rlp_walk_next_prog_length])
    (by rw [total_length]; norm_num) a i h

/-- Lift the local call at wrapper slot 12 into the complete embedded K20 code. -/
theorem callWalkInit {n : Nat} {Prest Q : Assertion} (oldRa : Word)
    (hpre : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 52) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 52)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 48) (B + 52) code
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 48) (calleeEntry := WI) (vOld := oldRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (104 : BitVec 21) (by decide) (by decide) hpre
    (CodeReq.Disjoint.singleton_ofProg (by decide)) hcallee
  exact cpsTripleWithin_extend_code (CodeReq.union_split_mono
    (fun a i hc => CodeReq.ofProg_mono_sub B (B + 48) rlpListNthItem_prog
        [.JAL .x1 (104 : BitVec 21)] 12 (by bv_omega) (by rfl)
        (by rw [total_length]; norm_num) (by rw [total_length]; norm_num) a i hc)
    walkInit_sub) hcall

/-- Lift the local call at wrapper slot 17 into the complete embedded K20 code. -/
theorem callWalkNext {n : Nat} {Prest Q : Assertion} (oldRa : Word)
    (hpre : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 72) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 72)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 68) (B + 72) code
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 68) (calleeEntry := WN) (vOld := oldRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (296 : BitVec 21) (by decide) (by decide) hpre
    (CodeReq.Disjoint.singleton_ofProg (by decide)) hcallee
  exact cpsTripleWithin_extend_code (CodeReq.union_split_mono
    (fun a i hc => CodeReq.ofProg_mono_sub B (B + 68) rlpListNthItem_prog
        [.JAL .x1 (296 : BitVec 21)] 17 (by bv_omega) (by rfl)
        (by rw [total_length]; norm_num) (by rw [total_length]; norm_num) a i hc)
    walkNext_sub) hcall

#print axioms callWalkInit
#print axioms callWalkNext

/-! ## Indexed wrapper-loop assertions -/

/-- Values preserved by K20's 64-byte ABI frame. -/
structure Saved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word

def listNthFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32),
   (.x20, 40), (.x21, 48)]

def savedVals (saved : Saved) : Reg → Word
  | .x1 => saved.ra
  | .x8 => saved.s0
  | .x9 => saved.s1
  | .x18 => saved.s2
  | .x19 => saved.s3
  | .x20 => saved.s4
  | .x21 => saved.s5
  | _ => 0

theorem listNthFrame_length : listNthFrame.length = 7 := by decide

theorem regsAt_listNthFrame (saved : Saved) :
    regsAt listNthFrame (savedVals saved) =
      ((.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
       (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
       (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)) := by
  simp [listNthFrame, regsAt, savedVals]
  rw [sepConj_emp_right']

/-- Exact seven saved-register cells in the frame. -/
def savedFrame (newSp : Word) (saved : Saved) : Assertion :=
  (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) **
  ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2) **
  ((newSp + 32) ↦ₘ saved.s3) ** ((newSp + 40) ↦ₘ saved.s4) **
  ((newSp + 48) ↦ₘ saved.s5)

theorem frameSlotsSaved_listNthFrame (newSp : Word) (saved : Saved) :
    frameSlotsSaved listNthFrame newSp (savedVals saved) = savedFrame newSp saved := by
  simp [listNthFrame, frameSlotsSaved, savedFrame, savedVals,
    sepConj_emp_right', signExtend12]

/-- Wrapper slots 8--11 copy the four stable ABI arguments into saved
    registers after the frame has been stored. -/
theorem setupMoves (listBase indexW offsetPtr lenPtr : Word)
    (v8 v9 v18 v19 : Word) :
    cpsTripleWithin 4 (B + 32) (B + 48) code
      ((.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ listBase) **
       (.x9 ↦ᵣ v9) ** (.x12 ↦ᵣ indexW) **
       (.x18 ↦ᵣ v18) ** (.x13 ↦ᵣ offsetPtr) **
       (.x19 ↦ᵣ v19) ** (.x14 ↦ᵣ lenPtr))
      ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) **
       (.x9 ↦ᵣ indexW) ** (.x12 ↦ᵣ indexW) **
       (.x18 ↦ᵣ offsetPtr) ** (.x13 ↦ᵣ offsetPtr) **
       (.x19 ↦ᵣ lenPtr) ** (.x14 ↦ᵣ lenPtr)) := by
  have h0 := mv_spec_gen_within .x8 .x10 listBase v8 (B + 32) (by decide)
  have h1 := mv_spec_gen_within .x9 .x12 indexW v9 (B + 36) (by decide)
  have h2 := mv_spec_gen_within .x18 .x13 offsetPtr v18 (B + 40) (by decide)
  have h3 := mv_spec_gen_within .x19 .x14 lenPtr v19 (B + 44) (by decide)
  have l0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 32) rlpListNthItem_prog 8 (.MV .x8 .x10)
      (by bv_omega) (by rw [total_length]; norm_num) (by rfl)
      (by rw [total_length]; norm_num)) h0
  have l1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 36) rlpListNthItem_prog 9 (.MV .x9 .x12)
      (by bv_omega) (by rw [total_length]; norm_num) (by rfl)
      (by rw [total_length]; norm_num)) h1
  have l2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 40) rlpListNthItem_prog 10 (.MV .x18 .x13)
      (by bv_omega) (by rw [total_length]; norm_num) (by rfl)
      (by rw [total_length]; norm_num)) h2
  have l3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 44) rlpListNthItem_prog 11 (.MV .x19 .x14)
      (by bv_omega) (by rw [total_length]; norm_num) (by rfl)
      (by rw [total_length]; norm_num)) h3
  have s0 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v9) ** (.x12 ↦ᵣ indexW) **
     (.x18 ↦ᵣ v18) ** (.x13 ↦ᵣ offsetPtr) **
     (.x19 ↦ᵣ v19) ** (.x14 ↦ᵣ lenPtr)) (by pcf) l0
  have s1 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) **
     (.x18 ↦ᵣ v18) ** (.x13 ↦ᵣ offsetPtr) **
     (.x19 ↦ᵣ v19) ** (.x14 ↦ᵣ lenPtr)) (by pcf) l1
  have s2 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) **
     (.x9 ↦ᵣ indexW) ** (.x12 ↦ᵣ indexW) **
     (.x19 ↦ᵣ v19) ** (.x14 ↦ᵣ lenPtr)) (by pcf) l2
  have s3 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) **
     (.x9 ↦ᵣ indexW) ** (.x12 ↦ᵣ indexW) **
     (.x18 ↦ᵣ offsetPtr) ** (.x13 ↦ᵣ offsetPtr)) (by pcf) l3
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s0 s1
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 s2
  have h0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 s3
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) h0123

def entryRest (listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
   (.x13 ↦ᵣ offsetPtr) ** (.x14 ↦ᵣ lenPtr) **
   regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
   regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
   bytesRegion listBase bytes ** (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))

def setupPost (newSp listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) : Assertion :=
  ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ saved.ra) **
   (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) **
   (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
   (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
   savedFrame newSp saved ** entryRest listBase listLenW indexW offsetPtr lenPtr
     oldOffset oldLen bytes)

theorem wrapperPrologue (sp0 newSp listBase listLenW indexW offsetPtr lenPtr
    oldOffset oldLen : Word) (saved : Saved) (bytes : List (BitVec 8))
    (hnewSp : newSp = sp0 + signExtend12 (-64 : BitVec 12)) :
    cpsTripleWithin 12 B (B + 48) code
      ((.x2 ↦ᵣ sp0) ** regsAt listNthFrame (savedVals saved) **
       frameSlotsOwn listNthFrame newSp **
       entryRest listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen bytes)
      (setupPost newSp listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-64 : BitVec 12) B (by decide)
  rw [← hnewSp] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B B rlpListNthItem_prog 0
      (.ADDI .x2 .x2 (-64 : BitVec 12)) rfl
      (by rw [total_length]; norm_num) (by rfl)
      (by rw [total_length]; norm_num)) ha0
  rw [show B + 4 = B + 4 from rfl] at ha
  have haF := cpsTripleWithin_frameR
    (regsAt listNthFrame (savedVals saved) ** frameSlotsOwn listNthFrame newSp **
      entryRest listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen bytes)
    (by pcf) ha
  have hs0 := storeSeq_spec listNthFrame newSp (savedVals saved) (B + 4) (by decide)
  have hstoreMono : ∀ a i,
      CodeReq.ofProg (B + 4) (storeProg listNthFrame) a = some i → code a = some i := by
    intro a i hmem
    exact CodeReq.ofProg_mono_sub B (B + 4) rlpListNthItem_prog
      (storeProg listNthFrame) 1 (by bv_omega) (by rfl)
      (by rw [total_length]; simp [listNthFrame])
      (by rw [total_length]; norm_num) a i hmem
  have hs := cpsTripleWithin_extend_code hstoreMono hs0
  rw [show B + 4 + BitVec.ofNat 64 (4 * listNthFrame.length) = B + 32 from by
    simp [listNthFrame]; bv_omega] at hs
  have hsF := cpsTripleWithin_frameR
    (entryRest listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen bytes)
    (by pcf) hs
  have hm0 := setupMoves listBase indexW offsetPtr lenPtr
    saved.s0 saved.s1 saved.s2 saved.s3
  have hmF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ saved.ra) **
     (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
     savedFrame newSp saved **
     ((.x11 ↦ᵣ listLenW) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
      (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))) (by pcf) hm0
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hsF
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_listNthFrame, frameSlotsSaved_listNthFrame] at hp
    unfold entryRest at hp
    xperm_hyp hp) h01 hmF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by unfold setupPost entryRest; xperm_hyp hp) h012

#print axioms setupMoves
#print axioms wrapperPrologue

def initStable (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) : Assertion :=
  ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) **
   (.x13 ↦ᵣ offsetPtr) ** (.x14 ↦ᵣ lenPtr) **
   (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
   savedFrame newSp saved ** (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))

def initCommon (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (B + 52)) ** bytesRegion listBase bytes

def initOutcome (listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (hoff : 0 < bytes.length) : Assertion := fun h =>
  (((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (2 : Word)) **
    ⌜BitVec.ofNat 64 listLen = (0 : Word)⌝) h) ∨
  (((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (1 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + signExtend12 (1 : BitVec 12))) **
    (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      listBase + (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)) = listBase + BitVec.ofNat 64 listLen⌝) h) ∨
  (((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (3 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      listBase + (((bytes[0]'hoff).zeroExtend 64 - (0xc0 : Word)) +
        signExtend12 (1 : BitVec 12)) ≠ listBase + BitVec.ofNat 64 listLen⌝) h) ∨
  (((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (4 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      BitVec.ult (listBase + BitVec.ofNat 64 listLen)
        (listBase + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true⌝) h) ∨
  (((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (5 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      ¬ BitVec.ult (listBase + BitVec.ofNat 64 listLen)
        (listBase + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true ∧ bytes[1]? = some 0⌝) h) ∨
  (((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (6 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      ¬ BitVec.ult (listBase + BitVec.ofNat 64 listLen)
        (listBase + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true ∧
      BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop 1).take
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true⌝) h) ∨
  (((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLen)) **
    (.x12 ↦ᵣ (7 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      ¬ BitVec.ult (listBase + BitVec.ofNat 64 listLen)
        (listBase + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true ∧
      ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop 1).take
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
      listBase + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop 1).take
          ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) ≠
        listBase + BitVec.ofNat 64 listLen⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
      signExtend12 (1 : BitVec 12)))) **
    (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
    ⌜BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
      ¬ BitVec.ult (listBase + BitVec.ofNat 64 listLen)
        (listBase + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true ∧
      ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop 1).take
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
      listBase + (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
        signExtend12 (1 : BitVec 12)) +
        BitVec.ofNat 64 (Nat.fromBytesBE ((bytes.drop 1).take
          ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)) =
        listBase + BitVec.ofNat 64 listLen⌝) h)

theorem initCallExact (listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (indexW : Word)
    (v5 v6 v7 v28 v29 v30 v31 oldRa : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 82 (B + 48) (B + 52) code
      ((.x1 ↦ᵣ oldRa) **
       ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) **
        (.x12 ↦ᵣ indexW) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase bytes))
      (((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
        initOutcome listBase bytes listLen (by omega))) := by
  have hoff : 0 < bytes.length := by omega
  have hwi := rlp_walk_init_spec_within WI listBase (B + 52)
    (BitVec.ofNat 64 listLen) indexW v5 v6 v7 v28 v29 v30 v31 bytes 0
    hsalign hoff (by omega) (hvalid 0 hoff)
    (fun hf8 => by
      have hlo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := BalAccountNonstorageFinalsSpec.not_ult_le hf8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun hf8 => by
      have hlo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := BalAccountNonstorageFinalsSpec.not_ult_le hf8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun hf8 => by
      intro k hk
      have hlo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := BalAccountNonstorageFinalsSpec.not_ult_le hf8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      exact hvalid _ (by omega))
  rw [show listBase + BitVec.ofNat 64 0 = listBase from by bv_omega] at hwi
  let Prest : Assertion :=
    ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) **
     (.x12 ↦ᵣ indexW) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
     (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes)
  let Q : Assertion :=
    ((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
      initOutcome listBase bytes listLen hoff)
  have hwi' : cpsTripleWithin 81 WI ((B + 52) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) (((.x1 ↦ᵣ (B + 52)) ** Prest)) Q :=
    cpsTripleWithin_weaken
      (fun h hp => by
        unfold Prest at hp
        xperm_hyp hp) (fun h hp => by
        unfold Q initCommon initOutcome
        simp only [Nat.zero_add] at hp ⊢
        xperm_hyp hp) hwi
  have hc := callWalkInit oldRa (by unfold Prest; pcf) hwi'
  simpa [Prest, Q] using hc

#print axioms initCallExact

def initRejected (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ status cursor endPtr : Word,
    (((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
       initCommon listBase bytes) **
       ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x20 ↦ᵣ saved.s4) **
        (.x21 ↦ᵣ saved.s5)) **
      ⌜status ≠ 0 ∧ Failure bytes listBase listLen index⌝)) h

theorem initRejectBranch (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
    status cursor endPtr : Word) (saved : Saved) (bytes : List (BitVec 8))
    (listLen index : Nat) (hstatus : status ≠ 0)
    (hfailure : Failure bytes listBase listLen index) :
    cpsTripleWithin 1 (B + 52) (B + 112) code
      (((.x12 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
       ((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
         initCommon listBase bytes) **
        ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
         (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5))))
      (initRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index) := by
  have hb0 := bne_spec_gen_within .x12 .x0 (60 : BitVec 13) status 0 (B + 52)
  rw [show B + 52 + signExtend13 (60 : BitVec 13) = B + 112 from by decide] at hb0
  have hb := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 52) rlpListNthItem_prog 13
      (.BNE .x12 .x0 (60 : BitVec 13)) (by bv_omega)
      (by rw [total_length]; norm_num) (by rfl)
      (by rw [total_length]; norm_num)) hb0
  have ht := cpsBranchWithin_takenPath hb (fun hp hfalse => by
    obtain ⟨_, _, _, _, _, hpure⟩ := hfalse
    exact hstatus ((sepConj_pure_right _).1 hpure).2)
  have htF := cpsTripleWithin_frameR
    (((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
       initCommon listBase bytes) **
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
       (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)))) (by pcf) ht
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hp => by
    unfold initRejected
    refine ⟨status, cursor, endPtr, ?_⟩
    have hp' : ((((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
        initCommon listBase bytes) **
        ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x20 ↦ᵣ saved.s4) **
          (.x21 ↦ᵣ saved.s5))) **
      ⌜status ≠ 0 ∧ Failure bytes listBase listLen index⌝) h) := by
      have hpAssoc : ((((initStable newSp listBase indexW offsetPtr lenPtr
          oldOffset oldLen saved ** initCommon listBase bytes) **
        ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x20 ↦ᵣ saved.s4) **
          (.x21 ↦ᵣ saved.s5))) **
        ⌜status ≠ 0 ∧ Failure bytes listBase listLen index⌝) h) := by
        refine (sepConj_pure_right h).2
          ⟨?_, And.intro hstatus hfailure⟩
        drop_pure hp
        unfold initCommon at hp ⊢
        xperm_hyp hp
      unfold initCommon at hpAssoc ⊢
      xperm_hyp hpAssoc
    unfold initCommon at hp' ⊢
    xperm_hyp hp') htF

#print axioms initRejectBranch

/-- Stable resources other than `s4`; `x20` is separated because slot 16 reads
    it while preparing the WalkNext call. -/
def stableRest (newSp listBase _indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) : Assertion :=
  ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) **
   (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
   savedFrame newSp saved **
   (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))

/-- Registers and framed resources stable across the K20 index loop. -/
def stableFrame (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) : Assertion :=
  (.x20 ↦ᵣ endPtr) **
  stableRest newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved

/-- Full resources stable at the loop header; the call-clobbered part is
    deliberately separate from `stableFrame` for call composition. -/
def loopFrame (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) : Assertion :=
  stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved **
  ((.x9 ↦ᵣ indexW) **
   regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
   regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
   regOwn .x1 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)

/-- Header invariant at wrapper slot 16 (`B+64`).  `count` is the number of
    already accepted children, so the remaining index measure is
    `index + 1 - count`; the invariant only re-enters while `count ≤ index`. -/
def loopInv (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index cursorOff : Nat)
    (j : Nat) : Assertion :=
  fun h => ∃ count off : Nat,
    ((loopFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       regOwn .x11 ** regOwn .x12 **
       (.x21 ↦ᵣ BitVec.ofNat 64 count))) **
     ⌜j = index + 1 - count ∧ count ≤ index ∧ off ≤ listLen ∧
       StrictPrefix bytes listBase endPtr cursorOff count off⌝) h

def initLoopPost (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ cursorOff endPtr,
    ((loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved
        bytes listLen index cursorOff (index + 1) **
      (regOwn .x13 ** regOwn .x14)) **
     ⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝) h

theorem initSuccessBranch (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
    endPtr : Word) (saved : Saved) (bytes : List (BitVec 8))
    (listLen index cursorOff : Nat)
    (hlist : StrictListPayload bytes listBase listLen cursorOff endPtr) :
    cpsTripleWithin 3 (B + 52) (B + 64) code
      (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
       ((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
         initCommon listBase bytes) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ endPtr) **
         (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5))))
      (initLoopPost newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index) := by
  have hb0 := bne_spec_gen_within .x12 .x0 (60 : BitVec 13) 0 0 (B + 52)
  have hb := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 52) rlpListNthItem_prog 13
      (.BNE .x12 .x0 (60 : BitVec 13)) (by bv_omega)
      (by rw [total_length]; norm_num) (by rfl)
      (by rw [total_length]; norm_num)) hb0
  have hn := cpsBranchWithin_ntakenPath hb (fun hp hfalse => by
    obtain ⟨_, _, _, _, _, hpure⟩ := hfalse
    exact ((sepConj_pure_right _).1 hpure).2 rfl)
  rw [show B + 52 + 4 = B + 56 from by decide] at hn
  have hnF := cpsTripleWithin_frameR
    (((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
       initCommon listBase bytes) **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ endPtr) **
       (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5))))
    (by pcf) hn
  have hm0 := mv_spec_gen_within .x20 .x11 endPtr saved.s4 (B + 56) (by decide)
  have hm := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 56) rlpListNthItem_prog 14 (.MV .x20 .x11)
      (by bv_omega) (by rw [total_length]; norm_num) (by rfl)
      (by rw [total_length]; norm_num)) hm0
  have hmF := cpsTripleWithin_frameR
    (((.x21 ↦ᵣ saved.s5) **
      ((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
        initCommon listBase bytes) **
       ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
        (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))))) (by pcf) hm
  have hl0 := li_spec_gen_within .x21 saved.s5 (0 : Word) (B + 60) (by decide)
  have hl := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 60) rlpListNthItem_prog 15 (.LI .x21 (0 : Word))
      (by bv_omega) (by rw [total_length]; norm_num) (by rfl)
      (by rw [total_length]; norm_num)) hl0
  have hlF := cpsTripleWithin_frameR
    (((.x20 ↦ᵣ endPtr) **
      ((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
        initCommon listBase bytes) **
       ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))))) (by pcf) hl
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    xperm_pure hp) hnF hmF
  let start : Assertion :=
    (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
      ((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
        initCommon listBase bytes) **
       ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ endPtr) **
        (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5))))
  let mid : Assertion :=
    (((.x11 ↦ᵣ endPtr) ** (.x20 ↦ᵣ endPtr)) **
      (.x21 ↦ᵣ saved.s5) **
      (initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
        initCommon listBase bytes) **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
       (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))))
  have h01' : cpsTripleWithin 2 (B + 52) (B + 60) code start mid := by
    simpa [start, mid] using h01
  have hmid : mid =
      ((.x21 ↦ᵣ saved.s5) ** (.x20 ↦ᵣ endPtr) **
       ((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
         initCommon listBase bytes) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
         (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
         (.x0 ↦ᵣ (0 : Word))))) := by
    unfold mid
    ac_rfl
  let finish : Assertion :=
    ((.x21 ↦ᵣ (0 : Word)) ** (.x20 ↦ᵣ endPtr) **
      ((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
        initCommon listBase bytes) **
       ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
        (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)))))
  have hlF' : cpsTripleWithin 1 (B + 60) (B + 64) code mid finish := by
    rw [hmid]
    simpa only [finish, show B + 60 + 4 = B + 64 by decide] using hlF
  have h012 := cpsTripleWithin_seq_same_cr h01' hlF'
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hp => by
    unfold finish at hp
    unfold initLoopPost
    refine ⟨cursorOff, endPtr, ?_⟩
    refine (sepConj_pure_right h).2 ⟨?_, hlist⟩
    have hpGrouped : (((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ offsetPtr) ** (.x14 ↦ᵣ lenPtr) ** (.x1 ↦ᵣ (B + 52))) **
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
       regOwn .x30 ** regOwn .x31 **
       ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) **
        (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
        savedFrame newSp saved ** (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen) **
        (.x20 ↦ᵣ endPtr) ** (.x21 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes))) h := by
      unfold initStable initCommon at hp
      xperm_hyp hp
    have hpOwned := sepConj_mono
      (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x13)
            (sepConj_mono (regIs_implies_regOwn .x14)
              (regIs_implies_regOwn .x1)))))
      (fun _ x => x) h hpGrouped
    have hbase :
        (((loopFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
            saved bytes **
          ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** regOwn .x11 **
           regOwn .x12 ** (.x21 ↦ᵣ (0 : Word)))) **
          (regOwn .x13 ** regOwn .x14)) h) := by
      unfold loopFrame stableFrame stableRest
      xperm_hyp hpOwned
    exact sepConj_mono_left (fun g hg => by
      unfold loopInv
      refine ⟨0, cursorOff, ?_⟩
      exact (sepConj_pure_right g).2 ⟨hg,
        ⟨by omega, by omega, hlist.cursor_le, StrictPrefix.zero⟩⟩) h hbase) h012

#print axioms initSuccessBranch

/-- Loop success station (`B+88`), before the two output stores. -/
def loopSelected (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (index cursorOff : Nat) : Assertion :=
  fun h => ∃ next len : Word,
    ((loopFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved bytes **
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
       (.x21 ↦ᵣ BitVec.ofNat 64 index))) **
     ⌜StrictNthItem bytes listBase endPtr index cursorOff next len⌝) h

/-- Loop reject station (`B+112`), before `li a0,1`. -/
def loopRejected (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index cursorOff : Nat) : Assertion :=
  fun h => ∃ count off : Nat, ∃ status : Word,
    ((loopFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
       (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ BitVec.ofNat 64 count))) **
     ⌜status ≠ 0 ∧ count ≤ index ∧
       StrictListPayload bytes listBase listLen cursorOff endPtr ∧
       StrictPrefix bytes listBase endPtr cursorOff count off ∧
       WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h

/-! ## One verified call block -/

def nextCommon (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  (.x1 ↦ᵣ (B + 72)) ** bytesRegion listBase bytes

def nextScratch (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (B + 72)) ** bytesRegion listBase bytes

def nextScratchOwned (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** regOwn .x1 ** bytesRegion listBase bytes

theorem nextScratch_implies_owned (listBase : Word) (bytes : List (BitVec 8)) :
    ∀ h, nextScratch listBase bytes h → nextScratchOwned listBase bytes h := by
  intro h hp
  unfold nextScratch at hp
  unfold nextScratchOwned
  exact sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x)
              (sepConj_mono (fun _ x => x)
                (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x)))))))) h hp

def nextOutcome (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) : Assertion := fun h =>
  rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off h ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (2 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 off) endPtr = true⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (3 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (4 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (5 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (6 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h)

/-- Slot 16's `mv a1,s4` followed by the local verified WalkNext call. -/
theorem nextCallBlock (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off listLen : Nat) (v5 v6 v7 v11 v12 v28 v29 v30 v31 oldRa : Word)
    (F : Assertion) (hF : F.pcFree)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hoff : off ≤ listLen) :
    cpsTripleWithin 89 (B + 64) (B + 72) code
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** (.x20 ↦ᵣ endPtr) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** F)
      ((nextCommon listBase bytes **
        (fun h =>
          rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off h ∨
          (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (2 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 off) endPtr = true⌝) h) ∨
          (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (3 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode bytes off
              (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
          (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (4 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode bytes off
              (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
          (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (5 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode bytes off
              (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
          (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (6 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode bytes off
              (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h))) **
       ((.x20 ↦ᵣ endPtr) ** F)) := by
  have hoffb : off < bytes.length := by omega
  have hmv0 := mv_spec_gen_within .x11 .x20 endPtr v11 (B + 64) (by decide)
  rw [show (B + 64) + 4 = B + 68 from by bv_omega] at hmv0
  have hmv := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub B (B + 64) rlpListNthItem_prog
      [.MV .x11 .x20] 16 (by bv_omega) (by rfl)
      (by rw [total_length]; norm_num) (by rw [total_length]; norm_num)) hmv0
  have hwn := rlp_walk_next_spec_within WN listBase endPtr (B + 72) v12
    v5 v6 v7 v28 v29 v30 v31 bytes off hsalign hoffb (by omega)
    (hvalid off hoffb)
    (fun _ _ => ⟨by omega, by omega, hvalid _ (by omega)⟩)
    (fun hb8 hc0 => by
      have hlo : ((bytes[off]'hoffb).zeroExtend 64 - (0xb7 : Word)).toNat ≤ 8 := by
        simp only [BitVec.ult, decide_eq_true_eq] at hb8 hc0
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
    (fun hf8 => by
      have hlo : ((bytes[off]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        simp only [BitVec.ult, decide_eq_true_eq] at hf8
        have h3 := (bytes[off]'hoffb).isLt
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
  have hwn' := cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwn
    (P' := (.x1 ↦ᵣ (B + 72)) **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes))
  have hcall := callWalkNext (n := 87) oldRa (by pcf) hwn'
  have hmvF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x12 ↦ᵣ v12) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
     (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** F) (by pcf; exact hF) hmv
  have hcallF := cpsTripleWithin_frameR ((.x20 ↦ᵣ endPtr) ** F)
    (by pcf; exact hF) hcall
  have hc := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hmvF hcallF
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => by unfold nextCommon; exact hq) hc

#print axioms nextCallBlock

/-! ## Wrapper dispatch instructions -/

private theorem liftBne72 (lhs rhs : Word) :
    cpsBranchWithin 1 (B + 72) code
      ((.x11 ↦ᵣ lhs) ** (.x0 ↦ᵣ rhs))
      (B + 112) ((.x11 ↦ᵣ lhs) ** (.x0 ↦ᵣ rhs) ** ⌜lhs ≠ rhs⌝)
      (B + 76) ((.x11 ↦ᵣ lhs) ** (.x0 ↦ᵣ rhs) ** ⌜lhs = rhs⌝) := by
  have h := bne_spec_gen_within .x11 .x0 (40 : BitVec 13) lhs rhs (B + 72)
  rw [show (B + 72) + signExtend13 (40 : BitVec 13) = B + 112 from by
        rw [show signExtend13 (40 : BitVec 13) = (40 : Word) from by decide]; bv_omega,
      show (B + 72) + 4 = B + 76 from by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (by
      unfold code
      exact CodeReq.ofProg_mem_at B (B + 72)
        rlpListNthItem_prog 18 (.BNE .x11 .x0 (40 : BitVec 13))
        (by bv_omega) (by rw [total_length]; norm_num)
        (by rfl) (by rw [total_length]; norm_num)) h

theorem statusReject (status : Word) (F : Assertion) (hF : F.pcFree)
    (hstatus : status ≠ 0) :
    cpsTripleWithin 1 (B + 72) (B + 112) code
      (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) ** F)
      (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) ** F) := by
  have ht := cpsBranchWithin_takenPath (liftBne72 status 0) (fun _ hfall => by
    obtain ⟨_, _, _, _, _, hpure⟩ := hfall
    exact hstatus (((sepConj_pure_right _).1 hpure).2))
  have ht' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h' hq => by
    refine sepConj_mono_right (fun h'' hp => ((sepConj_pure_right h'').1 hp).1) h' hq) ht
  exact cpsTripleWithin_frameR F hF ht'

theorem statusOk (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (B + 72) (B + 76) code
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** F)
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** F) := by
  have hf := cpsBranchWithin_ntakenPath (liftBne72 0 0) (fun _ htaken => by
    obtain ⟨_, _, _, _, _, hpure⟩ := htaken
    exact (((sepConj_pure_right _).1 hpure).2) rfl)
  have hf' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h' hq => by
    refine sepConj_mono_right (fun h'' hp => ((sepConj_pure_right h'').1 hp).1) h' hq) hf
  exact cpsTripleWithin_frameR F hF hf'

private theorem liftBeq76 (lhs rhs : Word) :
    cpsBranchWithin 1 (B + 76) code
      ((.x21 ↦ᵣ lhs) ** (.x9 ↦ᵣ rhs))
      (B + 88) ((.x21 ↦ᵣ lhs) ** (.x9 ↦ᵣ rhs) ** ⌜lhs = rhs⌝)
      (B + 80) ((.x21 ↦ᵣ lhs) ** (.x9 ↦ᵣ rhs) ** ⌜lhs ≠ rhs⌝) := by
  have h := beq_spec_gen_within .x21 .x9 (12 : BitVec 13) lhs rhs (B + 76)
  rw [show (B + 76) + signExtend13 (12 : BitVec 13) = B + 88 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (B + 76) + 4 = B + 80 from by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (by
      unfold code
      exact CodeReq.ofProg_mem_at B (B + 76)
        rlpListNthItem_prog 19 (.BEQ .x21 .x9 (12 : BitVec 13))
        (by bv_omega) (by rw [total_length]; norm_num)
        (by rfl) (by rw [total_length]; norm_num)) h

theorem indexSelected (value : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (B + 76) (B + 88) code
      (((.x21 ↦ᵣ value) ** (.x9 ↦ᵣ value)) ** F)
      (((.x21 ↦ᵣ value) ** (.x9 ↦ᵣ value)) ** F) := by
  have ht := cpsBranchWithin_takenPath (liftBeq76 value value) (fun _ hf => by
    obtain ⟨_, _, _, _, _, hpure⟩ := hf
    exact (((sepConj_pure_right _).1 hpure).2) rfl)
  have ht' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h' hq => by
    refine sepConj_mono_right (fun h'' hp => ((sepConj_pure_right h'').1 hp).1) h' hq) ht
  exact cpsTripleWithin_frameR F hF ht'

theorem indexContinue (countW indexW : Word) (F : Assertion) (hF : F.pcFree)
    (hne : countW ≠ indexW) :
    cpsTripleWithin 1 (B + 76) (B + 80) code
      (((.x21 ↦ᵣ countW) ** (.x9 ↦ᵣ indexW)) ** F)
      (((.x21 ↦ᵣ countW) ** (.x9 ↦ᵣ indexW)) ** F) := by
  have hf := cpsBranchWithin_ntakenPath (liftBeq76 countW indexW) (fun _ ht => by
    obtain ⟨_, _, _, _, _, hpure⟩ := ht
    exact hne (((sepConj_pure_right _).1 hpure).2))
  have hf' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h' hq => by
    refine sepConj_mono_right (fun h'' hp => ((sepConj_pure_right h'').1 hp).1) h' hq) hf
  exact cpsTripleWithin_frameR F hF hf'

theorem incrementBack (count : Nat) (F : Assertion) (hF : F.pcFree)
    :
    cpsTripleWithin 2 (B + 80) (B + 64) code
      ((.x21 ↦ᵣ BitVec.ofNat 64 count) ** F)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (count + 1)) ** F) := by
  have ha0 := addi_spec_gen_same_within .x21 (BitVec.ofNat 64 count)
    (1 : BitVec 12) (B + 80) (by decide)
  rw [show (B + 80) + 4 = B + 84 from by bv_omega] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub B (B + 80) rlpListNthItem_prog
      [.ADDI .x21 .x21 (1 : BitVec 12)] 20 (by bv_omega) (by rfl)
      (by rw [total_length]; norm_num) (by rw [total_length]; norm_num)) ha0
  have hj0 := jal_x0_spec_gen_within (-20 : BitVec 21) (B + 84)
  rw [show (B + 84) + signExtend21 (-20 : BitVec 21) = B + 64 from by
    rw [show signExtend21 (-20 : BitVec 21) = (-20 : Word) from by decide]; bv_omega] at hj0
  have hj := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub B (B + 84) rlpListNthItem_prog
      [.JAL .x0 (-20 : BitVec 21)] 21 (by bv_omega) (by rfl)
      (by rw [total_length]; norm_num) (by rw [total_length]; norm_num)) hj0
  have haF := cpsTripleWithin_frameR F hF ha
  have hnext : BitVec.ofNat 64 count + signExtend12 (1 : BitVec 12) =
      BitVec.ofNat 64 (count + 1) := by
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    bv_omega
  rw [hnext] at haF
  have hjF := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ BitVec.ofNat 64 (count + 1)) ** F) (by pcf; exact hF) hj
  rw [sepConj_emp_left'] at hjF
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) haF hjF

#print axioms statusReject
#print axioms statusOk
#print axioms indexSelected
#print axioms indexContinue
#print axioms incrementBack

/-! ## Semantic dispatch adapters -/

theorem dispatchFailure
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen index cursorOff count off : Nat) (status : Word)
    (hstatus : status ≠ 0)
    (hlist : StrictListPayload bytes listBase listLen cursorOff endPtr)
    (hcount : count ≤ index)
    (hprefix : StrictPrefix bytes listBase endPtr cursorOff count off)
    (hwalk : WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr) :
    cpsTripleWithin 1 (B + 72) (B + 112) code
      (nextScratch listBase bytes **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
         (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x21 ↦ᵣ BitVec.ofNat 64 count) **
         (.x9 ↦ᵣ indexW) **
         stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved))
      (loopRejected newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff) := by
  have ht := statusReject status
    (nextScratch listBase bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x12 ↦ᵣ (0 : Word)) **
       (.x21 ↦ᵣ BitVec.ofNat 64 count) **
       (.x9 ↦ᵣ indexW) **
       stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved))
    (by pcf) hstatus
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) ht
  · xperm_hyp hp
  · unfold loopRejected loopFrame
    refine ⟨count, off, status, ?_⟩
    have hq' := sepConj_mono
      (fun _ x => x)
      (sepConj_mono (nextScratch_implies_owned listBase bytes) (fun _ x => x)) h hq
    refine (sepConj_pure_right h).2
      ⟨?_, hstatus, hcount, hlist, hprefix, hwalk⟩
    unfold nextScratchOwned at hq'
    xperm_hyp hq'

#print axioms dispatchFailure

theorem dispatchSuccess
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen index cursorOff count off j : Nat) (next len : Word)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hlist : StrictListPayload bytes listBase listLen cursorOff endPtr)
    (hcount : count ≤ index) (hj : j = index + 1 - count)
    (hoff : off ≤ listLen)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hslack : listLen + 9 ≤ bytes.length)
    (hprefix : StrictPrefix bytes listBase endPtr cursorOff count off)
    (hitem : rlpItemDecode bytes off (listBase + BitVec.ofNat 64 off)
      endPtr next len) :
    cpsBranchWithin 4 (B + 72) code
      (nextScratch listBase bytes **
       ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ BitVec.ofNat 64 count) **
        (.x9 ↦ᵣ indexW) **
        stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved))
      (B + 88)
        (loopSelected newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes index cursorOff)
      (B + 64) (fun h => ∃ j', j' < j ∧
        loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes listLen index cursorOff j' h) := by
  subst indexW
  have hs := statusOk
    (nextScratch listBase bytes **
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
       (.x21 ↦ᵣ BitVec.ofNat 64 count) **
       (.x9 ↦ᵣ BitVec.ofNat 64 index) **
       stableFrame newSp listBase (BitVec.ofNat 64 index) offsetPtr lenPtr endPtr oldOffset oldLen saved))
    (by pcf)
  by_cases heq : count = index
  · subst count
    have hi := indexSelected (BitVec.ofNat 64 index)
      (nextScratch listBase bytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) **
         stableFrame newSp listBase (BitVec.ofNat 64 index) offsetPtr lenPtr endPtr oldOffset oldLen saved))
      (by pcf)
    have hc := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hs hi
    refine cpsTripleWithin_as_cpsBranchWithin_left _ _
      (cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hc))
    unfold loopSelected loopFrame
    refine ⟨next, len, ?_⟩
    have hq' := sepConj_mono
      (fun _ x => x)
      (sepConj_mono (nextScratch_implies_owned listBase bytes) (fun _ x => x)) h hq
    refine (sepConj_pure_right h).2 ⟨?_, StrictPrefix.select hprefix hitem⟩
    unfold nextScratchOwned at hq'
    xperm_hyp hq'
  · have hlt : count < index := by omega
    have hword : BitVec.ofNat 64 count ≠ BitVec.ofNat 64 index := by
      intro he
      have he' := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hlt hindex),
        Nat.mod_eq_of_lt hindex] at he'
      omega
    have hi := indexContinue (BitVec.ofNat 64 count) (BitVec.ofNat 64 index)
      (nextScratch listBase bytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) **
         stableFrame newSp listBase (BitVec.ofNat 64 index) offsetPtr lenPtr endPtr oldOffset oldLen saved))
      (by pcf) hword
    have hb := incrementBack count
      (nextScratch listBase bytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ BitVec.ofNat 64 index) **
         stableFrame newSp listBase (BitVec.ofNat 64 index) offsetPtr lenPtr endPtr oldOffset oldLen saved))
      (by pcf)
    have hc1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hs hi
    have hc := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hc1 hb
    refine cpsTripleWithin_as_cpsBranchWithin_right _ _
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hc)
    have hend := hlist.end_eq
    subst endPtr
    have hstep := StrictPrefix.step_bounds hprefix hitem hoff (by omega)
    refine ⟨index + 1 - (count + 1), by omega, ?_⟩
    unfold loopInv loopFrame
    refine ⟨count + 1, (next - listBase).toNat, ?_⟩
    have hq' := sepConj_mono
      (fun _ x => x)
        (sepConj_mono (nextScratch_implies_owned listBase bytes)
          (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn .x11)
            (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x))))) h hq
    refine (sepConj_pure_right h).2
      ⟨?_, rfl, by omega, hstep.2.2.1, hstep.2.2.2⟩
    rw [hstep.1] at hq'
    unfold nextScratchOwned at hq'
    xperm_hyp hq'

#print axioms dispatchSuccess

theorem cpsNBranchWithin_pre_or {n : Nat} {entry : Word} {cr : CodeReq}
    {P1 P2 : Assertion} {exits : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n entry cr P1 exits)
    (h2 : cpsNBranchWithin n entry cr P2 exits) :
    cpsNBranchWithin n entry cr (fun h => P1 h ∨ P2 h) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, hor, hRb⟩ := hPR
  rcases hor with hP | hP
  · exact h1 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  · exact h2 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

#print axioms cpsNBranchWithin_pre_or

/-! ## One complete loop round and the measure fold -/

def roundStable (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (count : Nat) : Assertion :=
  (.x20 ↦ᵣ endPtr) **
  stableRest newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
  (.x9 ↦ᵣ indexW) ** (.x21 ↦ᵣ BitVec.ofNat 64 count)

theorem callOk_shape
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (count off : Nat) :
    ∀ h, ((nextCommon listBase bytes **
      rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off) **
      roundStable newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved count) h →
      ∃ next len,
        ((nextScratch listBase bytes **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
           (.x0 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ BitVec.ofNat 64 count) **
           (.x9 ↦ᵣ indexW) **
           stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved)) **
         ⌜rlpItemDecode bytes off (listBase + BitVec.ofNat 64 off)
           endPtr next len⌝) h := by
  intro h hp
  obtain ⟨p1, p2, pd, pu, hleft, hstable⟩ := hp
  obtain ⟨q1, q2, qd, qu, hcommon, ⟨next, len, hbody⟩⟩ := hleft
  obtain ⟨r1, r2, rd, ru, h10, hrest⟩ := hbody
  obtain ⟨s1, s2, sd, su, h11, hrest2⟩ := hrest
  obtain ⟨h12, hitem⟩ := (sepConj_pure_right s2).1 hrest2
  refine ⟨next, len, (sepConj_pure_right h).2 ⟨?_, hitem⟩⟩
  have hregs : ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ len)) q2 :=
    ⟨r1, r2, rd, ru, h10, s1, s2, sd, su, h11, h12⟩
  have hp' : ((nextCommon listBase bytes **
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len))) **
      roundStable newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved count) h :=
    ⟨p1, p2, pd, pu, ⟨q1, q2, qd, qu, hcommon, hregs⟩, hstable⟩
  unfold nextCommon roundStable at hp'
  unfold nextScratch stableFrame
  xperm_hyp hp'

theorem callFail_shape
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen status : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (count off : Nat) :
    ∀ h, ((nextCommon listBase bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
       (.x12 ↦ᵣ (0 : Word)) **
       ⌜WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝)) **
      roundStable newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved count) h →
      ((nextScratch listBase bytes **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
         (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x21 ↦ᵣ BitVec.ofNat 64 count) ** (.x9 ↦ᵣ indexW) **
         stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved)) **
       ⌜WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h := by
  intro h hp
  obtain ⟨p1, p2, pd, pu, hleft, hstable⟩ := hp
  obtain ⟨q1, q2, qd, qu, hcommon, hbody⟩ := hleft
  obtain ⟨r1, r2, rd, ru, h10, hrest⟩ := hbody
  obtain ⟨s1, s2, sd, su, h11, hrest2⟩ := hrest
  obtain ⟨h12, hwalk⟩ := (sepConj_pure_right s2).1 hrest2
  refine (sepConj_pure_right h).2 ⟨?_, hwalk⟩
  have hregs : ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
      (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ (0 : Word))) q2 :=
    ⟨r1, r2, rd, ru, h10, s1, s2, sd, su, h11, h12⟩
  have hp' : ((nextCommon listBase bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ (0 : Word)))) **
      roundStable newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved count) h := ⟨p1, p2, pd, pu, ⟨q1, q2, qd, qu, hcommon, hregs⟩, hstable⟩
  unfold nextCommon roundStable at hp'
  unfold nextScratch stableFrame
  xperm_hyp hp'

#print axioms callOk_shape
#print axioms callFail_shape

theorem failureRegs_mono (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) (status : Word) (P : Prop)
    (himp : P → WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr) :
    ∀ h,
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
        (.x12 ↦ᵣ (0 : Word)) ** ⌜P⌝) h) →
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h) := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, h10, hp⟩ := hp
  obtain ⟨h3, h4, hd2, hu2, h11, hp⟩ := hp
  obtain ⟨h5, h6, hd3, hu3, h12, hP⟩ := hp
  have hP' : P := hP.2
  have hwalk : ⌜WalkFailure bytes off
      (listBase + BitVec.ofNat 64 off) endPtr⌝ h6 := by
    exact ⟨hP.1, himp hP'⟩
  exact ⟨h1, h2, hd, hu, h10,
    ⟨h3, h4, hd2, hu2, h11,
      ⟨h5, h6, hd3, hu3, h12, hwalk⟩⟩⟩

theorem loopRound
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen index cursorOff : Nat)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hlist : StrictListPayload bytes listBase listLen cursorOff endPtr)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (j : Nat) :
    cpsNBranchWithin 93 (B + 64) code
      (loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff j)
      [(B + 88, loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes index cursorOff),
       (B + 112, loopRejected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes listLen index cursorOff),
       (B + 64, fun h => ∃ j', j' < j ∧
        loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes listLen index cursorOff j' h)] := by
  unfold loopInv
  refine cpsNBranchWithin_exists_pre (fun count => ?_)
  refine cpsNBranchWithin_exists_pre (fun off => ?_)
  refine cpsNBranchWithin_pure_pre (fun hfacts => ?_)
  obtain ⟨hj, hcount, hoff, hprefix⟩ := hfacts
  -- Expose the call-clobbered owned registers; x11 differs on the first
  -- entry and later reentries but slot 16 overwrites it before the call.
  refine cpsNBranchWithin3_weaken
    (P := ((stableRest newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
      ((.x20 ↦ᵣ endPtr) ** (.x9 ↦ᵣ indexW) **
       (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       regOwn .x11 ** (.x21 ↦ᵣ BitVec.ofNat 64 count) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1))
    (fun h hp => by unfold loopFrame stableFrame at hp; xperm_hyp hp)
    (fun _ x => x) (fun _ x => x) (fun _ x => x) ?_
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn9
    (fun v5 v6 v7 v12 v28 v29 v30 v31 vRa => ?_)
  let P11 : Assertion :=
    ((stableRest newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
      ((.x20 ↦ᵣ endPtr) ** (.x9 ↦ᵣ indexW) **
       (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       (.x21 ↦ᵣ BitVec.ofNat 64 count) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x12 ↦ᵣ v12) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ vRa))
  refine cpsNBranchWithin_weaken_pre (P := P11 ** regOwn .x11)
    (fun h hp => by unfold P11; xperm_hyp hp) ?_
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn (P := P11) (fun v11 => ?_)
  have tcall := nextCallBlock listBase endPtr bytes off listLen
    v5 v6 v7 v11 v12 v28 v29 v30 v31 vRa
    (stableRest newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
      (.x9 ↦ᵣ indexW) ** (.x21 ↦ᵣ BitVec.ofNat 64 count))
    (by pcf) hsalign hslack hover hvalid hoff
  -- Success continuation, embedded in the common three-exit round.
  have hok : cpsNBranchWithin 4 (B + 72) code
      (fun h => ∃ next len,
        ((nextScratch listBase bytes **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
           (.x0 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ BitVec.ofNat 64 count) **
           (.x9 ↦ᵣ indexW) **
           stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved)) **
         ⌜rlpItemDecode bytes off (listBase + BitVec.ofNat 64 off)
           endPtr next len⌝) h)
      [(B + 88, loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes index cursorOff),
       (B + 112, loopRejected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes listLen index cursorOff),
       (B + 64, fun h => ∃ j', j' < j ∧
        loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes listLen index cursorOff j' h)] := by
    refine cpsNBranchWithin_exists_pre (fun next => ?_)
    refine cpsNBranchWithin_exists_pre (fun len => ?_)
    refine cpsNBranchWithin_pure_pre (fun hitem => ?_)
    exact cpsNBranchWithin_of_branch_mem (by simp) (by simp)
      (dispatchSuccess newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff count off j next len hindexW hindex hlist
        hcount hj hoff hover hslack hprefix hitem)
  -- One generic failure arm, embedded at the reject member.
  have hfail : ∀ status : Word, status ≠ 0 →
      cpsNBranchWithin 4 (B + 72) code
        (fun h =>
          ((nextScratch listBase bytes **
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
             (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
             (.x21 ↦ᵣ BitVec.ofNat 64 count) ** (.x9 ↦ᵣ indexW) **
             stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved)) **
           ⌜WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h)
        [(B + 88, loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
          oldOffset oldLen saved bytes index cursorOff),
         (B + 112, loopRejected newSp listBase indexW offsetPtr lenPtr endPtr
          oldOffset oldLen saved bytes listLen index cursorOff),
         (B + 64, fun h => ∃ j', j' < j ∧
          loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
            saved bytes listLen index cursorOff j' h)] := by
    intro status hstatus
    refine cpsNBranchWithin_pure_pre (fun hwalk => ?_)
    exact cpsNBranchWithin_mono_nSteps (by omega)
      (cpsNBranchWithin_of_triple (by simp)
        (dispatchFailure newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes listLen index cursorOff count off status hstatus hlist hcount
          hprefix hwalk))
  have harms := cpsNBranchWithin_pre_or hok
    (cpsNBranchWithin_pre_or (hfail 2 (by decide))
      (cpsNBranchWithin_pre_or (hfail 3 (by decide))
        (cpsNBranchWithin_pre_or (hfail 4 (by decide))
          (cpsNBranchWithin_pre_or (hfail 5 (by decide)) (hfail 6 (by decide))))))
  let callPost : Assertion :=
    (nextCommon listBase bytes ** nextOutcome listBase endPtr bytes off) **
      roundStable newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved count
  have hcont : cpsNBranchWithin 4 (B + 72) code callPost
      [(B + 88, loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes index cursorOff),
       (B + 112, loopRejected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes listLen index cursorOff),
       (B + 64, fun h => ∃ j', j' < j ∧
        loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes listLen index cursorOff j' h)] := by
    refine cpsNBranchWithin_weaken_pre ?_ harms
    intro h hp
    unfold callPost nextOutcome at hp
    -- Distribute the callee's common frame over its six outcomes.
    obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, hout⟩, hstable⟩ := hp
    rcases hout with hs | hb2 | hb3 | hb4 | hb5 | hb6
    · refine Or.inl (callOk_shape newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes count off h ?_)
      exact ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, hs⟩, hstable⟩
    · refine Or.inr (Or.inl (callFail_shape newSp listBase indexW offsetPtr lenPtr
        endPtr oldOffset oldLen 2 saved bytes count off h ?_))
      refine ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, ?_⟩, hstable⟩
      exact failureRegs_mono listBase endPtr bytes off 2 _ Or.inl h4 hb2
    · refine Or.inr (Or.inr (Or.inl (callFail_shape newSp listBase indexW offsetPtr
        lenPtr endPtr oldOffset oldLen 3 saved bytes count off h ?_)))
      refine ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, ?_⟩, hstable⟩
      exact failureRegs_mono listBase endPtr bytes off 3 _ Or.inr h4 hb3
    · refine Or.inr (Or.inr (Or.inr (Or.inl (callFail_shape newSp listBase indexW
        offsetPtr lenPtr endPtr oldOffset oldLen 4 saved bytes count off h ?_))))
      refine ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, ?_⟩, hstable⟩
      exact failureRegs_mono listBase endPtr bytes off 4 _ Or.inr h4 hb4
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (callFail_shape newSp listBase
        indexW offsetPtr lenPtr endPtr oldOffset oldLen 5 saved bytes count off h ?_)))))
      refine ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, ?_⟩, hstable⟩
      exact failureRegs_mono listBase endPtr bytes off 5 _ Or.inr h4 hb5
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      refine callFail_shape newSp listBase indexW offsetPtr lenPtr endPtr oldOffset
        oldLen 6 saved bytes count off h ?_
      refine ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, ?_⟩, hstable⟩
      exact failureRegs_mono listBase endPtr bytes off 6 _ Or.inr h4 hb6
  have tcall' : cpsTripleWithin 89 (B + 64) (B + 72) code _ callPost :=
    cpsTripleWithin_weaken (fun _ x => x) (fun h hp => by
    dsimp [callPost]
    unfold nextOutcome roundStable
    exact hp) tcall
  have hseq := cpsTripleWithin_seq_cpsNBranchWithin_same_cr tcall' hcont
  exact cpsNBranchWithin_mono_nSteps (by omega)
    (cpsNBranchWithin_weaken_pre (fun h hp => by
      unfold P11 at hp
      unfold stableRest savedFrame at hp ⊢
      xperm_hyp hp) hseq)

#print axioms loopRound

/-- The strict list scan folded over the remaining-index measure. -/
theorem listNthLoop
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen index cursorOff : Nat)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hlist : StrictListPayload bytes listBase listLen cursorOff endPtr)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (j : Nat) :
    cpsBranchWithin (93 * (j + 1)) (B + 64) code
      (loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff j)
      (B + 88) (loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes index cursorOff)
      (B + 112) (loopRejected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes listLen index cursorOff) :=
  cpsBranchWithin_of_nBranch2
    (measureTwoExitLoop_spec 93
      (loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff)
      (fun j' => loopRound newSp listBase indexW offsetPtr lenPtr endPtr oldOffset
        oldLen saved bytes listLen index cursorOff hindexW hindex hlist hsalign
        hslack hover hvalid j') j)

#print axioms listNthLoop

end EvmAsm.Codegen.RlpListNthItemSAsm
