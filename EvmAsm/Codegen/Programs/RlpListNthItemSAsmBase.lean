/-
  EvmAsm.Codegen.Programs.RlpListNthItemSAsm

  Genuine semantics and proof layer for the strict K20 `rlp_list_nth_item`
  replacement.  The emitted routine embeds the already-verified strict
  `rlp_walk_init` and `rlp_walk_next` programs behind a framed index loop.
-/

import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpListNthItemStrictList
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsWalk
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.Tactics.DropPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

/-! ## Pure strict semantics -/

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

#guard rlpListNthItem_prog.length = 194

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

theorem listNthFrameRegs_implies_owned
    (s0 s1 s2 s3 s4 s5 : Word) : ∀ h,
    (regOwn .x1 ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
      (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      (.x21 ↦ᵣ s5)) h → regsOwnAt listNthFrame h := by
  intro h hp
  unfold regsOwnAt listNthFrame
  simp only [List.foldr_cons, List.foldr_nil, sepConj_emp_right']
  exact sepConj_mono (fun _ hx => hx)
    (sepConj_mono (regIs_implies_regOwn .x8)
      (sepConj_mono (regIs_implies_regOwn .x9)
        (sepConj_mono (regIs_implies_regOwn .x18)
          (sepConj_mono (regIs_implies_regOwn .x19)
            (sepConj_mono (regIs_implies_regOwn .x20)
              (regIs_implies_regOwn .x21)))))) h hp

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
      bytes[1]? ≠ some (0 : BitVec 8) ∧
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
      bytes[1]? ≠ some (0 : BitVec 8) ∧
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
      bytes[1]? ≠ some (0 : BitVec 8) ∧
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
    (fun hf8 _ => by
      have hlo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := BalAccountNonstorageFinalsSpec.not_ult_le hf8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun hf8 _ => by
      have hlo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := BalAccountNonstorageFinalsSpec.not_ult_le hf8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun hf8 _ => by
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


def initNormalized (listBase : Word) (bytes : List (BitVec 8))
    (listLen index : Nat) : Assertion := fun h =>
  (∃ cursorOff endPtr,
    (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      ⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝) h)) ∨
  (∃ status cursor endPtr,
    (((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
      ⌜status ≠ 0 ∧ Failure bytes listBase listLen index⌝) h))

theorem longDecode_minimal_of_not_ult (bytes : List (BitVec 8))
    (hoff : 0 < bytes.length)
    (hlong : ¬ BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hmin : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
      ((bytes.drop 1).take
        ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
      (56 : Word) = true) :
    56 ≤ Nat.fromBytesBE ((bytes.drop 1).take
      ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) := by
  have hn : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
    have hb := (bytes[0]'hoff).isLt
    have hge := BalAccountNonstorageFinalsSpec.not_ult_le hlong
    bv_omega
  have hp := Nat.fromBytesBE_lt ((bytes.drop 1).take
    ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)
  have htake : ((bytes.drop 1).take
      ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat).length ≤ 8 :=
    le_trans (List.length_take_le _ _) hn
  have hdec : Nat.fromBytesBE ((bytes.drop 1).take
      ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) < 2 ^ 64 := by
    calc
      _ < 256 ^ ((bytes.drop 1).take
          ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat).length := hp
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by omega) htake
      _ = 2 ^ 64 := by norm_num
  have hge := BalAccountNonstorageFinalsSpec.not_ult_le hmin
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdec] at hge
  change 56 ≤ Nat.fromBytesBE ((bytes.drop 1).take
    ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) at hge
  exact hge

theorem threeRegs_pure {A B C : Assertion} {P : Prop} :
    ∀ h, (A ** B ** C ** ⌜P⌝) h → P := by
  intro h hp
  extract_pure_deep hp
  exact hp.1

theorem threeRegs_pure_mono {A B C : Assertion} {P Q : Prop}
    (himp : P → Q) : ∀ h, (A ** B ** C ** ⌜P⌝) h →
      (A ** B ** C ** ⌜Q⌝) h := by
  intro h hp
  extract_pure_deep hp
  rw [show (A ** B ** C ** ⌜Q⌝) = (((A ** B) ** C) ** ⌜Q⌝) by ac_rfl]
  exact (sepConj_pure_right h).2 ⟨hp.2, himp hp.1⟩

theorem initOutcome_to_normalized (listBase : Word) (bytes : List (BitVec 8))
    (listLen index : Nat) (hoff : 0 < bytes.length)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64) :
    ∀ h, initOutcome listBase bytes listLen hoff h →
      initNormalized listBase bytes listLen index h := by
  intro h hp
  unfold initOutcome at hp
  unfold initNormalized
  rcases hp with h0 | h1 | hs | h3 | h4 | h5 | h6 | h7 | hl
  · have hword : BitVec.ofNat 64 listLen = (0 : Word) := by
      exact threeRegs_pure h h0
    have hlen : listLen = 0 := by
      have hw := congrArg BitVec.toNat hword
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hw
      simpa using hw
    refine Or.inr ⟨2, listBase, 0, ?_⟩
    have hf : Failure bytes listBase listLen index := by
      subst listLen
      exact .init (noStrictList_of_empty bytes listBase)
    exact threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h0
  · have hc : BitVec.ofNat 64 listLen ≠ (0 : Word) ∧
        BitVec.ult ((bytes[0]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
      exact threeRegs_pure h h1
    refine Or.inr ⟨1, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen index :=
      .init (noStrictList_of_notlist bytes listBase listLen hoff hc.2)
    exact threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h1
  · have hc := threeRegs_pure h hs
    obtain ⟨_, hnot, hshort, hend⟩ := hc
    have hlist := shortInit_to_strict bytes listBase listLen hoff (by omega)
      hnot hshort hend
    refine Or.inl ⟨1, listBase + BitVec.ofNat 64 listLen, ?_⟩
    rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 by decide] at hs
    exact threeRegs_pure_mono (fun _ => hlist) h hs
  · have hc := threeRegs_pure h h3
    obtain ⟨_, _, hshort, hm⟩ := hc
    refine Or.inr ⟨3, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen index := .init
      (noStrictList_of_short_mismatch bytes listBase listLen hoff (by omega) hshort hm)
    exact threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h3
  · have hc := threeRegs_pure h h4
    obtain ⟨_, _, hlong, htrunc⟩ := hc
    refine Or.inr ⟨4, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen index := .init
      (noStrictList_of_long_header_truncated bytes listBase listLen hoff hslack hover
        hlong htrunc)
    exact threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h4
  · have hc := threeRegs_pure h h5
    obtain ⟨_, _, hlong, _, hzero⟩ := hc
    refine Or.inr ⟨5, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen index := .init
      (noStrictList_of_long_leading_zero bytes listBase listLen hoff hlong hzero)
    exact threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h5
  · have hc := threeRegs_pure h h6
    obtain ⟨_, _, hlong, _, _, hmin⟩ := hc
    refine Or.inr ⟨6, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen index := .init
      (noStrictList_of_long_nonminimal bytes listBase listLen hoff hlong hmin)
    exact threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h6
  · have hc := threeRegs_pure h h7
    obtain ⟨_, _, hlong, _, _, _, hm⟩ := hc
    refine Or.inr ⟨7, listBase, listBase + BitVec.ofNat 64 listLen, ?_⟩
    have hf : Failure bytes listBase listLen index := .init
      (noStrictList_of_long_mismatch bytes listBase listLen hoff hlong hm)
    exact threeRegs_pure_mono (fun _ => ⟨by decide, hf⟩) h h7
  · have hc := threeRegs_pure h hl
    obtain ⟨_, _, hlong, hfit, hbNZ, hmin, hend⟩ := hc
    have hoff1 : 1 < bytes.length := by omega
    have hfirst : bytes[1]? = some (bytes[1]'hoff1) := List.getElem?_eq_getElem hoff1
    have hnz : bytes[1]'hoff1 ≠ 0 := by
      intro hz
      apply hbNZ
      rw [hfirst, hz]
    have hminimal := longDecode_minimal_of_not_ult bytes hoff hlong hmin
    let cursorOff := 1 +
      ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
    have hlist := longInit_to_strict bytes listBase listLen hoff hslack hover hlong
      hfit hfirst hnz hminimal hend
    have hcursor : listBase +
        (((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = listBase + BitVec.ofNat 64 cursorOff := by
      unfold cursorOff
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
      have hb := (bytes[0]'hoff).isLt
      have hge := BalAccountNonstorageFinalsSpec.not_ult_le hlong
      bv_omega
    rw [hcursor] at hl
    exact Or.inl ⟨cursorOff, listBase + BitVec.ofNat 64 listLen, by
      exact threeRegs_pure_mono (fun _ => hlist) h hl⟩


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


theorem cpsNBranchWithin_pre_or_init {n : Nat} {entry : Word} {cr : CodeReq}
    {P1 P2 : Assertion} {exits : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n entry cr P1 exits)
    (h2 : cpsNBranchWithin n entry cr P2 exits) :
    cpsNBranchWithin n entry cr (fun h => P1 h ∨ P2 h) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, hpor, hRb⟩ := hPR
  cases hpor with
  | inl hP => exact h1 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  | inr hP => exact h2 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

theorem cpsTripleWithin_exists_assertion {α : Sort _} {n : Nat}
    {entry exit_ : Word} {cr : CodeReq} {P : α → Assertion} {Q : Assertion}
    (h : ∀ x, cpsTripleWithin n entry exit_ cr (P x) Q) :
    cpsTripleWithin n entry exit_ cr (fun hp => ∃ x, P x hp) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, ⟨x, hP⟩, hRb⟩ := hPR
  exact h x R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

end EvmAsm.Codegen.RlpListNthItemSAsm
