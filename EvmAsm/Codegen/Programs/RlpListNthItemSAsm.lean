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

namespace EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP
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
    off < (next - base).toNat ∧ (next - base).toNat ≤ endOff ∧
      StrictPrefix bytes base (base + BitVec.ofNat 64 endOff)
        startOff (count + 1) (next - base).toNat := by
  have ha := BalAccountNonstorageFinalsSpec.rlpItemDecode_advance hitem hoff hover
  exact ⟨ha.2.1, ha.2.2, StrictPrefix.step hprefix hitem⟩

/-- Successful K20 meaning: the complete input is one strict list and its
    zero-based `index` child exists.  The ABI outputs are the selected content
    offset and length (`next - len - base`, `len`). -/
def Success (bytes : List (BitVec 8)) (base : Word) (listLen index : Nat)
    (offset len : Word) : Prop :=
  ∃ cursorOff endPtr next,
    StrictListPayload bytes base listLen cursorOff endPtr ∧
    StrictNthItem bytes base endPtr index cursorOff next len ∧
    offset = next - len - base

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
      (hfail : ¬ ∃ next len, rlpItemDecode bytes off
        (base + BitVec.ofNat 64 off) endPtr next len) :
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

/-- Exact seven saved-register cells in the frame. -/
def savedFrame (newSp : Word) (saved : Saved) : Assertion :=
  (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) **
  ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2) **
  ((newSp + 32) ↦ₘ saved.s3) ** ((newSp + 40) ↦ₘ saved.s4) **
  ((newSp + 48) ↦ₘ saved.s5)

/-- Registers and framed resources stable across the K20 index loop. -/
def loopFrame (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) **
   (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) ** (.x20 ↦ᵣ endPtr) **
   savedFrame newSp saved **
   (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen) **
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
       regOwn .x11 ** regOwn .x12 ** (.x21 ↦ᵣ BitVec.ofNat 64 count))) **
     ⌜j = index + 1 - count ∧ count ≤ index ∧ off ≤ listLen ∧
       StrictPrefix bytes listBase endPtr cursorOff count off⌝) h

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
       ¬ ∃ next len, rlpItemDecode bytes off
         (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h

end EvmAsm.Codegen.RlpListNthItemSAsm
