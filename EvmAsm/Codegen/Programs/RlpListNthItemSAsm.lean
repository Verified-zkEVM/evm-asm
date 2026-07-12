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

/-- Exact seven saved-register cells in the frame. -/
def savedFrame (newSp : Word) (saved : Saved) : Assertion :=
  (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) **
  ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2) **
  ((newSp + 32) ↦ₘ saved.s3) ** ((newSp + 40) ↦ₘ saved.s4) **
  ((newSp + 48) ↦ₘ saved.s5)

/-- Registers and framed resources stable across the K20 index loop. -/
def stableFrame (newSp listBase _indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) : Assertion :=
  ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) **
   (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) ** (.x20 ↦ᵣ endPtr) **
   savedFrame newSp saved **
   (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))

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

end EvmAsm.Codegen.RlpListNthItemSAsm
