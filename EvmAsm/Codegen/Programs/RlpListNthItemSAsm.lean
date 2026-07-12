/-
  EvmAsm.Codegen.Programs.RlpListNthItemSAsm

  Genuine semantics and proof layer for the strict K20 `rlp_list_nth_item`
  replacement.  The emitted routine embeds the already-verified strict
  `rlp_walk_init` and `rlp_walk_next` programs behind a framed index loop.
-/

import EvmAsm.Codegen.Programs.RlpRead
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

/-- Successful K20 meaning: the complete input is one strict list and its
    zero-based `index` child exists.  The ABI outputs are the selected content
    offset and length (`next - len - base`, `len`). -/
def Success (bytes : List (BitVec 8)) (base : Word) (listLen index : Nat)
    (offset len : Word) : Prop :=
  ∃ cursorOff endPtr next,
    StrictListPayload bytes base listLen cursorOff endPtr ∧
    StrictNthItem bytes base endPtr index cursorOff next len ∧
    offset = next - len - base

/-- Unified semantic result.  Failure is not an unconstrained catch-all: it
    states that no strict successful decode exists for this input and index.
    This covers malformed/non-canonical outer lists, malformed/non-canonical
    children, and an out-of-bounds index. -/
inductive Result (bytes : List (BitVec 8)) (base : Word)
    (listLen index : Nat) : Word → Word → Word → Prop
  | ok (offset len : Word) (h : Success bytes base listLen index offset len) :
      Result bytes base listLen index 0 offset len
  | fail (h : ¬ ∃ offset len, Success bytes base listLen index offset len) :
      Result bytes base listLen index 1 0 0

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

end EvmAsm.Codegen.RlpListNthItemSAsm
