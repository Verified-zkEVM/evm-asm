/-
  Genuine strict semantics for `rlp_list_count_items`.

  The emitted wrapper counts a complete canonical traversal produced by the
  verified `rlp_walk_init` / `rlp_walk_next` routines.  The pure relations are
  deliberately shared with the strict K20 nth-item replacement.
-/

import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP
open EvmAsm.Codegen.RlpListNthItemSAsm

/-- Pure loop invariant after `count` successful strict item decodes. -/
structure LoopInvariant (bytes : List (BitVec 8)) (base : Word)
    (listLen cursorOff : Nat) (endPtr : Word) (count off : Nat)
    (cursor : Word) : Prop where
  h_list : StrictListPayload bytes base listLen cursorOff endPtr
  h_prefix : StrictPrefix bytes base endPtr cursorOff count off
  h_cursor : cursor = base + BitVec.ofNat 64 off
  h_off : off ≤ listLen
  h_count : count ≤ off

/-- A strict complete list traversal and its exact item count. -/
def Success (bytes : List (BitVec 8)) (base : Word) (listLen count : Nat) : Prop :=
  ∃ cursorOff endPtr,
    StrictListPayload bytes base listLen cursorOff endPtr ∧
    StrictPrefix bytes base endPtr cursorOff count listLen

/-- Strict count failure: either the outer list is malformed, or a canonical
    prefix reaches a cursor where no strict next item can be decoded. -/
inductive Failure (bytes : List (BitVec 8)) (base : Word) (listLen : Nat) : Prop
  | init (h_invalid : ¬ ∃ cursorOff endPtr,
      StrictListPayload bytes base listLen cursorOff endPtr) :
      Failure bytes base listLen
  | walk (cursorOff count off : Nat) (endPtr : Word)
      (h_list : StrictListPayload bytes base listLen cursorOff endPtr)
      (h_prefix : StrictPrefix bytes base endPtr cursorOff count off)
      (h_fail : WalkFailure bytes off (base + BitVec.ofNat 64 off) endPtr) :
      Failure bytes base listLen

/-- Genuine ABI result: success writes the exact strict item count; every
    malformed input writes zero and returns status one. -/
inductive Result (bytes : List (BitVec 8)) (base : Word) (listLen : Nat) :
    Word → Word → Prop
  | ok (count : Nat) (h_count : count < 2 ^ 64)
      (h_success : Success bytes base listLen count) :
      Result bytes base listLen 0 (BitVec.ofNat 64 count)
  | fail (h_failure : Failure bytes base listLen) :
      Result bytes base listLen 1 0

/-- The loop's natural measure is the number of declared list bytes not yet
    consumed. -/
def remaining (listLen off : Nat) : Nat := listLen - off

/-- One successful strict item decode extends the prefix and strictly reduces
    the remaining-byte measure. -/
theorem LoopInvariant.step
    {bytes : List (BitVec 8)} {base endPtr cursor next len : Word}
    {listLen cursorOff count off : Nat}
    (h_inv : LoopInvariant bytes base listLen cursorOff endPtr count off cursor)
    (h_item : rlpItemDecode bytes off cursor endPtr next len)
    (h_over : base.toNat + listLen + 9 < 2 ^ 64) :
    LoopInvariant bytes base listLen cursorOff endPtr (count + 1)
        (next - base).toNat next ∧
      remaining listLen (next - base).toNat < remaining listLen off := by
  have h_end : endPtr = base + BitVec.ofNat 64 listLen := h_inv.h_list.end_eq
  have h_item' : rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
      (base + BitVec.ofNat 64 listLen) next len := by
    simpa [h_inv.h_cursor, h_end] using h_item
  have h_prefix0 : StrictPrefix bytes base (base + BitVec.ofNat 64 listLen)
      cursorOff count off := by
    simpa [h_end] using h_inv.h_prefix
  obtain ⟨h_next, h_lt, h_le, h_prefix⟩ :=
    h_prefix0.step_bounds h_item' h_inv.h_off h_over
  have h_count := h_inv.h_count
  refine ⟨⟨h_inv.h_list, ?_, h_next, h_le, by omega⟩, ?_⟩
  · simpa [h_end] using h_prefix
  · unfold remaining
    omega

/-- Reaching the exclusive end converts the loop invariant into the genuine
    complete-count success relation. -/
theorem LoopInvariant.toSuccess
    {bytes : List (BitVec 8)} {base endPtr cursor : Word}
    {listLen cursorOff count off : Nat}
    (h_inv : LoopInvariant bytes base listLen cursorOff endPtr count off cursor)
    (h_done : cursor = endPtr)
    (h_over : base.toNat + listLen < 2 ^ 64) :
    Success bytes base listLen count := by
  have h_end : endPtr = base + BitVec.ofNat 64 listLen := h_inv.h_list.end_eq
  have h_addr : base + BitVec.ofNat 64 off =
      base + BitVec.ofNat 64 listLen := by
    rw [← h_inv.h_cursor, h_done, h_end]
  have h_off_lt : off < 2 ^ 64 := lt_of_le_of_lt h_inv.h_off (by omega)
  have h_base_off : base.toNat + off < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.add_le_add_left h_inv.h_off base.toNat) h_over
  have h_nat := congrArg BitVec.toNat h_addr
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h_off_lt, Nat.mod_eq_of_lt (by omega : listLen < 2 ^ 64),
    Nat.mod_eq_of_lt h_base_off, Nat.mod_eq_of_lt h_over] at h_nat
  have h_eq : off = listLen := by omega
  subst off
  exact ⟨cursorOff, endPtr, h_inv.h_list, h_inv.h_prefix⟩

/-- A failed strict walk from a loop station produces the unified semantic
    failure witness without weakening the already-decoded prefix. -/
theorem LoopInvariant.toFailure
    {bytes : List (BitVec 8)} {base endPtr cursor : Word}
    {listLen cursorOff count off : Nat}
    (h_inv : LoopInvariant bytes base listLen cursorOff endPtr count off cursor)
    (h_fail : WalkFailure bytes off cursor endPtr) :
    Failure bytes base listLen := by
  refine .walk cursorOff count off endPtr h_inv.h_list h_inv.h_prefix ?_
  simpa [h_inv.h_cursor] using h_fail

#print axioms LoopInvariant.step
#print axioms LoopInvariant.toSuccess
#print axioms LoopInvariant.toFailure

end EvmAsm.Codegen.RlpListCountItemsSAsm
