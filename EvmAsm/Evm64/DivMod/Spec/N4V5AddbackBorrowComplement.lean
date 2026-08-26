/-
  EvmAsm.Evm64.DivMod.Spec.N4V5AddbackBorrowComplement

  The n=4 v5 call-path borrow predicates are complementary: the addback-borrow
  condition `isAddbackBorrowN4CallV5` is exactly the negation of the skip-borrow
  condition `isSkipBorrowN4CallV5`.  Both are statements about the SAME outer
  mulsub of the v5 trial quotient — skip says `(if ult u4 c3 then 1 else 0) = 0`
  (no borrow), addback says the same expression `≠ 0` (borrow happened).

  This is the structural fact the v5-native shift≠0 cert-of-shape needs: when the
  runtime does NOT take the skip branch (`¬ isSkipBorrowN4CallV5`), the addback
  branch's borrow premise `isAddbackBorrowN4CallV5` holds for free.
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopPreloopCallAddback
public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopPreloopCallSkip

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 call-path addback-borrow predicate is the negation of the skip-borrow
    predicate: both decide the same `(if ult u4 c3 then 1 else 0)` on the v5
    trial's outer mulsub. -/
theorem isAddbackBorrowN4CallV5_iff_not_skipBorrow
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    isAddbackBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3 ↔
    ¬ isSkipBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold isAddbackBorrowN4CallV5 isSkipBorrowN4CallV5 mulsubN4NoBorrow
  exact Iff.rfl

/-- From "the runtime did not take the skip branch" derive the addback-borrow
    premise.  Discharges the addback branch's first conjunct in the cert-of-shape. -/
theorem isAddbackBorrowN4CallV5_of_not_skipBorrow
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : ¬ isSkipBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3) :
    isAddbackBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3 :=
  (isAddbackBorrowN4CallV5_iff_not_skipBorrow a0 a1 a2 a3 b0 b1 b2 b3).mpr h

end EvmAsm.Evm64
