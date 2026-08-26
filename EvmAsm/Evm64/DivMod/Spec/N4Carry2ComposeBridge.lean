/-
  EvmAsm.Evm64.DivMod.Spec.N4Carry2ComposeBridge

  Bridge the two surface forms of the n=4 v5 call-addback carry2 predicate:
  the `Evm` form `isAddbackCarry2NzN4CallV5Evm` (= the `@[irreducible]`
  `isAddbackCarry2NzN4CallV5Ab` over `getLimbN`, used by the semantic chain
  #7661/#7664) implies the Compose form `isAddbackCarry2NzN4CallV5`
  (FullPathN4V5NoNopPreloopCallAddback, used by the runtime certificate
  `n4ShiftNzLaneRuntimeCertV5Native`).

  Both unfold to the same `loopBodyN4CallAddbackCarry2NzV5` if-implication over the
  windowed limbs; the Evm side just hides it behind the irreducible `Ab` wrapper.
  (The borrow predicates are already definitionally equal, so only carry2 needs a
  bridge.)  This is the last plumbing piece for the n=4 shift≠0 cert-of-shape.
  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopPreloopCallAddback
public import EvmAsm.Evm64.DivMod.Spec.CallAddbackV5

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The `Evm` carry2 predicate implies the Compose carry2 predicate. -/
theorem isAddbackCarry2NzN4CallV5_of_Evm {a b : EvmWord}
    (h : isAddbackCarry2NzN4CallV5Evm a b) :
    isAddbackCarry2NzN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  rw [isAddbackCarry2NzN4CallV5Evm_def] at h
  unfold isAddbackCarry2NzN4CallV5Ab loopBodyN4CallAddbackCarry2NzV5 at h
  unfold isAddbackCarry2NzN4CallV5
  exact h

/-- The Compose borrow predicate implies the `Evm` borrow predicate. -/
theorem isAddbackBorrowN4CallV5Evm_of_compose {a b : EvmWord}
    (h : isAddbackBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    isAddbackBorrowN4CallV5Evm a b := by
  rw [isAddbackBorrowN4CallV5Evm_def]
  unfold isAddbackBorrowN4CallV5Ab loopBodyN4CallAddbackBorrowV5
  unfold isAddbackBorrowN4CallV5 at h
  exact h

end EvmAsm.Evm64
