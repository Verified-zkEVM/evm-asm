/-
  EvmAsm.Evm64.DivMod.Spec.N3V5Shift0BundleOfShape

  `loopN3SelectedBorrowCarryV5_shift0_of_shape`: the borrow-conditional carry
  bundle for the n=3 v5 SHIFT=0 loop, discharged from shape.  Shift=0 counterpart
  of `loopN3SelectedBorrowCarryV5_of_shape` (#7527): the divisor is the RAW
  `(b0, b1, b2, 0)` (already top-bit-aligned, `b2 ≥ 2^63`), so the loop runs the
  raw `iterN3V5 … b0 b1 b2 0 …` family directly (no normalization), over the
  shift=0 verbatim-dividend window `u0=a1, u1=a2, u2=a3, u3=0, uTop=0, u0Orig=a0`
  (read off the shift=0 preloop's loop pre-state, FullPathN3V5PreloopShift0).
  `v3 = 0` is literal (no shape facts needed); the per-digit carry discharges use
  `n3_call_addback_carry2_nz_of_borrow_of_call_shape` / `…N3Max…`.
  Bead `evm-asm-wbc4i.9.3.3.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3V5CallCarryOfCallShape
public import EvmAsm.Evm64.DivMod.Spec.N3V5MaxCarryOfMaxShape
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopLoopDefsBorrowCarry

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The shift=0 borrow-conditional carry bundle, discharged from shape. -/
theorem loopN3SelectedBorrowCarryV5_shift0_of_shape
    (a0 a1 a2 a3 b0 b1 b2 : Word) (bltu_1 bltu_0 : Bool)
    (hb2ge : b2.toNat ≥ 2 ^ 63)
    (hc1 : bltu_1 = true → BitVec.ult (0 : Word) b2 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (0 : Word) b2)
    (hc0 : bltu_0 = true →
      BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2) :
    loopN3SelectedBorrowCarryV5 bltu_1 bltu_0 b0 b1 b2 0 a1 a2 a3 0 0 a0 := by
  unfold loopN3SelectedBorrowCarryV5
  refine ⟨?_, ?_⟩
  · -- j=1 obligation, first (raw) window
    cases hb : bltu_1 with
    | true =>
      simp only [reduceIte]
      intro hborrow
      exact n3_call_addback_carry2_nz_of_borrow_of_call_shape _ _ _ _ _ _ _ _
        hb2ge (hc1 hb) hborrow
    | false =>
      rw [if_neg (by decide)]
      intro hborrow
      exact isAddbackCarry2NzN3Max_of_borrow_of_max_shape _ _ _ _ _ _ _ _
        hb2ge (hm1 hb) hborrow
  · -- j=0 obligation, second window (over `iterN3V5 bltu_1` of the raw window)
    cases hb : bltu_0 with
    | true =>
      simp only [reduceIte]
      intro hborrow
      exact n3_call_addback_carry2_nz_of_borrow_of_call_shape _ _ _ _ _ _ _ _
        hb2ge (hc0 hb) hborrow
    | false =>
      rw [if_neg (by decide)]
      intro hborrow
      exact isAddbackCarry2NzN3Max_of_borrow_of_max_shape _ _ _ _ _ _ _ _
        hb2ge (hm0 hb) hborrow

end EvmAsm.Evm64
