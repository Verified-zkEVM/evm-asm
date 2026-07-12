/-
  EvmAsm.Evm64.DivMod.Spec.N2V5Shift0BundleOfShape

  `loopN2SelectedBorrowCarryV5_shift0_of_shape`: the borrow-conditional carry
  bundle for the n=2 v5 SHIFT=0 loop, discharged from shape.  Shift=0 counterpart
  of `loopN2SelectedBorrowCarryV5_of_shape` (#7461): the divisor is the RAW
  `(b0, b1, 0, 0)` (already top-bit-aligned, `b1 ≥ 2^63`), so the loop runs the
  raw `iterN2V5 … b0 b1 0 0 …` family directly (no normalization).  `v2 = v3 = 0`
  are literal (no shape facts needed); the per-digit `u3 = uTop = 0` collapse is
  via `iterN2V5_collapse` and the per-digit carry discharges
  (`callAddbackCarry2NzV5_of_borrow_of_call_shape` / `…N2Max…`).  This is the
  satisfiable-from-shape carry hypothesis the shift=0 loop consumes.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5ShapeBoundShared
import EvmAsm.Evm64.DivMod.Spec.N2V5MaxCarryOfMaxShape
import EvmAsm.Evm64.DivMod.Spec.N2V5IterSelectedEq
import EvmAsm.Evm64.DivMod.Spec.N2V5ShapeBoundShared
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopDefsBorrowCarry

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The shift=0 borrow-conditional carry bundle, discharged from shape. -/
theorem loopN2SelectedBorrowCarryV5_shift0_of_shape
    (a0 a1 a2 a3 b0 b1 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb1ge : b1.toNat ≥ 2^63)
    (hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1)
    (hc1 : bltu_1 = true → BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    loopN2SelectedBorrowCarryV5 bltu_2 bltu_1 bltu_0 b0 b1 0 0 a2 a3 0 0 0 a1 a0 := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| (0:Word) ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : b1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hz] at hb1ge; simp at hb1ge
  have hvpos : 2^127 ≤ val256 b0 b1 0 0 := by simp only [EvmWord.val256, h0]; omega
  have hfwv : val256 a2 a3 0 0 < 2^64 * val256 b0 b1 0 0 := by
    have ha : val256 a2 a3 0 0 < 2^128 := by
      have := a2.isLt; have := a3.isLt; simp only [EvmWord.val256, h0]; omega
    calc val256 a2 a3 0 0 < 2^128 := ha
      _ ≤ 2^64 * 2^127 := by norm_num
      _ ≤ 2^64 * val256 b0 b1 0 0 := Nat.mul_le_mul_left _ hvpos
  have hR2 := iterN2V5_step bltu_2 b0 b1 a2 a3 0 hbnz hb1ge hfwv hc2 hm2
  obtain ⟨hR2u3, hR2uTop, _⟩ := iterN2V5_collapse bltu_2 b0 b1 a2 a3 0 hbnz hb1ge hfwv hc2 hm2
  have hR1valid := n2_next_window_lt a1
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 _ hR2.2
  obtain ⟨hR1u3, hR1uTop, _⟩ := iterN2V5_collapse bltu_1 b0 b1 a1
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 hbnz hb1ge hR1valid hc1 hm1
  unfold loopN2SelectedBorrowCarryV5
  simp only [loopN2IterSelectedV5_eq_iterN2V5]
  refine ⟨?_, ?_, ?_⟩
  · cases hb : bltu_2 with
    | true =>
      intro hborrow
      have hcall : (0:Word).toNat < b1.toNat := by
        have := hc2 hb; rw [BitVec.ult] at this; exact of_decide_eq_true this
      exact callAddbackCarry2NzV5_of_borrow_of_call_shape b0 b1 a2 a3 0 0 hb1ge hcall hborrow
    | false =>
      intro hborrow
      exact isAddbackCarry2NzN2Max_of_borrow_of_max_shape b0 b1 a2 a3 0 0 hb1ge (hm2 hb) hborrow
  · rw [hR2u3, hR2uTop]
    cases hb : bltu_1 with
    | true =>
      intro hborrow
      have hcall : (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1.toNat < b1.toNat := by
        have := hc1 hb; rw [BitVec.ult] at this; exact of_decide_eq_true this
      exact callAddbackCarry2NzV5_of_borrow_of_call_shape b0 b1 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 hb1ge hcall hborrow
    | false =>
      intro hborrow
      exact isAddbackCarry2NzN2Max_of_borrow_of_max_shape b0 b1 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 hb1ge (hm1 hb) hborrow
  · rw [hR2u3, hR2uTop, hR1u3, hR1uTop]
    cases hb : bltu_0 with
    | true =>
      intro hborrow
      have hcall : (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1.toNat < b1.toNat := by
        have := hc0 hb; rw [BitVec.ult] at this; exact of_decide_eq_true this
      exact callAddbackCarry2NzV5_of_borrow_of_call_shape b0 b1 a0
        (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1
        (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 hb1ge hcall hborrow
    | false =>
      intro hborrow
      exact isAddbackCarry2NzN2Max_of_borrow_of_max_shape b0 b1 a0
        (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1
        (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 hb1ge (hm0 hb) hborrow

end EvmAsm.Evm64
