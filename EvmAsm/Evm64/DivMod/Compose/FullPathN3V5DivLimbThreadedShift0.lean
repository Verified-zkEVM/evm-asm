/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5DivLimbThreadedShift0

  Threaded form of the n=3 v5 SHIFT=0 per-limb quotient facts: the four
  `(EvmWord.div a b).getLimbN i` equalities phrased in terms of the loop-frame
  digit iterates `n3Shift0R0`/`n3Shift0R1` (FullPathN3V5FrameShift0), as the
  shift=0 lane / post bridge (#7559) consume them.  Bridges the raw-iterate lane
  form (`n3_shift0_div_getLimbN_lane`, #7562): the only mismatch is the digit-0
  window's `u₄`, which is `n3Shift0R1`'s `rem₃` in the frame def but `0` in the
  lane form — and `iterN3V5_collapse` shows that `rem₃ = 0`.  n=3 / 2-digit analog
  of `n2_shift0_div_getLimbN_threaded` (FullPathN2V5LaneShift0).
  Bead `evm-asm-wbc4i.9.3.3.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3V5Shift0DivLimb
public import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5FrameShift0

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The four `(EvmWord.div a b).getLimbN i` shift=0 equalities, in `n3Shift0R*` form. -/
theorem n3_shift0_div_getLimbN_threaded (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 : Word) (bltu_1 bltu_0 : Bool)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3z : b.getLimbN 3 = 0)
    (hb2ge : b2.toNat ≥ 2^63)
    (hc1 : bltu_1 = true → BitVec.ult (0:Word) b2 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (0:Word) b2)
    (hc0 : bltu_0 = true →
      BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2) :
    (EvmWord.div a b).getLimbN 0 = (n3Shift0R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2).1 ∧
    (EvmWord.div a b).getLimbN 1 = (n3Shift0R1 bltu_1 a1 a2 a3 b0 b1 b2).1 ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  obtain ⟨hd0, hd1, hd2, hd3⟩ := n3_shift0_div_getLimbN_lane a b a0 a1 a2 a3 b0 b1 b2
    bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3z hb2ge hc1 hm1 hc0 hm0
  have h0 : (0:Word).toNat = 0 := rfl
  have hvpos : 2^191 ≤ val256 b0 b1 b2 0 := by simp only [EvmWord.val256, h0]; omega
  have hfwv : val256 a1 a2 a3 0 < 2^64 * val256 b0 b1 b2 0 := by
    have ha : val256 a1 a2 a3 0 < 2^192 := by
      have := a1.isLt; have := a2.isLt; have := a3.isLt
      simp only [EvmWord.val256, h0]; omega
    calc val256 a1 a2 a3 0 < 2^192 := ha
      _ ≤ 2^64 * 2^191 := by norm_num
      _ ≤ 2^64 * val256 b0 b1 b2 0 := Nat.mul_le_mul_left _ hvpos
  obtain ⟨hR1u4, _⟩ := iterN3V5_collapse bltu_1 b0 b1 b2 a1 a2 a3 0 hb2ge hfwv hc1 hm1
  refine ⟨?_, hd1, hd2, hd3⟩
  simp only [n3Shift0R0, n3Shift0R1]
  rw [hR1u4]
  exact hd0

end EvmAsm.Evm64
