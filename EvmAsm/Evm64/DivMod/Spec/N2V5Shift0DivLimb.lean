/-
  EvmAsm.Evm64.DivMod.Spec.N2V5Shift0DivLimb

  Per-limb form of the n=2 v5 SHIFT=0 quotient correctness: each limb of
  `EvmWord.div a b` equals the corresponding shift=0 schoolbook digit
  (the raw `iterN2V5 …`-based quotient digit).  Decomposes the quotient-word
  equality `n2_shift0_quotient_word_eq_div_lane` (#7467) into the four
  `(EvmWord.div a b).getLimbN i = digit_i` equalities via `getLimbN_fromLimbs_*`.
  These are the `hdiv0..hdiv3` facts the n=2 shift=0 lane feeds to the post
  bridge `n2_shift0_epiloguePost_to_divStackDispatchPostV5` (#7475).
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0Shared
import EvmAsm.Evm64.EvmWordArith.DivLimbBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The four `(EvmWord.div a b).getLimbN i` shift=0 digit equalities. -/
theorem n2_shift0_div_getLimbN_lane (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2z : b.getLimbN 2 = 0) (hb3z : b.getLimbN 3 = 0)
    (hb1ge : b1.toNat ≥ 2^63)
    (hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1)
    (hc1 : bltu_1 = true → BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    (EvmWord.div a b).getLimbN 0 =
        (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).1 ∧
    (EvmWord.div a b).getLimbN 1 =
        (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).1 ∧
    (EvmWord.div a b).getLimbN 2 = (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  have hword := n2_shift0_quotient_word_eq_div_lane a b a0 a1 a2 a3 b0 b1 bltu_2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2z hb3z hb1ge hc2 hm2 hc1 hm1 hc0 hm0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← hword]
  · exact EvmWord.getLimbN_fromLimbs_0
  · exact EvmWord.getLimbN_fromLimbs_1
  · exact EvmWord.getLimbN_fromLimbs_2
  · exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
