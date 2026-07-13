/-
  EvmAsm.Evm64.DivMod.Compose.V6QuotientBridge

  Bridge from the v6 fast-path body's stored quotient digits to the v5 model
  digits `fullDivN1R*V5`, en route to `EvmWord.div a b` (the final `dr466`
  fast-arm correctness). The body stores `q[j] = v6chainQ_j = div128V5CodeQuot`
  of the normalized window; the model digit's quotient (`fullDivN1R_jV5.1`) is
  the v5 capped trial `div128Quot_v5` (via `iterN1Call_v5`), which under the
  digit's no-borrow regime needs no double-addback correction. Combined with
  `div128V5CodeQuot_eq_div128Quot_v5` and the definitional normalization match
  (`fullDivN1Shift b0 = (clzResult b0).1`), this yields `v6chainQ_j =
  fullDivN1R_jV5.1`.

  This file proves the top digit (`R3`); the lower digits (`R2`/`R1`/`R0`) follow
  the identical shape (`unfold fullDivN1R{2,1,0}V5; simp [iterN1V5_true]; unfold
  iterN1Call_v5; rw [iterWithDoubleAddback_no_borrow]`), threading the previous
  digit's remainder limb as `uHi`. Bead `evm-asm-dr466`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Defs
import EvmAsm.Evm64.DivMod.LoopIterN1.N1V5IterChainShared
import EvmAsm.Evm64.DivMod.LoopDefs.Iter

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Top digit (`j=3`) quotient extraction: under the no-borrow regime, the v5
    model's top quotient digit equals the v5 capped 128/64 quotient
    `div128Quot_v5 u4 u3 v0` of the normalized window — which the v6 body
    computes as `div128V5CodeQuot u4 u3 v0` (= `div128Quot_v5`, by
    `div128V5CodeQuot_eq_div128Quot_v5`). -/
theorem fullDivN1R3V5_quot_eq_div128 (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb : ¬ BitVec.ult (0 : Word)
      (mulsubN4 (div128Quot_v5 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
                                (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
                                (fullDivN1NormV b0 b1 b2 b3).1)
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0).2.2.2.2) :
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 =
      div128Quot_v5 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
                    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
                    (fullDivN1NormV b0 b1 b2 b3).1 := by
  rw [fullDivN1R3V5_eq_iterN1Call_v5]
  unfold iterN1Call_v5
  rw [iterWithDoubleAddback_no_borrow hb]

/-- Digit `j=2` quotient extraction (threads digit 3's remainder limb as `uHi`). -/
theorem fullDivN1R2V5_quot_eq_div128 (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb : ¬ BitVec.ult (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      (mulsubN4 (div128Quot_v5 (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                                (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
                                (fullDivN1NormV b0 b1 b2 b3).1)
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1).2.2.2.2) :
    (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1 =
      div128Quot_v5 (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
                    (fullDivN1NormV b0 b1 b2 b3).1 := by
  unfold fullDivN1R2V5
  simp only [iterN1V5_true]
  unfold iterN1Call_v5
  rw [iterWithDoubleAddback_no_borrow hb]

/-- Digit `j=1` quotient extraction (threads digit 2's remainder limb as `uHi`). -/
theorem fullDivN1R1V5_quot_eq_div128 (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb : ¬ BitVec.ult (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      (mulsubN4 (div128Quot_v5 (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                                (fullDivN1NormU a0 a1 a2 a3 b0).2.1
                                (fullDivN1NormV b0 b1 b2 b3).1)
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1).2.2.2.2) :
    (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1 =
      div128Quot_v5 (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
                    (fullDivN1NormV b0 b1 b2 b3).1 := by
  unfold fullDivN1R1V5
  simp only [iterN1V5_true]
  unfold iterN1Call_v5
  rw [iterWithDoubleAddback_no_borrow hb]

/-- Digit `j=0` quotient extraction (threads digit 1's remainder limb as `uHi`). -/
theorem fullDivN1R0V5_quot_eq_div128 (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb : ¬ BitVec.ult (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      (mulsubN4 (div128Quot_v5 (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                                (fullDivN1NormU a0 a1 a2 a3 b0).1
                                (fullDivN1NormV b0 b1 b2 b3).1)
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).1
        (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1).2.2.2.2) :
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1 =
      div128Quot_v5 (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                    (fullDivN1NormU a0 a1 a2 a3 b0).1
                    (fullDivN1NormV b0 b1 b2 b3).1 := by
  unfold fullDivN1R0V5
  simp only [iterN1V5_true]
  unfold iterN1Call_v5
  rw [iterWithDoubleAddback_no_borrow hb]

end EvmAsm.Evm64
