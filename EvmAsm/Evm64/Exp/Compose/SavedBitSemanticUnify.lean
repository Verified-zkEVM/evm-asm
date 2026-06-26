/-
  EvmAsm.Evm64.Exp.Compose.SavedBitSemanticUnify

  Unification of the two EXP square-and-multiply semantic developments:
  the fixed-path accumulator run (`expTwoMulFixedAccumulatorRun`, defined over a
  processed-bit count with the `AccumulatorTarget`/`Invariant` framework) and the
  bit-list fold (`EvmWord.expSqMulFold` over `natBitsMsb`).  Both compute
  `EvmWord.exp`, so the full 256-step run from the unit accumulator agrees with
  the canonical MSB fold.  This records that the two formulations are
  interchangeable, so downstream EXP closure can use whichever is convenient.

  Bead evm-asm-6snn.4.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant
import EvmAsm.Evm64.EvmWordArith.Exp

namespace EvmAsm.Evm64.Exp.Compose

/-- The full fixed-loop accumulator run from the initial (zero-prefix) target
    equals the canonical MSB-first square-and-multiply fold from the unit
    accumulator — both compute `EvmWord.exp baseWord exponentWord`. -/
theorem expTwoMulFixedAccumulatorRun_eq_expSqMulFold
    (baseWord exponentWord : EvmWord) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord
        (expTwoMulFixedAccumulatorTarget baseWord exponentWord 0) 0 256 =
      EvmWord.expSqMulFold baseWord 1
        (EvmWord.natBitsMsb 256 exponentWord.toNat) := by
  rw [expTwoMulFixedAccumulatorRun_eq_exp_of_start_zero rfl,
    EvmWord.expSqMulFold_natBitsMsb]

end EvmAsm.Evm64.Exp.Compose
