/-
  EvmAsm.Evm64.DivMod.Spec.N2V5R2R1Dispatch

  Dispatch-form equalities for the n=2 v5 per-digit results `fullDivN2R2V5` /
  `fullDivN2R1V5`: each (irreducible) family result equals the `if`-on-flag
  selection between `iterWithDoubleAddback (divKTrialCallV5QHat …)` (call regime)
  and `iterN2Max …` (max regime).  These are the glue that connects the runtime
  borrow-flag definitions used by the borrow-dispatched full path
  (`evm_div_n2_stack_pre_to_unified_post_v5_noNop_borrowCarry`, stated with
  `iterN2Max` / `iterWithDoubleAddback` `match` forms) to the `fullDivN2R2V5` /
  `fullDivN2R1V5` forms over which the carry bundle
  (`loopN2SelectedBorrowCarryV5_of_shape`) is stated — needed for the n=2 lane.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5FamiliesShapeShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `fullDivN2R2V5` as an `if`-on-`bltu_2` dispatch between the call-regime
    (`iterWithDoubleAddback`) and max-regime (`iterN2Max`) iterations. -/
theorem fullDivN2R2V5_eq_dispatch (bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 =
      (if bltu_2 then
        iterWithDoubleAddback
          (divKTrialCallV5QHat (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
          (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 0
      else
        iterN2Max
          (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 0) := by
  simp only [fullDivN2R2V5, iterN2V5]

/-- `fullDivN2R1V5` as an `if`-on-`bltu_1` dispatch, threaded on the `R2V5`
    remainder. -/
theorem fullDivN2R1V5_eq_dispatch (bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 =
      (if bltu_1 then
        iterWithDoubleAddback
          (divKTrialCallV5QHat (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
            (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
          (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.1
          (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
          (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
          (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
          (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      else
        iterN2Max
          (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.1
          (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
          (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
          (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
          (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1) := by
  simp only [fullDivN2R1V5, iterN2V5]

end EvmAsm.Evm64
