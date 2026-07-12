/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopDefsBorrowCarry

  `loopN2SelectedBorrowCarryV5`: the borrow-conditional analog of
  `loopN2SelectedCarryV5` (FullPathN2V5NoNopLoopDefs).  Each per-digit carry fact
  is required ONLY conditionally on that digit's runtime borrow — so unlike the
  unconditional `loopN2SelectedCarryV5` (which is false when a call digit's trial
  is exact, c3 = 0), this predicate IS satisfiable from shape (call digits via
  `callAddbackCarry2NzV5_of_borrow_n2` (#7431), max digits vacuously since the
  saturated trial never borrows).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopDispatchShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Borrow-conditional selected-carry bundle for the n=2 v5 loop: per digit,
    `borrow → carry`, with the trial and carry predicate picked by the branch. -/
def loopN2SelectedBorrowCarryV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word) : Prop :=
  let r2 := loopN2IterSelectedV5 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let r1 := loopN2IterSelectedV5 bltu_1 v0 v1 v2 v3
    u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  (if bltu_2 then
    (BitVec.ult uTop (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3) →
      callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
   else
    (BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)) ∧
  (if bltu_1 then
    (BitVec.ult r2.2.2.2.2.1
      (mulsubN4_c3 (divKTrialCallV5QHat r2.2.2.1 r2.2.1 v1)
        v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1) →
      callAddbackCarry2NzV5 v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1)
   else
    (BitVec.ult r2.2.2.2.2.1
      (mulsubN4_c3 (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1)) ∧
  (if bltu_0 then
    (BitVec.ult r1.2.2.2.2.1
      (mulsubN4_c3 (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1)
        v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      callAddbackCarry2NzV5 v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)
   else
    (BitVec.ult r1.2.2.2.2.1
      (mulsubN4_c3 (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1) →
      isAddbackCarry2NzN2Max v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1))

end EvmAsm.Evm64
