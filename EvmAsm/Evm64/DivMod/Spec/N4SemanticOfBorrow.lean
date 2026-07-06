/-
  EvmAsm.Evm64.DivMod.Spec.N4SemanticOfBorrow

  The n=4 v5 call+addback-BEQ semantic from a SINGLE runtime input, under `U4 = 0`:
    `n4CallAddbackBeqSemanticHoldsV5 a b`  (i.e. `qOut = qTrue = val256 a / val256 b`)
  follows from just the borrow condition `isAddbackBorrowN4CallV5Evm a b` (plus the
  n=4 shape `b3 ≠ 0` / `clz b3 ≠ 0` and `U4 = 0`).

  Consolidates the semantic-discharge chain: the `+1` `hq_over` (#7579, via
  `qHat ≤ 1` under `U4 = 0`), `h_carry2` from `h_borrow` (#7580), and `h_rem_lt`
  from the runtime conditions (#7199) all fed into
  `n4CallAddbackBeqSemanticHoldsV5_of_runtime_conditions_legacy`.  All three previously-
  hypothesised runtime conditions (`hq_over`, `h_carry2`, `h_rem_lt`) are now
  discharged; the only remaining runtime input on the U4=0 single-addback branch is
  `h_borrow`, which the n=4 v5 code path establishes by execution.  Bead
  `evm-asm-wbc4i.8.2.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N4Carry2OfBorrow

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The n=4 v5 semantic from the borrow condition alone, under `U4 = 0`. -/
theorem n4CallAddbackBeqSemanticHoldsV5_of_borrow_u4_zero {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hu4 : (n4CallAddbackBeqU4 a b).toNat = 0)
    (h_borrow : isAddbackBorrowN4CallV5Evm a b) :
    n4CallAddbackBeqSemanticHoldsV5 a b :=
  n4CallAddbackBeqSemanticHoldsV5_of_runtime_conditions_legacy hb3nz hshift_nz
    (n4CallAddbackBeqQHatV5_le_window_div_plus_one_of_u4_zero hb3nz hu4)
    h_borrow
    (n4CallAddbackBeqCarry2_of_borrow_and_u4_zero hb3nz hu4 h_borrow)
    (n4CallAddbackBeqIterRNormVal_lt_BNormVal_of_runtimeV5
      (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)
      (n4CallAddbackBeqQHatV5_le_window_div_plus_one_of_u4_zero hb3nz hu4)
      h_borrow)

end EvmAsm.Evm64
