/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopShiftNzCertOfShape

  Discharge the n=4 v5 shift≠0 native runtime certificate
  `n4ShiftNzLaneRuntimeCertV5Native` (#7642) from the SHAPE alone (`b3 ≠ 0` +
  `clz b3 ≠ 0`), with no runtime inputs.  The v5-native analogue of the shift0
  cert-of-shape `evm_div_n4_shift0_cert_of_shape` (#7635).

  Case split on the v5 skip-borrow:
  * `isSkipBorrowN4CallV5`  → the skip disjunct (trivially);
  * `¬ isSkipBorrowN4CallV5` → the addback disjunct, fully discharged from shape:
    - `isAddbackBorrowN4CallV5` from the borrow complement (#7643);
    - `isAddbackCarry2NzN4CallV5` from `n4CallAddbackBeqCarry2_of_borrow_gen`
      (#7664) via the Compose↔Evm bridges (#7665);
    - `n4CallAddbackBeqSemanticHoldsV5` (qOut = qTrue) from the U4-general semantic
      `n4CallAddbackBeqSemanticHoldsV5_gen` (#7661).

  With this, the n=4 shift≠0 lane's runtime certificate holds unconditionally on
  the n=4 shape — the last math/plumbing piece before the unconditional lane.
  Bead `evm-asm-wbc4i.8.2.2`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneAddbackShared
import EvmAsm.Evm64.DivMod.Spec.N4V5AddbackBorrowComplement
import EvmAsm.Evm64.DivMod.Spec.N4SemanticGen
import EvmAsm.Evm64.DivMod.Spec.N4Carry2OfBorrowGen
import EvmAsm.Evm64.DivMod.Spec.N4Carry2ComposeBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The n=4 v5 shift≠0 native runtime certificate holds for any `a b` of the n=4
    shape (`b3 ≠ 0`, `clz b3 ≠ 0`) — no runtime inputs. -/
theorem evm_div_n4_shiftNz_cert_of_shape_native (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4ShiftNzLaneRuntimeCertV5Native a b := by
  have hcall := isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hshift_nz
  by_cases hskip : isSkipBorrowN4CallV5
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  · exact Or.inl hskip
  · have hborrow_c := isAddbackBorrowN4CallV5_of_not_skipBorrow hskip
    have hborrow_e := isAddbackBorrowN4CallV5Evm_of_compose hborrow_c
    have hcarry2_e := n4CallAddbackBeqCarry2_of_borrow_gen hb3nz hshift_nz hcall hborrow_e
    have hsem := n4CallAddbackBeqSemanticHoldsV5_gen hb3nz hshift_nz hcall hborrow_e hcarry2_e
    have hcarry2_c := isAddbackCarry2NzN4CallV5_of_Evm hcarry2_e
    exact Or.inr ⟨hborrow_c, hcarry2_c, hsem⟩

end EvmAsm.Evm64
