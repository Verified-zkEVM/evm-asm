/-
  EvmAsm.Evm64.DivMod.Spec.N4Carry2OfBorrow

  The n=4 v5 `h_carry2` runtime condition (`isAddbackCarry2NzN4CallV5Evm`) from the
  `h_borrow` runtime condition, under `U4 = 0`.

  Chain (all proven): the borrow `isAddbackBorrowN4CallV5Evm` gives `U4 < c3`
  (`n4CallAddbackBeqBorrow_raw_of_runtimeV5`), hence `c3 ≠ 0`; with the `+1`
  trial bound under `U4 = 0` (`n4CallAddbackBeqQHatV5_le_window_div_plus_one_of_u4_zero`,
  #7579), `mulsubN4_c3_ne_zero_imp_one` pins `c3 = 1`; the generic
  `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero` (with the `+2` weakened
  from the `+1`) then gives the named `isAddbackCarry2Nz`, and the reverse bridge
  `isAddbackCarry2NzN4CallV5Evm_of_named` (#7578) packages it as the runtime
  predicate.

  This collapses the n=4 v5 semantic's `h_carry2` (and `hq_over`, `h_rem_lt`) so that,
  under `U4 = 0`, the only remaining runtime input is `h_borrow` itself (plus the
  dispatcher routing that establishes `U4 = 0` / `h_borrow`).  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N4Carry2OfNamed
public import EvmAsm.Evm64.DivMod.Spec.N4QHatLeOne

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Under `U4 = 0`, the n=4 v5 `h_carry2` condition follows from `h_borrow`. -/
theorem n4CallAddbackBeqCarry2_of_borrow_and_u4_zero {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hu4 : (n4CallAddbackBeqU4 a b).toNat = 0)
    (h_borrow : isAddbackBorrowN4CallV5Evm a b) :
    isAddbackCarry2NzN4CallV5Evm a b := by
  apply isAddbackCarry2NzN4CallV5Evm_of_named
  apply isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero
  · exact n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz
  · exact le_trans (n4CallAddbackBeqQHatV5_le_window_div_plus_one_of_u4_zero hb3nz hu4)
      (by omega)
  · intro _
    have hborrow_raw := n4CallAddbackBeqBorrow_raw_of_runtimeV5 h_borrow
    have hc3_nz :
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b)
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2 ≠ 0 := by
      intro h0
      rw [h0] at hborrow_raw
      have : ¬ BitVec.ult (n4CallAddbackBeqU4 a b) (0 : Word) := by
        rw [BitVec.ult_eq_decide]; simp
      exact this hborrow_raw
    exact mulsubN4_c3_ne_zero_imp_one
      (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)
      (n4CallAddbackBeqQHatV5_le_window_div_plus_one_of_u4_zero hb3nz hu4)
      hc3_nz

end EvmAsm.Evm64
