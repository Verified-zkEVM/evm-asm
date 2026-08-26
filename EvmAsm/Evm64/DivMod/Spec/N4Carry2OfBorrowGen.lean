/-
  EvmAsm.Evm64.DivMod.Spec.N4Carry2OfBorrowGen

  U4-general n=4 v5 `h_carry2` (`isAddbackCarry2NzN4CallV5Evm`) from `h_borrow` +
  the n=4 shape — with NO `U4 = 0` restriction.

  U4-general counterpart of `n4CallAddbackBeqCarry2_of_borrow_and_u4_zero`
  (N4Carry2OfBorrow).  Routes the generic
  `isAddbackCarry2Nz_of_overestimate_c3_uTop_plus_one_of_carry_zero` (#7663) with:
  * the full-dividend `+2` overestimate `qHat ≤ qTrue + 2`
    (`n4CallAddbackBeqQHatV5_le_qTrue_plus_two_of_call`, #7573), rewritten to
    `qHat ≤ (U4·2^256 + val256 U)/BNormVal + 2` via
    `n4CallAddbackBeqNormalized_div_eq_qTrueV5`;
  * `c3 = U4 + 1` on borrow (`n4CallAddbackBeq_c3_eq_uTop_plus_one_of_borrow`, #7656).

  With this, all three semantic runtime conditions (`hq_over`, `h_carry2`,
  `h_rem_lt`) are discharged from `h_borrow` for ANY `U4`.  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4Carry2C3UTopPlusOne
public import EvmAsm.Evm64.DivMod.Spec.N4C3EqUTopPlusOne
public import EvmAsm.Evm64.DivMod.Spec.N4QHatBound
public import EvmAsm.Evm64.DivMod.Spec.N4Carry2OfNamed

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The n=4 v5 `h_carry2` condition follows from `h_borrow` for ANY `U4`. -/
theorem n4CallAddbackBeqCarry2_of_borrow_gen {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_borrow : isAddbackBorrowN4CallV5Evm a b) :
    isAddbackCarry2NzN4CallV5Evm a b := by
  apply isAddbackCarry2NzN4CallV5Evm_of_named
  apply isAddbackCarry2Nz_of_overestimate_c3_uTop_plus_one_of_carry_zero
  · exact n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz
  · have h := n4CallAddbackBeqQHatV5_le_qTrue_plus_two_of_call hb3nz hshift_nz hcall
    rw [← n4CallAddbackBeqNormalized_div_eq_qTrueV5 hshift_nz] at h
    unfold n4CallAddbackBeqUNormValV5 n4CallAddbackBeqBNormVal at h
    rw [show val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) +
          (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256 =
        (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256 +
          val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
            (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) from by ring] at h
    exact h
  · intro _
    have hb_raw := n4CallAddbackBeqBorrow_raw_of_runtimeV5 h_borrow
    have hc3 := n4CallAddbackBeq_c3_eq_uTop_plus_one_of_borrow hb3nz hshift_nz hcall hb_raw
    rw [hc3, BitVec.toNat_add, show (1 : Word).toNat = 1 from by decide]
    have := n4CallAddbackBeqU4_lt_pow63_of_shift_nz (a := a) hshift_nz
    omega

end EvmAsm.Evm64
