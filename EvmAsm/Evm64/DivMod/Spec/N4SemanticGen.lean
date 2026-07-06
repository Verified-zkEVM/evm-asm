/-
  EvmAsm.Evm64.DivMod.Spec.N4SemanticGen

  The U4-general n=4 v5 call-addback semantic `n4CallAddbackBeqSemanticHoldsV5`
  (`qOut = qTrue`), from the n=4 shape + the runtime borrow/carry2 conditions —
  with NO `U4 = 0` restriction.

  Assembly:
  * `U4 = 0`  → existing single-addback chain
    `n4CallAddbackBeqSemanticHoldsV5_of_borrow_u4_zero` (#7580);
  * `U4 ≥ 1`  → `qHat ≥ 2` (#7658) feeds the U4-general conservation
    `n4CallAddbackBeqQOutV5_conservation_compact_gen` (#7657)
    (`UNormVal = QOut·BNorm + R`), and the U4-general borrow remainder bound
    `iterWithDoubleAddback_borrow_remainder_lt_gen` (#7659) gives `R < BNorm`;
    Euclidean uniqueness (`quotient_eq_div_of_mul_add_remainder_lt`) then yields
    `QOut = UNormVal / BNormVal`, which is `qTrue` by
    `n4CallAddbackBeqNormalized_div_eq_qTrueV5`.

  This removes the `U4 = 0` gate on the n=4 addback semantic — the last piece of
  the addback-half math.  Bead `evm-asm-wbc4i.8.2.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N4QHatGeTwo
import EvmAsm.Evm64.DivMod.Spec.N4QOutConservationGen
import EvmAsm.Evm64.EvmWordArith.DivN4BorrowRemainderLtGen
import EvmAsm.Evm64.DivMod.Spec.N4SemanticOfBorrow

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- U4-general borrow remainder bound in the folded n=4 form (wrapper over #7659).
    `unfold` (delta, no whnf evaluation) bridges the def to the explicit iterate. -/
theorem n4CallAddbackBeqIterRNormVal_lt_BNormVal_gen {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    n4CallAddbackBeqIterRNormValV5 a b < n4CallAddbackBeqBNormVal b := by
  have hb_raw := n4CallAddbackBeqBorrow_raw_of_runtimeV5 h_borrow
  have hc3 := n4CallAddbackBeq_c3_eq_uTop_plus_one_of_borrow hb3nz hshift_nz hcall hb_raw
  have hcarry2g := n4CallAddbackBeqCarry2Nz_of_runtimeV5 h_carry2
  have hrem := iterWithDoubleAddback_borrow_remainder_lt_gen
    (n4CallAddbackBeqQHatV5 a b)
    (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqU4 a b) hb_raw hc3 hcarry2g
  simp only [] at hrem
  unfold n4CallAddbackBeqIterRNormValV5 n4CallAddbackBeqIterOutV5 n4CallAddbackBeqBNormVal
  exact hrem

/-- U4 ≥ 1 addback semantic: `qOut = qTrue`. -/
theorem n4CallAddbackBeqSemanticHoldsV5_of_u4_pos {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hu4_pos : 1 ≤ (n4CallAddbackBeqU4 a b).toNat)
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    n4CallAddbackBeqSemanticHoldsV5 a b := by
  have hq2 := n4CallAddbackBeqQHatV5_ge_two_of_u4_pos hb3nz hshift_nz hcall hu4_pos h_borrow
  have hcons := n4CallAddbackBeqQOutV5_conservation_compact_gen
    hb3nz hshift_nz hcall h_borrow h_carry2 hq2
  have hBpos : 0 < n4CallAddbackBeqBNormVal b := by
    simpa [n4CallAddbackBeqBNormVal] using n4CallAddbackBeqNormalizedDivisor_pos hb3nz
  have hrem' := n4CallAddbackBeqIterRNormVal_lt_BNormVal_gen
    hb3nz hshift_nz hcall h_borrow h_carry2
  have hqout := quotient_eq_div_of_mul_add_remainder_lt hBpos hcons hrem'
  show (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b
  rw [hqout, n4CallAddbackBeqNormalized_div_eq_qTrueV5 hshift_nz]

/-- U4-general n=4 v5 call-addback semantic, no `U4 = 0` restriction. -/
theorem n4CallAddbackBeqSemanticHoldsV5_gen {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    n4CallAddbackBeqSemanticHoldsV5 a b := by
  by_cases hu4 : (n4CallAddbackBeqU4 a b).toNat = 0
  · exact n4CallAddbackBeqSemanticHoldsV5_of_borrow_u4_zero hb3nz hshift_nz hu4 h_borrow
  · exact n4CallAddbackBeqSemanticHoldsV5_of_u4_pos hb3nz hshift_nz hcall (by omega)
      h_borrow h_carry2

/-- Runtime-condition semantic bridge with the v5 trial-bound obligations
    discharged by the U4-general n=4 addback argument. -/
theorem n4CallAddbackBeqSemanticHoldsV5_of_runtime_conditions {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    n4CallAddbackBeqSemanticHoldsV5 a b :=
  n4CallAddbackBeqSemanticHoldsV5_gen hb3nz hshift_nz hcall h_borrow h_carry2

end EvmAsm.Evm64
