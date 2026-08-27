/-
  EvmAsm.Evm64.DivMod.Spec.N4C3EqUTopPlusOne

  Discharges the `hc3_of_borrow` obligation of the U4-general
  `iterWithDoubleAddback_val256_conservation_gen` (#7653) for the n=4 v5 call path:
  on the borrow branch (`U4 < c3`), the four-limb mulsub borrow is exactly
  `c3 = U4 + 1`.

  Two steps:
  * `n4CallAddbackBeqQHatV5_mul_B3Prime_le_topwindow`: `qHat·B3' ≤ U4·2^64 + U3`,
    because the v5 trial `qHat` is the FLOOR of the top window
    (`divKTrialCallV5QHat_eq_floor` + `Nat.div_mul_le_self`).
  * feeding that to the tight borrow bound `mulsubN4_c3_le_uTop_plus_one` (#7654)
    gives `c3 ≤ U4 + 1`; with the borrow `U4 < c3` and `U4 < 2^63` (so no wrap),
    `c3 = U4 + 1`.

  This is the last deferred premise of the U4-general n=4 conservation.
  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivN4C3LeUTopPlusOne
public import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntime
public import EvmAsm.Evm64.DivMod.Spec.CallAddbackV5
public import EvmAsm.Evm64.EvmWordArith.DivV5TrialOverestimate

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The v5 trial quotient is the floor of the top window, so `qHat·B3' ≤ U4·2^64 + U3`. -/
theorem n4CallAddbackBeqQHatV5_mul_B3Prime_le_topwindow {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (n4CallAddbackBeqQHatV5 a b).toNat * (n4CallAddbackBeqB3Prime b).toNat ≤
      (n4CallAddbackBeqU4 a b).toNat * 2 ^ 64 + (n4CallAddbackBeqU3 a b).toNat := by
  have hB3 : (n4CallAddbackBeqB3Prime b).toNat ≥ 2 ^ 63 :=
    n4CallAddbackBeqB3Prime_ge_pow63 hb3nz
  have hu4_lt : (n4CallAddbackBeqU4 a b).toNat < (n4CallAddbackBeqB3Prime b).toNat := by
    have h_decomp := n4CallAddbackBeqU4_lt_vTop_of_call hcall
    rw [div128Quot_vTop_decomp (n4CallAddbackBeqB3Prime b)]
    simpa [divKTrialCallV4DHi, divKTrialCallV4DLo] using h_decomp
  rw [n4CallAddbackBeqQHatV5_eq_normalized, ← divKTrialCallV5QHat_eq_div128Quot_v5,
    divKTrialCallV5QHat_eq_floor _ _ _ hB3 hu4_lt]
  exact Nat.div_mul_le_self _ _

/-- On the borrow branch (`U4 < c3`), the n=4 v5 mulsub borrow is exactly `U4 + 1`.
    This is the `hc3_of_borrow` premise of `iterWithDoubleAddback_val256_conservation_gen`. -/
theorem n4CallAddbackBeq_c3_eq_uTop_plus_one_of_borrow {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    BitVec.ult (n4CallAddbackBeqU4 a b)
        (mulsubN4 (n4CallAddbackBeqQHatV5 a b)
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2 →
      (mulsubN4 (n4CallAddbackBeqQHatV5 a b)
          (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2 =
        n4CallAddbackBeqU4 a b + 1 := by
  intro hborrow
  have hc3_le := mulsubN4_c3_le_uTop_plus_one (n4CallAddbackBeqQHatV5 a b)
    (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqU4 a b)
    (n4CallAddbackBeqQHatV5_mul_B3Prime_le_topwindow hb3nz hcall)
  have hbt : (n4CallAddbackBeqU4 a b).toNat <
      (mulsubN4 (n4CallAddbackBeqQHatV5 a b)
        (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
        (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2.toNat := by
    rw [EvmWord.ult_iff] at hborrow; exact hborrow
  have hu4_small : (n4CallAddbackBeqU4 a b).toNat < 2 ^ 63 :=
    n4CallAddbackBeqU4_lt_pow63_of_shift_nz hshift_nz
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from by decide]
  omega

end EvmAsm.Evm64
