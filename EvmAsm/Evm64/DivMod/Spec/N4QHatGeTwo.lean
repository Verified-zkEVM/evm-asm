/-
  EvmAsm.Evm64.DivMod.Spec.N4QHatGeTwo

  On the U4 ≥ 1 addback (borrow) branch, the n=4 v5 trial quotient satisfies
  `qHat ≥ 2` — the remaining `hq_ge_2` premise of the U4-general conservation
  `n4CallAddbackBeqQOutV5_conservation_compact_gen` (#7657).

  Argument: with `U4 ≥ 1`, `UNormVal ≥ 2^256 > BNormVal`, so `qTrue := UNormVal /
  BNormVal ≥ 1`.  On borrow, `c3 = U4 + 1` (#7656); the mulsub identity then gives
  `qHat·BNormVal = UNormVal + 2^256 - MR > UNormVal ≥ qTrue·BNormVal`, hence
  `qHat > qTrue ≥ 1`, i.e. `qHat ≥ 2`.

  (The `U4 = 0` branch has `qHat ≤ 1` and is handled by the existing
  single-addback chain `N4SemanticOfBorrow`.)
  Bead `evm-asm-wbc4i.8.2.2`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N4C3EqUTopPlusOne
public import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeV5

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- On the U4 ≥ 1 borrow branch, `qHat ≥ 2`. -/
theorem n4CallAddbackBeqQHatV5_ge_two_of_u4_pos {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hu4_pos : 1 ≤ (n4CallAddbackBeqU4 a b).toNat)
    (h_borrow : isAddbackBorrowN4CallV5Evm a b) :
    2 ≤ (n4CallAddbackBeqQHatV5 a b).toNat := by
  have hb_raw := n4CallAddbackBeqBorrow_raw_of_runtimeV5 h_borrow
  have hc3 := n4CallAddbackBeq_c3_eq_uTop_plus_one_of_borrow hb3nz hshift_nz hcall hb_raw
  have hu4_small := n4CallAddbackBeqU4_lt_pow63_of_shift_nz (a := a) hshift_nz
  have hid := mulsubN4_val256_eq (n4CallAddbackBeqQHatV5 a b)
    (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)
  simp only [] at hid
  set ms := mulsubN4 (n4CallAddbackBeqQHatV5 a b)
    (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) with hmsdef
  -- c3.toNat = U4.toNat + 1.
  have hc3t : ms.2.2.2.2.toNat = (n4CallAddbackBeqU4 a b).toNat + 1 := by
    rw [hc3, BitVec.toNat_add, show (1 : Word).toNat = 1 from by decide]; omega
  rw [hc3t, Nat.add_mul, Nat.one_mul] at hid
  -- bounds.
  have hMR : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2 ^ 256 := val256_bound _ _ _ _
  have hB_pos : 0 < val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) :=
    n4CallAddbackBeqNormalizedDivisor_pos hb3nz
  have hB_lt : val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) < 2 ^ 256 :=
    val256_bound _ _ _ _
  -- D := val256 U + U4*2^256 ; D ≥ 2^256 ≥ B, so qTrue := D/B ≥ 1.
  have hu4m : 2 ^ 256 ≤ (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256 := by
    calc 2 ^ 256 = 1 * 2 ^ 256 := by ring
      _ ≤ (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256 := Nat.mul_le_mul_right _ hu4_pos
  have hD_ge_B : val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) ≤
      val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) +
        (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256 := by omega
  have hqT_ge1 : 1 ≤
      (val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) +
        (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256) /
      val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) :=
    (Nat.one_le_div_iff hB_pos).mpr hD_ge_B
  have hqT_mul := Nat.div_mul_le_self
    (val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) +
      (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256)
    (val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b))
  -- qHat·B > D  (from hid + MR < 2^256).
  have hqhat_gt :
      val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) +
        (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256 <
      (n4CallAddbackBeqQHatV5 a b).toNat *
        val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) := by
    linarith [hid, hMR]
  have hmul_lt :
      (val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) +
        (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256) /
      val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) *
      val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) <
      (n4CallAddbackBeqQHatV5 a b).toNat *
        val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) := by
    omega
  have hqT_lt := Nat.lt_of_mul_lt_mul_right hmul_lt
  omega

end EvmAsm.Evm64
