/-
  EvmAsm.Evm64.DivMod.Spec.N1V5Shift0LaneFirstDigit

  First-digit loop conditions for the v5 n=1 **shift=0** lane.  On the shift=0
  branch the loop runs at `v = (b0, 0, 0, 0)`, `u0 = a3`, `u1 = u2 = u3 = uTop = 0`
  (the copy-AU layout; see `N1V5Shift0Bounds`), with the already-normalized
  single-limb divisor `b0 ≥ 2^63`.

  The top-digit (`j=3`) `bltu` and `no-borrow` hypotheses of
  `divK_loop_n1_call_unified_v5_spec_within_noNop` then follow directly from the
  generic single-limb cores (`iterN1V5_true_remainder_lt_of_v0_norm_call`,
  `mulsubN4NoBorrow_div128Quot_v5_of_norm_call`), which need only `v0 ≥ 2^63` and
  `uTop < v0` — both supplied by `b0_ge_pow63_of_clz_zero`.  Shift=0 counterparts
  of `n1v5_lane_bltu_3/2_of_shape` and `n1v5_lane_hborrow_3_of_shape`.  Bead
  `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Bounds
public import EvmAsm.Evm64.DivMod.Spec.N1V5LaneBltu
public import EvmAsm.Evm64.DivMod.Spec.N1V5LaneHborrow

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- shift=0 first digit `0 < b0.toNat` helper. -/
private theorem b0_toNat_pos_of_clz_zero (b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    (0 : Word).toNat < b0.toNat := by
  have h := b0_ge_pow63_of_clz_zero b0 hb0nz hclz
  have hz : (0 : Word).toNat = 0 := by decide
  omega

/-- n=1 shift=0 lane, `j=3` (top digit) `bltu`: `u1 = 0 < v0 = b0`. -/
theorem n1v5_shift0_lane_bltu_3 (b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    BitVec.ult (0 : Word) b0 :=
  zero_ult_b0_of_clz_zero b0 hb0nz hclz

/-- n=1 shift=0 lane, `j=2` `bltu`: the top-digit remainder's low limb `< b0`. -/
theorem n1v5_shift0_lane_bltu_2 (a3 b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    BitVec.ult (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.1 b0 := by
  apply n1v5_bltu_limb0_of_val256_lt
  rw [← iterN1V5_true]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call b0 a3 0
    (b0_ge_pow63_of_clz_zero b0 hb0nz hclz)
    (b0_toNat_pos_of_clz_zero b0 hb0nz hclz)

/-- n=1 shift=0 lane, `j=3` (top digit) no-borrow: the single-limb mulsub for
    the first trial leaves no top borrow. -/
theorem n1v5_shift0_lane_hborrow_3 (a3 b0 : Word) (hb0nz : b0 ≠ 0)
    (hclz : (clzResult b0).1 = 0) :
    mulsubN4NoBorrow (divKTrialCallV5QHat 0 a3 b0) b0 0 0 0 a3 0 0 0 0 := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  exact mulsubN4NoBorrow_div128Quot_v5_of_norm_call b0 a3 0 0
    (b0_ge_pow63_of_clz_zero b0 hb0nz hclz)
    (b0_toNat_pos_of_clz_zero b0 hb0nz hclz)

end EvmAsm.Evm64
