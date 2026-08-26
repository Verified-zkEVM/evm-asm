/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.NoWrap

  No-wrap properties for the V5 cap-bounded multiplications: under
  `algorithmQ{1,0}cV5 < 2^32` (from `CapBounds`) and `dLo < 2^32`, the
  product `q*c * dLo` fits in BitVec 64 unconditionally.

  v4's `algorithmQ1dV4_dLo_no_wrap` (Phase1bBound.lean:1007) required
  `≤ 2^32 + 1` and a careful case-analysis; V5's bounds make this
  unconditional and trivial.

  Bead `evm-asm-wbc4i.4.6.4` (V5.4.0.5). Prerequisite for V5.4.1, V5.4.4.
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.CapBounds
public import EvmAsm.Evm64.EvmWordArith.Div128FinalAssembly

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 normalized `dLo = (vTop << 32) >> 32` is bounded by `2^32`.
    Mirrors the v4 lemma at `Phase1bBound.lean:138`. -/
theorem divKTrialCallV5DLo_lt_pow32 (vTop : Word) :
    (divKTrialCallV5DLo vTop).toNat < 2^32 := by
  unfold divKTrialCallV5DLo
  exact Word_ushiftRight_32_lt_pow32

/-- The v5 `un1 = uLo >> 32` is bounded by `2^32`. -/
theorem divKTrialCallV5Un1_lt_pow32 (uLo : Word) :
    (divKTrialCallV5Un1 uLo).toNat < 2^32 := by
  unfold divKTrialCallV5Un1
  exact Word_ushiftRight_32_lt_pow32

/-- The v5 `dHi = vTop >> 32` is bounded by `2^32`. -/
theorem divKTrialCallV5DHi_lt_pow32 (vTop : Word) :
    (divKTrialCallV5DHi vTop).toNat < 2^32 := by
  unfold divKTrialCallV5DHi
  exact Word_ushiftRight_32_lt_pow32

/-- The v5 `un0 = (uLo << 32) >> 32` is bounded by `2^32`. -/
theorem divKTrialCallV5Un0_lt_pow32 (uLo : Word) :
    (divKTrialCallV5Un0 uLo).toNat < 2^32 := by
  unfold divKTrialCallV5Un0
  exact Word_ushiftRight_32_lt_pow32

/-- `Q1c * dLo` does not wrap mod 2^64 under the V5 cap. Strictly
    tighter than v4's analog (no hypothesis on `vTop`). -/
theorem algorithmQ1cV5_dLo_no_wrap (uHi vTop : Word) :
    (algorithmQ1cV5 uHi vTop * divKTrialCallV5DLo vTop).toNat =
      (algorithmQ1cV5 uHi vTop).toNat * (divKTrialCallV5DLo vTop).toNat := by
  rw [BitVec.toNat_mul]
  apply Nat.mod_eq_of_lt
  have h_q := algorithmQ1cV5_lt_pow32 uHi vTop
  have h_d := divKTrialCallV5DLo_lt_pow32 vTop
  have : (algorithmQ1cV5 uHi vTop).toNat * (divKTrialCallV5DLo vTop).toNat <
      2^32 * 2^32 := Nat.mul_lt_mul'' h_q h_d
  calc (algorithmQ1cV5 uHi vTop).toNat * (divKTrialCallV5DLo vTop).toNat
      < 2^32 * 2^32 := this
    _ = 2^64 := by norm_num

/-- `Q0c * dLo` does not wrap mod 2^64 under the V5 cap. -/
theorem algorithmQ0cV5_dLo_no_wrap (uHi uLo vTop : Word) :
    (algorithmQ0cV5 uHi uLo vTop * divKTrialCallV5DLo vTop).toNat =
      (algorithmQ0cV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat := by
  rw [BitVec.toNat_mul]
  apply Nat.mod_eq_of_lt
  have h_q := algorithmQ0cV5_lt_pow32 uHi uLo vTop
  have h_d := divKTrialCallV5DLo_lt_pow32 vTop
  have : (algorithmQ0cV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat <
      2^32 * 2^32 := Nat.mul_lt_mul'' h_q h_d
  calc (algorithmQ0cV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat
      < 2^32 * 2^32 := this
    _ = 2^64 := by norm_num

/-- Bridge to the V5 irreducible family: `Q0c * dLo` no-wrap via
    `divKTrialCallV5Q0c_eq_algorithm`. -/
theorem divKTrialCallV5Q0c_dLo_no_wrap (uHi uLo vTop : Word) :
    (divKTrialCallV5Q0c uHi uLo vTop * divKTrialCallV5DLo vTop).toNat =
      (divKTrialCallV5Q0c uHi uLo vTop).toNat *
        (divKTrialCallV5DLo vTop).toNat := by
  rw [divKTrialCallV5Q0c_eq_algorithm]
  exact algorithmQ0cV5_dLo_no_wrap uHi uLo vTop

end EvmAsm.Evm64
