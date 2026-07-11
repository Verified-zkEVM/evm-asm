/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.CapBounds

  V5-specific upper bounds derived directly from the Phase-1a / Phase-2a
  cap structure. These are the foundational sub-2^32 bounds that v4's
  proofs had to derive carefully (giving ≤ 2^32, not <); V5 has them
  for free because the cap branch writes exactly 0xFFFFFFFF = 2^32 - 1.

  Bead `evm-asm-wbc4i.4.6.3` (V5.4.0.4). Prerequisite for V5.4.1, V5.4.4,
  V5.5.1, V5.5.2.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Algorithm
import EvmAsm.Rv64.AddrNorm

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Helper: `0xFFFFFFFF.toNat = 2^32 - 1`. Used by both Q1c and Q0c
    bound proofs. -/
private theorem v5_capCap_toNat :
    ((BitVec.allOnes 64) >>> (32 : BitVec 6).toNat : Word).toNat = 2^32 - 1 := by
  decide

/-- The DIVU result `q1 := rv64_divu uHi dHi` is bounded by `2^32` from
    the if-then-else branch in `algorithmQ1cV5` when `hi1 = 0`. -/
private theorem rv64_divu_lt_pow32_of_hi1_zero (uHi dHi : Word)
    (h : (rv64_divu uHi dHi) >>> (32 : BitVec 6).toNat = (0 : Word)) :
    (rv64_divu uHi dHi).toNat < 2^32 := by
  have hd : ((rv64_divu uHi dHi) >>> (32 : BitVec 6).toNat).toNat = 0 := by
    rw [h]; rfl
  rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32] at hd
  rw [Nat.shiftRight_eq_div_pow] at hd
  have : (rv64_divu uHi dHi).toNat / 2^32 = 0 := hd
  exact Nat.div_eq_zero_iff.mp this |>.resolve_left (by decide)

/-- Q1c is strictly less than 2^32 unconditionally under the V5 cap. -/
theorem algorithmQ1cV5_lt_pow32 (uHi vTop : Word) :
    (algorithmQ1cV5 uHi vTop).toNat < 2^32 := by
  rw [algorithmQ1cV5_unfold]
  by_cases h : (rv64_divu uHi (divKTrialCallV5DHi vTop)) >>> (32 : BitVec 6).toNat = (0 : Word)
  · simp only [h, if_true]
    exact rv64_divu_lt_pow32_of_hi1_zero _ _ h
  · simp only [h, if_false]
    rw [v5_capCap_toNat]
    omega

/-- Same for Q0c. -/
theorem algorithmQ0cV5_lt_pow32 (uHi uLo vTop : Word) :
    (algorithmQ0cV5 uHi uLo vTop).toNat < 2^32 := by
  rw [algorithmQ0cV5_unfold]
  by_cases h : (rv64_divu (divKTrialCallV5Un21 uHi uLo vTop)
                  (divKTrialCallV5DHi vTop)) >>> (32 : BitVec 6).toNat = (0 : Word)
  · simp only [h, if_true]
    exact rv64_divu_lt_pow32_of_hi1_zero _ _ h
  · simp only [h, if_false]
    rw [v5_capCap_toNat]
    omega

/-- Bridge: `divKTrialCallV5Q0c` (the irreducible) inherits Q0c's cap
    bound via the `_eq_algorithm` equation. -/
theorem divKTrialCallV5Q0c_lt_pow32 (uHi uLo vTop : Word) :
    (divKTrialCallV5Q0c uHi uLo vTop).toNat < 2^32 := by
  rw [divKTrialCallV5Q0c_eq_algorithm]
  exact algorithmQ0cV5_lt_pow32 uHi uLo vTop

end EvmAsm.Evm64
