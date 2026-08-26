/-
  EvmAsm.Evm64.EvmWordArith.DivKnuthATopWindowFits

  Generalised structural discharge of `Knuth128_64TopWindowLeVal256DivPlusOne`
  beyond the existing trivial "equal-window" case (`DivKnuthAEqualWindow`).

  The existing `Knuth128_64TopWindowLeVal256DivPlusOne_of_eq_window` (PR #7045)
  discharges the predicate when `val256(u) = uHi*2^64 + uLo` AND
  `val256(v) = vTop` — i.e., u and v are both *exactly* their top-window
  values, with no lower limbs.

  This file generalises the `u`-side condition: the predicate still holds
  when `val256(u)` is at least `(uHi*2^64 + uLo) * 2^128` — i.e., the top
  window FITS as the high half of `val256(u)`, possibly with arbitrary
  lower bits.  This is more aligned with typical algorithm states where
  the dividend has non-trivial low limbs below the trial top window.

  The `v`-side condition `val256(v) = vTop` is retained.  Generalising
  both sides simultaneously is the open Knuth-A val256 frontier (bead
  `7.1.4.1` and adjacent) and requires the full classical Knuth Theorem A
  argument with the algorithm-state structural relationship.

  Also exports the natural composition with
  `DivKTrialCallV4QHatLeFloorPlusOne_of_exact` to produce the
  `divKTrialCallV4QHat ≤ val256(u)/val256(v) + 2` overestimate consumed
  by the BLT-path bridges, under the same structural conditions.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivV4TrialFromExactQuotient
public import EvmAsm.Evm64.EvmWordArith.DivV4TrialVal256Composition

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Discharge `Knuth128_64TopWindowLeVal256DivPlusOne` when the 128-bit top
    window `(uHi, uLo)` fits as the high half of `val256(u)` (with any
    lower bits) and `val256(v) = vTop`.

    Strictly generalises `Knuth128_64TopWindowLeVal256DivPlusOne_of_eq_window`:
    the `u_eq` premise `val256(u) = uHi*2^64 + uLo` is replaced with the
    looser `(uHi*2^64 + uLo) * 2^128 ≤ val256(u)`. -/
theorem Knuth128_64TopWindowLeVal256DivPlusOne_of_top_window_fits_val256_and_v_eq_vTop
    (uHi uLo vTop : Word) (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (h_v_eq : val256 v0 v1 v2 v3 = vTop.toNat)
    (h_u_fits : (uHi.toNat * 2^64 + uLo.toNat) * 2^128 ≤ val256 u0 u1 u2 u3) :
    Knuth128_64TopWindowLeVal256DivPlusOne uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 := by
  unfold Knuth128_64TopWindowLeVal256DivPlusOne
  rw [h_v_eq]
  set U := uHi.toNat * 2^64 + uLo.toNat with hU_def
  set valU := val256 u0 u1 u2 u3 with hvalU_def
  -- Goal: U / vTop.toNat ≤ valU / vTop.toNat + 1
  by_cases hvTop_pos : vTop.toNat = 0
  · -- Both sides reduce: U / 0 = 0 and valU / 0 = 0, so 0 ≤ 0 + 1.
    rw [hvTop_pos]
    simp [Nat.div_zero]
  · -- vTop > 0.  We show U ≤ valU / vTop and then U/vTop ≤ U.
    have hvTop_pos' : 0 < vTop.toNat := Nat.pos_of_ne_zero hvTop_pos
    have hvTop_lt_pow64 : vTop.toNat < 2^64 := vTop.isLt
    -- Step 1: U * vTop ≤ U * 2^128 (since vTop < 2^64 ≤ 2^128).
    have hvTop_le_pow128 : vTop.toNat ≤ 2^128 := by
      have h64_le_128 : (2 : Nat)^64 ≤ 2^128 := by decide
      omega
    have h_U_vTop_le_U_pow128 : U * vTop.toNat ≤ U * 2^128 :=
      Nat.mul_le_mul_left U hvTop_le_pow128
    -- Step 2: U * 2^128 ≤ valU (the hypothesis).
    have h_U_pow128_le_valU : U * 2^128 ≤ valU := h_u_fits
    -- Step 3: chain: U * vTop ≤ valU.
    have h_U_vTop_le_valU : U * vTop.toNat ≤ valU :=
      le_trans h_U_vTop_le_U_pow128 h_U_pow128_le_valU
    -- Step 4: U ≤ valU / vTop (since vTop > 0).
    have h_U_le_valU_div : U ≤ valU / vTop.toNat :=
      (Nat.le_div_iff_mul_le hvTop_pos').2 h_U_vTop_le_valU
    -- Step 5: U / vTop ≤ U (since vTop ≥ 1).
    have h_U_div_le_U : U / vTop.toNat ≤ U := Nat.div_le_self U vTop.toNat
    -- Combine and add 1.
    omega

/-- End-to-end `+2` val256-overestimate of `divKTrialCallV4QHat` under the
    "exact-trial" + "top-window-fits-val256(u)" + "val256(v) = vTop"
    structural conditions.

    Generalises `divKTrialCallV4QHat_le_val256_div_plus_two_of_exact_and_eq_window`
    (PR #7054): the `u_eq` premise is replaced with the looser
    `top_window_fits_val256` condition, so the lemma applies to algorithm
    states where the dividend has non-trivial low limbs below the trial
    top window. -/
theorem divKTrialCallV4QHat_le_val256_div_plus_two_of_exact_and_top_window_fits_v_eq_vTop
    (uHi uLo vTop : Word) (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (h_exact : (divKTrialCallV4QHat uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat)
    (h_v_eq : val256 v0 v1 v2 v3 = vTop.toNat)
    (h_u_fits : (uHi.toNat * 2^64 + uLo.toNat) * 2^128 ≤ val256 u0 u1 u2 u3) :
    (divKTrialCallV4QHat uHi uLo vTop).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2 :=
  divKTrialCallV4QHat_le_val256_div_plus_two uHi uLo vTop
    v0 v1 v2 v3 u0 u1 u2 u3
    (DivKTrialCallV4QHatLeFloorPlusOne_of_exact uHi uLo vTop h_exact)
    (Knuth128_64TopWindowLeVal256DivPlusOne_of_top_window_fits_val256_and_v_eq_vTop
      uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 h_v_eq h_u_fits)

end EvmAsm.Evm64
