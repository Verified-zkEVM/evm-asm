/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.V4QHatBoundCounterexamples

  Kernel-checked counterexamples refuting the Knuth-A `+1` bound on
  `div128Quot_v4` (bead `evm-asm-9iqmw.7.1.4.1`) AND demonstrating that
  `div128Quot_v4` can significantly UNDERSHOOT the true quotient.

  Found by a python search of the wide-uHi+wide-rhatc regime (2,000,000
  trials):
    * Max overshoot:  +2  (bead 7.1.4.1 target was +1 — REFUTED)
    * Max undershoot: -8480520837 ≈ -1.97 * 2^32

  These witnesses establish that the correct unconditional bound for
  `div128Quot_v4` is `qHat ≤ q_true + 2` (Knuth-B), NOT `qHat ≤ q_true + 1`
  (Knuth-A).  The buggy ULTs inside Phase-1b and Phase-2 (which truncate
  to low 32 bits) prevent the 2-correction design from delivering the
  Knuth-A guarantee.

  In the undershoot direction, the existing unconditional `Q1dd ≤ q_true_1`
  UB (which gives `qHat = (Q1dd<<32)|Q0dd ≤ q_true + 2` in
  combination with `Q0dd < 2^33`) is not symmetric — there is no
  unconditional LB `qHat ≥ q_true`.  The undershoot regime is the
  same regime where bead `7.1.4.1.9` (PR #7077) showed `un21 ≥ vTop`:
  Q1dd undershoots q_true_high by up to 2, and Phase-2 doesn't fully
  compensate.

  Companion to `Un21WideUHiCounterexample.lean` (PR #7077) and
  `Q1ddUndershootFromWideUn21.lean` (PR #7079).
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.TrialCall
public import EvmAsm.Evm64.DivMod.LoopDefs.IterV4

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Overshoot witness inputs: `div128Quot_v4 = q_true + 2`. -/
abbrev cePlus2_uHi : Word := BitVec.ofNat 64 0x928ED4518F7DD083
abbrev cePlus2_uLo : Word := BitVec.ofNat 64 0xC3887FC013FF1573
abbrev cePlus2_vTop : Word := BitVec.ofNat 64 0x928ED451C34118C1

/-- Normalisation holds for the overshoot witness. -/
theorem cePlus2_vTop_ge_pow63 : cePlus2_vTop.toNat ≥ 2^63 := by decide

/-- Call regime holds for the overshoot witness. -/
theorem cePlus2_uHi_lt_vTop : cePlus2_uHi.toNat < cePlus2_vTop.toNat := by decide

/-- **Bead 7.1.4.1 refutation.** Under just normalisation + call regime,
    `div128Quot_v4` can exceed the true quotient by `2`, refuting the
    Knuth-A `+1` bound. -/
theorem cePlus2_div128Quot_v4_eq_q_true_plus_two :
    (div128Quot_v4 cePlus2_uHi cePlus2_uLo cePlus2_vTop).toNat =
      (cePlus2_uHi.toNat * 2^64 + cePlus2_uLo.toNat) / cePlus2_vTop.toNat + 2 :=
  by decide

/-- `div128Quot_v4` is NOT bounded by `q_true + 1` (Knuth-A) under just
    normalisation + call regime.  The correct unconditional bound is
    `q_true + 2` (Knuth-B). -/
theorem div128Quot_v4_not_le_q_true_plus_one_under_normalisation :
    ∃ uHi uLo vTop : Word,
      vTop.toNat ≥ 2^63 ∧
      uHi.toNat < vTop.toNat ∧
      ¬ ((div128Quot_v4 uHi uLo vTop).toNat ≤
          (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1) :=
  ⟨cePlus2_uHi, cePlus2_uLo, cePlus2_vTop,
    cePlus2_vTop_ge_pow63,
    cePlus2_uHi_lt_vTop,
    by
      have h := cePlus2_div128Quot_v4_eq_q_true_plus_two
      omega⟩

/-- Undershoot witness inputs: `div128Quot_v4 < q_true` by ≈ 2*2^32. -/
abbrev ceUnd_uHi : Word := BitVec.ofNat 64 0x81A6C3EA81786CF7
abbrev ceUnd_uLo : Word := BitVec.ofNat 64 0xAB97850C4B79C4F7
abbrev ceUnd_vTop : Word := BitVec.ofNat 64 0x81A6C3EA83EB4E16

/-- Normalisation holds for the undershoot witness. -/
theorem ceUnd_vTop_ge_pow63 : ceUnd_vTop.toNat ≥ 2^63 := by decide

/-- Call regime holds for the undershoot witness. -/
theorem ceUnd_uHi_lt_vTop : ceUnd_uHi.toNat < ceUnd_vTop.toNat := by decide

/-- **Undershoot witness.** `div128Quot_v4 + 8480520837 = q_true`,
    i.e., `div128Quot_v4` is approximately `1.97 * 2^32` BELOW the
    true quotient.  Demonstrates that there is no unconditional
    `div128Quot_v4 ≥ q_true - C` bound for small `C`. -/
theorem ceUnd_div128Quot_v4_plus_gap_eq_q_true :
    (div128Quot_v4 ceUnd_uHi ceUnd_uLo ceUnd_vTop).toNat + 8480520837 =
      (ceUnd_uHi.toNat * 2^64 + ceUnd_uLo.toNat) / ceUnd_vTop.toNat :=
  by decide

/-- `div128Quot_v4` is NOT bounded below by `q_true - 2^32` (or any small
    constant) under just normalisation + call regime. The actual undershoot
    can be approximately `2 * 2^32`. -/
theorem div128Quot_v4_not_ge_q_true_minus_pow32_under_normalisation :
    ∃ uHi uLo vTop : Word,
      vTop.toNat ≥ 2^63 ∧
      uHi.toNat < vTop.toNat ∧
      (div128Quot_v4 uHi uLo vTop).toNat + 2^32 <
        (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat :=
  ⟨ceUnd_uHi, ceUnd_uLo, ceUnd_vTop,
    ceUnd_vTop_ge_pow63,
    ceUnd_uHi_lt_vTop,
    by
      have h := ceUnd_div128Quot_v4_plus_gap_eq_q_true
      omega⟩

/-- Empirical observation pinned: `qHat ≤ q_true + 2` is the correct
    unconditional bound for the overshoot witness.  This matches the
    pre-existing `div128Quot_v4_counterexampleA_within_two_addbacks`
    style of bound from `EvmAsm.Evm64.DivMod.Counterexamples`. -/
theorem cePlus2_div128Quot_v4_le_q_true_plus_two :
    (div128Quot_v4 cePlus2_uHi cePlus2_uLo cePlus2_vTop).toNat ≤
      (cePlus2_uHi.toNat * 2^64 + cePlus2_uLo.toNat) / cePlus2_vTop.toNat + 2 :=
  by
    have h := cePlus2_div128Quot_v4_eq_q_true_plus_two
    omega

end EvmAsm.Evm64
