/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21WideUHiCounterexample

  Kernel-checked counterexample: `divKTrialCallV4Un21 uHi uLo vTop < vTop`
  does NOT hold under just `vTop ≥ 2^63` and `uHi < vTop`. The conjecture
  fails specifically in the wide-uHi + wide-rhatc regime, where the
  Phase-1b 1st-correction ULT uses only the low 32 bits of `rhatc` and
  over-corrects `q1c` to `q_true_1 - 1`. The resulting `un21` exceeds
  `vTop` by `2^34 - 1`.

  This pins the negative answer to bead `evm-asm-9iqmw.7.1.4.1.9`:
  there is no `divKTrialCallV4Un21_lt_vTop_of_normalisation_and_call`
  lemma; the un21<vTop case-split inside bead `7.1.4.1` must dispatch
  the wide-uHi+wide-rhatc regime separately (the `un21 ≥ vTop` branch).

  Concrete witness:
    uHi  = 0x80000002_80000000 = 2^63 + 2^33 + 2^31
    uLo  = 0
    vTop = 0x80000002_FFFFFFFF = 2^63 + 2^33 + 2^32 - 1
  ⇒ dHi  = 0x80000002 = 2^31 + 2 (> 2^31, so wide rhatc possible)
    dLo  = 0xFFFFFFFF = 2^32 - 1
    q_true_1 = 2^32 - 1
    q1 = 2^32, rhat = 2^31, hi1 = 1 (wide uHi triggers Phase-1a correction)
    q1c = 2^32 - 1 (= q_true_1), rhatc = 2^32 + 2 (wide rhatc)
    buggy ULT fires: (rhatc % 2^32) * 2^32 + un1 = 2^33 < q1c*dLo ≈ 2^64
    But real check would have rhatc * 2^32 + un1 ≈ 2^64 + 2^33 ≥ q1c*dLo.
    Over-correction: q1' = q1c - 1 = q_true_1 - 1 = 2^32 - 2.
    rhat' = rhatc + dHi = 2^32 + 2^31 + 4 (still > 2^32, so Phase-1b 2nd
    correction guard `rhat' >> 32 = 0` fails).
    Q1dd = q1' = 2^32 - 2 (undershoot by 1).
    Rhatdd = rhat' = 2^32 + 2^31 + 4.
    un21 = (Rhatdd << 32 | un1) - Q1dd*dLo
         = (2^31 + 4) * 2^32 - (2^32 - 2)*(2^32 - 1)
         = 2^63 + 2^34 - (2^64 - 3*2^32 + 2)  (wraps mod 2^64)
         = 2^63 + 7*2^32 - 2
         = vTop + (2^34 - 1)
    so un21 > vTop.
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.TrialCall

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Counterexample input `uHi` to the wide-uHi failure regime of
    `divKTrialCallV4Un21 _ _ _ < vTop`. -/
abbrev ceWideUHi_uHi : Word := BitVec.ofNat 64 (2^63 + 2^33 + 2^31)

/-- Counterexample input `uLo`: zero (forces `un1 = 0`). -/
abbrev ceWideUHi_uLo : Word := BitVec.ofNat 64 0

/-- Counterexample input `vTop`: normalized (≥ 2^63), with
    `dHi = 2^31 + 2 > 2^31` and `dLo = 2^32 - 1` (max). -/
abbrev ceWideUHi_vTop : Word := BitVec.ofNat 64 (2^63 + 2^33 + 2^32 - 1)

/-- Normalisation holds: `vTop ≥ 2^63`. -/
theorem ceWideUHi_vTop_ge_pow63 : ceWideUHi_vTop.toNat ≥ 2^63 := by decide

/-- Call regime holds: `uHi < vTop`. -/
theorem ceWideUHi_uHi_lt_vTop :
    ceWideUHi_uHi.toNat < ceWideUHi_vTop.toNat := by decide

/-- Wide-uHi regime witness: `uHi ≥ dHi * 2^32`. -/
theorem ceWideUHi_uHi_ge_dHi_pow32 :
    ceWideUHi_uHi.toNat ≥
      (divKTrialCallV4DHi ceWideUHi_vTop).toNat * 2^32 := by
  delta divKTrialCallV4DHi
  decide

/-- Wide-rhatc trigger: `dHi > 2^31` (strictly), so `rhatc` can exceed `2^32`. -/
theorem ceWideUHi_dHi_gt_pow31 :
    (divKTrialCallV4DHi ceWideUHi_vTop).toNat > 2^31 := by
  delta divKTrialCallV4DHi
  decide

/-- The Phase-1b output `Q1dd` undershoots `q_true_1` by exactly 1.
    `q_true_1 = (uHi * 2^32 + un1) / vTop = 2^32 - 1`, but `Q1dd = 2^32 - 2`. -/
theorem ceWideUHi_Q1dd_lt_q_true_1 :
    (divKTrialCallV4Q1dd ceWideUHi_uHi ceWideUHi_uLo ceWideUHi_vTop).toNat <
      (ceWideUHi_uHi.toNat * 2^32 +
        (divKTrialCallV4Un1 ceWideUHi_uLo).toNat) /
        ceWideUHi_vTop.toNat := by
  delta divKTrialCallV4Q1dd divKTrialCallV4DHi divKTrialCallV4DLo
        divKTrialCallV4Un1
  decide

/-- **Conjecture failure.** Under just the running hypotheses
    `vTop ≥ 2^63` and `uHi < vTop`, the bound `un21 < vTop` does NOT hold.
    Concretely `un21 = vTop + (2^34 - 1) > vTop`. -/
theorem ceWideUHi_un21_ge_vTop :
    (divKTrialCallV4Un21 ceWideUHi_uHi ceWideUHi_uLo ceWideUHi_vTop).toNat ≥
      ceWideUHi_vTop.toNat := by
  delta divKTrialCallV4Un21 divKTrialCallV4Q1dd divKTrialCallV4Rhatdd
        divKTrialCallV4DHi divKTrialCallV4DLo divKTrialCallV4Un1
  decide

/-- The exact gap: `un21 = vTop + (2^34 - 1)`. -/
theorem ceWideUHi_un21_eq_vTop_plus_gap :
    (divKTrialCallV4Un21 ceWideUHi_uHi ceWideUHi_uLo ceWideUHi_vTop).toNat =
      ceWideUHi_vTop.toNat + (2^34 - 1) := by
  delta divKTrialCallV4Un21 divKTrialCallV4Q1dd divKTrialCallV4Rhatdd
        divKTrialCallV4DHi divKTrialCallV4DLo divKTrialCallV4Un1
  decide

/-- Top-level statement: there exists `(uHi, uLo, vTop)` satisfying
    normalisation and the call regime, with `un21 ≥ vTop`. This refutes
    `divKTrialCallV4Un21_lt_vTop_of_normalisation_and_call`. -/
theorem divKTrialCallV4Un21_lt_vTop_fails_under_normalisation_and_call :
    ∃ uHi uLo vTop : Word,
      vTop.toNat ≥ 2^63 ∧
      uHi.toNat < vTop.toNat ∧
      ¬ ((divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat) :=
  ⟨ceWideUHi_uHi, ceWideUHi_uLo, ceWideUHi_vTop,
    ceWideUHi_vTop_ge_pow63,
    ceWideUHi_uHi_lt_vTop,
    fun h => absurd h (Nat.not_lt.2 ceWideUHi_un21_ge_vTop)⟩

end EvmAsm.Evm64
