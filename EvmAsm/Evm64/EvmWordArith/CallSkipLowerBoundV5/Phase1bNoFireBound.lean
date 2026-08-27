/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Phase1bNoFireBound

  The no-fire dLo bound at the V5 cap level:
  `¬ algorithmPhase1bFireV5 ⇒ Q1c * dLo ≤ Rhatc * 2^32 + un1`.

  V5's Phase-1b 1st-correction guard is `rhatc >>> 32 = 0 ∧ BLTU`, so
  `¬ fire` decomposes into either:
  - `rhatc >>> 32 ≠ 0`: bound holds by sheer magnitude (rhatc*2^32 ≥ 2^64).
  - `rhatc >>> 32 = 0 ∧ ¬ BLTU`: bound holds by the failed unsigned
    comparison directly.

  Reuses v4's `phase1b_no_fire_dLo_bound_of_rhat_hi_{zero,nonzero}`
  (generic over `q1c, rhatc, dLo, un1`) — no V5-specific lemmas needed.

  Bead `evm-asm-wbc4i.4.6.7` (V5.4.0.8). Prerequisite for V5.4.1.
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cEuclidean
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase1bBound

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem algorithmQ1cV5_dLo_bound_of_phase1b_no_fire
    (uHi uLo vTop : Word)
    (h_no_fire : ¬ algorithmPhase1bFireV5 uHi uLo vTop) :
    (algorithmQ1cV5 uHi vTop).toNat * (divKTrialCallV5DLo vTop).toNat ≤
      (algorithmRhatcV5 uHi vTop).toNat * 2^32 +
        (divKTrialCallV5Un1 uLo).toNat := by
  set q1c := algorithmQ1cV5 uHi vTop with hq1c
  set rhatc := algorithmRhatcV5 uHi vTop with hrhatc
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un1 := divKTrialCallV5Un1 uLo with hun1
  have h_q1c_le : q1c.toNat ≤ 2^32 := by
    rw [hq1c]; have := algorithmQ1cV5_lt_pow32 uHi vTop; omega
  have h_dLo_lt : dLo.toNat < 2^32 := by
    rw [hdLo]; exact divKTrialCallV5DLo_lt_pow32 vTop
  have h_un_lt : un1.toNat < 2^32 := by
    rw [hun1]; exact divKTrialCallV5Un1_lt_pow32 uLo
  by_cases h_rhat_hi : rhatc >>> (32 : BitVec 6).toNat = (0 : Word)
  · -- rhatc small: no-fire ⇒ ¬ BLTU (since the high-half precondition holds).
    have h_ult_false :
        ¬ BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un1) (q1c * dLo) := by
      intro h_ult
      apply h_no_fire
      delta algorithmPhase1bFireV5 algorithmRhatUn1cV5
      refine ⟨h_rhat_hi, ?_⟩
      simpa [hq1c, hrhatc, hdLo, hun1] using h_ult
    have h_q1c_dLo_no_wrap : (q1c * dLo).toNat = q1c.toNat * dLo.toNat := by
      rw [hq1c, hdLo]; exact algorithmQ1cV5_dLo_no_wrap uHi vTop
    exact phase1b_no_fire_dLo_bound_of_rhat_hi_zero q1c rhatc dLo un1
      h_rhat_hi h_un_lt h_q1c_dLo_no_wrap h_ult_false
  · -- rhatc large: bound trivially holds.
    exact phase1b_no_fire_dLo_bound_of_rhat_hi_nonzero q1c rhatc dLo un1
      h_q1c_le h_dLo_lt h_rhat_hi

end EvmAsm.Evm64
