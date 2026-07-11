/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bNoFireBound

  The "no-fire" Knuth-D3 bound for `div128Quot_phase2b_q0'`: when the
  correction's BLTU test fails (i.e., `¬ BitVec.ult rhatUn1 (q * dLo)`)
  and `rhat < 2^32`, the resulting (un-corrected) quotient `q` already
  satisfies the Knuth D3 invariant `q.toNat * dLo.toNat ≤
  rhat.toNat * 2^32 + un.toNat`.

  This is the structurally trivial sub-case of the v4 Phase-1b
  2-correction post-condition (bead `evm-asm-9iqmw.7.1.3.1.1.2.1`).
  The two remaining sub-cases (`rhat ≥ 2^32` no-fire, and 2nd
  correction fires) are tracked separately.

  Generic in `q`/`rhat`/`dLo`/`un` so the same lemma serves both
  Phase-1b 2-correction (bead 7.1.3.1.1.2.1) and Phase-2 2-correction
  (bead 7.1.4.x) callers.
-/

import EvmAsm.Evm64.EvmWordArith.Div128Lemmas
import EvmAsm.Evm64.EvmWordArith.Common
import EvmAsm.Evm64.DivMod.LoopDefs.Iter
import EvmAsm.Rv64.AddrNorm

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- **Phase-2b no-fire case-b bound.** When `rhat < 2^32` and the BLTU
    test against the half-word combine `(rhat <<< 32) ||| un` fails,
    the un-corrected quotient `q` satisfies the Knuth D3 invariant
    `q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un.toNat`.

    Requires `un < 2^32` (the standard `un1 := uLo >>> 32` shape) and
    `(q * dLo).toNat = q.toNat * dLo.toNat` (no Word-multiplication
    wrap — typically discharged by `div128Quot_q1_prime_dLo_no_wrap`
    when `q = q1'`).

    Two consequences in one statement:
    1. `div128Quot_phase2b_q0' q rhat dLo un = q` (the correction
       doesn't fire, since the BLTU test failed).
    2. `q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un.toNat` (the
       BLTU-complement bound). -/
theorem div128Quot_phase2b_q0'_dLo_bound_no_fire_case_b
    (q rhat dLo un : Word)
    (h_rhat_lt : rhat.toNat < 2^32)
    (h_un_lt : un.toNat < 2^32)
    (h_no_wrap : (q * dLo).toNat = q.toNat * dLo.toNat)
    (h_no_ult : ¬ BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)) :
    div128Quot_phase2b_q0' q rhat dLo un = q ∧
    q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un.toNat := by
  refine ⟨?_, ?_⟩
  · -- Step 1: the correction does not fire (the BLTU test failed).
    unfold div128Quot_phase2b_q0'
    by_cases h_hi : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
    · rw [if_pos h_hi]; simp only []; rw [if_neg h_no_ult]
    · rw [if_neg h_hi]
  · -- Step 2: BLTU-complement gives the bound.
    have h_le : (q * dLo).toNat ≤
        ((rhat <<< (32 : BitVec 6).toNat) ||| un).toNat := by
      rcases (Decidable.em (BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un)
              (q * dLo))) with h | h
      · exact absurd h h_no_ult
      · rw [ult_iff] at h
        omega
    rw [h_no_wrap] at h_le
    rw [show ((32 : BitVec 6).toNat) = (32 : Nat) from rfl] at h_le
    rw [halfword_combine rhat un h_rhat_lt h_un_lt] at h_le
    exact h_le

/-- **Phase-2b no-fire case-a bound.** When `rhat ≥ 2^32`, the
    `phase2b_q0'` correction trivially does not fire (the outer
    `rhat >>> 32 = 0` guard fails), so the output is `q` unchanged.

    Under the standard size bounds `q.toNat ≤ 2^32 + 1` (Knuth's
    `+1` overshoot for 1-correction Phase-1b, supplied by
    `div128Quot_q1_prime_le_pow32_plus_one`) and `dLo.toNat < 2^32`
    (lower half-word), we have `q * dLo < 2^64 ≤ rhat * 2^32 ≤
    rhat * 2^32 + un`. So the Knuth-D3 invariant holds. -/
theorem div128Quot_phase2b_q0'_dLo_bound_no_fire_case_a
    (q rhat dLo un : Word)
    (h_q_le : q.toNat ≤ 2^32 + 1)
    (h_dLo_lt : dLo.toNat < 2^32)
    (h_rhat_ge : rhat.toNat ≥ 2^32)
    (h_no_wrap : (q * dLo).toNat = q.toNat * dLo.toNat) :
    div128Quot_phase2b_q0' q rhat dLo un = q ∧
    q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un.toNat := by
  -- Outer guard `rhat >>> 32 = 0` fails since rhat ≥ 2^32.
  have h_hi_ne : rhat >>> (32 : BitVec 6).toNat ≠ (0 : Word) := by
    rw [show ((32 : BitVec 6).toNat) = (32 : Nat) from rfl]
    intro h_eq
    have h_toNat : (rhat >>> 32).toNat = 0 := by
      rw [h_eq]; rfl
    rw [BitVec.toNat_ushiftRight] at h_toNat
    -- (rhat.toNat >>> 32) = 0 ↔ rhat.toNat < 2^32, contradicting h_rhat_ge.
    have h_div : rhat.toNat / 2^32 = 0 := by
      rwa [Nat.shiftRight_eq_div_pow] at h_toNat
    have h_lt : rhat.toNat < 2^32 := Nat.div_eq_zero_iff.mp h_div |>.elim
      (fun h => absurd h (by decide)) id
    omega
  refine ⟨?_, ?_⟩
  · -- Correction doesn't fire — outer if hits the else branch.
    unfold div128Quot_phase2b_q0'
    rw [if_neg h_hi_ne]
  · -- Bound: q * dLo < 2^64 ≤ rhat * 2^32 ≤ rhat * 2^32 + un.
    have h_q_dLo_lt : q.toNat * dLo.toNat < 2^64 := by
      have hbd : q.toNat * dLo.toNat ≤ (2^32 + 1) * (2^32 - 1) := by
        have hdLo_le : dLo.toNat ≤ 2^32 - 1 := by omega
        exact Nat.mul_le_mul h_q_le hdLo_le
      have : (2^32 + 1) * (2^32 - 1) = 2^64 - 1 := by decide
      omega
    have h_rhat_pow : rhat.toNat * 2^32 ≥ 2^64 := by
      have : rhat.toNat * 2^32 ≥ 2^32 * 2^32 := Nat.mul_le_mul_right _ h_rhat_ge
      have h_64 : (2^32 : Nat) * 2^32 = 2^64 := by decide
      omega
    omega

/-- **Phase-2b no-fire combined bound.** Unified wrapper over case-a
    (`rhat ≥ 2^32`, outer guard fails) and case-b (`rhat < 2^32 ∧
    ¬ult`, inner guard fails).

    Takes the full set of size preconditions plus the algorithm-level
    "no-fire" condition `h_no_fire : ¬ (rhat >>> 32 = 0 ∧ ult)` (the
    negation of the `phase2b_q0'` correction guard). Dispatches via
    case-split on `rhat.toNat < 2^32 ∨ ¬ult` and invokes the
    appropriate sub-case helper.

    This is the form callers of bead 7.1.3.1.1.2 use to discharge the
    Phase-1b 2-correction post-condition's "no-fire" branch in one
    shot. -/
theorem div128Quot_phase2b_q0'_dLo_bound_no_fire
    (q rhat dLo un : Word)
    (h_q_le : q.toNat ≤ 2^32 + 1)
    (h_dLo_lt : dLo.toNat < 2^32)
    (h_un_lt : un.toNat < 2^32)
    (h_no_wrap : (q * dLo).toNat = q.toNat * dLo.toNat)
    (h_no_fire :
      ¬ (rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo))) :
    div128Quot_phase2b_q0' q rhat dLo un = q ∧
    q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un.toNat := by
  by_cases h_rhat_lt : rhat.toNat < 2^32
  · -- Case-b: rhat < 2^32 ⇒ rhat >>> 32 = 0 ⇒ no-fire forces ¬ult.
    have h_rhat_hi_zero : rhat >>> (32 : BitVec 6).toNat = (0 : Word) := by
      apply BitVec.eq_of_toNat_eq
      show (rhat >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat
      rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
          Nat.shiftRight_eq_div_pow]
      rw [Nat.div_eq_of_lt h_rhat_lt]
      rfl
    have h_no_ult :
        ¬ BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) := by
      intro h_ult; exact h_no_fire ⟨h_rhat_hi_zero, h_ult⟩
    exact div128Quot_phase2b_q0'_dLo_bound_no_fire_case_b
      q rhat dLo un h_rhat_lt h_un_lt h_no_wrap h_no_ult
  · -- Case-a: rhat ≥ 2^32.
    have h_rhat_ge : rhat.toNat ≥ 2^32 := by omega
    exact div128Quot_phase2b_q0'_dLo_bound_no_fire_case_a
      q rhat dLo un h_q_le h_dLo_lt h_rhat_ge h_no_wrap

end EvmAsm.Evm64
