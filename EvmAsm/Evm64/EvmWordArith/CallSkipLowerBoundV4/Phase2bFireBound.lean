/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bFireBound

  The "correction-fires" Knuth-D3 bound for `div128Quot_phase2b_q0'`:
  when both `rhat >>> 32 = 0` and `BitVec.ult rhatUn1 (q * dLo)` hold,
  the correction fires (`phase2b_q0' q rhat dLo un = q + signExtend12 4095`,
  i.e. `q - 1` in Word arithmetic) and the post-correction value
  satisfies the Knuth D3 invariant under an "overshoot ≤ vTop"
  precondition.

  Companion to `Phase2bNoFireBound.lean` (cases a + b + unified
  no-fire). Together they cover all sub-cases of the v4 Phase-1b
  2-correction post-condition (bead `evm-asm-9iqmw.7.1.3.1.1.2.1`).

  The `h_overshoot_le_vTop` precondition encodes the 1-correction
  Knuth-B "+2 overshoot ≤ 2·vTop" structural bound, which the
  algorithm-specific caller (Phase-1b 1-correction → 2-correction
  composition) must discharge. Establishing it is the remaining
  algorithm-level math content; this helper is purely arithmetic.
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bNoFireBound
public import EvmAsm.Evm64.DivMod.LoopBody.TrialCall

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- **Fire identity for `phase2b_q0'`.** When both correction-guard
    sub-conditions hold (`rhat >>> 32 = 0` and the BLTU test), the
    Phase-2b correction fires and returns `q + signExtend12 4095`
    (i.e., `q - 1` in Word arithmetic, since `signExtend12 4095 =
    (2^64 - 1 : Word) = -1`). -/
theorem div128Quot_phase2b_q0'_eq_q_dec_of_fire
    (q rhat dLo un : Word)
    (h_rhat_hi_zero : rhat >>> (32 : BitVec 6).toNat = (0 : Word))
    (h_ult : BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)) :
    div128Quot_phase2b_q0' q rhat dLo un = q + signExtend12 4095 := by
  rw [← div128Quot_phase2b_q0'_and_form]
  exact if_pos ⟨h_rhat_hi_zero, h_ult⟩

/-- **Phase-2b fire-case Knuth-D3 bound.** Under the standard size
    preconditions plus `q ≥ 1` (needed for non-trivial Word subtraction)
    and the algorithm-level "overshoot ≤ vTop" assumption
    `q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un.toNat + dHi.toNat * 2^32 + dLo.toNat`,
    the corrected `phase2b_q0'` value satisfies the Knuth-D3 invariant
    against the corrected `rhat + dHi`.

    Two consequences in one statement:
    1. `phase2b_q0' q rhat dLo un = q + signExtend12 4095`.
    2. `(phase2b_q0' q rhat dLo un).toNat * dLo.toNat ≤
        (rhat + dHi).toNat * 2^32 + un.toNat`.

    The `h_overshoot_le_vTop` precondition encodes Knuth's "the
    1-correction trial overshoots the true partial dividend by at most
    one vTop" bound — a property of the algorithm's q1' construction
    that callers must discharge separately (typically via the existing
    `div128Quot_q1_prime_le_pow32_plus_one` chain). -/
theorem div128Quot_phase2b_q0'_dLo_bound_fire_case
    (q rhat dLo dHi un : Word)
    (h_no_wrap_rhat : (rhat + dHi).toNat = rhat.toNat + dHi.toNat)
    (h_q_pos : q.toNat ≥ 1)
    (h_rhat_hi_zero : rhat >>> (32 : BitVec 6).toNat = (0 : Word))
    (h_ult : BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo))
    (h_overshoot_le_vTop :
      q.toNat * dLo.toNat ≤
        rhat.toNat * 2^32 + un.toNat + dHi.toNat * 2^32 + dLo.toNat) :
    div128Quot_phase2b_q0' q rhat dLo un = q + signExtend12 4095 ∧
    (q + signExtend12 4095).toNat * dLo.toNat ≤
      (rhat + dHi).toNat * 2^32 + un.toNat := by
  refine ⟨div128Quot_phase2b_q0'_eq_q_dec_of_fire q rhat dLo un h_rhat_hi_zero h_ult, ?_⟩
  -- `signExtend12 4095 = (2^64 - 1 : Word)`, so `q + signExtend12 4095 = q - 1` (mod 2^64).
  have h_se_toNat : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
  have h_add_toNat : (q + signExtend12 4095).toNat = q.toNat - 1 := by
    rw [BitVec.toNat_add, h_se_toNat]
    omega
  rw [h_add_toNat, h_no_wrap_rhat]
  -- Goal: (q.toNat - 1) * dLo.toNat ≤ (rhat.toNat + dHi.toNat) * 2^32 + un.toNat.
  -- Step 1: distribute the Word subtraction and the (rhat + dHi) multiplication.
  have hq_dLo : (q.toNat - 1) * dLo.toNat = q.toNat * dLo.toNat - dLo.toNat := by
    rw [Nat.sub_mul, Nat.one_mul]
  have h_rh_dHi_distrib :
      (rhat.toNat + dHi.toNat) * 2^32 = rhat.toNat * 2^32 + dHi.toNat * 2^32 := by
    rw [Nat.add_mul]
  rw [hq_dLo, h_rh_dHi_distrib]
  -- Goal: q.toNat * dLo.toNat - dLo.toNat ≤
  --       rhat.toNat * 2^32 + dHi.toNat * 2^32 + un.toNat.
  -- Direct from h_overshoot_le_vTop.
  omega

end EvmAsm.Evm64
