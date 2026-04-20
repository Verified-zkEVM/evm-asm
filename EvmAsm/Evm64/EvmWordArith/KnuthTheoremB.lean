/-
  EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

  Toward Knuth's TAOCP Vol 2 §4.3.1 Theorem B for the n=4 max-trial
  call path: `div128Quot u_top u3 b3'` overestimates the true quotient
  `⌊val256(a) / val256(b)⌋` by at most 2.

  This is the major remaining math gap for call-trial DIV/MOD stack
  specs (the real shift > 0 runtime path, after max-trial under
  `hshift_nz` was shown vacuous in `MaxTrialVacuity.lean`).

  See `memory/project_knuth_theorem_b_plan.md` for the 6-PR breakdown.

  Currently contains:
  - `val256_div_scale_invariant` (Step 0).
  - `rv64_divu_toNat` (Step 1a — RV64 divu → Nat div bridge).
  - `val256_ge_pow255_of_normalized` — normalized divisor ≥ 2^255.
  - `val256_split_hi2` — split val256 into (hi2-limb * 2^128 + lo2-limb) form.
-/

import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Scale invariance of integer division on val256: multiplying both operands
    by `2^s` doesn't change the quotient. Entry point for lifting normalized
    val256 computations back to un-normalized quotients.

    Trivial from `Nat.mul_div_mul_right`. -/
theorem val256_div_scale_invariant
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (s : Nat) :
    (val256 a0 a1 a2 a3 * 2^s) / (val256 b0 b1 b2 b3 * 2^s) =
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
  have hpos : 0 < (2 : Nat)^s := by positivity
  rw [Nat.mul_div_mul_right _ _ hpos]

/-- RV64 unsigned divide maps to Nat div on toNat (for nonzero divisor).

    Entry-level bridge for reasoning about `div128Quot`, which composes two
    `rv64_divu` calls with correction steps. The zero-divisor case returns
    `BitVec.allOnes 64` and is handled separately at call sites. -/
theorem rv64_divu_toNat (a b : Word) (hb : b ≠ 0) :
    (rv64_divu a b).toNat = a.toNat / b.toNat := by
  unfold rv64_divu
  split
  · rename_i hbeq
    exfalso; apply hb
    simp at hbeq
    exact hbeq
  · rw [BitVec.toNat_udiv]

/-- Under the normalization precondition `b3.toNat ≥ 2^63`, the 4-limb
    divisor is at least `2^255` (i.e. the top bit of the 256-bit value
    is set). Used by Knuth B to bound `v_nat` from below.

    Proof: `val256 ≥ b3.toNat * 2^192 ≥ 2^63 * 2^192 = 2^255`. -/
theorem val256_ge_pow255_of_normalized
    (b0 b1 b2 b3 : Word) (hb3 : b3.toNat ≥ 2^63) :
    val256 b0 b1 b2 b3 ≥ 2^255 := by
  unfold val256
  have h : b3.toNat * 2^192 ≥ 2^63 * 2^192 := Nat.mul_le_mul_right _ hb3
  have hpow : (2:Nat)^63 * 2^192 = 2^255 := by norm_num
  nlinarith

/-- Split a 4-limb value into its high-2-limb half and low-2-limb half:
    `val256 a0 a1 a2 a3 = (a3*B + a2) * B^2 + (a1*B + a0)` where `B = 2^64`.
    Used by Knuth B to express the "trial quotient" in terms of
    `u_top * 2^64 + u3` (the high pair) and `u2 * 2^64 + u1` (the low pair). -/
theorem val256_split_hi2 (a0 a1 a2 a3 : Word) :
    val256 a0 a1 a2 a3 =
      (a3.toNat * 2^64 + a2.toNat) * 2^128 +
      (a1.toNat * 2^64 + a0.toNat) := by
  unfold val256; ring

end EvmAsm.Evm64
