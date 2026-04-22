/-
  EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose

  Final closure work for the call+skip DIV path. Lifts the pure-Nat
  composition identities from `Div128KnuthLower.lean` to the Word-level
  `div128Quot` algorithm's actual Euclidean chain, and (eventually)
  connects to the outer mulsub + skip-borrow check to yield the exact
  `div128Quot = val256(a)/val256(b)` equality needed for call+skip
  correctness.

  Task roadmap (see `memory/project_un21_lt_vTop_plan.md`):
  - **Task 1** (this file): algorithm-level KB-Compose lift.
  - Task 2: Piece A composition (qHat ≤ val256/val256 + 2).
  - Task 3: outer mulsub + skip-borrow extraction.
  - Task 4: tight Phase 1 (Knuth Theorem C Word-level).
  - Task 5: tight Phase 2 (hard case).
  - Task 6: final call+skip DIV stack spec.

  Starting with a V2 of KB-Compose that accommodates `rhat' ≥ 2^32`
  (which can occur under Phase 1b's check-fires branch).
-/

import EvmAsm.Evm64.EvmWordArith.Div128KnuthLower

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **KB-Compose V2: accommodates `rhat' ≥ 2^32`.** Algebraic variant of
    `knuth_compose_qHat_vTop_le_nat` using `rhat' % 2^32` in the un21
    hypothesis — matches what KB-3m (`div128Quot_un21_additive_identity`)
    gives at the Word level when Phase 1b's `rhat'` exceeds 2^32.

    ```
    (q1' * 2^32 + q0') * (dHi * 2^32 + dLo) ≤ uHi * 2^64 + div_un1 * 2^32 + div_un0
    ```

    Hypotheses:
    - `h_ph1_eucl`: q1' * dHi + rhat' = uHi (Phase 1b Euclidean).
    - `h_ph1_no_wrap_lo`: q1' * dLo ≤ (rhat' % 2^32)*2^32 + div_un1
      (the "B ≤ A" no-wrap for KB-3m's un21 identity).
    - `h_un21_ph2`: q0' * dHi + rhat2' = (rhat' % 2^32)*2^32 + div_un1
      - q1' * dLo (un21 identity combined with Phase 2b Euclidean).
    - `h_ph2_no_wrap`: q0' * dLo ≤ rhat2' * 2^32 + div_un0 (Phase 2 no-wrap).

    Proof: similar algebra to KB-Compose, but carrying the `(rhat'/2^32)*2^96`
    correction that arises from `rhat' * 2^64 = (rhat'/2^32)*2^96 +
    (rhat' % 2^32)*2^64`. The correction is non-negative, so the ≤
    bound survives. -/
theorem knuth_compose_qHat_vTop_le_nat_v2
    (q1' q0' rhat' rhat2' dHi dLo div_un1 div_un0 uHi : Nat)
    (h_ph1_eucl : q1' * dHi + rhat' = uHi)
    (h_ph1_no_wrap_lo : q1' * dLo ≤ (rhat' % 2^32) * 2^32 + div_un1)
    (h_un21_ph2 : q0' * dHi + rhat2' =
      (rhat' % 2^32) * 2^32 + div_un1 - q1' * dLo)
    (h_ph2_no_wrap : q0' * dLo ≤ rhat2' * 2^32 + div_un0) :
    (q1' * 2^32 + q0') * (dHi * 2^32 + dLo) ≤
    uHi * 2^64 + div_un1 * 2^32 + div_un0 := by
  -- Eliminate Nat subtraction in un21 identity.
  have h_un21_plus :
      q0' * dHi + rhat2' + q1' * dLo = (rhat' % 2^32) * 2^32 + div_un1 := by
    omega
  -- Multiply un21 identity by 2^32.
  have h_mul : q0' * dHi * 2^32 + rhat2' * 2^32 + q1' * dLo * 2^32 =
               (rhat' % 2^32) * 2^64 + div_un1 * 2^32 := by
    have h := congr_arg (· * 2^32) h_un21_plus
    simp only at h
    have h_expand_lhs :
        (q0' * dHi + rhat2' + q1' * dLo) * 2^32 =
        q0' * dHi * 2^32 + rhat2' * 2^32 + q1' * dLo * 2^32 := by ring
    have h_expand_rhs :
        ((rhat' % 2^32) * 2^32 + div_un1) * 2^32 =
        (rhat' % 2^32) * 2^64 + div_un1 * 2^32 := by ring
    linarith
  -- uHi * 2^64 = q1' * dHi * 2^64 + rhat' * 2^64 (Phase 1b Euclidean ×2^64).
  have h_uHi_mul : uHi * 2^64 = q1' * dHi * 2^64 + rhat' * 2^64 := by
    have h_expand : (q1' * dHi + rhat') * 2^64 =
        q1' * dHi * 2^64 + rhat' * 2^64 := by ring
    have := congr_arg (· * 2^64) h_ph1_eucl
    simp only at this
    linarith
  -- Decompose rhat' * 2^64 = (rhat'/2^32)*2^96 + (rhat' % 2^32)*2^64.
  have h_rhat_split : rhat' * 2^64 =
      (rhat' / 2^32) * 2^96 + (rhat' % 2^32) * 2^64 := by
    have h_div_mod : (rhat' / 2^32) * 2^32 + rhat' % 2^32 = rhat' := by
      have := Nat.div_add_mod rhat' (2^32)
      linarith
    calc rhat' * 2^64
        = ((rhat' / 2^32) * 2^32 + rhat' % 2^32) * 2^64 := by rw [h_div_mod]
      _ = (rhat' / 2^32) * 2^96 + (rhat' % 2^32) * 2^64 := by ring
  -- Expand LHS of goal via `ring`.
  have h_lhs : (q1' * 2^32 + q0') * (dHi * 2^32 + dLo) =
               q1' * dHi * 2^64 + q1' * dLo * 2^32 +
               q0' * dHi * 2^32 + q0' * dLo := by
    ring
  rw [h_lhs]
  -- Intermediate facts for linarith.
  -- (1) uHi * 2^64 = q1' * dHi * 2^64 + (rhat'/2^32)*2^96 + (rhat' % 2^32)*2^64.
  have h_uHi_split :
      uHi * 2^64 = q1' * dHi * 2^64 + (rhat' / 2^32) * 2^96 +
                   (rhat' % 2^32) * 2^64 := by
    linarith
  -- (2) q0' * dHi * 2^32 + q1' * dLo * 2^32 ≤ (rhat' % 2^32)*2^64 + div_un1 * 2^32.
  -- From h_mul, rhat2' * 2^32 ≥ 0 gives this.
  have h_mid_le :
      q0' * dHi * 2^32 + q1' * dLo * 2^32 ≤
        (rhat' % 2^32) * 2^64 + div_un1 * 2^32 := by
    linarith
  -- (3) q0' * dLo ≤ rhat2' * 2^32 + div_un0 (given).
  -- (4) (rhat' / 2^32) * 2^96 ≥ 0 (Nat).
  have h_high_ge : 0 ≤ (rhat' / 2^32) * 2^96 := Nat.zero_le _
  -- Combine.
  linarith

end EvmAsm.Evm64
