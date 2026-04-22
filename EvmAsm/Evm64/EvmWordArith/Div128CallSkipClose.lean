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
import EvmAsm.Evm64.EvmWordArith.Div128FinalAssembly

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

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

-- ============================================================================
-- Task 1 Step 2: algorithm-level lift of KB-Compose V2
-- ============================================================================

/-- **Algorithm-level lift of KB-Compose V2 (Task 1 Step 2).**
    Connects the pure-Nat `knuth_compose_qHat_vTop_le_nat_v2` to the actual
    `div128Quot` algorithm's Euclidean chain (Phase 1b + un21 case + Phase 2b)
    and the final halfword combine (`div128Quot_toNat_eq_strict`) to yield:

    ```
    (div128Quot uHi uLo vTop).toNat * vTop.toNat ≤ uHi.toNat * 2^64 + uLo.toNat
    ```

    i.e., `qHat * vTop ≤ top128`, the core upper bound (Knuth Theorem B upper
    direction). Combined with skip-borrow analysis (future Task 3), this
    yields the `qHat = val256(a) / val256(b)` direction for call+skip DIV.

    Hypotheses (dispatch):
    - `hdHi_ge`: normalization (`dHi ≥ 2^31`), from the shift-normalization
      branch of the call path.
    - `hdLo_lt`: `dLo < 2^32`, automatic from `Word_ushiftRight_32_lt_pow32`.
    - `huHi_lt_vTop`: call-trial precondition (`uHi < vTop`).
    - `h_ph1_no_wrap_lo`: the B ≤ A no-wrap for Phase 1b's multiplication
      check (the `h_un21_case.1` branch). **TODO**: discharge under the
      tight Phase 1 result (Task 4 — Knuth Theorem C Word-level).
    - `h_ph2_no_wrap`: Phase 2 no-wrap. **TODO**: discharge in Task 5
      (hard case; requires un21 < vTop plus additional case analysis).
    - `hq0_lt`: `q0'.toNat < 2^32` (from KB-6b when un21 < vTop). -/
theorem div128Quot_qHat_vTop_le
    (uHi uLo vTop : Word)
    (hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                 (32 : BitVec 6).toNat).toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2Un0 (q0c * dLo) then q0c + signExtend12 4095
               else q0c
    let rhat2' := if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c
    q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat →
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat →
    q0'.toNat < 2^32 →
    (div128Quot uHi uLo vTop).toNat * vTop.toNat ≤
      uHi.toNat * 2^64 + uLo.toNat := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc rhatUn1 q1' rhat'
    cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c rhat2Un0 q0' rhat2'
    h_ph1_no_wrap_lo h_ph2_no_wrap hq0_lt
  -- Algorithm-level setup.
  have hdHi_ne : dHi ≠ 0 := by
    intro heq
    rw [show dHi = vTop >>> (32 : BitVec 6).toNat from rfl] at heq
    rw [heq] at hdHi_ge
    simp at hdHi_ge
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  -- Phase 1a invariants.
  have h_post1a := div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  have h_rhatc_lt := div128Quot_rhatc_lt_2dHi uHi dHi hdHi_ne hdHi_lt
  -- Phase 1b Euclidean: q1' * dHi + rhat' = uHi.
  have h_ph1_eucl : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat :=
    div128Quot_phase1b_post uHi dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post1a h_rhatc_lt
  -- un21 value (no-wrap case = A - B).
  have h_un21_case := div128Quot_un21_toNat_case uHi dHi dLo uLo rhatUn1
    hdHi_ge hdLo_lt huHi_lt_vTop
  have h_un21 : un21.toNat =
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat - q1'.toNat * dLo.toNat :=
    h_un21_case.1 h_ph1_no_wrap_lo
  -- Phase 2a invariants (instantiate Phase 1a on un21).
  have h_post2a := div128Quot_first_round_post un21 dHi hdHi_ne hdHi_lt
  have h_rhat2c_lt := div128Quot_rhatc_lt_2dHi un21 dHi hdHi_ne hdHi_lt
  -- Phase 2b Euclidean against un21: q0' * dHi + rhat2' = un21.
  have h_ph2b : q0'.toNat * dHi.toNat + rhat2'.toNat = un21.toNat :=
    div128Quot_phase1b_post un21 dHi q0c rhat2c dLo rhat2Un0 hdHi_lt h_post2a h_rhat2c_lt
  -- Combine h_ph2b + h_un21 to feed KB-Compose V2.
  have h_un21_ph2 : q0'.toNat * dHi.toNat + rhat2'.toNat =
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat - q1'.toNat * dLo.toNat := by
    rw [h_ph2b, h_un21]
  -- Pure-Nat KB-Compose V2.
  have h_compose := knuth_compose_qHat_vTop_le_nat_v2
    q1'.toNat q0'.toNat rhat'.toNat rhat2'.toNat dHi.toNat dLo.toNat
    div_un1.toNat div_un0.toNat uHi.toNat
    h_ph1_eucl h_ph1_no_wrap_lo h_un21_ph2 h_ph2_no_wrap
  -- Output formula: (div128Quot ...).toNat = q1' * 2^32 + q0'.
  have h_div_eq :
      (div128Quot uHi uLo vTop).toNat = q1'.toNat * 2^32 + q0'.toNat :=
    div128Quot_toNat_eq_strict uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt
      huHi_lt_vTop hq0_lt
  -- vTop and uLo decompositions.
  have h_vtop : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uLo : uLo.toNat = div_un1.toNat * 2^32 + div_un0.toNat :=
    div128Quot_vTop_decomp uLo
  calc (div128Quot uHi uLo vTop).toNat * vTop.toNat
      = (q1'.toNat * 2^32 + q0'.toNat) * (dHi.toNat * 2^32 + dLo.toNat) := by
          rw [h_div_eq, h_vtop]
    _ ≤ uHi.toNat * 2^64 + div_un1.toNat * 2^32 + div_un0.toNat := h_compose
    _ = uHi.toNat * 2^64 + uLo.toNat := by rw [h_uLo]; ring

-- ============================================================================
-- Task 2: Compose qHat bound with Piece A (`knuth_theorem_b_from_clz`)
-- ============================================================================

/-- **Task 2: `div128Quot ≤ val256(a)/val256(b) + 2` under call-trial + norm.**

    Composes Task 1 (`div128Quot_qHat_vTop_le`, multiplication form:
    `qHat * vTop ≤ uHi * 2^64 + uLo`) with Piece A (`knuth_theorem_b_from_clz`:
    `(u4 * 2^64 + un3) / b3' ≤ val256(a)/val256(b) + 2`) via
    `Nat.le_div_iff_mul_le`, yielding:

    ```
    (div128Quot u4 un3 b3').toNat ≤ val256(a)/val256(b) + 2
    ```

    i.e., the algorithm's trial quotient overestimates `val256(a)/val256(b)`
    by at most 2 under normalization + call-trial. Still conditional on
    Task 1's two no-wrap hypotheses (TODO Tasks 4/5).

    Identification: `uHi := u4`, `uLo := un3`, `vTop := b3'` where these are
    the CLZ-normalized top halves of a/b. -/
theorem div128Quot_le_val256_div_plus_two
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    -- Task 1 no-wrap hypotheses (specialized to u4, un3, b3'):
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let div_un0 := (un3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2Un0 (q0c * dLo) then q0c + signExtend12 4095
               else q0c
    let rhat2' := if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c
    q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat →
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat →
    q0'.toNat < 2^32 →
    (div128Quot u4 un3 b3').toNat ≤
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc
    rhatUn1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c rhat2Un0
    q0' rhat2' h_ph1_no_wrap h_ph2_no_wrap hq0_lt
  -- Discharge Task 1 preconditions.
  have hb3prime_ge_pow63 : b3'.toNat ≥ 2^63 := b3_prime_ge_pow63 b3 b2 hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 := div128Quot_dHi_ge_pow31 b3' hb3prime_ge_pow63
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hu4_lt_b3prime : u4.toNat < b3'.toNat := isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_vtop : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have hu4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vtop]; exact hu4_lt_b3prime
  -- Task 1 gives multiplication bound.
  have h_task1 := div128Quot_qHat_vTop_le u4 un3 b3' hdHi_ge hdLo_lt hu4_lt_vTop
    h_ph1_no_wrap h_ph2_no_wrap hq0_lt
  -- Convert multiplication bound to division bound via Nat.le_div_iff_mul_le.
  have hb3prime_pos : 0 < b3'.toNat := by omega
  have h_div_le : (div128Quot u4 un3 b3').toNat ≤
      (u4.toNat * 2^64 + un3.toNat) / b3'.toNat :=
    (Nat.le_div_iff_mul_le hb3prime_pos).mpr h_task1
  -- Piece A gives the abstract bound.
  have h_piece_a := knuth_theorem_b_from_clz a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz hcall
  -- Transitivity.
  calc (div128Quot u4 un3 b3').toNat
      ≤ (u4.toNat * 2^64 + un3.toNat) / b3'.toNat := h_div_le
    _ ≤ val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := h_piece_a

end EvmAsm.Evm64
