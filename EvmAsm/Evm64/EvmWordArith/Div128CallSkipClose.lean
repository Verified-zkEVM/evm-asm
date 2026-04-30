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

-- Both `Div128KnuthLower` and `Div128FinalAssembly` transitively reach
-- `Div128QuotientBounds → KnuthTheoremB`, which imports `MaxTrialVacuity`
-- (→ `Compose.FullPathN4`) and `DivN4Overestimate` (→ `DivMod.LoopSemantic`).
import EvmAsm.Evm64.EvmWordArith.Div128FinalAssembly
import EvmAsm.Evm64.EvmWordArith.Div128KB6Composition

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord
open EvmAsm.Rv64.AddrNorm (word_toNat_0 word_toNat_1)

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
  have : uHi * 2^64 = q1' * dHi * 2^64 + rhat' * 2^64 := by
    have h_expand : (q1' * dHi + rhat') * 2^64 =
        q1' * dHi * 2^64 + rhat' * 2^64 := by ring
    have := congr_arg (· * 2^64) h_ph1_eucl
    simp only at this
    linarith
  -- Decompose rhat' * 2^64 = (rhat'/2^32)*2^96 + (rhat' % 2^32)*2^64.
  have : rhat' * 2^64 =
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
  have : 0 ≤ (rhat' / 2^32) * 2^96 := Nat.zero_le _
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
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    -- rhat2' mirrors the Phase 2b guard: fires → no check adjustment
    -- (rhat2c); fall-through → the Phase 1b check may have added dHi.
    let rhat2' := if rhat2cHi = 0 then
                    (if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat →
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat →
    q0'.toNat < 2^32 →
    (div128Quot uHi uLo vTop).toNat * vTop.toNat ≤
      uHi.toNat * 2^64 + uLo.toNat := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc rhatUn1 q1' rhat'
    cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c rhat2Un0 rhat2cHi q0' rhat2'
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
  -- Phase 1b Euclidean: q1' * dHi + rhat' = uHi.
  have h_ph1_eucl : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat :=
    div128Quot_phase1b_post uHi dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post1a
      (div128Quot_rhatc_lt_2dHi uHi dHi hdHi_ne hdHi_lt)
  -- un21 value (no-wrap case = A - B).
  have h_un21_case := div128Quot_un21_toNat_case uHi dHi dLo uLo rhatUn1
    hdHi_ge hdLo_lt huHi_lt_vTop
  have h_un21 : un21.toNat =
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat - q1'.toNat * dLo.toNat :=
    h_un21_case.1 h_ph1_no_wrap_lo
  -- Phase 2a invariants (instantiate Phase 1a on un21).
  have h_post2a := div128Quot_first_round_post un21 dHi hdHi_ne hdHi_lt
  have h_rhat2c_lt := div128Quot_rhatc_lt_2dHi un21 dHi hdHi_ne hdHi_lt
  -- Phase 2b Euclidean against un21: q0' * dHi + rhat2' = un21. Uses
  -- div128Quot_phase2b_post (KB-5a), which accommodates the guard via the
  -- guarded rhat2' definition.
  have h_ph2b : q0'.toNat * dHi.toNat + rhat2'.toNat = un21.toNat :=
    div128Quot_phase2b_post un21 dHi hdHi_lt q0c rhat2c dLo h_post2a h_rhat2c_lt
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
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let rhat2' := if rhat2cHi = 0 then
                    (if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat →
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat →
    q0'.toNat < 2^32 →
    (div128Quot u4 un3 b3').toNat ≤
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc
    rhatUn1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c rhat2Un0
    rhat2cHi q0' rhat2' h_ph1_no_wrap h_ph2_no_wrap hq0_lt
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

-- ============================================================================
-- Task 3: Outer mulsub + skip-borrow upper bound
-- ============================================================================

/-- **T3-A: Extract `c3 ≤ u4` from `isSkipBorrowN4Call`.** Mirror of
    `c3_le_u_top_of_skip_borrow` (which handles `isSkipBorrowN4Max`) for
    the call-trial path, where `qHat = div128Quot u4 u3 b3'` rather than
    the max trial `2^64 - 1`. -/
theorem c3_le_u4_of_skip_borrow_call
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let b2' := (b2 <<< shift) ||| (b1 >>> antiShift)
    let b1' := (b1 <<< shift) ||| (b0 >>> antiShift)
    let b0' := b0 <<< shift
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let u2 := (a2 <<< shift) ||| (a1 >>> antiShift)
    let u1 := (a1 <<< shift) ||| (a0 >>> antiShift)
    let u0 := a0 <<< shift
    let qHat := div128Quot u4 u3 b3'
    (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat ≤ u4.toNat := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  unfold isSkipBorrowN4Call at h
  simp only [] at h
  by_cases hlt : BitVec.ult u4 (mulsubN4_c3 qHat b0' b1' b2' b3' u0 u1 u2 u3)
  · rw [if_pos hlt] at h
    exact absurd h (by decide)
  · rw [ult_iff] at hlt
    unfold mulsubN4_c3 at hlt
    omega

/-- **T3-B: `qHat * val256(b) ≤ val256(a)` under call + skip + norm.**

    Combines:
    - `mulsubN4_val256_eq`: val256(u) + c3 * 2^256 = val256(un) + qHat * val256(v').
    - `c3_le_u4_of_skip_borrow_call` (T3-A): c3 ≤ u4.
    - `u_val256_eq_scaled_with_overflow` (hnorm_u): val256(u) + u4 * 2^256 = val256(a) * 2^shift.
    - `b3_prime_val256_eq_scaled` (hnorm_v): val256(v') = val256(b) * 2^shift.
    - `val256_pos_of_or_ne_zero`: val256(b) > 0 when b ≠ 0, so can cancel 2^shift > 0.

    Conclusion: `qHat.toNat * val256(b) ≤ val256(a)` (unscaled). -/
theorem div128Quot_call_skip_mul_val256_b_le_val256_a
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hskip : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (div128Quot u4 u3 b3').toNat * val256 b0 b1 b2 b3 ≤ val256 a0 a1 a2 a3 := by
  intro shift antiShift b3' u4 u3
  -- Unfold all the normalized quantities.
  set b2' := (b2 <<< shift) ||| (b1 >>> antiShift)
  set b1' := (b1 <<< shift) ||| (b0 >>> antiShift)
  set b0' := b0 <<< shift
  set u2 := (a2 <<< shift) ||| (a1 >>> antiShift)
  set u1 := (a1 <<< shift) ||| (a0 >>> antiShift)
  set u0 := a0 <<< shift
  set qHat := div128Quot u4 u3 b3'
  -- Extract c3 ≤ u4 from skip-borrow.
  have h_c3_le := c3_le_u4_of_skip_borrow_call hskip
  -- mulsubN4 Euclidean: val256(u) + c3 * 2^256 = val256(un) + qHat * val256(v')
  have h_mulsub := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  -- Normalization: val256(u) + u4 * 2^256 = val256(a) * 2^shift.
  have h_norm_u := u_val256_eq_scaled_with_overflow a0 a1 a2 a3 b3 hshift_nz
  have h_norm_v := b3_prime_val256_eq_scaled b0 b1 b2 b3 hshift_nz
  -- Extract val256(v') = val256(b) * 2^shift from h_norm_v.
  -- Its argument names match b0', b1', b2', b3' after unfolding.
  have h_un_bound : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 :=
    val256_bound _ _ _ _
  -- From h_mulsub: qHat * val256(v') = val256(u) + c3 * 2^256 - val256(un)
  --              ≤ val256(u) + c3 * 2^256
  --              ≤ val256(u) + u4 * 2^256
  --              = val256(a) * 2^shift   (from h_norm_u)
  have h_qHat_mul_v' : qHat.toNat * val256 b0' b1' b2' b3' ≤
      val256 a0 a1 a2 a3 * 2^(clzResult b3).1.toNat := by
    -- h_mulsub: val256 u0..u3 + ms.2.2.2.2.toNat * 2^256 = val256 un + qHat * val256 v'
    -- So qHat * val256 v' = val256 u + c3 * 2^256 - val256 un.
    have : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 := h_un_bound
    -- Combine: qHat * val256 v' ≤ val256 u + c3 * 2^256.
    have : qHat.toNat * val256 b0' b1' b2' b3' ≤
        val256 u0 u1 u2 u3 + ms.2.2.2.2.toNat * 2^256 := by omega
    -- Use c3 ≤ u4.
    have : val256 u0 u1 u2 u3 + ms.2.2.2.2.toNat * 2^256 ≤
        val256 u0 u1 u2 u3 + u4.toNat * 2^256 := by
      apply Nat.add_le_add_left
      exact Nat.mul_le_mul_right _ h_c3_le
    -- Use h_norm_u.
    have : val256 u0 u1 u2 u3 + u4.toNat * 2^256 =
        val256 a0 a1 a2 a3 * 2^(clzResult b3).1.toNat := h_norm_u
    omega
  -- Now use h_norm_v to rewrite val256(v') = val256(b) * 2^shift.
  rw [h_norm_v] at h_qHat_mul_v'
  -- Extract scale: qHat * val256(b) * 2^shift ≤ val256(a) * 2^shift, so divide.
  have hpow_pos : 0 < (2 : Nat)^(clzResult b3).1.toNat := by positivity
  have h_mul_rearr : qHat.toNat * (val256 b0 b1 b2 b3 * 2^(clzResult b3).1.toNat) =
      qHat.toNat * val256 b0 b1 b2 b3 * 2^(clzResult b3).1.toNat := by ring
  rw [h_mul_rearr] at h_qHat_mul_v'
  exact Nat.le_of_mul_le_mul_right h_qHat_mul_v' hpow_pos

/-- **T3: Outer mulsub + skip-borrow upper bound on div128Quot.**

    Under the call-path preconditions (`isCallTrialN4`), normalization
    (`hshift_nz`), the runtime skip-borrow check (`isSkipBorrowN4Call`),
    and `b3 ≠ 0`, the algorithm's trial quotient is bounded by the true
    quotient:

    ```
    (div128Quot u4 u3 b3').toNat ≤ val256(a) / val256(b)
    ```

    This bypasses the no-wrap hypotheses of Tasks 1/2 (which were needed
    for the Knuth-B upper chain `qHat ≤ val256(a)/val256(b) + 2`) by
    using the outer mulsub borrow directly. The skip branch's correctness
    relies on `c3 ≤ u4`, which converts the mulsub Euclidean into the
    exact upper bound.

    Composed with a Task 5 lower bound, this will close the exact equality
    `qHat = val256(a) / val256(b)` for the DIV call+skip stack spec. -/
theorem div128Quot_call_skip_le_val256_div
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hskip : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (div128Quot u4 u3 b3').toNat ≤
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
  intro shift antiShift b3' u4 u3
  have h_bnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hv_pos : 0 < val256 b0 b1 b2 b3 := val256_pos_of_or_ne_zero h_bnz
  have h_mul := div128Quot_call_skip_mul_val256_b_le_val256_a
    a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz hskip
  simp only [] at h_mul
  exact (Nat.le_div_iff_mul_le hv_pos).mpr h_mul

-- ============================================================================
-- Pure-Nat digit-tightness utilities (used downstream by Phase 1/2 tight)
-- ============================================================================

/-- **Digit-decomposition tightness (pure Nat).** When a 2-digit value
    `q1 * 2^32 + q0` is upper-bounded by `q_true_1 * 2^32 + q_true_0`
    (with `q_true_0 < 2^32`), and the top digit is lower-bounded by
    `q_true_1`, the top digit is exactly `q_true_1`.

    Insight: if `q1 ≥ q_true_1 + 1`, then `q1 * 2^32 ≥ (q_true_1 + 1) * 2^32
    = q_true_1 * 2^32 + 2^32 > q_true_1 * 2^32 + q_true_0`, contradicting
    the upper bound. Hence `q1 = q_true_1`, and `q0 ≤ q_true_0` follows.

    **Usage**: this is the key step showing Phase 1 tight (q1' = q_true_1)
    is a free consequence of T3's `qHat ≤ q_true_full` combined with
    KB-LB7's `q1' ≥ q_true_1`. Obsoletes the originally-planned Task 4
    (Phase 1 tight via Knuth Theorem C Word-level, ~150 lines). -/
theorem digit_tight_of_le_and_ge {q1 q0 q_true_1 q_true_0 : Nat}
    (h_q_true_0_lt : q_true_0 < 2^32)
    (h_le : q1 * 2^32 + q0 ≤ q_true_1 * 2^32 + q_true_0)
    (h_ge : q_true_1 ≤ q1) :
    q1 = q_true_1 ∧ q0 ≤ q_true_0 := by
  have h_q1_le : q1 ≤ q_true_1 := by
    by_contra h
    push Not at h
    have h_mul : (q_true_1 + 1) * 2^32 ≤ q1 * 2^32 :=
      Nat.mul_le_mul_right _ h
    have h_rearr : (q_true_1 + 1) * 2^32 = q_true_1 * 2^32 + 2^32 := by ring
    omega
  have h_q1_eq : q1 = q_true_1 := Nat.le_antisymm h_q1_le h_ge
  refine ⟨h_q1_eq, ?_⟩
  rw [h_q1_eq] at h_le
  omega

/-- **q_true_full digit lower bound (pure Nat).** The full 2-digit true
    quotient is at least `q_true_1 * 2^32`, where `q_true_1` is the Phase 1
    abstract first digit. Proof: multiply Phase 1 Euclidean by `2^32`,
    bound `div_un0 ≥ 0`. -/
theorem q_true_full_ge_q_true_1_mul_pow32_nat
    {uHi div_un1 div_un0 dHi dLo : Nat}
    (hvTop_pos : 0 < dHi * 2^32 + dLo) :
    (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) * 2^32 ≤
      (uHi * 2^64 + div_un1 * 2^32 + div_un0) / (dHi * 2^32 + dLo) := by
  set vTop_nat := dHi * 2^32 + dLo
  set q_true_1 := (uHi * 2^32 + div_un1) / vTop_nat
  have h_euc : q_true_1 * vTop_nat ≤ uHi * 2^32 + div_un1 :=
    Nat.div_mul_le_self _ _
  have h_le : q_true_1 * 2^32 * vTop_nat ≤
      uHi * 2^64 + div_un1 * 2^32 + div_un0 := by
    have h_rearr : q_true_1 * 2^32 * vTop_nat = q_true_1 * vTop_nat * 2^32 := by ring
    have h_mul : q_true_1 * vTop_nat * 2^32 ≤ (uHi * 2^32 + div_un1) * 2^32 :=
      Nat.mul_le_mul_right _ h_euc
    have h_expand : (uHi * 2^32 + div_un1) * 2^32 =
        uHi * 2^64 + div_un1 * 2^32 := by ring
    linarith
  exact (Nat.le_div_iff_mul_le hvTop_pos).mpr h_le

/-- **q_true_full digit upper bound (pure Nat).** The full 2-digit true
    quotient is strictly less than `(q_true_1 + 1) * 2^32`. Proof: from
    `Nat.lt_mul_div_succ`, `vTop * (q_true_1 + 1) > uHi * 2^32 + div_un1`;
    multiply by `2^32` and bound `div_un0 < 2^32`. -/
theorem q_true_full_lt_q_true_1_succ_mul_pow32_nat
    {uHi div_un1 div_un0 dHi dLo : Nat}
    (hvTop_pos : 0 < dHi * 2^32 + dLo)
    (hdiv_un0_lt : div_un0 < 2^32) :
    (uHi * 2^64 + div_un1 * 2^32 + div_un0) / (dHi * 2^32 + dLo) <
      ((uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) + 1) * 2^32 := by
  set vTop_nat := dHi * 2^32 + dLo
  set q_true_1 := (uHi * 2^32 + div_un1) / vTop_nat
  have h_lt : uHi * 2^32 + div_un1 < vTop_nat * (q_true_1 + 1) :=
    Nat.lt_mul_div_succ _ hvTop_pos
  have h_num_lt : uHi * 2^64 + div_un1 * 2^32 + div_un0 <
      vTop_nat * (q_true_1 + 1) * 2^32 := by
    have h_plus_one : uHi * 2^32 + div_un1 + 1 ≤ vTop_nat * (q_true_1 + 1) := h_lt
    have : (uHi * 2^32 + div_un1 + 1) * 2^32 ≤
        vTop_nat * (q_true_1 + 1) * 2^32 :=
      Nat.mul_le_mul_right _ h_plus_one
    have h_expand_lhs : (uHi * 2^32 + div_un1 + 1) * 2^32 =
        uHi * 2^64 + div_un1 * 2^32 + 2^32 := by ring
    linarith
  have h_eq_rearr : vTop_nat * (q_true_1 + 1) * 2^32 =
      ((q_true_1 + 1) * 2^32) * vTop_nat := by ring
  rw [h_eq_rearr] at h_num_lt
  exact (Nat.div_lt_iff_lt_mul hvTop_pos).mpr h_num_lt

/-- **CLZ-normalized strict KB-6d**: `div128Quot ≤ val256(a)/val256(b) + 2`
    in the call-trial CLZ-normalized form, under the all-phases no-wrap
    invariant.

    Composes `div128Quot_le_q_true` (strict KB-6d from
    `Div128FinalAssembly`) with Piece A (`knuth_theorem_b_from_clz`):
    - `div128Quot u4 un3 b3' ≤ (u4*2^64 + un3)/b3'`         (strict KB-6d)
    - `(u4*2^64 + un3)/b3' ≤ val256(a)/val256(b) + 2`       (Piece A)

    Result: `div128Quot u4 un3 b3' ≤ val256(a)/val256(b) + 2`.

    Mirror of `div128Quot_le_val256_div_plus_two` (which takes
    unbundled `h_ph1_no_wrap_lo`, `h_ph2_no_wrap`, `hq0_lt`), but uses
    the bundled `Div128AllPhasesNoWrapInv` predicate. Cleaner API for
    downstream stack-spec consumers. -/
theorem div128Quot_le_val256_div_plus_two_with_inv
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    Div128AllPhasesNoWrapInv u4 un3 b3' →
    (div128Quot u4 un3 b3').toNat ≤
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := by
  intro shift antiShift u4 un3 b3' h_inv
  -- Discharge strict KB-6d preconditions.
  have hb3prime_ge_pow63 : b3'.toNat ≥ 2^63 := b3_prime_ge_pow63 b3 b2 hb3nz _
  have hu4_lt_b3prime : u4.toNat < b3'.toNat := isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have hcall_strict : u4.toNat * 2^64 + un3.toNat < b3'.toNat * 2^64 := by
    have hun3 : un3.toNat < 2^64 := un3.isLt
    have : u4.toNat * 2^64 + 2^64 ≤ b3'.toNat * 2^64 := by
      have : u4.toNat + 1 ≤ b3'.toNat := hu4_lt_b3prime
      calc u4.toNat * 2^64 + 2^64
          = (u4.toNat + 1) * 2^64 := by ring
        _ ≤ b3'.toNat * 2^64 := Nat.mul_le_mul_right _ this
    omega
  -- Strict KB-6d: div128Quot u4 un3 b3' ≤ (u4*2^64 + un3)/b3'.
  have h_kb6d := div128Quot_le_q_true u4 un3 b3' hb3prime_ge_pow63 hcall_strict h_inv
  -- Piece A: (u4*2^64 + un3)/b3' ≤ val256(a)/val256(b) + 2.
  have h_piece_a := knuth_theorem_b_from_clz a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz hcall
  -- Compose via transitivity.
  exact Nat.le_trans h_kb6d h_piece_a

/-- **q1' < 2^32 in call-trial CLZ-normalized form** (CLOSED).

    Wrapper around `div128Quot_q1_prime_lt_pow32` (KB-3e''') that takes
    the CLZ-normalized inputs `u4`, `un3`, `b3'` directly. Building
    block for the discharge bridge — gives the unconditional
    `q1' < 2^32` fact that's needed downstream to:
    1. Apply `div128Quot_toNat_eq_strict` (drops the `% 2^32` from
       KB-6a's output formula).
    2. Get `(q1' << 32) | q0' = q1' * 2^32 + q0'` (no OR-overlap on
       q1' side, under the additional `q0' < 2^32`).

    Pure consequence of hcall + the CLZ normalization (b3' ≥ 2^63);
    no skip-borrow needed. -/
theorem div128Quot_q1_prime_lt_pow32_call
    (a2 a3 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    q1'.toNat < 2^32 := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc rhatUn1 q1'
  have hb3prime_ge_pow63 : b3'.toNat ≥ 2^63 := b3_prime_ge_pow63 b3 b2 hb3nz _
  have hdHi_ge : dHi.toNat ≥ 2^31 := div128Quot_dHi_ge_pow31 b3' hb3prime_ge_pow63
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hu4_lt_b3prime : u4.toNat < b3'.toNat := isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_vtop : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have hu4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vtop]; exact hu4_lt_b3prime
  exact div128Quot_q1_prime_lt_pow32 u4 dHi dLo un3 hdHi_ge hdHi_lt hdLo_lt hu4_lt_vTop

/- **Discharge bridge** (REMOVED): a `div128_all_phases_no_wrap_of_skip_borrow`
   stub was previously here, claiming `isSkipBorrowN4Call` implies
   `Div128AllPhasesNoWrapInv`. It was sorry'd because the bridge from
   Phase-1-level `q_top_phase1 := (u4*2^32 + un3>>32)/b3'` to
   val256-level `q_true_top := val256(a)/val256(b)/2^32` is genuinely
   hard — these quantities differ at the multi-precision level by up to
   Knuth's overshoot bound (Theorem B says `+2`).

   Closed building blocks toward the discharge are still available in
   this file and `CallSkipLowerBoundV2.lean`:
   - `div128Quot_call_skip_eq_val256_div` (tight equality).
   - `val256_div_val256_lt_pow64`, `val256_div_q_true_digits_lt_pow32`.
   - `div128Quot_q1_prime_lt_pow32_call`.
   - `div128Quot_or_left_ge_q1_prime_shift{,_existential}`.
   - `div128Quot_q1_prime_le_q_true_top_call_skip` (Phase 1 upper).

   Estimated remaining work: ~300–500 LOC of Knuth-style algebra
   (3–7 days) for the Phase-1-level ↔ val256-level bridge plus Phase 2
   mirrors plus wrap conjunct derivations. There's also a real risk
   that the `un21 < vTop` or Phase 2 no-wrap conjunct turns out subtly
   false (the predecessor `Div128PhaseNoWrapInv` strong form was shown
   FALSE in `project_kb6d_false_counterexample.md`).

   The conditional theorems (`div128Quot_le_q_true`,
   `div128Quot_le_val256_div_plus_two_with_inv`, etc.) remain available
   for callers willing to construct `Div128AllPhasesNoWrapInv` by some
   other means. -/

end EvmAsm.Evm64
