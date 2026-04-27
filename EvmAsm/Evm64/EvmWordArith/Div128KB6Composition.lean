/-
  EvmAsm.Evm64.EvmWordArith.Div128KB6Composition

  KB-6c assembly identity, KB-6c parent, and KB-6d (Knuth Theorem B at
  div128Quot level), plus their strict (`+0`) variants under the
  all-phases no-wrap invariant. Split from `Div128FinalAssembly.lean`
  (issue #61) to stay under the 1500-line file-size cap.

  This file contains:
  - **KB-6c-aux1**: pure-Nat assembly identity (Phase 2b + KB-3m).
  - **KB-6c-aux2**: drop corrections, get `(q1'*2^32 + q0')*vTop ≤
    uHi*2^64 + uLo + q0'*dLo`.
  - **Nat_le_div_add_two_of_mul_le**: pure-Nat division step.
  - **KB-6c-aux4**: `q0'*dLo ≤ 2*vTop` under normalization.
  - **KB-6c-pure-nat**: pure-Nat KB-6c (`+2` form).
  - **KB-6c-pure-nat-strict**: pure-Nat KB-6c-strict (`+0` form, with
    Phase 2 no-wrap).
  - **KB-6c parent / strict**: algorithm-level wrappers, conditional on
    `Div128PhaseNoWrapInv` / `Div128AllPhasesNoWrapInv`.
  - **KB-6d / strict**: `div128Quot.toNat ≤ q_true + 2` (or `≤ q_true`
    in strict form).

  Predicate definitions (`Div128PhaseNoWrapInv`,
  `Div128AllPhasesNoWrapInv`) live in `Div128FinalAssembly.lean`.
-/

import EvmAsm.Evm64.EvmWordArith.Div128FinalAssembly

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv6_toNat_32)

/-- **KB-6c-aux1: pure-Nat assembly identity for Phase 2b + KB-3m.**

    Pure Nat algebra. Composes Phase 2b post
    `q0'*dHi + rhat2' = un21` with KB-3m additive identity
    `un21 + r1*2^64 + q1'*vTop = uHi*2^32 + div_un1` and the
    decompositions `vTop = dHi*2^32 + dLo`, `uLo = div_un1*2^32 + div_un0`.

    Multiplying KB-3m by 2^32 and substituting Phase 2b post yields:
    ```
    (q1'*2^32 + q0')*vTop + rhat2'*2^32 + r1*2^96 + div_un0
      = uHi*2^64 + uLo + q0'*dLo
    ```

    Used in KB-6c to relate `(q1'*2^32 + q0')*vTop` to `(uHi*2^64 + uLo)`
    modulo a bounded correction. Note: Phase 1b post (`q1'*dHi + rhat' = uHi`)
    is NOT needed here since `rhat'` cancels out via the identity — `r1`
    plays the role of the wrap-around `rhat'/2^32` directly. -/
theorem div128Quot_kb6c_assembly_identity
    (q1' q0' rhat2' un21 uHi uLo vTop dHi dLo div_un1 div_un0 r1 : Nat)
    (h_phase2b : q0' * dHi + rhat2' = un21)
    (h_kb3m : un21 + r1 * 2^64 + q1' * vTop = uHi * 2^32 + div_un1)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_uLo : uLo = div_un1 * 2^32 + div_un0) :
    (q1' * 2^32 + q0') * vTop + rhat2' * 2^32 + r1 * 2^96 + div_un0 =
      uHi * 2^64 + uLo + q0' * dLo := by
  subst h_vTop h_uLo
  -- Substitute h_phase2b: un21 = q0'*dHi + rhat2'.
  rw [show un21 = q0' * dHi + rhat2' from h_phase2b.symm] at h_kb3m
  -- h_kb3m: q0'*dHi + rhat2' + r1*2^64 + q1'*(dHi*2^32+dLo) = uHi*2^32 + div_un1.
  -- Multiply by 2^32 and rearrange.
  have h_kb3m_scaled :
      (q0' * dHi + rhat2' + r1 * 2^64 + q1' * (dHi * 2^32 + dLo)) * 2^32 =
      (uHi * 2^32 + div_un1) * 2^32 := by
    rw [h_kb3m]
  -- Pure ring arithmetic from here; the LHS_goal - RHS_goal = 2^32 * (h_kb3m_scaled).
  have h_pow : (2^32 : Nat) * 2^32 = 2^64 := by decide
  have h_pow2 : (2^32 : Nat) * 2^64 = 2^96 := by decide
  have h_pow3 : (2^32 : Nat) * 2^32 * 2^32 = 2^96 := by decide
  -- Expand both sides via ring lemmas, then linarith for cancellation.
  nlinarith [h_kb3m_scaled, sq_nonneg (q1' : Nat), sq_nonneg (q0' : Nat),
             Nat.zero_le rhat2', Nat.zero_le r1, Nat.zero_le div_un0,
             Nat.zero_le dHi, Nat.zero_le dLo, Nat.zero_le div_un1]

/-- **KB-6c-aux2: drop non-negative correction terms from KB-6c-aux1.**

    From the KB-6c assembly identity, dropping the non-negative
    correction terms `rhat2'*2^32 + r1*2^96 + div_un0` yields the
    inequality:
    ```
    (q1'*2^32 + q0')*vTop ≤ uHi*2^64 + uLo + q0'*dLo
    ```

    Pure Nat algebra; trivial from KB-6c-aux1 + `Nat.le.intro`. -/
theorem div128Quot_kb6c_assembly_inequality
    (q1' q0' rhat2' un21 uHi uLo vTop dHi dLo div_un1 div_un0 r1 : Nat)
    (h_phase2b : q0' * dHi + rhat2' = un21)
    (h_kb3m : un21 + r1 * 2^64 + q1' * vTop = uHi * 2^32 + div_un1)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_uLo : uLo = div_un1 * 2^32 + div_un0) :
    (q1' * 2^32 + q0') * vTop ≤ uHi * 2^64 + uLo + q0' * dLo := by
  have h_id := div128Quot_kb6c_assembly_identity q1' q0' rhat2' un21 uHi uLo
    vTop dHi dLo div_un1 div_un0 r1 h_phase2b h_kb3m h_vTop h_uLo
  omega

/-- **KB-6c-aux3: from `X*v ≤ Y + 2*v` derive `X ≤ Y/v + 2`.**

    Pure Nat division lemma. Used to convert the KB-6c-aux2 inequality
    (after bounding `q0'*dLo ≤ 2*vTop`) into the final
    `q1'*2^32 + q0' ≤ q_true + 2` form. -/
theorem Nat_le_div_add_two_of_mul_le
    (X Y v : Nat) (hv : 0 < v)
    (h : X * v ≤ Y + 2 * v) :
    X ≤ Y / v + 2 := by
  by_cases hX : X ≤ 2
  · have h1 : 0 ≤ Y / v := Nat.zero_le _
    omega
  · push Not at hX
    -- X ≥ 3, so X - 2 ≥ 1. Subtract 2*v from both sides of h.
    have hX_sub : (X - 2) * v ≤ Y := by
      have h_eq : X = (X - 2) + 2 := by omega
      have h_split : X * v = (X - 2) * v + 2 * v := by
        conv_lhs => rw [h_eq]
        rw [Nat.add_mul]
      linarith
    have h_div : X - 2 ≤ Y / v := (Nat.le_div_iff_mul_le hv).mpr hX_sub
    omega

/-- **KB-6c-aux4: `q0' * dLo ≤ 2 * vTop` under normalization.**

    Pure Nat arithmetic. Under the standard div128Quot preconditions:
    - `q0' < 2^32` (KB-6b under un21 < vTop).
    - `dLo < 2^32` (definition).
    - `vTop ≥ 2^63` (normalization).

    We have `q0' * dLo < 2^32 * 2^32 = 2^64 ≤ 2 * 2^63 ≤ 2 * vTop`.
    Used in KB-6c to convert `(q1'*2^32 + q0')*vTop ≤ uHi*2^64 + uLo
    + q0'*dLo` into the form needed for `Nat_le_div_add_two_of_mul_le`. -/
theorem div128Quot_kb6c_q0_dLo_bound
    (q0' dLo vTop : Nat)
    (hq0' : q0' < 2^32)
    (hdLo : dLo < 2^32)
    (hvTop : vTop ≥ 2^63) :
    q0' * dLo ≤ 2 * vTop := by
  have h1 : q0' * dLo ≤ (2^32 - 1) * (2^32 - 1) := by
    apply Nat.mul_le_mul <;> omega
  have h2 : (2^32 - 1) * (2^32 - 1) ≤ 2 * 2^63 := by decide
  have h3 : 2 * 2^63 ≤ 2 * vTop := by omega
  omega

/-- **KB-6c-pure-nat: pure-Nat KB-6c quotient assembly bound.**

    Composes KB-6c-aux1 (assembly identity), KB-6c-aux2 (drop
    corrections), KB-6c-aux4 (q0'*dLo ≤ 2*vTop), and the
    Nat division step (`Nat_le_div_add_two_of_mul_le`):

    ```
    q1' * 2^32 + q0' ≤ (uHi * 2^64 + uLo) / vTop + 2
    ```

    All hypotheses are pure-Nat. The algorithm-level KB-6c
    (`div128Quot_q1_prime_q0_prime_le_q_true_plus_two`) becomes a
    one-step application of this lemma, after extracting the relevant
    Nat values from the algorithm's let-chain and discharging
    h_phase2b/h_kb3m/h_vTop/h_uLo/hq0' from the existing infrastructure
    (Phase 2b post, KB-3m, KB-3k, uLo decomposition, KB-6b). -/
theorem div128Quot_kb6c_pure_nat
    (q1' q0' rhat2' un21 uHi uLo vTop dHi dLo div_un1 div_un0 r1 : Nat)
    (h_phase2b : q0' * dHi + rhat2' = un21)
    (h_kb3m : un21 + r1 * 2^64 + q1' * vTop = uHi * 2^32 + div_un1)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_uLo : uLo = div_un1 * 2^32 + div_un0)
    (hq0' : q0' < 2^32)
    (hdLo : dLo < 2^32)
    (hvTopNorm : vTop ≥ 2^63) :
    q1' * 2^32 + q0' ≤ (uHi * 2^64 + uLo) / vTop + 2 := by
  have h_ineq := div128Quot_kb6c_assembly_inequality
    q1' q0' rhat2' un21 uHi uLo vTop dHi dLo div_un1 div_un0 r1
    h_phase2b h_kb3m h_vTop h_uLo
  have h_q0_dLo := div128Quot_kb6c_q0_dLo_bound q0' dLo vTop hq0' hdLo hvTopNorm
  have h_combined :
      (q1' * 2^32 + q0') * vTop ≤ uHi * 2^64 + uLo + 2 * vTop := by omega
  have hvTop_pos : 0 < vTop := by omega
  exact Nat_le_div_add_two_of_mul_le _ _ _ hvTop_pos h_combined

/-- **KB-6c-pure-nat-strict: tight version of pure-Nat KB-6c**.

    Under the additional Phase 2 no-wrap hypothesis
    `q0' * dLo ≤ rhat2' * 2^32 + div_un0`, the bound tightens by 2:

    ```
    q1' * 2^32 + q0' ≤ (uHi * 2^64 + uLo) / vTop
    ```

    (no `+2`). This matches the tighter `div128Quot_qHat_vTop_le`
    bound from `Div128CallSkipClose.lean` (Task 1's
    `qHat * vTop ≤ uHi*2^64 + uLo`).

    Proof: KB-6c-aux1's identity
    `(q1'*2^32 + q0')*vTop + rhat2'*2^32 + r1*2^96 + div_un0 =
       uHi*2^64 + uLo + q0'*dLo`
    plus Phase 2 no-wrap (`q0'*dLo ≤ rhat2'*2^32 + div_un0`) gives
    `(q1'*2^32 + q0')*vTop ≤ uHi*2^64 + uLo`, then `Nat.le_div_iff_mul_le`
    closes. -/
theorem div128Quot_kb6c_pure_nat_strict
    (q1' q0' rhat2' un21 uHi uLo vTop dHi dLo div_un1 div_un0 r1 : Nat)
    (h_phase2b : q0' * dHi + rhat2' = un21)
    (h_kb3m : un21 + r1 * 2^64 + q1' * vTop = uHi * 2^32 + div_un1)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_uLo : uLo = div_un1 * 2^32 + div_un0)
    (h_phase2_no_wrap : q0' * dLo ≤ rhat2' * 2^32 + div_un0)
    (hvTop_pos : 0 < vTop) :
    q1' * 2^32 + q0' ≤ (uHi * 2^64 + uLo) / vTop := by
  have h_id := div128Quot_kb6c_assembly_identity
    q1' q0' rhat2' un21 uHi uLo vTop dHi dLo div_un1 div_un0 r1
    h_phase2b h_kb3m h_vTop h_uLo
  -- h_id: (q1'*2^32 + q0')*vTop + rhat2'*2^32 + r1*2^96 + div_un0
  --       = uHi*2^64 + uLo + q0'*dLo.
  -- Combined with q0'*dLo ≤ rhat2'*2^32 + div_un0:
  -- (q1'*2^32 + q0')*vTop ≤ uHi*2^64 + uLo.
  have h_mul_bound :
      (q1' * 2^32 + q0') * vTop ≤ uHi * 2^64 + uLo := by omega
  exact (Nat.le_div_iff_mul_le hvTop_pos).mpr h_mul_bound

/-- **KB-6c: Quotient assembly upper bound (STUB).**

    The Nat-level composition of Phase 1b and Phase 2b quotient bounds:

    ```
    q1'.toNat * 2^32 + q0'.toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 2
    ```

    **Proof outline** (sub-decomposition):
    - **`div128Quot_kb6c_assembly_identity`** (CLOSED, pure Nat): the
      algebraic identity `(q1'*2^32 + q0')*vTop + correction =
      uHi*2^64 + uLo + q0'*dLo` from the three Euclideans + decomps.
    - From this, derive `(q1'*2^32 + q0')*vTop ≤ uHi*2^64 + uLo + q0'*dLo`
      (drop non-negative correction terms).
    - Bound `q0'*dLo ≤ 2*vTop` via Knuth-B: q0' ≤ 2^32 (KB-6b), dLo < 2^32,
      so q0'*dLo < 2^64 ≤ 2*vTop (under vTop ≥ 2^63).
    - Use Nat-division: from `X*vTop ≤ Y + 2*vTop`, get `X ≤ Y/vTop + 2`.

    Equivalent to **Knuth Theorem B for the assembled 64-bit quotient**,
    instantiated to our algorithm's specific control flow. Tracked in
    issue #1337. -/
theorem div128Quot_q1_prime_q0_prime_le_q_true_plus_two
    (uHi uLo vTop : Word)
    (hvTop_norm : vTop.toNat ≥ 2^63)
    (hcall : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64)
    (h_inv : Div128PhaseNoWrapInv uHi uLo vTop) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q1'.toNat * 2^32 + q0'.toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 2 := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0'
  -- (Mirror KB-6d's preconditions derivation.)
  have h_vtop := div128Quot_vTop_decomp vTop
  simp only [] at h_vtop
  have hdHi_ge : dHi.toNat ≥ 2^31 := by
    show (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : vTop.toNat ≥ 2^63 := hvTop_norm
    have : (2^63 : Nat) = 2^31 * 2^32 := by decide
    omega
  have hdHi_lt : dHi.toNat < 2^32 := by
    show (vTop >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h := vTop.isLt; omega
  have hdLo_lt : dLo.toNat < 2^32 := by
    show ((vTop <<< (32 : BitVec 6).toNat) >>>
          (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_shiftLeft]
    have h_mod : (vTop.toNat * 2^(32 : BitVec 6).toNat) % 2^64 < 2^64 :=
      Nat.mod_lt _ (by norm_num)
    omega
  have h_uHi_lt_vTop_raw : uHi.toNat < vTop.toNat := by
    by_contra h; push Not at h
    have : vTop.toNat * 2^64 ≤ uHi.toNat * 2^64 := Nat.mul_le_mul_right _ h
    have huLo := uLo.isLt
    have : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64 := hcall
    omega
  have huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vtop]; exact h_uHi_lt_vTop_raw
  -- Apply Knuth-C invariant (now an EXPLICIT HYPOTHESIS h_inv).
  simp only [Div128PhaseNoWrapInv] at h_inv
  obtain ⟨h_un21_lt, h_no_wrap⟩ := h_inv
  -- Discharge h_kb3m via KB-3m + no-wrap conjunct.
  have h_kb3m_partial :=
    div128Quot_un21_additive_identity uHi dHi dLo uLo vTop rhatUn1
      hdHi_ge hdLo_lt huHi_lt_vTop rfl rfl
  simp only [] at h_kb3m_partial
  have h_kb3m : un21.toNat + (rhat'.toNat / 2^32) * 2^64 +
      q1'.toNat * vTop.toNat = uHi.toNat * 2^32 + div_un1.toNat :=
    h_kb3m_partial h_no_wrap
  -- Discharge h_phase2b via Phase 2b post.
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_post_phase2a :=
    div128Quot_first_round_post un21 dHi hdHi_ne hdHi_lt
  simp only [] at h_post_phase2a
  have h_rhat2c_bound :=
    div128Quot_rhatc_lt_2dHi un21 dHi hdHi_ne hdHi_lt
  simp only [] at h_rhat2c_bound
  have h_phase2b_full :=
    @div128Quot_phase2b_post div_un0 un21 dHi hdHi_lt q0c rhat2c dLo
      h_post_phase2a h_rhat2c_bound
  simp only [] at h_phase2b_full
  -- h_phase2b_full conclusion uses an `if`-guarded rhat2'; need just q0' part.
  -- The Euclidean form `q0'*dHi + rhat2'_some = un21` for some rhat2'.
  -- Set rhat2'_used as the if-guarded value from h_phase2b_full's let.
  set rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat with hrhat2cHi_def
  set rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0 with hrhat2Un0_def
  let rhat2'_used : Word :=
    if rhat2cHi = 0 then
      (if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c)
    else rhat2c
  have h_phase2b : q0'.toNat * dHi.toNat + rhat2'_used.toNat = un21.toNat :=
    h_phase2b_full
  -- Discharge hq0' < 2^32 via KB-6b.
  have h_q0'_lt :=
    div128Quot_q0_prime_lt_pow32 _ _ _ uLo hdHi_ge hdHi_lt hdLo_lt h_un21_lt
  simp only [] at h_q0'_lt
  -- uLo decomposition.
  have h_uLo : uLo.toNat = div_un1.toNat * 2^32 + div_un0.toNat := by
    show uLo.toNat = (uLo >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
        BitVec.toNat_shiftLeft, bv6_toNat_32]
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have h_lo : uLo.toNat * 2^32 % 2^64 / 2^32 = uLo.toNat % 2^32 := by
      have := uLo.isLt; omega
    rw [h_lo]
    have := Nat.div_add_mod uLo.toNat (2^32)
    omega
  -- Apply pure-Nat KB-6c.
  exact div128Quot_kb6c_pure_nat
    q1'.toNat q0'.toNat rhat2'_used.toNat un21.toNat
    uHi.toNat uLo.toNat vTop.toNat dHi.toNat dLo.toNat
    div_un1.toNat div_un0.toNat (rhat'.toNat / 2^32)
    h_phase2b h_kb3m h_vtop h_uLo h_q0'_lt hdLo_lt hvTop_norm

/-- **KB-6d: `div128Quot` upper bound (Knuth Theorem B at div128Quot level).**

    The user-facing closing theorem of Knuth Theorem B for `div128Quot`:

    ```
    (div128Quot uHi uLo vTop).toNat ≤ (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 2
    ```

    under standard preconditions:
    - `vTop.toNat ≥ 2^63` (normalized divisor — top bit set).
    - `uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64` (no-overflow / call-path:
      the dividend fits in a single 64-bit quotient digit's range times `2^64`).

    This is the bound that downstream call-trial DIV/MOD stack specs need
    to reason about the at-most-2-addback correction chain.

    **Composition** (sub-stubs separated for tractable proof attempts):
    1. **`div128Quot_un21_lt_vTop`** (STUB, Knuth-C): `un21 < vTop`.
    2. **`div128Quot_q0_prime_lt_pow32`** (KB-6b, CLOSED): under `un21 < vTop`,
       `q0' < 2^32`.
    3. **`div128Quot_toNat_eq_strict`** (KB-6a strict, CLOSED): under `q0' < 2^32`,
       `div128Quot.toNat = q1'.toNat * 2^32 + q0'.toNat`.
    4. **`div128Quot_q1_prime_q0_prime_le_q_true_plus_two`** (KB-6c, STUB):
       `q1' * 2^32 + q0' ≤ q_true + 2`.

    The composition itself is a mechanical chain of `have`s once the
    two stubs above are filled. The hard math is isolated in those two
    stubs:
    - **`div128Quot_un21_lt_vTop`** (Knuth-C, ~300-400 lines).
    - **`div128Quot_q1_prime_q0_prime_le_q_true_plus_two`** (KB-6c Nat
      assembly, ~80-150 lines).

    Tracked in issue #1337. -/
theorem div128Quot_le_q_true_plus_two (uHi uLo vTop : Word)
    (hvTop_norm : vTop.toNat ≥ 2^63)
    (hcall : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64)
    (h_inv : Div128PhaseNoWrapInv uHi uLo vTop) :
    (div128Quot uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 2 := by
  -- Step 0: derive intermediate preconditions from hvTop_norm + hcall.
  -- vTop = dHi * 2^32 + dLo  (KB-3k, unconditional).
  have h_vtop := div128Quot_vTop_decomp vTop
  simp only [] at h_vtop
  -- hdHi_ge: dHi ≥ 2^31  (from vTop ≥ 2^63 + decomp + dLo < 2^32).
  have hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h1 : vTop.toNat ≥ 2^63 := hvTop_norm
    have h2 : (2^63 : Nat) = 2^31 * 2^32 := by decide
    omega
  -- hdHi_lt: dHi < 2^32  (from vTop < 2^64).
  have hdHi_lt : (vTop >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h := vTop.isLt
    omega
  -- hdLo_lt: dLo < 2^32  (mod-2^32 of a Nat).
  have hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                  (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_shiftLeft]
    have h_mod : (vTop.toNat * 2^(32 : BitVec 6).toNat) % 2^64 < 2^64 :=
      Nat.mod_lt _ (by norm_num)
    omega
  -- huHi_lt_vTop: uHi < vTop  (from hcall + uLo ≥ 0; written via dHi*2^32+dLo).
  have h_uHi_lt_vTop_raw : uHi.toNat < vTop.toNat := by
    by_contra h
    push Not at h
    have : vTop.toNat * 2^64 ≤ uHi.toNat * 2^64 := Nat.mul_le_mul_right _ h
    have huLo := uLo.isLt
    have : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64 := hcall
    omega
  have huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_vtop]; exact h_uHi_lt_vTop_raw
  -- Step 1: extract un21 < vTop ∧ no-wrap from explicit hypothesis.
  have h_inv_unfolded := h_inv
  simp only [Div128PhaseNoWrapInv] at h_inv_unfolded
  have h_un21_lt := h_inv_unfolded.1
  -- Step 2: q0' < 2^32  (KB-6b, CLOSED, requires un21 < vTop).
  have h_q0'_lt :=
    div128Quot_q0_prime_lt_pow32 _ _ _ uLo hdHi_ge hdHi_lt hdLo_lt h_un21_lt
  simp only [] at h_q0'_lt
  -- Step 3: div128Quot.toNat = q1'.toNat * 2^32 + q0'.toNat  (KB-6a strict, CLOSED).
  have h_eq :=
    div128Quot_toNat_eq_strict uHi uLo vTop
      hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop
  simp only [] at h_eq
  -- Step 4: q1'.toNat * 2^32 + q0'.toNat ≤ q_true + 2  (KB-6c, conditional).
  have h_assemble :=
    div128Quot_q1_prime_q0_prime_le_q_true_plus_two uHi uLo vTop
      hvTop_norm hcall h_inv
  simp only [] at h_assemble
  -- Step 5: combine.
  rw [h_eq h_q0'_lt]
  exact h_assemble

/-- **Strict variant of KB-6c parent**: tight assembly bound under
    the all-phases no-wrap invariant.

    Mirrors `div128Quot_q1_prime_q0_prime_le_q_true_plus_two` but
    drops the `+2` looseness by also assuming Phase 2 no-wrap.

    ```
    q1'.toNat * 2^32 + q0'.toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat
    ```

    Composed via `div128Quot_kb6c_pure_nat_strict`. -/
theorem div128Quot_q1_prime_q0_prime_le_q_true_strict
    (uHi uLo vTop : Word)
    (hvTop_norm : vTop.toNat ≥ 2^63)
    (hcall : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64)
    (h_inv : Div128AllPhasesNoWrapInv uHi uLo vTop) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q1'.toNat * 2^32 + q0'.toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0'
  have h_vtop := div128Quot_vTop_decomp vTop
  simp only [] at h_vtop
  have hdHi_ge : dHi.toNat ≥ 2^31 := by
    show (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : vTop.toNat ≥ 2^63 := hvTop_norm
    have : (2^63 : Nat) = 2^31 * 2^32 := by decide
    omega
  have hdHi_lt : dHi.toNat < 2^32 := by
    show (vTop >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h := vTop.isLt; omega
  have hdLo_lt : dLo.toNat < 2^32 := by
    show ((vTop <<< (32 : BitVec 6).toNat) >>>
          (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_shiftLeft]
    have h_mod : (vTop.toNat * 2^(32 : BitVec 6).toNat) % 2^64 < 2^64 :=
      Nat.mod_lt _ (by norm_num)
    omega
  have h_uHi_lt_vTop_raw : uHi.toNat < vTop.toNat := by
    by_contra h; push Not at h
    have : vTop.toNat * 2^64 ≤ uHi.toNat * 2^64 := Nat.mul_le_mul_right _ h
    have huLo := uLo.isLt
    have : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64 := hcall
    omega
  have huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vtop]; exact h_uHi_lt_vTop_raw
  -- Extract three conjuncts from the all-phases invariant.
  simp only [Div128AllPhasesNoWrapInv] at h_inv
  obtain ⟨h_un21_lt, h_no_wrap, h_phase2_no_wrap⟩ := h_inv
  -- Discharge h_kb3m via KB-3m + Phase 1 no-wrap conjunct.
  have h_kb3m_partial :=
    div128Quot_un21_additive_identity uHi dHi dLo uLo vTop rhatUn1
      hdHi_ge hdLo_lt huHi_lt_vTop rfl rfl
  simp only [] at h_kb3m_partial
  have h_kb3m : un21.toNat + (rhat'.toNat / 2^32) * 2^64 +
      q1'.toNat * vTop.toNat = uHi.toNat * 2^32 + div_un1.toNat :=
    h_kb3m_partial h_no_wrap
  -- Discharge h_phase2b via Phase 2b post.
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_post_phase2a :=
    div128Quot_first_round_post un21 dHi hdHi_ne hdHi_lt
  simp only [] at h_post_phase2a
  have h_rhat2c_bound :=
    div128Quot_rhatc_lt_2dHi un21 dHi hdHi_ne hdHi_lt
  simp only [] at h_rhat2c_bound
  have h_phase2b_full :=
    @div128Quot_phase2b_post div_un0 un21 dHi hdHi_lt q0c rhat2c dLo
      h_post_phase2a h_rhat2c_bound
  simp only [] at h_phase2b_full
  set rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat with hrhat2cHi_def
  set rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0 with hrhat2Un0_def
  let rhat2'_used : Word :=
    if rhat2cHi = 0 then
      (if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c)
    else rhat2c
  have h_phase2b : q0'.toNat * dHi.toNat + rhat2'_used.toNat = un21.toNat :=
    h_phase2b_full
  -- uLo decomposition.
  have h_uLo : uLo.toNat = div_un1.toNat * 2^32 + div_un0.toNat := by
    show uLo.toNat = (uLo >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
        BitVec.toNat_shiftLeft, bv6_toNat_32]
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have h_lo : uLo.toNat * 2^32 % 2^64 / 2^32 = uLo.toNat % 2^32 := by
      have := uLo.isLt; omega
    rw [h_lo]
    have := Nat.div_add_mod uLo.toNat (2^32)
    omega
  have hvTop_pos : 0 < vTop.toNat := by omega
  exact div128Quot_kb6c_pure_nat_strict
    q1'.toNat q0'.toNat rhat2'_used.toNat un21.toNat
    uHi.toNat uLo.toNat vTop.toNat dHi.toNat dLo.toNat
    div_un1.toNat div_un0.toNat (rhat'.toNat / 2^32)
    h_phase2b h_kb3m h_vtop h_uLo h_phase2_no_wrap hvTop_pos

/-- **Strict KB-6d**: `div128Quot.toNat ≤ q_true` (no `+2`) under the
    all-phases no-wrap invariant.

    Tight version of `div128Quot_le_q_true_plus_two`. Composes
    KB-6a strict + the strict KB-6c parent. -/
theorem div128Quot_le_q_true (uHi uLo vTop : Word)
    (hvTop_norm : vTop.toNat ≥ 2^63)
    (hcall : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64)
    (h_inv : Div128AllPhasesNoWrapInv uHi uLo vTop) :
    (div128Quot uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat := by
  -- Derive intermediate preconditions (mirror KB-6d's preconditions block).
  have h_vtop := div128Quot_vTop_decomp vTop
  simp only [] at h_vtop
  have hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h1 : vTop.toNat ≥ 2^63 := hvTop_norm
    have h2 : (2^63 : Nat) = 2^31 * 2^32 := by decide
    omega
  have hdHi_lt : (vTop >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h := vTop.isLt; omega
  have hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                  (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_shiftLeft]
    have h_mod : (vTop.toNat * 2^(32 : BitVec 6).toNat) % 2^64 < 2^64 :=
      Nat.mod_lt _ (by norm_num)
    omega
  have h_uHi_lt_vTop_raw : uHi.toNat < vTop.toNat := by
    by_contra h; push Not at h
    have : vTop.toNat * 2^64 ≤ uHi.toNat * 2^64 := Nat.mul_le_mul_right _ h
    have huLo := uLo.isLt
    have : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64 := hcall
    omega
  have huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_vtop]; exact h_uHi_lt_vTop_raw
  -- Extract un21 < vTop from the all-phases invariant for KB-6b.
  have h_inv_unfolded := h_inv
  simp only [Div128AllPhasesNoWrapInv] at h_inv_unfolded
  have h_un21_lt := h_inv_unfolded.1
  -- KB-6b: q0' < 2^32.
  have h_q0'_lt :=
    div128Quot_q0_prime_lt_pow32 _ _ _ uLo hdHi_ge hdHi_lt hdLo_lt h_un21_lt
  simp only [] at h_q0'_lt
  -- KB-6a strict: div128Quot.toNat = q1'.toNat * 2^32 + q0'.toNat.
  have h_eq :=
    div128Quot_toNat_eq_strict uHi uLo vTop
      hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop
  simp only [] at h_eq
  -- Strict KB-6c: q1'.toNat * 2^32 + q0'.toNat ≤ q_true.
  have h_assemble :=
    div128Quot_q1_prime_q0_prime_le_q_true_strict uHi uLo vTop
      hvTop_norm hcall h_inv
  simp only [] at h_assemble
  rw [h_eq h_q0'_lt]
  exact h_assemble

end EvmAsm.Evm64
