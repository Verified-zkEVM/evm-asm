/-
  EvmAsm.Evm64.DivMod.LoopDefs.IterV4Invariants

  Word-level no-wrap invariants for `div128Quot_v4` — the algorithm
  with full Knuth D3 2-correction in BOTH phases.

  Phase-1 content (slim). Phase-2 content lives in
  `IterV4InvariantsPhase2.lean`. Phase-1 helpers live in
  `IterV4InvariantsHelpers.lean`. Phase-1 overshoot dispatchers and
  `_phase1_perfect` live in `IterV4InvariantsOvershoots.lean`
  (split for the file-size guardrail, issue #1419).

  These re-derive the invariants that were deleted from v2 in PR #1393
  (commit `037579c1`) when sub-case b of `phase2_no_wrap_lo` was proven
  FALSE in double-addback for v2's 1-correction Phase-2.

  Under v4, with q0'' = q*_phase2 exactly, the no-wrap invariants are
  expected to hold UNCONDITIONALLY (not just under runtime
  preconditions).

  Critical-path target for issue #1337 → issue #61 stack spec closure.
-/

import EvmAsm.Evm64.DivMod.LoopDefs.IterV4InvariantsOvershoots

namespace EvmAsm.Evm64

open EvmAsm.Rv64


/-- **Pure-Nat algebraic core for un21 < vTop.**

    Given Phase-1 perfect (`(q1'' + 1) * vTop > uHi*2^32 + div_un1`)
    plus Phase-1 Euclidean (`rhat'' = uHi - q1''*dHi`,
    `q1'' * dHi ≤ uHi`) and the Phase-1 no-wrap bound, derives
    `rhat'' * 2^32 + div_un1 - q1'' * dLo < vTop`.

    Proof: substitute rhat'' and simplify. Final step is an omega
    inequality once products are expanded. -/
theorem div128Quot_v4_un21_lt_vTop_arith
    (uHi vTop dHi dLo div_un1 q1'' rhat'' : Nat)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_q1''_succ_gt : (q1'' + 1) * vTop > uHi * 2^32 + div_un1)
    (h_rhat''_eq : rhat'' = uHi - q1'' * dHi)
    (h_q1''_dHi_le : q1'' * dHi ≤ uHi)
    (h_no_wrap : q1'' * dLo ≤ rhat'' * 2^32 + div_un1) :
    rhat'' * 2^32 + div_un1 - q1'' * dLo < vTop := by
  -- Linearize products via `set`.
  set A := q1'' * dHi * 2 ^ 32 with hA
  set B := q1'' * dLo with hB
  -- Expand rhat'' * 2^32 = (uHi - q1''*dHi) * 2^32 = uHi*2^32 - A.
  have h_rhat_mul : rhat'' * 2 ^ 32 = uHi * 2 ^ 32 - A := by
    rw [h_rhat''_eq, Nat.sub_mul]
  have h_A_le : A ≤ uHi * 2 ^ 32 :=
    Nat.mul_le_mul_right _ h_q1''_dHi_le
  -- Expand (q1''+1)*vTop = A + B + dHi*2^32 + dLo.
  have h_succ_eq : (q1'' + 1) * vTop = A + B + (dHi * 2 ^ 32 + dLo) := by
    rw [h_vTop, Nat.add_mul, Nat.one_mul, Nat.mul_add, ← Nat.mul_assoc]
  rw [h_succ_eq] at h_q1''_succ_gt
  rw [h_rhat_mul, h_vTop]
  omega


/-- **Pure-Nat truncation-absorbing un21 < vTop.**

    Strengthens `_un21_lt_vTop_arith` to handle the Word-level
    truncation in `(rhat'' << 32) | div_un1`: when `rhat'' ≥ 2^32`,
    the OR-shift truncates to `rhat'' mod 2^32`, but the modular
    Word subtraction `cu_rhat_un1 - cu_q1_dlo` absorbs the truncation
    correctly. Result: `un21.toNat = Phase-1 remainder < vTop`.

    Proof outline: case-split on `k = rhat'' / 2^32 ∈ {0, 1}`.
    The bound `rhat'' < 2^33` follows from `q1'' * dLo < 2^64` plus
    `Phase-1 remainder < vTop ≤ 2^64`. Both branches reduce to the
    Phase-1 remainder bound from `_un21_lt_vTop_arith`. -/
theorem div128Quot_v4_un21_lt_vTop_truncation_arith
    (uHi vTop dHi dLo div_un1 q1'' rhat'' : Nat)
    (h_vTop_eq : vTop = dHi * 2^32 + dLo)
    (h_dLo_lt : dLo < 2^32)
    (h_vTop_le : vTop ≤ 2^64)
    (h_q1''_succ_gt : (q1'' + 1) * vTop > uHi * 2^32 + div_un1)
    (h_q1''_dHi_le : q1'' * dHi ≤ uHi)
    (h_rhat''_eq : rhat'' = uHi - q1'' * dHi)
    (h_no_wrap : q1'' * dLo ≤ rhat'' * 2^32 + div_un1)
    (h_q1''_le : q1'' ≤ 2^32) :
    ((rhat'' % 2^32) * 2^32 + div_un1 + 2^64 - q1'' * dLo) % 2^64 < vTop := by
  -- The Phase-1 remainder bound (without truncation).
  have h_rem_lt : rhat'' * 2^32 + div_un1 - q1'' * dLo < vTop :=
    div128Quot_v4_un21_lt_vTop_arith uHi vTop dHi dLo div_un1 q1'' rhat''
      h_vTop_eq h_q1''_succ_gt h_rhat''_eq h_q1''_dHi_le h_no_wrap
  -- Phase-1 remainder also < 2^64.
  have h_rem_lt_pow64 : rhat'' * 2^32 + div_un1 - q1'' * dLo < 2^64 :=
    lt_of_lt_of_le h_rem_lt h_vTop_le
  -- Q*dLo < 2^64.
  have h_QdLo_lt : q1'' * dLo < 2^64 := by
    calc q1'' * dLo
        ≤ 2^32 * dLo := Nat.mul_le_mul_right _ h_q1''_le
      _ < 2^32 * 2^32 := (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr h_dLo_lt
      _ = 2^64 := by decide
  -- rhat'' < 2^33: rhat''*2^32 + div_un1 = q1''*dLo + r_phase1 < 2^64 + 2^64 = 2^65.
  have h_rhat_lt : rhat'' < 2^33 := by
    by_contra h_not
    have h_ge : 2^33 ≤ rhat'' := Nat.le_of_not_lt h_not
    have h1 : 2^65 ≤ rhat'' * 2^32 := by
      calc (2^65 : Nat) = 2^33 * 2^32 := by decide
        _ ≤ rhat'' * 2^32 := Nat.mul_le_mul_right _ h_ge
    omega
  -- Decompose rhat'' = (rhat'' / 2^32) * 2^32 + rhat'' % 2^32.
  have h_div_mod : (rhat'' / 2^32) * 2^32 + (rhat'' % 2^32) = rhat'' := by
    have := Nat.div_add_mod rhat'' (2^32)
    linarith
  have h_mod_lt : rhat'' % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
  -- k = rhat'' / 2^32 ≤ 1.
  have h_k_le : rhat'' / 2^32 ≤ 1 := by
    have h1 : rhat'' < 2 * 2^32 := by
      have : (2 * 2^32 : Nat) = 2^33 := by decide
      omega
    omega
  -- Case split: k = 0 or k = 1.
  interval_cases (rhat'' / 2^32)
  · -- k = 0: rhat'' = rhat'' % 2^32, so rhat'' < 2^32.
    have h_rhat_eq : rhat'' = rhat'' % 2^32 := by omega
    have h_rhat_lt32 : rhat'' < 2^32 := by omega
    -- Goal becomes: (rhat''*2^32 + div_un1 + 2^64 - q1''*dLo) % 2^64 < vTop.
    have h_eq1 : rhat'' % 2^32 = rhat'' := h_rhat_eq.symm
    rw [h_eq1]
    -- Rewrite (rhat''*2^32 + div_un1 + 2^64 - q1''*dLo) = r_phase1 + 2^64.
    have h_eq2 : rhat'' * 2^32 + div_un1 + 2^64 - q1'' * dLo
              = (rhat'' * 2^32 + div_un1 - q1'' * dLo) + 2^64 := by omega
    rw [h_eq2]
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt h_rem_lt_pow64]
    exact h_rem_lt
  · -- k = 1: rhat'' = 2^32 + rhat'' % 2^32, so 2^32 ≤ rhat'' < 2^33.
    have h_rhat_eq : rhat'' = 2^32 + rhat'' % 2^32 := by omega
    -- (rhat'' % 2^32)*2^32 + 2^64 = rhat''*2^32.
    have h_mul_eq : (rhat'' % 2^32) * 2^32 + 2^64 = rhat'' * 2^32 := by
      conv_rhs => rw [h_rhat_eq]
      ring
    -- Substitute.
    have h_eq : (rhat'' % 2^32) * 2^32 + div_un1 + 2^64 - q1'' * dLo
              = rhat'' * 2^32 + div_un1 - q1'' * dLo := by omega
    rw [h_eq, Nat.mod_eq_of_lt h_rem_lt_pow64]
    exact h_rem_lt


/-- **Phase-1 final Euclidean bridge (v4)**: after v4's 2-correction
    Phase-1b, the post-correction `q1''` and `rhat''` satisfy the
    Phase-1a Euclidean at the Nat level:

    ```
    q1''.toNat * dHi.toNat ≤ uHi.toNat
    rhat''.toNat = uHi.toNat - q1''.toNat * dHi.toNat
    rhat''.toNat < 2 ^ 32   -- ⚠ FALSE in some cases — see below
    ```

    Each Phase-1b correction maintains the Word-level invariant
    `q*dHi + rhat = uHi`. Bridging through 2 corrections reduces to the
    `_phase1_rhatc_bridge` already proven for q1c/rhatc, plus reasoning
    about the `phase2b_q0'` decrement + corresponding rhat increment.

    **⚠ KNOWN ISSUE (2026-04-28)**: Empirical search found counterexamples
    where `rhat''.toNat ≥ 2^32` after Phase-1b 2-correction (concrete:
    dHi=2^31, dLo=2^32-1, uHi=9223371822106411008 gives rhat''=2^32).
    The third claim is therefore FALSE under some shift-normalized
    inputs. v4's algorithm STILL produces the correct full quotient
    (verified empirically) — the Phase-2 setup `(rhat'' << 32) | div_un1`
    truncates rhat'' to its low 32 bits, but the downstream Phase-2
    div arithmetic still yields the right answer via different
    mechanism than `_un21_lt_vTop`'s current proof.

    **CONSEQUENCE**: my proof of `_un21_lt_vTop` (which uses this bridge)
    has a soundness gap in the rhat'' ≥ 2^32 cases. The proof is
    structurally correct GIVEN the bridge, but the bridge's third claim
    is wrong. Need to either:
    - Drop the third claim and re-prove `_un21_lt_vTop` differently
      (handle rhat'' ≥ 2^32 case via the truncation mechanism).
    - Find a tighter algorithmic invariant that holds universally.

    Stub kept for now to expose the gap. Sorry intentional. -/
theorem div128Quot_v4_phase1_final_eucl_bridge
    (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    q1''.toNat * dHi.toNat ≤ uHi.toNat ∧
    rhat''.toNat = uHi.toNat - q1''.toNat * dHi.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
  have hdHi_ge : dHi.toNat ≥ 2^31 :=
    div128Quot_dHi_ge_pow31 vTop h_vTop_ge_pow63
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  have h_uHi_lt_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact h_uHi_lt_vTop
  -- Phase-1a Eucl on (q1c, rhatc).
  obtain ⟨h_q1c_dHi_le, h_rhatc_eq⟩ :=
    div128Quot_v4_phase1_rhatc_bridge uHi vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_q1c_lt_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt h_uHi_lt_decomp
  -- rhatc < 2*dHi, so rhatc + dHi < 3*dHi < 2^64.
  have h_rhatc_lt_2_dHi : rhatc.toNat < 2 * dHi.toNat :=
    div128Quot_v4_phase1_rhatc_lt_2_dHi uHi vTop h_vTop_ge_pow63 h_uHi_lt_vTop
  have h_rhatc_dHi_no_overflow : rhatc.toNat + dHi.toNat < 2^64 := by
    have h1 : rhatc.toNat + dHi.toNat < 3 * dHi.toNat := by linarith
    have h2 : 3 * dHi.toNat < 3 * 2^32 := by linarith
    linarith [show (3 : Nat) * 2^32 < 2^64 from by decide]
  -- 1st correction: Eucl on (q1', rhat').
  obtain ⟨h_q1'_dHi_le, h_rhat'_eq⟩ :=
    div128Quot_v4_phase1_one_correction_eucl
      uHi q1c rhatc dHi dLo div_un1
      hdHi_lt h_q1c_dHi_le h_rhatc_eq h_q1c_lt_pow32 h_rhatc_dHi_no_overflow
  -- q1'.toNat ≤ q1c.toNat ≤ 2^32 (phase2b_q0' returns q1c or q1c - 1).
  have h_q1'_le_q1c : q1'.toNat ≤ q1c.toNat := by
    show (div128Quot_phase2b_q0' q1c rhatc dLo div_un1).toNat ≤ q1c.toNat
    unfold div128Quot_phase2b_q0'
    by_cases h_g : rhatc >>> (32 : BitVec 6).toNat = 0
    · simp only [h_g, if_true]
      by_cases h_b : BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) (q1c * dLo)
      · rw [if_pos h_b, BitVec.toNat_add, signExtend12_4095_toNat]
        -- (q1c + 2^64 - 1) mod 2^64. If q1c.toNat = 0, this is 2^64 - 1.
        -- If q1c.toNat ≥ 1, this is q1c.toNat - 1 ≤ q1c.toNat.
        -- BLTU firing implies q1c ≥ 1 (since q1c * dLo > 0).
        by_cases h_q1c_zero : q1c.toNat = 0
        · -- Contradiction: BLTU fires but q1c * dLo = 0.
          exfalso
          have h_q1c_dLo_zero : (q1c * dLo).toNat = 0 := by
            rw [BitVec.toNat_mul, h_q1c_zero, Nat.zero_mul, Nat.zero_mod]
          have := BitVec.ult_iff_toNat_lt.mp h_b
          rw [h_q1c_dLo_zero] at this
          exact Nat.not_lt_zero _ this
        · have h_q1c_pos : q1c.toNat ≥ 1 := by omega
          have hq1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
          rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt hq1c_lt_word]
          omega
      · rw [if_neg h_b]
    · simp only [h_g, if_false]; rfl
  have h_q1'_lt_pow32 : q1'.toNat ≤ 2^32 := le_trans h_q1'_le_q1c h_q1c_lt_pow32
  -- rhat'.toNat ≤ rhatc.toNat + dHi.toNat (rhat' = rhatc or rhatc + dHi).
  have h_rhat'_le : rhat'.toNat ≤ rhatc.toNat + dHi.toNat := by
    show (if rhatc >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1)
                            (q1c * dLo)
             then rhatc + dHi else rhatc)
          else rhatc).toNat ≤ rhatc.toNat + dHi.toNat
    by_cases h_g : rhatc >>> (32 : BitVec 6).toNat = 0
    · simp only [h_g, if_true]
      by_cases h_b : BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) (q1c * dLo)
      · rw [if_pos h_b, BitVec.toNat_add]
        exact le_of_eq (Nat.mod_eq_of_lt h_rhatc_dHi_no_overflow)
      · rw [if_neg h_b]; linarith
    · simp only [h_g, if_false]; linarith
  -- rhat'.toNat + dHi.toNat < 2^64.
  have h_rhat'_dHi_no_overflow : rhat'.toNat + dHi.toNat < 2^64 := by
    have : rhat'.toNat + dHi.toNat ≤ rhatc.toNat + 2 * dHi.toNat := by linarith
    have : rhatc.toNat + 2 * dHi.toNat < 4 * dHi.toNat := by linarith
    have : 4 * dHi.toNat < 4 * 2^32 := by linarith
    linarith [show (4 : Nat) * 2^32 < 2^64 from by decide]
  -- 2nd correction: Eucl on (q1'', rhat'').
  exact div128Quot_v4_phase1_one_correction_eucl
    uHi q1' rhat' dHi dLo div_un1
    hdHi_lt h_q1'_dHi_le h_rhat'_eq h_q1'_lt_pow32 h_rhat'_dHi_no_overflow


/-- **Phase-1 no-wrap (v4)**: after v4's 2-correction Phase-1b, the
    quotient `q1''` doesn't overshoot the Phase-1 sub-divisor's remainder
    word, so the Phase-2 setup `un21 = (rhat'' << 32 | div_un1) -
    q1'' * dLo` doesn't underflow.

    Symmetric to the top-level `_phase2_no_wrap_lo` (Phase-2 version):
    just swap the indices (q1''→q0'', rhat''→rhat2'', div_un1→div_un0).
    Both are corollaries of the corresponding `_perfect` lemma plus
    Knuth's classical D3 invariant.

    Pure-Word stub for now; depends on `_phase1_perfect`. -/
theorem div128Quot_v4_phase1_no_wrap_lo (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    q1''.toNat * dLo.toNat ≤ rhat''.toNat * 2^32 + div_un1.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
  -- `_phase1_perfect` gives q1''.toNat = q_true.
  have h_perfect := div128Quot_v4_phase1_perfect uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  -- Phase-1 final Euclidean bridge: q1''*dHi + rhat'' = uHi at toNat.
  have h_bridge := div128Quot_v4_phase1_final_eucl_bridge uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q1''_dHi_le, h_rhat''_eq⟩ := h_bridge
  -- Apply pure-Nat helper: q1'' ≤ q_true gives the no-wrap inequality.
  have h_q1''_le : q1''.toNat ≤ (uHi.toNat * 2 ^ 32 + div_un1.toNat) / vTop.toNat := by
    rw [h_perfect]
    have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
      div128Quot_vTop_decomp vTop
    rw [h_decomp]
  have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  exact div128Quot_v4_phase1_no_bltu_arith uHi.toNat vTop.toNat dHi.toNat dLo.toNat
    div_un1.toNat q1''.toNat rhat''.toNat
    h_decomp h_q1''_dHi_le h_rhat''_eq h_q1''_le


/-- **un21 < vTop under v4** (Phase-2 Knuth invariant).

    Per `project_un21_lt_vTop_plan.md`, this was a hard invariant under
    v2/v3 because Phase-1 truncation could produce un21 ~ 2 * vTop.
    Under v4, with Phase-1 perfect (`q1'' = q*_phase1`), un21 equals the
    Phase-1 remainder modulo Word-level truncation, which is < vTop. -/
theorem div128Quot_v4_un21_lt_vTop (uHi uLo vTop : Word)
    (h_vTop_ge_pow63 : vTop.toNat ≥ 2^63)
    (h_uHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := div128Quot_phase2b_q0' q1c rhatc dLo div_un1
    let rhat' :=
      if rhatc >>> (32 : BitVec 6).toNat = 0 then
        let qDlo := q1c * dLo
        let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
      else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1'' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    un21.toNat < vTop.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc q1' rhat' q1'' rhat''
        cu_rhat_un1 cu_q1_dlo un21
  -- Standard Word-level facts.
  have hdHi_lt : dHi.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have h_div_un1_lt : div_un1.toNat < 2 ^ 32 := Word_ushiftRight_32_lt_pow32
  have h_decomp : vTop.toNat = dHi.toNat * 2 ^ 32 + dLo.toNat :=
    div128Quot_vTop_decomp vTop
  -- `_phase1_perfect`: q1''.toNat = q_true.
  have h_perfect := div128Quot_v4_phase1_perfect uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  -- Phase-1 final Eucl: q1''*dHi + rhat'' = uHi.
  have h_eucl := div128Quot_v4_phase1_final_eucl_bridge uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  obtain ⟨h_q1''_dHi_le, h_rhat''_eq⟩ := h_eucl
  -- Phase-1 no-wrap.
  have h_no_wrap := div128Quot_v4_phase1_no_wrap_lo uHi uLo vTop
    h_vTop_ge_pow63 h_uHi_lt_vTop
  -- q1''.toNat ≤ 2^32 (Knuth bound).
  have h_q1''_lt : q1''.toNat ≤ 2 ^ 32 := by
    have h_q_true_lt : (uHi.toNat * 2^32 + div_un1.toNat) /
                       (dHi.toNat * 2^32 + dLo.toNat) < 2^32 :=
      div128Quot_q_true_1_lt_pow32 uHi dHi dLo div_un1 h_div_un1_lt
        (h_decomp ▸ h_uHi_lt_vTop)
    linarith [h_perfect]
  -- Word↔Nat bridges.
  -- cu_q1_dlo.toNat = q1''*dLo (no overflow).
  have h_q_dLo_eq : (q1'' * dLo).toNat = q1''.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    calc q1''.toNat * dLo.toNat
        ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1''_lt
      _ < 2^32 * 2^32 := (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr hdLo_lt
      _ = 2^64 := by decide
  -- cu_rhat_un1.toNat = (rhat'' % 2^32) * 2^32 + div_un1 via halfword_combine_mod.
  have h_rhatUn1_mod : ((rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
                       (rhat''.toNat % 2^32) * 2^32 + div_un1.toNat := by
    rw [EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    exact halfword_combine_mod rhat'' div_un1 h_div_un1_lt
  -- (q1'' + 1) * vTop > uHi*2^32 + div_un1 (no-overshoot, from Phase-1 perfect).
  have h_vTop_pos : 0 < vTop.toNat :=
    lt_of_lt_of_le (by decide : (0 : Nat) < 2 ^ 63) h_vTop_ge_pow63
  have h_q1''_succ_gt : (q1''.toNat + 1) * vTop.toNat >
                        uHi.toNat * 2 ^ 32 + div_un1.toNat := by
    have h_pos' : 0 < dHi.toNat * 2 ^ 32 + dLo.toNat := by
      have := h_decomp ▸ h_vTop_pos; omega
    have h := Nat.lt_div_mul_add (a := uHi.toNat * 2 ^ 32 + div_un1.toNat) h_pos'
    rw [show (q1''.toNat + 1) * vTop.toNat
          = q1''.toNat * vTop.toNat + vTop.toNat from by ring]
    rw [h_perfect, h_decomp]
    exact h
  -- vTop ≤ 2^64 (Word).
  have h_vTop_le_pow64 : vTop.toNat ≤ 2 ^ 64 := by
    have := vTop.isLt
    omega
  -- un21.toNat = (cu_rhat_un1.toNat + (2^64 - cu_q1_dlo.toNat)) % 2^64.
  have h_un21_eq : un21.toNat =
      ((rhat''.toNat % 2 ^ 32) * 2 ^ 32 + div_un1.toNat + 2 ^ 64 -
        q1''.toNat * dLo.toNat) % 2 ^ 64 := by
    show (cu_rhat_un1 - cu_q1_dlo).toNat = _
    rw [BitVec.toNat_sub']
    rw [show cu_rhat_un1 = (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1 from rfl]
    rw [show cu_q1_dlo = q1'' * dLo from rfl]
    rw [h_rhatUn1_mod, h_q_dLo_eq]
    -- Goal: (X + (2^64 - Y)) % 2^64 = (X + 2^64 - Y) % 2^64.
    have h_Y_lt : q1''.toNat * dLo.toNat < 2 ^ 64 := by
      calc q1''.toNat * dLo.toNat
          ≤ 2^32 * dLo.toNat := Nat.mul_le_mul_right _ h_q1''_lt
        _ < 2^32 * 2^32 := (Nat.mul_lt_mul_left (by decide : 0 < 2^32)).mpr hdLo_lt
        _ = 2^64 := by decide
    congr 1
    omega
  rw [h_un21_eq]
  exact div128Quot_v4_un21_lt_vTop_truncation_arith uHi.toNat vTop.toNat
    dHi.toNat dLo.toNat div_un1.toNat q1''.toNat rhat''.toNat
    h_decomp hdLo_lt h_vTop_le_pow64 h_q1''_succ_gt h_q1''_dHi_le h_rhat''_eq
    h_no_wrap h_q1''_lt

end EvmAsm.Evm64
