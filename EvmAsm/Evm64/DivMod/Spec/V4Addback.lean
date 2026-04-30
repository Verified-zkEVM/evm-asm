/-
  EvmAsm.Evm64.DivMod.Spec.V4Addback

  v4 call-addback-beq closure (`n4CallAddbackBeqSemanticHolds_v4` and
  `n4CallAddbackBeqSemanticHolds_v4_of_call_addback_beq`) along with the
  Layer 2a/2c/3 lemmas it consumes.

  Split out of `Spec.V4` (issue #1078, slice 3) to keep both files under
  the 1500-line cap. `Spec.V4` continues to own the v4 irreducible
  component accessors, bridge theorems, and the v4 call-skip closure,
  which this file imports via `EvmAsm.Evm64.DivMod.Spec.V4`.
-/

import EvmAsm.Evm64.DivMod.Spec.V4

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- **v4 version of `n4CallAddbackBeqSemanticHolds`**, using
    `div128Quot_v4` (full 2-correction Knuth D3 in BOTH phases).

    The v1 predicate `n4CallAddbackBeqSemanticHolds` is **provably FALSE**
    under runtime preconditions (see
    `n4CallAddbackBeqSemanticHolds_counterexample`) due to v1's
    1-correction Phase-1b allowing 2^32-scale qHat overshoots. The v2
    predicate fixes Phase-1b only; the v4 predicate fixes BOTH phases,
    eliminating the counterexample input class by construction.

    Mirror of `n4CallAddbackBeqSemanticHolds` for the v4 algorithm.
    Closure proof `n4CallAddbackBeqSemanticHolds_v4_of_call_addback_beq`
    is the next critical-path target (still in stub form). -/
def n4CallAddbackBeqSemanticHolds_v4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  let b0' := (b.getLimbN 0) <<< shift
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  let u0 := (a.getLimbN 0) <<< shift
  let qHat := div128Quot_v4 u4 u3 b3'  -- v4: 2 D3 correction iterations in BOTH phases.
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let q_out : Word :=
    if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
    else qHat + signExtend12 4095
  q_out.toNat =
    val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem n4CallAddbackBeqSemanticHolds_v4_def {a b : EvmWord} :
    n4CallAddbackBeqSemanticHolds_v4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
     let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
     let b0' := (b.getLimbN 0) <<< shift
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
     let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
     let u0 := (a.getLimbN 0) <<< shift
     let qHat := div128Quot_v4 u4 u3 b3'
     let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
     let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
     let q_out : Word :=
       if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
       else qHat + signExtend12 4095
     q_out.toNat =
       val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :=
  rfl

/-- **Layer 1 stub: v4 Knuth-B at val256 level.** Under the runtime
    preconditions, the v4 trial digit `qHat` (equal to the exact 128/64
    quotient by `div128Quot_v4_eq_q_true_normalized`) is at most 2 above
    the true val256-level quotient.

    Mirror of the v1 statement (which is FALSE for v1 due to overshoots).
    For v4, this is the val256-level lift of the per-phase Knuth-B
    bounds: since v4's qHat = (u4*2^64 + u3) / b3' exactly, and Knuth-B
    at the val256 level says `(u4*2^64+u3)/b3' ≤ val256(a)/val256(b) + 2`,
    we get `qHat ≤ val256(a)/val256(b) + 2` directly.

    Sub-stub for the addback closure's Layer 1. -/
theorem div128Quot_v4_qHat_le_q_true_plus_two (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (div128Quot_v4 u4 u3 b3').toNat ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2 := by
  rw [isCallTrialN4Evm_def] at hcall
  intro shift antiShift b3' u4 u3
  -- Standard Knuth preconditions.
  have h_b3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) hb3nz _
  have h_u4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hcall
  have h_shift_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h | h
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_u4_lt_pow63 : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz (a.getLimbN 3) (clzResult (b.getLimbN 3)).1
      h_shift_pos (clzResult_fst_toNat_le (b.getLimbN 3))
  -- Convert v4 quotient to the (u4*2^64 + u3)/b3' form.
  have h_eq := div128Quot_v4_eq_q_true_normalized u4 u3 b3'
    h_b3'_ge h_u4_lt_b3' h_u4_lt_pow63
  rw [h_eq]
  -- Apply the existing val256-level Knuth-B (Piece A).
  exact knuth_theorem_b_from_clz
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hb3nz hshift_nz hcall

/-- **v4 mirror of `u_top_lt_c3_of_addback_borrow_call`**: from
    `isAddbackBorrowN4Call_v4`, extract the Nat-level inequality
    `u4.toNat < c3.toNat`. Used by Layer 2a/2c to derive the qHat
    overshoot via the val256-level Euclidean equation. -/
theorem u_top_lt_c3_of_addback_borrow_call_v4
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (h : isAddbackBorrowN4Call_v4 a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    let qHat := div128Quot_v4 u4 u3 b3'
    u4.toNat <
    (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat
  unfold isAddbackBorrowN4Call_v4 at h
  simp only [] at h
  by_cases hlt : BitVec.ult u4 (mulsubN4_c3 qHat b0' b1' b2' b3' u0 u1 u2 u3)
  · rw [EvmWord.ult_iff] at hlt
    unfold mulsubN4_c3 at hlt
    exact hlt
  · rw [if_neg hlt] at h
    exact absurd rfl h

/-- **Pure-Nat helper for Layer 2a-fwd**: captures the val256-level math
    chain (carry = 0 ∧ u4 < c3 → qHat overshoots by ≥ 2) with no Word /
    BitVec / EvmWord machinery in the type. Used to avoid kernel deep
    recursion when attempting to inline the chain at the Word level.

    Hypotheses (all pure-Nat):
    - `h_norm_u`: `Vu + U4 * p256 = Va * p_shift`
      (val256(u_norm) + u4 * 2^256 = val256(a) * 2^shift, from
      `u_val256_eq_scaled_with_overflow`).
    - `h_norm_v`: `Vv = Vb * p_shift`
      (val256(v_norm) = val256(b) * 2^shift, from
      `b3_prime_val256_eq_scaled`).
    - `h_combined`: `Q * Vv + Vab = Vu + c3 * p256 + Vv`
      (combines `mulsubN4_val256_eq` + `addbackN4_val256_eq` under
      carry = 0).
    - `h_u4_lt_c3`: `U4 < c3` (from
      `u_top_lt_c3_of_addback_borrow_call_v4`).
    - `h_Vab_lt`: `Vab < p256` (from `val256_bound` with `p256 = 2^256`).
    - `h_Vb_pos`: `0 < Vb` (from `b3 ≠ 0` via val256 lower bound).

    Conclusion: `Q ≥ Va / Vb + 2`, i.e., qHat overshoots q_true by ≥ 2. -/
theorem n4CallAddback_v4_carry_zero_imp_overshoot_arith
    (Va Vb Vu Vv Vab Q U4 c3 p_shift p256 : ℕ)
    (h_Vb_pos : 0 < Vb)
    (h_norm_u : Vu + U4 * p256 = Va * p_shift)
    (h_norm_v : Vv = Vb * p_shift)
    (h_combined : Q * Vv + Vab = Vu + c3 * p256 + Vv)
    (h_u4_lt_c3 : U4 < c3)
    (h_Vab_lt : Vab < p256) :
    Q ≥ Va / Vb + 2 := by
  -- After substitution: Q * Vb * p_shift + Vab + U4 * p256 = (Va + Vb) * p_shift + c3 * p256
  have h1 : Q * Vb * p_shift + Vab + U4 * p256 = (Va + Vb) * p_shift + c3 * p256 := by
    have hQVv : Q * Vv = Q * Vb * p_shift := by rw [h_norm_v]; ring
    have h_comb' : Q * Vb * p_shift + Vab = Vu + c3 * p256 + Vb * p_shift := by
      rw [← hQVv, ← h_norm_v]; exact h_combined
    have key : Q * Vb * p_shift + Vab + U4 * p256 =
               (Vu + U4 * p256) + c3 * p256 + Vb * p_shift := by linarith
    rw [h_norm_u] at key
    linarith [key]
  -- c3 ≥ U4 + 1, so c3 * p256 ≥ U4 * p256 + p256
  have hc3_ge : c3 * p256 ≥ U4 * p256 + p256 := by
    have hc3 : c3 ≥ U4 + 1 := h_u4_lt_c3
    have hmul : (U4 + 1) * p256 ≤ c3 * p256 := Nat.mul_le_mul_right _ hc3
    linarith [hmul, Nat.add_one_mul U4 p256]
  -- Q * Vb * p_shift + Vab ≥ (Va + Vb) * p_shift + p256
  have h2 : Q * Vb * p_shift + Vab ≥ (Va + Vb) * p_shift + p256 := by linarith
  -- Vab < p256 → Q * Vb * p_shift > (Va + Vb) * p_shift
  have h3 : Q * Vb * p_shift > (Va + Vb) * p_shift := by linarith
  -- Cancel p_shift: Q * Vb > Va + Vb
  have h4 : Q * Vb > Va + Vb := Nat.lt_of_mul_lt_mul_right h3
  -- Q ≥ 1 (else Q * Vb = 0, contradicting Va + Vb < Q * Vb)
  have hQ_pos : 1 ≤ Q := by
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQ_pos
    · exfalso; rw [hQ0] at h4; simp at h4
    · exact hQ_pos
  -- (Q - 1) * Vb > Va
  have h7 : Va < (Q - 1) * Vb := by
    have hQVb : Q * Vb = (Q - 1) * Vb + Vb := by
      have hQ_eq : (Q - 1) + 1 = Q := Nat.sub_add_cancel hQ_pos
      conv_lhs => rw [← hQ_eq]
      rw [Nat.add_mul, Nat.one_mul]
    omega
  -- Va / Vb < Q - 1
  have h8 : Va / Vb < Q - 1 := (Nat.div_lt_iff_lt_mul h_Vb_pos).mpr h7
  omega

/-- **Pure-Nat helper for Layer 2a-back**. Companion to
    `n4CallAddback_v4_carry_zero_imp_overshoot_arith`. From the same
    val256-level algebraic frame, plus the algorithmic facts
    `Q = q_true + 2` (Knuth-B equality), `c3 = U4 + 1` (single-addback
    closure), and `carry ≤ 1` (addbackN4_carry_le_one), derives
    `carry = 0`.

    Math: substitute c3 = U4+1 + Q = Va/Vb+2 into mulsub. With
    `(Va/Vb)*Vb + r = Va` (r = Va mod Vb < Vb), derive
    `Vms + 2*Vv = p256 + r*p_shift`. Since r*p_shift < Vv, get
    `Vms + Vv < p256`. So addback's `Vab + carry*p256 = Vms + Vv < p256`,
    forcing `carry = 0` (else carry = 1 → Vab + p256 ≥ p256 contradicts).

    The `c3 = U4 + 1` precondition is the genuine algorithmic content
    isolated as a separate sub-stub
    (`n4CallAddback_v4_c3_eq_u4_plus_one_under_overshoot`). -/
theorem n4CallAddback_v4_overshoot_ge_two_imp_carry_zero_arith
    (Va Vb Vu Vv Vab Vms Q U4 c3 carry p_shift p256 : ℕ)
    (h_p_shift_pos : 0 < p_shift)
    (h_Vb_pos : 0 < Vb)
    (h_norm_u : Vu + U4 * p256 = Va * p_shift)
    (h_norm_v : Vv = Vb * p_shift)
    (h_mulsub : Vu + c3 * p256 = Vms + Q * Vv)
    (h_addback : Vms + Vv = Vab + carry * p256)
    (h_carry_le : carry ≤ 1)
    (h_Q_le : Q ≤ Va / Vb + 2)
    (h_Q_ge : Q ≥ Va / Vb + 2)
    (h_c3_eq : c3 = U4 + 1) :
    carry = 0 := by
  have h_Q_eq : Q = Va / Vb + 2 := by omega
  set r := Va % Vb with hr_def
  have h_r_lt_Vb : r < Vb := Nat.mod_lt _ h_Vb_pos
  have h_Va_decomp : (Va / Vb) * Vb + r = Va := Nat.div_add_mod' Va Vb
  -- Vms + Q * Vv = Va * p_shift + p256.
  have hA : Vms + Q * Vv = Va * p_shift + p256 := by
    have h1 : Vu + (U4 + 1) * p256 = Vms + Q * Vv := by rw [← h_c3_eq]; exact h_mulsub
    have h2 : Vu + U4 * p256 + p256 = Vms + Q * Vv := by
      linarith [h1, Nat.add_one_mul U4 p256]
    linarith [h2, h_norm_u]
  -- (Va / Vb) * Vb * p_shift + r * p_shift = Va * p_shift.
  have hB : (Va / Vb) * Vb * p_shift + r * p_shift = Va * p_shift := by
    have h1 : ((Va / Vb) * Vb + r) * p_shift = Va * p_shift := by rw [h_Va_decomp]
    linarith [h1, Nat.add_mul ((Va / Vb) * Vb) r p_shift]
  -- Q * Vv = (Va/Vb) * Vb * p_shift + 2 * (Vb * p_shift).
  have hC : Q * Vv = (Va / Vb) * Vb * p_shift + 2 * (Vb * p_shift) := by
    rw [h_Q_eq, h_norm_v, Nat.add_mul]; ring
  -- Vms + (Va/Vb)*Vb*p_shift + 2*Vv = Va*p_shift + p256.
  have hD : Vms + ((Va / Vb) * Vb * p_shift + 2 * Vv) = Va * p_shift + p256 := by
    have hVv2 : 2 * Vv = 2 * (Vb * p_shift) := by rw [h_norm_v]
    linarith [hA, hC, hVv2]
  -- Vms + 2 * Vv = p256 + r * p_shift.
  have hE : Vms + 2 * Vv = p256 + r * p_shift := by linarith [hD, hB]
  -- r * p_shift < Vv.
  have hF : r * p_shift < Vv := by
    rw [h_norm_v]
    exact Nat.mul_lt_mul_of_pos_right h_r_lt_Vb h_p_shift_pos
  -- Vms + Vv < p256.
  have hG : Vms + Vv < p256 := by
    have hE2 : Vms + Vv + Vv = p256 + r * p_shift := by linarith [hE]
    linarith [hE2, hF]
  -- Vab + carry * p256 = Vms + Vv < p256, with carry ≤ 1, so carry = 0.
  have hH : Vab + carry * p256 < p256 := by linarith [hG, h_addback]
  rcases Nat.lt_or_ge carry 1 with h1 | h1
  · omega
  · have hc1 : carry = 1 := by omega
    rw [hc1] at hH; omega

/-- **Layer 2a-fwd: carry = 0 → qHat overshoots by ≥ 2.**

    Forward direction of the carry partition.

    Proof outline (concrete):
    1. From `_haddback`: borrow check fires, so c3 = mulsubN4 top borrow ≥ 1.
       Combined with `mulsubN4_c3_le_one` (preconditioned on qHat ≤ q*_norm + 1):
       c3 = 1.
    2. By contrapositive of `addbackN4_first_carry_one`: if c3 = 1 and
       carry = 0, then ¬(qHat ≤ q*_norm + 1), i.e., qHat ≥ q*_norm + 2.
    3. Bridge q*_norm → q_true (val256(a)/val256(b)).

    **Bridge gap (3) note**: q*_norm = val256(u_norm) / val256(v_norm). For
    the call-trial branch with u4 > 0, q*_norm < q_true is possible
    (val256(u_norm) only sees the low 256 bits of u_norm; the u4 carry is
    elsewhere). The proper bridge uses the FULL 8-limb u_norm_total =
    val256(u_norm) + u4 * 2^256 = val256(a) * 2^shift. The relationship
    qHat ≥ q*_norm + 2 alone may NOT directly give qHat ≥ q_true + 2.

    Cleanest path forward (next iteration): use a different intermediate —
    `qHat * val256(v_norm) > val256(u_norm) + 2 * val256(v_norm)` from c3 = 1
    + carry = 0 (mulsub-then-no-addback wraparound), then divide by 2^shift
    via `b3_prime_val256_eq_scaled` to get qHat * val256(b) > val256(a) +
    val256(b) (modulo carry adjustments), hence qHat ≥ q_true + 2. -/
theorem n4CallAddback_v4_carry_zero_imp_overshoot_ge_two (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hcall : isCallTrialN4Evm a b)
    (haddback : isAddbackBorrowN4CallEvm_v4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v4 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    carry = 0 → qHat.toNat ≥ q_true + 2 := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms carry q_true h_carry
  -- Step 1: u4.toNat < c3.toNat from haddback
  rw [isAddbackBorrowN4CallEvm_v4_def] at haddback
  have h_u4_lt_c3 := u_top_lt_c3_of_addback_borrow_call_v4
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    haddback
  simp only [] at h_u4_lt_c3
  change u4.toNat < (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
    at h_u4_lt_c3
  -- Step 2: mulsub val256 eq
  have h_mulsub := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub
  -- Step 3: addback val256 eq (u4_new = 0; carry independent of u4_new)
  have h_addback :=
    addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  simp only [] at h_addback
  -- Step 4: carry.toNat = 0 from carry = 0 hypothesis
  have h_carry_zero :
      (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat = 0 := by
    show carry.toNat = 0
    rw [h_carry]; rfl
  -- Step 5/6: norm-u, norm-v from CLZ-based shift lemmas.
  have h_norm_u := u_val256_eq_scaled_with_overflow
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 3) hshift_nz
  have h_norm_v := b3_prime_val256_eq_scaled
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hshift_nz
  -- Step 7: val256_bound for the addback low-4 result.
  have h_Vab_lt :
      val256
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.2.1
        < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  -- Step 8: 0 < val256(b) (from b3 ≠ 0 → val256 ≥ 2^192).
  have h_Vb_pos : 0 < val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
        (b.getLimbN 3) := by
    have := EvmWord.val256_ge_pow192_of_limb3
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3nz
    have hpow : (2:Nat)^192 > 0 := Nat.two_pow_pos 192
    omega
  -- Step 9: alias the val256 expressions and apply the pure-Nat helper.
  set Va := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  set Vb := val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  set Vu := val256 u0 u1 u2 u3
  set Vv := val256 b0' b1' b2' b3'
  set Vab := val256
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.2.1
  set Q := qHat.toNat
  set U4 := u4.toNat
  set c3 := (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
  set p_shift := (2 : ℕ) ^ (clzResult (b.getLimbN 3)).1.toNat
  show Q ≥ Va / Vb + 2
  apply n4CallAddback_v4_carry_zero_imp_overshoot_arith
    Va Vb Vu Vv Vab Q U4 c3 p_shift (2^256)
  · exact h_Vb_pos
  · show Vu + U4 * 2^256 = Va * p_shift
    exact h_norm_u
  · show Vv = Vb * p_shift
    exact h_norm_v
  · -- h_combined: Q * Vv + Vab = Vu + c3 * 2^256 + Vv
    show Q * Vv + Vab = Vu + c3 * 2^256 + Vv
    rw [h_carry_zero] at h_addback
    simp at h_addback
    linarith [h_mulsub, h_addback]
  · show U4 < c3
    exact h_u4_lt_c3
  · show Vab < 2^256
    exact h_Vab_lt

/-- **Pure-Nat helper for c3 = u4 + 1 via the 128/64 trial digit.**

    The algorithmic CRUX: rules out `c3 - u4 = 2` by exploiting
    `qHat < 2^64` (the 128/64 trial digit is bounded by the base) and
    `Vv_lo < 2^192` (the lower three limbs of v_norm fit in 192 bits),
    so `qHat * Vv_lo < 2^256`.

    Key identity (provable from `mulsubN4_val256_eq` + 128/64 trial):

      Vms + qHat * Vv_lo + U4 * 2^256 = Vu_lo + c3 * 2^256 + rhat * 2^192

    With `qHat * Vv_lo < 2^256` and `Vms < 2^256`, the LHS < (U4+2)*2^256.
    For c3 ≥ U4 + 2: RHS ≥ (U4+2)*2^256 + Vu_lo + rhat*2^192 > LHS,
    contradiction. So c3 ≤ U4 + 1, and combined with U4 < c3, c3 = U4 + 1. -/
theorem c3_eq_u4_plus_one_via_128_64_trial_arith
    (Vu_lo Vv_lo Vms qHat U4 c3 rhat : ℕ)
    (h_qHat_lt : qHat < 2^64)
    (h_Vv_lo_lt : Vv_lo < 2^192)
    (h_Vms_lt : Vms < 2^256)
    (h_key : Vms + qHat * Vv_lo + U4 * 2^256 = Vu_lo + c3 * 2^256 + rhat * 2^192)
    (h_u4_lt_c3 : U4 < c3) :
    c3 = U4 + 1 := by
  have h_qVv_lt : qHat * Vv_lo < 2^64 * 2^192 := by
    apply Nat.mul_lt_mul_of_lt_of_le h_qHat_lt (le_of_lt h_Vv_lo_lt)
    exact Nat.two_pow_pos 192
  have h_qVv_lt' : qHat * Vv_lo < 2^256 := by
    have : (2:Nat)^64 * 2^192 = 2^256 := by norm_num
    omega
  by_contra h_ne
  have h_c3_ge : c3 ≥ U4 + 2 := by omega
  have h_c3_mul : c3 * 2^256 ≥ (U4 + 2) * 2^256 := Nat.mul_le_mul_right _ h_c3_ge
  have h_split : (U4 + 2) * 2^256 = U4 * 2^256 + 2 * 2^256 := by ring
  nlinarith [h_qVv_lt', h_Vms_lt, h_c3_mul, h_split, h_key]

/-- **c3 = u4 + 1 under haddback + qHat = q_true + 2** (CLOSED).

    Algorithmic invariant for v4's call+addback BEQ branch. The proof
    combines the val256-level mulsub Euclidean with the v4-specific
    128/64 trial digit structure (qHat = (u4*2^64 + u3) / b3'):

    1. From the 128/64 division: u4*2^64 + u3 = qHat*b3' + rhat,
       0 ≤ rhat < b3' < 2^64.
    2. Multiplied by 2^192 and combined with `mulsubN4_val256_eq`,
       yields the KEY identity (no Va/Vb/r involved):

         Vms + qHat * Vv_lo + u4 * 2^256
           = Vu_lo + c3 * 2^256 + rhat * 2^192

       where Vu_lo, Vv_lo are the lower 192 bits of u_norm/v_norm.
    3. Since qHat < 2^64 (BitVec 64 bound) and Vv_lo < 2^192,
       qHat * Vv_lo < 2^256. So if c3 ≥ u4 + 2, the LHS would be
       too small to equal the RHS — contradiction.
    4. Combined with `u4 < c3` (haddback): c3 = u4 + 1.

    The hypothesis `qHat ≥ q_true + 2` is NOT used directly — the proof
    works for any qHat coming from the 128/64 trial. (The hypothesis
    is part of the parent Layer 2a-back theorem's signature.) -/
theorem n4CallAddback_v4_c3_eq_u4_plus_one_under_overshoot (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (haddback : isAddbackBorrowN4CallEvm_v4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v4 u4 u3 b3'
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    qHat.toNat ≥ q_true + 2 →
    (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat = u4.toNat + 1 := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat q_true _h_overshoot
  -- 1. u4 < c3 from haddback.
  rw [isAddbackBorrowN4CallEvm_v4_def] at haddback
  have h_u4_lt_c3 := u_top_lt_c3_of_addback_borrow_call_v4
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) haddback
  simp only [] at h_u4_lt_c3
  change u4.toNat < (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
    at h_u4_lt_c3
  -- 2. mulsub Euclidean.
  have h_mulsub := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub
  -- 3. v4 = 128/64 trial digit (the algorithmic fact).
  rw [isCallTrialN4Evm_def] at hcall
  have h_b3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 (b.getLimbN 3) (b.getLimbN 2) hb3nz _
  have h_u4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hcall
  have h_clz_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h0 | h0
    · exfalso; apply hshift_nz; exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exact h0
  have h_clz_le_63 : (clzResult (b.getLimbN 3)).1.toNat ≤ 63 :=
    clzResult_fst_toNat_le _
  have h_u4_lt_pow63 : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz (a.getLimbN 3) (clzResult (b.getLimbN 3)).1
      h_clz_pos h_clz_le_63
  have h_qHat_eq := div128Quot_v4_eq_q_true_normalized u4 u3 b3'
    h_b3'_ge h_u4_lt_b3' h_u4_lt_pow63
  -- 4. 128/64 division: u4*2^64 + u3 = qHat*b3' + rhat, rhat < b3'.
  set rhat := (u4.toNat * 2^64 + u3.toNat) % b3'.toNat with hrhat_def
  have h_b3'_pos : 0 < b3'.toNat := by
    have : (0 : Nat) < 2^63 := by decide
    omega
  have h_div_mod : qHat.toNat * b3'.toNat + rhat = u4.toNat * 2^64 + u3.toNat := by
    rw [h_qHat_eq, hrhat_def]
    exact Nat.div_add_mod' (u4.toNat * 2^64 + u3.toNat) b3'.toNat
  have h_rhat_lt : rhat < b3'.toNat := Nat.mod_lt _ h_b3'_pos
  have h_rhat_lt_pow64 : rhat < 2^64 := by
    have : b3'.toNat < 2^64 := b3'.isLt
    omega
  -- 5. Set up val256 aliases and split into low/high halves.
  set Vu_lo := u0.toNat + u1.toNat * 2^64 + u2.toNat * 2^128 with hVu_lo_def
  set Vv_lo := b0'.toNat + b1'.toNat * 2^64 + b2'.toNat * 2^128 with hVv_lo_def
  set Vms := val256
        (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).1
        (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.1
        (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.1
        (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.1
  set c3 := (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
  have h_Vu_eq : val256 u0 u1 u2 u3 = Vu_lo + u3.toNat * 2^192 := by
    show u0.toNat + u1.toNat * 2^64 + u2.toNat * 2^128 + u3.toNat * 2^192 =
         (u0.toNat + u1.toNat * 2^64 + u2.toNat * 2^128) + u3.toNat * 2^192
    ring
  have h_Vv_eq : val256 b0' b1' b2' b3' = Vv_lo + b3'.toNat * 2^192 := by
    show b0'.toNat + b1'.toNat * 2^64 + b2'.toNat * 2^128 + b3'.toNat * 2^192 =
         (b0'.toNat + b1'.toNat * 2^64 + b2'.toNat * 2^128) + b3'.toNat * 2^192
    ring
  have h_mulsub' : Vu_lo + u3.toNat * 2^192 + c3 * 2^256 =
                   Vms + qHat.toNat * (Vv_lo + b3'.toNat * 2^192) := by
    rw [← h_Vu_eq, ← h_Vv_eq]; exact h_mulsub
  -- 6. KEY identity via algebraic combination.
  -- From h_mulsub' (after distributing): Vu_lo + u3*2^192 + c3*p256
  --   = Vms + qHat*Vv_lo + qHat*b3'*2^192.
  -- From h_div_mod (multiplied by 2^192):
  --   qHat*b3'*2^192 + rhat*2^192 = u4*2^256 + u3*2^192.
  have h_mulsub_distr : Vu_lo + u3.toNat * 2^192 + c3 * 2^256 =
                        Vms + qHat.toNat * Vv_lo + qHat.toNat * b3'.toNat * 2^192 := by
    have h_qVlo : qHat.toNat * (Vv_lo + b3'.toNat * 2^192) =
                  qHat.toNat * Vv_lo + qHat.toNat * b3'.toNat * 2^192 := by ring
    linarith [h_mulsub', h_qVlo]
  have h_div_mod_192 : qHat.toNat * b3'.toNat * 2^192 + rhat * 2^192 =
                       u4.toNat * 2^256 + u3.toNat * 2^192 := by
    have h_lhs : (qHat.toNat * b3'.toNat + rhat) * 2^192 =
                 qHat.toNat * b3'.toNat * 2^192 + rhat * 2^192 := by ring
    have h_rhs : (u4.toNat * 2^64 + u3.toNat) * 2^192 =
                 u4.toNat * 2^256 + u3.toNat * 2^192 := by ring
    have h_eq : (qHat.toNat * b3'.toNat + rhat) * 2^192 =
                (u4.toNat * 2^64 + u3.toNat) * 2^192 := by rw [h_div_mod]
    linarith [h_lhs, h_rhs, h_eq]
  have h_key : Vms + qHat.toNat * Vv_lo + u4.toNat * 2^256 =
               Vu_lo + c3 * 2^256 + rhat * 2^192 := by
    linarith [h_mulsub_distr, h_div_mod_192]
  -- 7. Bounds.
  have h_qHat_lt : qHat.toNat < 2^64 := qHat.isLt
  have h_Vv_lo_lt : Vv_lo < 2^192 := by
    have h0 : b0'.toNat < 2^64 := b0'.isLt
    have h1 : b1'.toNat < 2^64 := b1'.isLt
    have h2 : b2'.toNat < 2^64 := b2'.isLt
    show b0'.toNat + b1'.toNat * 2^64 + b2'.toNat * 2^128 < 2^192
    nlinarith [h0, h1, h2]
  have h_Vms_lt : Vms < 2^256 := EvmWord.val256_bound _ _ _ _
  -- 8. Apply the pure-Nat helper.
  show c3 = u4.toNat + 1
  exact c3_eq_u4_plus_one_via_128_64_trial_arith
    Vu_lo Vv_lo Vms qHat.toNat u4.toNat c3 rhat
    h_qHat_lt h_Vv_lo_lt h_Vms_lt h_key h_u4_lt_c3

/-- **Layer 2a-back: qHat overshoots by ≥ 2 → carry = 0.**

    Backward direction. Wired through:
    - `n4CallAddback_v4_c3_eq_u4_plus_one_under_overshoot` (sub-stub):
      `c3 = u4 + 1` under the runtime preconditions.
    - `div128Quot_v4_qHat_le_q_true_plus_two` (Layer 1): `qHat ≤ q_true + 2`.
    - `n4CallAddback_v4_overshoot_ge_two_imp_carry_zero_arith`: pure-Nat
      algebraic helper that closes from `c3 = u4 + 1`. -/
theorem n4CallAddback_v4_overshoot_ge_two_imp_carry_zero (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (haddback : isAddbackBorrowN4CallEvm_v4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v4 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    qHat.toNat ≥ q_true + 2 → carry = 0 := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms carry q_true h_overshoot
  -- 1. h_u4_lt_c3 from haddback (used implicitly via h_c3_eq).
  rw [isAddbackBorrowN4CallEvm_v4_def] at haddback
  -- 2. mulsub eq.
  have h_mulsub := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub
  -- 3. addback eq.
  have h_addback :=
    addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3'
  simp only [] at h_addback
  -- 4. carry ≤ 1.
  have h_carry_le_word :=
    addbackN4_carry_le_one ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  -- 5. norm-u, norm-v.
  have h_norm_u := u_val256_eq_scaled_with_overflow
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 3) hshift_nz
  have h_norm_v := b3_prime_val256_eq_scaled
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hshift_nz
  -- 6. Vb pos.
  have h_Vb_pos : 0 < val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
        (b.getLimbN 3) := by
    have := EvmWord.val256_ge_pow192_of_limb3
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3nz
    have hpow : (2:Nat)^192 > 0 := Nat.two_pow_pos 192
    omega
  -- 7. p_shift > 0.
  have h_p_shift_pos : 0 < (2 : ℕ) ^ (clzResult (b.getLimbN 3)).1.toNat :=
    Nat.two_pow_pos _
  -- 8. Layer 1: qHat ≤ q_true + 2.
  have h_Q_le := div128Quot_v4_qHat_le_q_true_plus_two a b hb3nz hshift_nz hcall
  simp only [] at h_Q_le
  change qHat.toNat ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2
    at h_Q_le
  -- 9. SUB-STUB: c3 = u4 + 1 under haddback + overshoot.
  rw [← isAddbackBorrowN4CallEvm_v4_def] at haddback
  have h_c3_eq :=
    n4CallAddback_v4_c3_eq_u4_plus_one_under_overshoot a b hb3nz hshift_nz hcall haddback
  simp only [] at h_c3_eq
  specialize h_c3_eq h_overshoot
  -- 10. Set aliases and apply the pure-Nat helper.
  set Va := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
  set Vb := val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  set Vu := val256 u0 u1 u2 u3
  set Vv := val256 b0' b1' b2' b3'
  set Vab := val256
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.1
        (addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 b0' b1' b2' b3').2.2.2.1
  set Vms := val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
  set Q := qHat.toNat
  set U4 := u4.toNat
  set c3 := (mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3).2.2.2.2.toNat
  set carryNat :=
    (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3').toNat
  set p_shift := (2 : ℕ) ^ (clzResult (b.getLimbN 3)).1.toNat
  have h_carryNat_zero :=
    n4CallAddback_v4_overshoot_ge_two_imp_carry_zero_arith
      Va Vb Vu Vv Vab Vms Q U4 c3 carryNat p_shift (2^256)
      h_p_shift_pos h_Vb_pos
      (by show Vu + U4 * 2^256 = Va * p_shift; exact h_norm_u)
      (by show Vv = Vb * p_shift; exact h_norm_v)
      (by show Vu + c3 * 2^256 = Vms + Q * Vv; exact h_mulsub)
      (by show Vms + Vv = Vab + carryNat * 2^256; exact h_addback)
      h_carry_le_word
      h_Q_le h_overshoot h_c3_eq
  -- 11. Convert carryNat = 0 to carry = 0 (Word).
  show (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3') = 0
  apply BitVec.eq_of_toNat_eq
  exact h_carryNat_zero

/-- **Layer 2a sub-stub: addback carry detects ≥-2 overshoot.**

    Pure algorithmic content: under shift-norm preconditions, the
    addback carry is 0 ⟺ qHat overshoots val256(a)/val256(b) by at
    least 2.

    Wired via `_imp_overshoot_ge_two` (forward) and
    `_overshoot_ge_two_imp_carry_zero` (backward). -/
theorem n4CallAddback_v4_carry_zero_iff_overshoot_ge_two (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (haddback : isAddbackBorrowN4CallEvm_v4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v4 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (carry = 0 ↔ qHat.toNat ≥ q_true + 2) :=
  ⟨n4CallAddback_v4_carry_zero_imp_overshoot_ge_two a b hb3nz hshift_nz hcall haddback,
   n4CallAddback_v4_overshoot_ge_two_imp_carry_zero a b hb3nz hshift_nz hcall haddback⟩

/-- **Layer 2c-arith sub-stub (intermediate)**: under shift-norm + the
    borrow gating, `qHat * val256(b) > val256(a)`. This is the val256-level
    statement that the qHat overshoots q_true.

    Proof outline (sketch):
    1. From `u_top_lt_c3_of_addback_borrow_call_v4`: u4.toNat < c3.toNat.
    2. mulsubN4_val256_eq: val256(u_norm) + c3 * 2^256 = val256(un) + qHat * val256(v_norm).
    3. So qHat * val256(v_norm) ≥ val256(u_norm) + (u4 + 1) * 2^256 - val256(un).
    4. val256(un) < 2^256, so qHat * val256(v_norm) > val256(u_norm) + u4 * 2^256.
    5. u_val256_eq_scaled_with_overflow: val256(u_norm) + u4 * 2^256 = val256(a) * 2^shift.
    6. b3_prime_val256_eq_scaled: val256(v_norm) = val256(b) * 2^shift.
    7. Cancel 2^shift: qHat * val256(b) > val256(a). -/
theorem n4CallAddbackBeq_v4_qHat_mul_b_gt_a (a b : EvmWord)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hcall : isCallTrialN4Evm a b)
    (haddback : isAddbackBorrowN4CallEvm_v4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (div128Quot_v4 u4 u3 b3').toNat *
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) >
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) := by
  intro shift antiShift b3' u4 u3
  -- Step 1: u4 < c3 from haddback.
  rw [isAddbackBorrowN4CallEvm_v4_def] at haddback
  have h_c3_gt := u_top_lt_c3_of_addback_borrow_call_v4
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) haddback
  simp only [] at h_c3_gt
  -- Set up local Word aliases for the val256 reasoning.
  set b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
  set b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
  set b0' := (b.getLimbN 0) <<< shift
  set u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
  set u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
  set u0 := (a.getLimbN 0) <<< shift
  set qHat := div128Quot_v4 u4 u3 b3' with hqHat
  -- Step 2: mulsubN4_val256_eq.
  have h_mulsub := mulsubN4_val256_eq qHat b0' b1' b2' b3' u0 u1 u2 u3
  simp only [] at h_mulsub
  set ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3 with hms
  -- Step 3+4: c3 ≥ u4 + 1, val256(un) < 2^256.
  have h_c3_ge : ms.2.2.2.2.toNat ≥ u4.toNat + 1 := h_c3_gt
  have h_un_lt : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 :=
    EvmWord.val256_bound _ _ _ _
  -- Step 5: u_val256_eq_scaled_with_overflow.
  have h_norm_u := u_val256_eq_scaled_with_overflow
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 3) hshift_nz
  simp only [] at h_norm_u
  -- Step 6: b3_prime_val256_eq_scaled.
  have h_norm_v := b3_prime_val256_eq_scaled
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hshift_nz
  simp only [] at h_norm_v
  -- val256-level inequality: qHat * val256(v_norm) > val256(a) * 2^shift.
  have h_qHat_v_norm : qHat.toNat * val256 b0' b1' b2' b3' >
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) *
        2^(clzResult (b.getLimbN 3)).1.toNat := by
    -- From h_mulsub: val256 u + c3*2^256 = val256 un + qHat*val256 v_norm.
    -- So qHat * val256 v_norm = val256 u + c3*2^256 - val256 un.
    -- ≥ val256 u + (u4 + 1)*2^256 - (2^256 - 1)
    -- = val256 u + u4*2^256 + 1
    -- > val256 u + u4*2^256
    -- = val256 a * 2^shift  (h_norm_u)
    have h1 : val256 u0 u1 u2 u3 + ms.2.2.2.2.toNat * 2^256 =
              val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
              qHat.toNat * val256 b0' b1' b2' b3' := h_mulsub
    have h2 : (u4.toNat + 1) * 2^256 ≤ ms.2.2.2.2.toNat * 2^256 :=
      Nat.mul_le_mul_right _ h_c3_ge
    have h3 : val256 u0 u1 u2 u3 + (u4.toNat + 1) * 2^256 ≤
              val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
              qHat.toNat * val256 b0' b1' b2' b3' := by linarith
    -- Use h_un_lt to get strict inequality.
    -- Simplify: with set aliases for 2^256 to help omega.
    set p256 := (2 : Nat)^256 with hp256
    have h_un_lt' : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < p256 := h_un_lt
    have h_eq_step : val256 u0 u1 u2 u3 + (u4.toNat + 1) * p256 =
                     val256 u0 u1 u2 u3 + u4.toNat * p256 + p256 := by ring
    have h5 : val256 u0 u1 u2 u3 + u4.toNat * p256 <
              qHat.toNat * val256 b0' b1' b2' b3' := by linarith
    rw [h_norm_u] at h5
    exact h5
  -- Step 7: cancel 2^shift from both sides.
  rw [h_norm_v] at h_qHat_v_norm
  have hpow_pos : 0 < (2 : Nat)^(clzResult (b.getLimbN 3)).1.toNat := by positivity
  have h_mul_rearr : qHat.toNat *
      (val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2^(clzResult (b.getLimbN 3)).1.toNat) =
      qHat.toNat * val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) *
        2^(clzResult (b.getLimbN 3)).1.toNat := by ring
  rw [h_mul_rearr] at h_qHat_v_norm
  exact Nat.lt_of_mul_lt_mul_right h_qHat_v_norm

theorem n4CallAddbackBeq_v4_qHat_ge_q_true_plus_one (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (haddback : isAddbackBorrowN4CallEvm_v4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v4 u4 u3 b3'
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    qHat.toNat ≥ q_true + 1 := by
  intro shift antiShift b3' u4 u3 qHat q_true
  -- val256-level overshoot: qHat * val256(b) > val256(a).
  have h_overshoot := n4CallAddbackBeq_v4_qHat_mul_b_gt_a a b
    hshift_nz hcall haddback
  -- val256(b) > 0 (from b3 ≠ 0).
  have h_b_pos : 0 < val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
    -- val256(b) ≥ b3.toNat * 2^192. Since b3 ≠ 0, b3.toNat ≥ 1.
    have h_b3_pos : 0 < (b.getLimbN 3).toNat := by
      rcases Nat.eq_zero_or_pos (b.getLimbN 3).toNat with h | h
      · exfalso; apply hb3nz; exact BitVec.eq_of_toNat_eq h
      · exact h
    show 0 < val256 _ _ _ _
    unfold val256
    have h_pow : 0 < (b.getLimbN 3).toNat * 2^192 :=
      Nat.mul_pos h_b3_pos (by decide)
    omega
  -- qHat > val256(a) / val256(b) ⟺ qHat * val256(b) > val256(a) (given val256(b) > 0).
  -- Equivalently: q_true < qHat.toNat, so qHat.toNat ≥ q_true + 1.
  have h_lt : q_true < qHat.toNat := by
    rw [show q_true = val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                       val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) from rfl]
    exact (Nat.div_lt_iff_lt_mul h_b_pos).mpr h_overshoot
  omega

/-- **Layer 2 stub: carry partition for v4.** The post-mulsub addback carry
    is 0 iff the trial digit overshoots q_true by exactly 2.

    Mathematical content (val256 reasoning):
    - mulsub computes `a - qHat*b mod 2^256`.
    - addbackN4_carry returns 0 ⟺ the mulsub result + b STILL doesn't
      reach 2^256 (i.e., still wrapped around) ⟺ qHat overshoots q_true
      by ≥ 2 ⟺ (combined with Knuth-B from Layer 1) qHat = q_true + 2.
    - Conversely carry ≠ 0 ⟺ mulsub + b reaches 2^256 ⟺ overshoot ≤ 1
      ⟺ qHat ∈ {q_true, q_true+1}.

    The strengthening "carry ≠ 0 ⟹ qHat = q_true + 1" requires
    excluding qHat = q_true. This follows from the runtime call+addback+BEQ
    branch's gating: that branch only fires when the trial division
    detected an overshoot at all (i.e., qHat > q_true). The
    `isCallTrialN4Evm` precondition encodes this gating implicitly.

    Sub-stub for the addback closure's Layer 2. -/
theorem n4CallAddback_v4_carry_partition (a b : EvmWord)
    (_hb3nz : b.getLimbN 3 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_hcall : isCallTrialN4Evm a b)
    (_haddback : isAddbackBorrowN4CallEvm_v4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v4 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    -- Strong partition: carry=0 ⟺ qHat=q_true+2, AND carry≠0 ⟹ qHat=q_true+1
    -- (the call+addback+BEQ branch only fires when qHat overshoots, so
    -- qHat=q_true is excluded).
    (carry = 0 ↔ qHat.toNat = q_true + 2) ∧
      (carry ≠ 0 → qHat.toNat = q_true + 1) := by
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms carry q_true
  -- Layer 1: qHat ≤ q_true + 2.
  have h_le : qHat.toNat ≤ q_true + 2 :=
    div128Quot_v4_qHat_le_q_true_plus_two a b _hb3nz _hshift_nz _hcall
  -- Layer 2a: carry = 0 ↔ qHat ≥ q_true + 2.
  have h_2a : (carry = 0 ↔ qHat.toNat ≥ q_true + 2) :=
    n4CallAddback_v4_carry_zero_iff_overshoot_ge_two a b _hb3nz _hshift_nz _hcall _haddback
  -- Layer 2c: qHat ≥ q_true + 1 (runtime gating from call+addback+BEQ).
  have h_ge_one : qHat.toNat ≥ q_true + 1 :=
    n4CallAddbackBeq_v4_qHat_ge_q_true_plus_one a b _hb3nz _hshift_nz _hcall _haddback
  refine ⟨?_, ?_⟩
  · -- carry = 0 ↔ qHat = q_true + 2.
    constructor
    · intro h_carry
      have h_ge_2 := h_2a.mp h_carry
      omega
    · intro h_eq
      exact h_2a.mpr (by omega)
  · -- carry ≠ 0 → qHat = q_true + 1.
    intro h_carry
    have h_lt_2 : ¬ qHat.toNat ≥ q_true + 2 := fun h => h_carry (h_2a.mpr h)
    omega

/-- **`n4CallAddbackBeqSemanticHolds_v4` closure**: under the runtime
    call-addback-BEQ preconditions, the v4 predicate holds.

    Composes:
    - Layer 1 (`_qHat_le_q_true_plus_two`): qHat ≤ q_true + 2.
    - Layer 2 (`_carry_partition`): carry=0 ⟺ qHat = q_true + 2.
    - Layer 3 (q_out arithmetic): both branches yield q_out = q_true.

    Stub for the next critical-path iteration. The proof structure
    (per `project_addback_beq_closure_plan_v2.md`). -/
theorem n4CallAddbackBeqSemanticHolds_v4_of_call_addback_beq (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (haddback : isAddbackBorrowN4CallEvm_v4 a b) :
    n4CallAddbackBeqSemanticHolds_v4 a b := by
  rw [n4CallAddbackBeqSemanticHolds_v4_def]
  intro shift antiShift b3' b2' b1' b0' u4 u3 u2 u1 u0 qHat ms carry q_out
  -- Layer 1: qHat ≤ q_true + 2.
  have h_le := div128Quot_v4_qHat_le_q_true_plus_two a b hb3nz hshift_nz hcall
  -- Layer 2: carry partition (refined: covers both branches).
  have h_partition := n4CallAddback_v4_carry_partition a b hb3nz hshift_nz hcall haddback
  obtain ⟨h_carry_zero_iff, h_carry_nz_imp⟩ := h_partition
  -- Notation aliases (q_true at val256 level).
  set q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                  val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    with h_q_true_def
  -- q_out is defined as `if carry = 0 then qHat - 2 else qHat - 1` (Word).
  -- Goal: q_out.toNat = q_true.
  -- Case-split on carry.
  by_cases h_carry : carry = 0
  · -- carry = 0: qHat = q_true + 2.
    have h_qHat_eq : qHat.toNat = q_true + 2 := h_carry_zero_iff.mp h_carry
    -- q_out = qHat + signExtend12 4095 + signExtend12 4095.
    show (if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
          else qHat + signExtend12 4095).toNat = q_true
    rw [if_pos h_carry]
    -- Compute (qHat - 2).toNat.
    rw [BitVec.toNat_add, BitVec.toNat_add, signExtend12_4095_toNat]
    have h_qHat_ge_2 : qHat.toNat ≥ 2 := by linarith
    have h_qHat_lt_word : qHat.toNat < 2^64 := qHat.isLt
    -- (qHat + (2^64-1)) % 2^64 = qHat - 1.
    have h_step1 : (qHat.toNat + (2^64 - 1)) % 2^64 = qHat.toNat - 1 := by
      rw [show qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : qHat.toNat - 1 < 2^64)]
    rw [h_step1]
    -- ((qHat - 1) + (2^64 - 1)) % 2^64 = qHat - 2.
    have h_step2 : (qHat.toNat - 1 + (2^64 - 1)) % 2^64 = qHat.toNat - 2 := by
      rw [show qHat.toNat - 1 + (2^64 - 1) = (qHat.toNat - 2) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : qHat.toNat - 2 < 2^64)]
    rw [h_step2]
    -- qHat.toNat - 2 = q_true.
    omega
  · -- carry ≠ 0: qHat = q_true + 1.
    have h_qHat_eq : qHat.toNat = q_true + 1 := h_carry_nz_imp h_carry
    show (if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
          else qHat + signExtend12 4095).toNat = q_true
    rw [if_neg h_carry]
    rw [BitVec.toNat_add, signExtend12_4095_toNat]
    have h_qHat_ge_1 : qHat.toNat ≥ 1 := by linarith
    have h_step1 : (qHat.toNat + (2^64 - 1)) % 2^64 = qHat.toNat - 1 := by
      rw [show qHat.toNat + (2^64 - 1) = (qHat.toNat - 1) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by have := qHat.isLt; omega)]
    rw [h_step1]
    omega

end EvmAsm.Evm64
