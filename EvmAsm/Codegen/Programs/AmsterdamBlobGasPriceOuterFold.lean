/- A finite outer-loop fold for the K70 round adapter (#12851).

   The round proof exposes the ordinary exits followed by one QBACK exit.
   This file supplies the list-level induction that repeats that shape a
   finite number of times and then consumes a terminal continuation.  The
   state invariant and the arithmetic relation between successive states are
   intentionally supplied by the caller; this theorem does not weaken either
   the round post or the CodeReq.
-/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14RoundQBackComposition
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceModel

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Stateless.SpecRef
open EvmAsm.Codegen.AmsterdamBlobGasPrice
open EvmAsm.Codegen.AmsterdamBlobGasPriceDivisionBridge
open EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec
open EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

set_option exponentiation.threshold 384
set_option maxRecDepth 8000

/- The linked QBACK post carries six concrete quotient limbs.  These small
   bridges turn the pure 384-bit division/addition results into the canonical
   limb lists used by the model, without putting an arithmetic premise on the
   machine post. -/
theorem div384by64_quot_to_natToLimbs
    (d : Word) (ws : List Word) (n : Nat)
    (hd : 0 < d.toNat) (hd63 : d.toNat ≤ 2 ^ 63)
    (hlen : ws.length = 6)
    (hval : limbsToNat ws / d.toNat = n) :
    (div384by64 d ws).1 = natToLimbs 6 n := by
  have hquot := div384by64_quot d ws hd hd63
  have hquot_val : limbsToNat (div384by64 d ws).1 = n := by
    rw [hquot, hval]
  have hquot_len : (div384by64 d ws).1.length = 6 := by
    rw [div384by64_length, hlen]
  have hquot_bound :
      limbsToNat (div384by64 d ws).1 < 2 ^ (64 * 6) :=
    limbsToNat_lt _ 6 hquot_len
  apply natToLimbs_eq_of_limbsToNat
    (div384by64 d ws).1 6 n hquot_len
  · rw [← hquot_val]
    exact hquot_bound
  · exact hquot_val

theorem add384_low_to_natToLimbs
    (as ss : List Word) (n : Nat)
    (hlen : as.length = 6) (hlen2 : ss.length = 6)
    (hsum : limbsToNat as + limbsToNat ss < 2 ^ 384)
    (hval : limbsToNat as + limbsToNat ss = n) :
    (add384Run as ss (0 : Word)).1 = natToLimbs 6 n := by
  have hlow := add384_low_of_lt as ss hlen hlen2 hsum
  have hout_len : (add384Run as ss (0 : Word)).1.length = 6 := by
    rw [add384Run_length as ss 0 (by omega)]
    exact hlen
  have hout_bound :
      limbsToNat (add384Run as ss (0 : Word)).1 < 2 ^ (64 * 6) :=
    limbsToNat_lt _ 6 hout_len
  have hn_bound : n < 2 ^ (64 * 6) := by
    have hn_bound' : n < 2 ^ 384 := by
      rw [← hval]
      exact hsum
    simpa only [show 64 * 6 = 384 by decide] using hn_bound'
  apply natToLimbs_eq_of_limbsToNat
    (add384Run as ss (0 : Word)).1 6 n hout_len hn_bound
  rw [hlow, hval]

/- These irreducible wrappers keep the machine-shaped lists folded while the
   model bridge is elaborated.  The equalities below identify them with the
   existing source post definitions, so they do not introduce a second
   computation. -/
@[irreducible] def qbackWordsModel
    (iVal excess a0 a1 a2 a3 a4 a5 : Word) : List Word :=
  (divstSix (taylorDW * iVal)
    (roundP0 a0 excess) (roundP1 a0 a1 excess)
    (roundP2 a0 a1 a2 excess) (roundP3 a0 a1 a2 a3 excess)
    (roundP4 a0 a1 a2 a3 a4 excess)
    (roundP5 a0 a1 a2 a3 a4 a5 excess)).1

@[irreducible] def sbackWordsModel
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) : List Word :=
  (add384Run [a0, a1, a2, a3, a4, a5]
    [s0, s1, s2, s3, s4, s5] (0 : Word)).1

theorem qbackWordsModel_eq_existing
    (iVal excess a0 a1 a2 a3 a4 a5 : Word) :
    qbackWordsModel iVal excess a0 a1 a2 a3 a4 a5 =
      taylorRoundBackedgeQuotient iVal excess a0 a1 a2 a3 a4 a5 := by
  unfold qbackWordsModel taylorRoundBackedgeQuotient
  rfl

theorem sbackWordsModel_eq_existing
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word) :
    sbackWordsModel a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 =
      taylorRoundBackedgeSum a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 := by
  unfold sbackWordsModel taylorRoundBackedgeSum
  rw [roundS_eq_add384Run]

/- The linked exit-divide window is the Body5 mirror of the Body3 divider
   already connected to the pure model by `DivisionBridge`.  Keep the
   namespace bridge explicit: the two source files deliberately duplicate
   the machine definition, so an unqualified `divst` is not enough to make
   this equality visible to Lean. -/
theorem body5_divst_eq_body3_divst
    (dv r0 t0 q0 : Word) (j : Nat) :
    AmsterdamBlobGasPriceBody5Spec.divst dv r0 t0 q0 j =
      AmsterdamBlobGasPriceBody3Spec.divst dv r0 t0 q0 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [AmsterdamBlobGasPriceBody5Spec.divst,
      AmsterdamBlobGasPriceBody3Spec.divst]
    rw [ih]

/- `exitdivQ*` are the quotient limbs of the linked Body5 mirror.  This
   theorem only changes representation: it identifies their six-step list
   with the Body3-shaped `divstSix` consumed by `DivisionBridge`. -/
theorem exitdiv_q_eq_divstSix
    (s0 s1 s2 s3 s4 s5 : Word) :
    [exitdivQ0 s0 s1 s2 s3 s4 s5, exitdivQ1 s0 s1 s2 s3 s4 s5,
      exitdivQ2 s0 s1 s2 s3 s4 s5, exitdivQ3 s0 s1 s2 s3 s4 s5,
      exitdivQ4 s0 s1 s2 s3 s4 s5, exitdivQ5 s0 s1 s2 s3 s4 s5] =
      (AmsterdamBlobGasPriceDivisionBridge.divstSix
        EvmAsm.Codegen.AmsterdamBlobGasPriceBodySpec.taylorDW
        s0 s1 s2 s3 s4 s5).1 := by
  simp only [exitdivQ0, exitdivQ1, exitdivQ2, exitdivQ3, exitdivQ4,
    exitdivQ5, exitdivZ0, exitdivZ1, exitdivZ2, exitdivZ3, exitdivZ4,
    exitdivZ5, AmsterdamBlobGasPriceDivisionBridge.divstSix]
  simp only [body5_divst_eq_body3_divst]

/- The terminal exit-divide is the model's final `sum / D`.  At a successful
   model result, the prefix invariant at `j = 495` has zero accumulator, so
   the linked six-limb sum is exactly the quotient input consumed by
   `exitdivQ*`.  This is a terminal step lemma, not a new machine-post
   premise: all arithmetic facts come from the existing `h_some` result and
   the invariant's sum equality. -/
theorem exitdiv_q_model_step
    (num result : Nat) (s0 s1 s2 s3 s4 s5 : Word)
    (h_num : num < taylorWord64Bound)
    (h_some : taylor384Aux num taylorDenominator 1 taylorDenominator 0 =
      some result)
    (h_s : limbsToNat [s0, s1, s2, s3, s4, s5] =
      (priceLoopPrefix num 495).2) :
    [exitdivQ0 s0 s1 s2 s3 s4 s5, exitdivQ1 s0 s1 s2 s3 s4 s5,
      exitdivQ2 s0 s1 s2 s3 s4 s5, exitdivQ3 s0 s1 s2 s3 s4 s5,
      exitdivQ4 s0 s1 s2 s3 s4 s5, exitdivQ5 s0 s1 s2 s3 s4 s5] =
      natToLimbs 6 result := by
  have h_zero := priceLoopPrefix_acc_zero_of_some num result h_num h_some
  have h_rel := priceLoopPrefix_taylorNatAux num 495
  rw [taylorNatAux.eq_1, if_pos h_zero] at h_rel
  have h_init := taylor384Aux_some_implies_nat_lt
    num 1 taylorDenominator 0 result h_some
  have h_result : (priceLoopPrefix num 495).2 / taylorDenominator = result := by
    rw [h_rel, h_init.2]
  have hval : limbsToNat [s0, s1, s2, s3, s4, s5] /
      taylorDW.toNat = result := by
    rw [h_s]
    have hD : taylorDW.toNat = taylorDenominator := by decide
    rw [hD, h_result]
  have hdiv := AmsterdamBlobGasPriceDivisionBridge.divstSix_eq_div384by64
    taylorDW s0 s1 s2 s3 s4 s5
  have hq := div384by64_quot_to_natToLimbs
    taylorDW [s0, s1, s2, s3, s4, s5] result
    (by decide) (by decide) (by simp) hval
  have hq' :
      (AmsterdamBlobGasPriceDivisionBridge.divstSix
        taylorDW s0 s1 s2 s3 s4 s5).1 = natToLimbs 6 result := by
    rw [hdiv]
    exact hq
  rw [exitdiv_q_eq_divstSix]
  exact hq'

/- QBACK's quotient is the next model accumulator when the ordinary
   recurrence is still live.  The `some` hypothesis supplies the strict
   256-bit result bound; the local `h_acc` and `h_j` hypotheses are the same
   guards that the emitted round has already taken. -/
theorem qbackWordsModel_eq_prefix
    (num result j : Nat) (iVal excess : Word)
    (a0 a1 a2 a3 a4 a5 : Word)
    (h_num : num < taylorWord64Bound)
    (h_some : taylor384Aux num taylorDenominator 1 taylorDenominator 0 =
      some result)
    (h_acc : (priceLoopPrefix num j).1 ≠ 0)
    (h_a : limbsToNat [a0, a1, a2, a3, a4, a5] =
      (priceLoopPrefix num j).1)
    (h_i : iVal = taylorLoopIndex j)
    (h_excess : excess.toNat = num)
    (h_j : j < 495) :
    qbackWordsModel iVal excess a0 a1 a2 a3 a4 a5 =
      natToLimbs 6 (priceLoopPrefix num (j + 1)).1 := by
  have hD : taylorDW.toNat = taylorDenominator := by decide
  have hiNat : iVal.toNat = j + 1 := by
    rw [h_i]
    simp [taylorLoopIndex, BitVec.toNat_ofNat]
    have hj : j + 1 ≤ 495 := by omega
    omega
  have hdivisor := priceLoopPrefix_divisor_lt_word64 j h_j
  have hdivisor_pos : 0 < taylorDenominator * (j + 1) := by
    norm_num [taylorDenominator]
  have hdivisor63 : taylorDenominator * (j + 1) ≤ 2 ^ 63 := by
    have hbound : taylorDenominator * 495 ≤ 2 ^ 63 := by decide
    exact le_trans
      (Nat.mul_le_mul_left taylorDenominator (by omega)) hbound
  have hden_value :
      (taylorDW * iVal).toNat = taylorDenominator * (j + 1) := by
    rw [BitVec.toNat_mul, hD, hiNat]
    have hdivisor' : taylorDenominator * (j + 1) < 2 ^ 64 := by
      simpa [taylorWord64Bound] using hdivisor
    exact Nat.mod_eq_of_lt hdivisor'
  have h_product := priceLoopPrefix_product_lt_word384_of_some
    num result j h_num h_some h_acc
  have h_product' : (priceLoopPrefix num j).1 * num < 2 ^ 384 := by
    simpa [taylorWord384Bound] using h_product
  have hmul_value :
      limbsToNat [roundP0 a0 excess, roundP1 a0 a1 excess,
        roundP2 a0 a1 a2 excess, roundP3 a0 a1 a2 a3 excess,
        roundP4 a0 a1 a2 a3 a4 excess,
        roundP5 a0 a1 a2 a3 a4 a5 excess] =
        (priceLoopPrefix num j).1 * num := by
    rw [roundP_eq_mul384Run]
    have hlow := mul384_low_of_lt
      [a0, a1, a2, a3, a4, a5] excess
      (by simp) (by simpa [h_a, h_excess] using h_product')
    rw [hlow, h_a, h_excess]
  have hden_pos : 0 < (taylorDW * iVal).toNat := by
    rw [hden_value]
    exact hdivisor_pos
  have hden_63 : (taylorDW * iVal).toNat ≤ 2 ^ 63 := by
    rw [hden_value]
    exact hdivisor63
  have hqdiv :
      limbsToNat
          [roundP0 a0 excess, roundP1 a0 a1 excess,
            roundP2 a0 a1 a2 excess, roundP3 a0 a1 a2 a3 excess,
            roundP4 a0 a1 a2 a3 a4 excess,
            roundP5 a0 a1 a2 a3 a4 a5 excess] /
          (taylorDW * iVal).toNat =
        (priceLoopPrefix num j).1 * num /
          (taylorDenominator * (j + 1)) := by
    rw [hmul_value, hden_value]
  have hnext :
      (priceLoopPrefix num (j + 1)).1 =
        (priceLoopPrefix num j).1 * num /
          (taylorDenominator * (j + 1)) := by
    rw [priceLoopPrefix_step]
  let ws : List Word :=
    [roundP0 a0 excess, roundP1 a0 a1 excess,
      roundP2 a0 a1 a2 excess, roundP3 a0 a1 a2 a3 excess,
      roundP4 a0 a1 a2 a3 a4 excess,
      roundP5 a0 a1 a2 a3 a4 a5 excess]
  have hws_len : ws.length = 6 := by simp [ws]
  have hq := div384by64_quot_to_natToLimbs
    (taylorDW * iVal) ws (priceLoopPrefix num (j + 1)).1
    hden_pos hden_63 hws_len (by rw [hqdiv, ← hnext])
  unfold qbackWordsModel
  rw [divstSix_eq_div384by64]
  simpa [ws] using hq

theorem sbackWordsModel_eq_prefix
    (num result j : Nat)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (h_some : taylor384Aux num taylorDenominator 1 taylorDenominator 0 =
      some result)
    (h_acc : (priceLoopPrefix num j).1 ≠ 0)
    (h_a : limbsToNat [a0, a1, a2, a3, a4, a5] =
      (priceLoopPrefix num j).1)
    (h_s : limbsToNat [s0, s1, s2, s3, s4, s5] =
      (priceLoopPrefix num j).2) :
    sbackWordsModel a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 =
      natToLimbs 6 (priceLoopPrefix num (j + 1)).2 := by
  have hsum := priceLoopPrefix_sum_lt_word384_of_some
    num result j h_some h_acc
  have hsum' : (priceLoopPrefix num j).1 + (priceLoopPrefix num j).2 <
      2 ^ 384 := by
    simpa [taylorWord384Bound, Nat.add_comm] using hsum
  have hsum_value :
      limbsToNat [a0, a1, a2, a3, a4, a5] +
          limbsToNat [s0, s1, s2, s3, s4, s5] =
        (priceLoopPrefix num j).1 + (priceLoopPrefix num j).2 := by
    rw [h_a, h_s]
  have hnext :
      (priceLoopPrefix num (j + 1)).2 =
        (priceLoopPrefix num j).2 + (priceLoopPrefix num j).1 := by
    rw [priceLoopPrefix_step]
  have hlist := add384_low_to_natToLimbs
    [a0, a1, a2, a3, a4, a5] [s0, s1, s2, s3, s4, s5]
    (priceLoopPrefix num (j + 1)).2
    (by simp) (by simp)
    (by simpa [hsum_value, Nat.add_comm] using hsum')
    (by rw [hsum_value, hnext]; omega)
  unfold sbackWordsModel
  exact hlist

/- Convert the concrete QBACK post to the model-linked backedge post.  The
   parity adapter already supplies the machine-state part; these two model
   equalities replace only its quotient and sum lists. -/
theorem taylor_round_qback_model_step
    (num result j : Nat) (newSp excess outPtr iVal : Word)
    (vals : Reg → Word) (evenBase oddBase : Word)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : Word)
    (v7 v28 v29 v30 v31 : Word) (FR : Assertion)
    (h_num : num < taylorWord64Bound)
    (h_some : taylor384Aux num taylorDenominator 1 taylorDenominator 0 =
      some result)
    (h_acc : (priceLoopPrefix num j).1 ≠ 0)
    (h_a : limbsToNat [a0, a1, a2, a3, a4, a5] =
      (priceLoopPrefix num j).1)
    (h_s : limbsToNat [s0, s1, s2, s3, s4, s5] =
      (priceLoopPrefix num j).2)
    (h_i : iVal = taylorLoopIndex j)
    (h_excess : excess.toNat = num)
    (h_j : j < 495) :
    ∀ h,
      taylorRoundSourceQBACKComputed newSp excess outPtr iVal
        (parityBuffer j evenBase oddBase)
        (parityBuffer j oddBase evenBase) vals
        a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
        v7 v28 v29 v30 v31 FR h →
      (taylorLoopInvParityAt newSp excess outPtr vals (j + 1)
        (iVal + signExtend12 (1 : BitVec 12)) evenBase oddBase
        (natToLimbs 6 (priceLoopPrefix num (j + 1)).1)
        [a0, a1, a2, a3, a4, a5]
        (natToLimbs 6 (priceLoopPrefix num (j + 1)).2) FR **
        (.x0 ↦ᵣ (0 : Word))) h := by
  intro h hp
  have hparity := taylor_round_source_qback_computed_to_parity
    newSp excess outPtr iVal vals j evenBase oddBase
    a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
    v7 v28 v29 v30 v31 FR h hp
  have hq := qbackWordsModel_eq_prefix
    num result j iVal excess a0 a1 a2 a3 a4 a5
    h_num h_some h_acc h_a h_i h_excess h_j
  have hs := sbackWordsModel_eq_prefix
    num result j a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5
    h_some h_acc h_a h_s
  rw [qbackWordsModel_eq_existing] at hq
  rw [sbackWordsModel_eq_existing] at hs
  rw [hq, hs] at hparity
  exact hparity

theorem nbranch_extend_last
    {n1 n2 : Nat} {entry mid : Word} {cr : CodeReq}
    {P Q : Assertion} {terminal exits2 : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P
      (terminal ++ [(mid, Q)]))
    (h2 : cpsNBranchWithin n2 mid cr Q exits2) :
    cpsNBranchWithin (n1 + n2) entry cr P (terminal ++ exits2) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ :=
    h1 R hR s hcr hPR hpc
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hterminal | hmid
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex, List.mem_append.mpr (Or.inl hterminal), hpc1, hQ1⟩
  · rcases hmid with hmid | hnil
    · subst ex
      have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
      obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ :=
        h2 R hR s1 hcr' hQ1 hpc1
      exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
        stepN_add_eq hstep1 hstep2, ex2,
        List.mem_append.mpr (Or.inr hmem2), hpc2, hQ2⟩
    · simp at hnil

/- When the continuation has the same terminal list as the current round,
   discard the duplicate copy introduced by ordinary list concatenation. -/
theorem nbranch_extend_last_same_terminal
    {n1 n2 : Nat} {entry mid : Word} {cr : CodeReq}
    {P Q : Assertion} {terminal : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n1 entry cr P
      (terminal ++ [(mid, Q)]))
    (h2 : cpsNBranchWithin n2 mid cr Q terminal) :
    cpsNBranchWithin (n1 + n2) entry cr P terminal := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, ex, hmem, hpc1, hQ1⟩ :=
    h1 R hR s hcr hPR hpc
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hterminal | hmid
  · exact ⟨k1, Nat.le_trans hk1 (Nat.le_add_right n1 n2), s1,
      hstep1, ex, hterminal, hpc1, hQ1⟩
  · rcases hmid with hmid | hnil
    · subst ex
      have hcr' := CodeReq.SatisfiedBy_preserved hstep1 hcr
      obtain ⟨k2, hk2, s2, hstep2, ex2, hmem2, hpc2, hQ2⟩ :=
        h2 R hR s1 hcr' hQ1 hpc1
      exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
        stepN_add_eq hstep1 hstep2, ex2, hmem2, hpc2, hQ2⟩
    · simp at hnil

/- A finite fold of a round with a fixed terminal exit list.  Each of the
   first `N` rounds has the same terminal list and a QBACK transition to the
   next invariant.  The final continuation is supplied separately at `inv N`;
   this avoids treating a zero-round run as if it had already reached a
   terminal arm. -/
theorem finite_nbranch_loop_spec
    {N m mLast : Nat} {hdr : Word} {cr : CodeReq}
    {inv : Nat → Assertion} {terminal : List (Word × Assertion)}
    (hround : ∀ j, j < N →
      cpsNBranchWithin m hdr cr (inv j)
        (terminal ++ [(hdr, inv (j + 1))]))
    (htail : cpsNBranchWithin mLast hdr cr (inv N) terminal) :
    cpsNBranchWithin (m * N + mLast) hdr cr (inv 0) terminal := by
  revert mLast inv
  induction N using Nat.strongRecOn with
  | _ N ih =>
      intro mLast inv hround htail
      cases N with
      | zero =>
          simpa using htail
      | succ N =>
          have hfirst := hround 0 (by omega)
          have hround' : ∀ j, j < N →
              cpsNBranchWithin m hdr cr (inv (j + 1))
                (terminal ++ [(hdr, inv ((j + 1) + 1))]) := by
            intro j hj
            exact hround (j + 1) (by omega)
          have htail' : cpsNBranchWithin mLast hdr cr (inv (N + 1)) terminal := by
            simpa [Nat.succ_eq_add_one] using htail
          have hrest := ih N (by omega) (mLast := mLast)
            (inv := fun j => inv (j + 1)) hround' htail'
          have hfold := nbranch_extend_last_same_terminal hfirst hrest
          simpa [Nat.succ_eq_add_one, Nat.mul_succ, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using hfold

theorem taylor_outer_fold_from_rounds
    {N m mLast : Nat} {hdr : Word} {cr : CodeReq}
    {inv : Nat → Assertion} {terminal : List (Word × Assertion)}
    (hround : ∀ j, j < N →
      cpsNBranchWithin m hdr cr (inv j)
        (terminal ++ [(hdr, inv (j + 1))]))
    (htail : cpsNBranchWithin mLast hdr cr (inv N) terminal) :
    cpsNBranchWithin (m * N + mLast) hdr cr (inv 0) terminal :=
  finite_nbranch_loop_spec hround htail

#print axioms finite_nbranch_loop_spec
#print axioms taylor_outer_fold_from_rounds
#print axioms nbranch_extend_last
#print axioms nbranch_extend_last_same_terminal

end EvmAsm.Codegen.AmsterdamBlobGasPriceOuterSpec
