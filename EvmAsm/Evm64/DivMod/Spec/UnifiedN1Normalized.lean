/-
  EvmAsm.Evm64.DivMod.Spec.UnifiedN1Normalized

  Normalized-mulsub n=1 wrappers split out from `Spec.Unified` to keep the
  public unified spec file under the line-count guardrail.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.UnifiedExactNoNop

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Unified-bound wrapper for `evm_div_n1_stack_spec_within_word` from the
    normalized n=1 Euclidean equation. -/
theorem evm_div_n1_stack_spec_within_word_uni_of_normalized_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_limbs_normalized_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hmulsub hge
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n1_stack_spec_within_word bltu_3 bltu_2 bltu_1 bltu_0
      sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
      hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for `evm_div_n1_stack_spec_within_word_exact_x1`
    from the normalized n=1 Euclidean equation. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_uni_of_normalized_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_limbs_normalized_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hmulsub hge
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n1_stack_spec_within_word_exact_x1 bltu_3 bltu_2 bltu_1 bltu_0
      sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
      hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Trial-bundled n=1 exact-x1 DIV wrapper from normalized mulsub plus
    quotient-overestimate obligations. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_trial_normalized_mulsub_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) /
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) ≤
          ((fullDivN1R3 bltu_3
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
            ((fullDivN1R2 bltu_3 bltu_2
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
            ((fullDivN1R1 bltu_3 bltu_2 bltu_1
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
            ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hge⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact evm_div_n1_stack_spec_within_word_exact_x1_uni_of_normalized_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign
    (by simpa [ha3, hb0] using hbltu_3)
    (by simpa [ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_2)
    (by simpa [ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_1)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_0)
    hcarry2
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hge)

/-- Shape-specialized n=1 exact-x1 DIV wrapper from normalized mulsub plus
    quotient-overestimate obligations. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_shape_normalized_mulsub_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) /
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) ≤
          ((fullDivN1R3 bltu_3
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
            ((fullDivN1R2 bltu_3 bltu_2
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
            ((fullDivN1R1 bltu_3 bltu_2 bltu_1
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
            ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have htrial : N1TrialWitnesses a b :=
    n1TrialWitnesses_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  exact evm_div_n1_stack_spec_within_word_exact_x1_trial_normalized_mulsub_overestimate_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 hpath

/-- Unified-bound wrapper for `evm_div_n1_stack_spec_within_word_noNop`
    from the normalized n=1 Euclidean equation. -/
theorem evm_div_n1_stack_spec_within_word_noNop_uni_of_normalized_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_limbs_normalized_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hmulsub hge
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n1_stack_spec_within_word_noNop bltu_3 bltu_2 bltu_1 bltu_0
      sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
      hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for
    `evm_div_n1_stack_spec_within_word_exact_x1_noNop` from the normalized
    n=1 Euclidean equation. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_uni_of_normalized_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_limbs_normalized_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hmulsub hge
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n1_stack_spec_within_word_exact_x1_noNop
      bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
      hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2
      hdivWord)

/-- Trial-bundled n=1 DIV wrapper from normalized mulsub plus
    quotient-overestimate obligations. -/
theorem evm_div_n1_stack_spec_within_word_trial_normalized_mulsub_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) /
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) ≤
          ((fullDivN1R3 bltu_3
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
            ((fullDivN1R2 bltu_3 bltu_2
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
            ((fullDivN1R1 bltu_3 bltu_2 bltu_1
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
            ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hge⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact evm_div_n1_stack_spec_within_word_uni_of_normalized_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign
    (by simpa [ha3, hb0] using hbltu_3)
    (by simpa [ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_2)
    (by simpa [ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_1)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_0)
    hcarry2
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hge)

/-- Shape-specialized n=1 DIV wrapper from normalized mulsub plus
    quotient-overestimate obligations. -/
theorem evm_div_n1_stack_spec_within_word_shape_normalized_mulsub_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) /
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) ≤
          ((fullDivN1R3 bltu_3
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
            ((fullDivN1R2 bltu_3 bltu_2
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
            ((fullDivN1R1 bltu_3 bltu_2 bltu_1
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
            ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have htrial : N1TrialWitnesses a b :=
    n1TrialWitnesses_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  exact evm_div_n1_stack_spec_within_word_trial_normalized_mulsub_overestimate_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 hpath

/-- Trial-bundled n=1 exact-x1/no-NOP DIV wrapper from normalized mulsub plus
    normalized final-remainder obligations. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_trial_normalized_remainder_uni
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hrem_lt⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact evm_div_n1_stack_spec_within_word_exact_x1_noNop_uni_of_normalized_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign
    (by simpa [ha3, hb0] using hbltu_3)
    (by simpa [ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_2)
    (by simpa [ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_1)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_0)
    hcarry2
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
    (by
      exact fullDivN1QuotientOverestimate_of_normalized_mulsub_remainder_lt
        bltu_3 bltu_2 bltu_1 bltu_0
        (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
        (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hrem_lt))

/-- Trial-bundled n=1 exact-x1/no-NOP DIV wrapper from normalized mulsub
    plus quotient-overestimate obligations. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_trial_normalized_mulsub_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) /
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) ≤
          ((fullDivN1R3 bltu_3
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
            ((fullDivN1R2 bltu_3 bltu_2
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
            ((fullDivN1R1 bltu_3 bltu_2 bltu_1
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
            ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hge⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact evm_div_n1_stack_spec_within_word_exact_x1_noNop_uni_of_normalized_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign
    (by simpa [ha3, hb0] using hbltu_3)
    (by simpa [ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_2)
    (by simpa [ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_1)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_0)
    hcarry2
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hge)

/-- Shape-specialized n=1 exact-x1/no-NOP DIV wrapper from normalized mulsub
    plus quotient-overestimate obligations. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_shape_normalized_mulsub_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) /
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) ≤
          ((fullDivN1R3 bltu_3
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
            ((fullDivN1R2 bltu_3 bltu_2
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
            ((fullDivN1R1 bltu_3 bltu_2 bltu_1
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
            ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have htrial : N1TrialWitnesses a b :=
    n1TrialWitnesses_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  exact evm_div_n1_stack_spec_within_word_exact_x1_noNop_trial_normalized_mulsub_overestimate_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 hpath

/-- Shape-specialized n=1 exact-x1/no-NOP DIV wrapper from normalized mulsub
    plus normalized final-remainder obligations. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_shape_normalized_remainder_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have htrial : N1TrialWitnesses a b :=
    n1TrialWitnesses_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  exact evm_div_n1_stack_spec_within_word_exact_x1_noNop_trial_normalized_remainder_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 hpath

/-- Trial-bundled n=1 no-NOP DIV callable wrapper from normalized mulsub plus
    normalized final-remainder obligations. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_trial_normalized_remainder_uni
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hrem_lt⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat :=
    fullDivN1QuotientOverestimate_of_normalized_mulsub_remainder_lt
      bltu_3 bltu_2 bltu_1 bltu_0
      (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
      (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hrem_lt)
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_limbs_normalized_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz
      (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
      hge
  exact evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_uni
    bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign
    (by simpa [ha3, hb0] using hbltu_3)
    (by simpa [ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_2)
    (by simpa [ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_1)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_0)
    hcarry2 hdivWord

/-- Shape-specialized n=1 no-NOP DIV callable wrapper from normalized mulsub
    plus normalized final-remainder obligations. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_shape_normalized_remainder_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have htrial : N1TrialWitnesses a b :=
    n1TrialWitnesses_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  exact evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_trial_normalized_remainder_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 hpath

/-- Trial-bundled n=1 no-NOP DIV callable wrapper from normalized mulsub plus
    quotient-overestimate obligations. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_trial_normalized_mulsub_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) /
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) ≤
          ((fullDivN1R3 bltu_3
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
            ((fullDivN1R2 bltu_3 bltu_2
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
            ((fullDivN1R1 bltu_3 bltu_2 bltu_1
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
            ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hge⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_limbs_normalized_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz
      (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
      (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hge)
  exact evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_uni
    bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign
    (by simpa [ha3, hb0] using hbltu_3)
    (by simpa [ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_2)
    (by simpa [ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_1)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_0)
    hcarry2 hdivWord

/-- Shape-specialized n=1 no-NOP DIV callable wrapper from normalized mulsub
    plus quotient-overestimate obligations. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_shape_normalized_mulsub_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) /
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) ≤
          ((fullDivN1R3 bltu_3
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
            ((fullDivN1R2 bltu_3 bltu_2
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
            ((fullDivN1R1 bltu_3 bltu_2 bltu_1
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
            ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have htrial : N1TrialWitnesses a b :=
    n1TrialWitnesses_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  exact evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_trial_normalized_mulsub_overestimate_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 hpath

/-- Trial-bundled n=1 no-NOP DIV wrapper from normalized mulsub plus
    quotient-overestimate obligations. -/
theorem evm_div_n1_stack_spec_within_word_noNop_trial_normalized_mulsub_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) /
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) ≤
          ((fullDivN1R3 bltu_3
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
            ((fullDivN1R2 bltu_3 bltu_2
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
            ((fullDivN1R1 bltu_3 bltu_2 bltu_1
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
            ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hge⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact evm_div_n1_stack_spec_within_word_noNop_uni_of_normalized_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign
    (by simpa [ha3, hb0] using hbltu_3)
    (by simpa [ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_2)
    (by simpa [ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_1)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hbltu_0)
    hcarry2
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hge)

/-- Shape-specialized n=1 no-NOP DIV wrapper from normalized mulsub plus
    quotient-overestimate obligations. -/
theorem evm_div_n1_stack_spec_within_word_noNop_shape_normalized_mulsub_overestimate_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&&
        ~~~(1 : Word) = base + div128CallRetOff)
    (hcarry2 : Carry2NzAll
      (b.getLimbN 0 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64))
      ((b.getLimbN 1 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 0 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 2 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 1 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64)))
      ((b.getLimbN 3 <<< (((clzResult (b.getLimbN 0)).1).toNat % 64)) |||
        (b.getLimbN 2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 0)).1).toNat % 64))))
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) /
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) ≤
          ((fullDivN1R3 bltu_3
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 192 +
            ((fullDivN1R2 bltu_3 bltu_2
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 128 +
            ((fullDivN1R1 bltu_3 bltu_2 bltu_1
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2 ^ 64 +
            ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
                (a.getLimbN 0) (a.getLimbN 1)
                (a.getLimbN 2) (a.getLimbN 3)
                (b.getLimbN 0) (b.getLimbN 1)
                (b.getLimbN 2) (b.getLimbN 3)).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have htrial : N1TrialWitnesses a b :=
    n1TrialWitnesses_of_getLimbN_shape_shift_nz
      a b hbnzGet hb3z hb2z hb1z hshift_nz
  exact evm_div_n1_stack_spec_within_word_noNop_trial_normalized_mulsub_overestimate_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 hpath

end EvmAsm.Evm64
