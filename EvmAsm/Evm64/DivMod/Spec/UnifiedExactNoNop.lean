/-
  EvmAsm.Evm64.DivMod.Spec.UnifiedExactNoNop

  Unified-bound exact-x1 no-NOP DIV branch wrappers split out from
  `Spec.Unified` to keep the public dispatcher file under the size cap.

  Legacy carry note: these wrappers still thread the raw normalized
  `Carry2NzAll` package through exact no-NOP stack surfaces. N2/N3 final v4
  stack work should use selected/reachable carry wrappers instead of extending
  these compatibility surfaces.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1ExactNoNop
public import EvmAsm.Evm64.DivMod.Spec.N1TrialWitnesses
public import EvmAsm.Evm64.DivMod.Spec.N1Harith
public import EvmAsm.Evm64.DivMod.Spec.Unified

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Unified-bound wrapper for
    `evm_div_n1_stack_spec_within_word_exact_x1_noNop`. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_uni
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
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
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
    fullDivN1QuotientWord_eq_div_of_limbs_mulsub_overestimate
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

/-- Trial-bundled wrapper for the n=1 exact-x1/no-NOP DIV surface.

    The trial bundle owns the branch booleans.  Callers provide the remaining
    raw arithmetic obligations for those booleans; this wrapper delegates to
    the existing exact-x1 no-NOP surface. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_trial_uni
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
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (harith : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
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
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1QuotientOverestimate bltu_3 bltu_2 bltu_1 bltu_0
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
  obtain ⟨hmulsub, hge⟩ :=
    harith bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact evm_div_n1_stack_spec_within_word_exact_x1_noNop_uni
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
    (by simpa [fullDivN1MulSubEq, ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hmulsub)
    (by simpa [fullDivN1QuotientOverestimate, ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hge)

/-- Trial-bundled n=1 exact-x1/no-NOP DIV wrapper from raw mulsub plus
    final-remainder obligations.

    This derives the quotient-overestimate part of `harith` before delegating
    to the trial-bundled exact wrapper. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_trial_remainder_uni
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
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
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
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1RemainderLt bltu_3 bltu_2 bltu_1 bltu_0
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
  exact evm_div_n1_stack_spec_within_word_exact_x1_noNop_trial_uni
    sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2
    (fun bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0 =>
      let hpair := hpath bltu_3 bltu_2 bltu_1 bltu_0
        hbltu_3 hbltu_2 hbltu_1 hbltu_0
      fullDivN1Harith_of_mulsub_remainder_lt
        bltu_3 bltu_2 bltu_1 bltu_0
        (by simpa [hb0, hb1, hb2, hb3] using hbnz) hpair.1 hpair.2)

/-- Shape-specialized n=1 exact-x1/no-NOP DIV wrapper.

    This derives the `N1TrialWitnesses` bundle from the public n=1 divisor
    shape and delegates to the trial-bundled exact wrapper. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_shape_trial_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
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
    (harith : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
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
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1QuotientOverestimate bltu_3 bltu_2 bltu_1 bltu_0
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
  exact evm_div_n1_stack_spec_within_word_exact_x1_noNop_trial_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 harith

/-- Shape-specialized n=1 exact-x1/no-NOP DIV wrapper from raw mulsub plus
    final-remainder obligations. -/
theorem evm_div_n1_stack_spec_within_word_exact_x1_noNop_shape_remainder_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
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
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1RemainderLt bltu_3 bltu_2 bltu_1 bltu_0
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
  exact evm_div_n1_stack_spec_within_word_exact_x1_noNop_trial_remainder_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 hpath

/-- Unified-bound wrapper for
    `evm_div_n1_stack_spec_within_word_noNop_callableOwnPost`. -/
theorem evm_div_n1_stack_spec_within_word_noNop_callableOwnPost_uni
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
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hdivWord : fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n1_stack_spec_within_word_noNop_callableOwnPost
      bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
      hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for the n=1 no-NOP DIV callable surface whose
    precondition keeps `x1` outside the scratch bundle. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_uni
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
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
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (hdivWord : fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost
      bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
      hshift_nz halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Trial-bundled wrapper for the n=1 no-NOP DIV callable surface whose
    precondition keeps `x1` outside the scratch bundle.

    The trial bundle owns the branch booleans.  Callers provide the remaining
    raw arithmetic obligations for those booleans; this wrapper derives the
    quotient-word equality and delegates to the existing preNoX1 callable
    surface. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_trial_uni
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
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
    (harith : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
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
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1QuotientOverestimate bltu_3 bltu_2 bltu_1 bltu_0
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
  have hbnzGet :
      b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
        b.getLimbN 3 ≠ 0 := by
    simpa [hb0, hb1, hb2, hb3] using hbnz
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0, hdivWord⟩ :=
    N1TrialWitnesses.exists_quotient_word htrial hbnzGet harith
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
    hcarry2
    (by simpa [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] using hdivWord)

/-- Trial-bundled n=1 no-NOP DIV callable wrapper from raw mulsub plus
    final-remainder obligations.

    This derives the quotient-word equality via the remainder-bound eliminator
    before delegating to the callable preNoX1 surface. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_trial_remainder_uni
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
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (htrial : N1TrialWitnesses a b)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64))))
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
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1RemainderLt bltu_3 bltu_2 bltu_1 bltu_0
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
  exact evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_trial_uni
    sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2
    (fun bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0 =>
      let hpair := hpath bltu_3 bltu_2 bltu_1 bltu_0
        hbltu_3 hbltu_2 hbltu_1 hbltu_0
      fullDivN1Harith_of_mulsub_remainder_lt
        bltu_3 bltu_2 bltu_1 bltu_0
        (by simpa [hb0, hb1, hb2, hb3] using hbnz) hpair.1 hpair.2)

/-- Shape-specialized n=1 no-NOP DIV callable wrapper whose precondition keeps
    `x1` outside the scratch bundle.

    This derives the `N1TrialWitnesses` bundle from the public n=1 divisor
    shape and delegates to the trial-bundled callable wrapper. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_shape_trial_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
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
    (harith : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
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
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1QuotientOverestimate bltu_3 bltu_2 bltu_1 bltu_0
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
  exact evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_trial_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 harith

/-- Shape-specialized n=1 no-NOP DIV callable wrapper from raw mulsub plus
    final-remainder obligations. -/
theorem evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_shape_remainder_uni
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
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
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1RemainderLt bltu_3 bltu_2 bltu_1 bltu_0
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
  exact evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_trial_remainder_uni
    sp base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
    rfl rfl rfl rfl rfl rfl rfl rfl hbnzGet hb3z hb2z hb1z
    hshift_nz halign htrial hcarry2 hpath

/-- Unified-bound wrapper for
    `evm_div_n2_stack_spec_within_word_exact_x1_noNop`. -/
theorem evm_div_n2_stack_spec_within_word_exact_x1_noNop_uni
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hdivWord :=
    fullDivN2QuotientWord_eq_div_of_limbs_mulsub_overestimate
      bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hmulsub hge
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n2_stack_spec_within_word_exact_x1_noNop
      bltu_2 bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1nz
      hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for
    `evm_div_n2_stack_spec_within_word_noNop_callableOwnPost`. -/
theorem evm_div_n2_stack_spec_within_word_noNop_callableOwnPost_uni
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdivWord : fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n2_stack_spec_within_word_noNop_callableOwnPost
      bltu_2 bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1nz
      hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for the n=2 no-NOP DIV callable surface whose
    precondition keeps `x1` outside the scratch bundle. -/
theorem evm_div_n2_stack_spec_within_word_noNop_preNoX1_callableOwnPost_uni
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hdivWord : fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n2_stack_spec_within_word_noNop_preNoX1_callableOwnPost
      bltu_2 bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1nz
      hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for
    `evm_div_n3_stack_spec_within_word_exact_x1_noNop`. -/
theorem evm_div_n3_stack_spec_within_word_exact_x1_noNop_uni
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : isTrialN3_j1 bltu_1 a3 b1 b2)
    (hbltu_0 : isTrialN3_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b2).1).toNat % 64))
      ((b1 <<< (((clzResult b2).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b2 <<< (((clzResult b2).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b3 <<< (((clzResult b2).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64))))
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b2).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  have hdivWord :=
    fullDivN3QuotientWord_eq_div_of_limbs_mulsub_overestimate
      bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hmulsub hge
  exact
  cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n3_stack_spec_within_word_exact_x1_noNop bltu_1 bltu_0
      sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2nz
      hshift_nz halign hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for
    `evm_div_n3_stack_spec_within_word_noNop_callableOwnPost`. -/
theorem evm_div_n3_stack_spec_within_word_noNop_callableOwnPost_uni
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : isTrialN3_j1 bltu_1 a3 b1 b2)
    (hbltu_0 : isTrialN3_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b2).1).toNat % 64))
      ((b1 <<< (((clzResult b2).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b2 <<< (((clzResult b2).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b3 <<< (((clzResult b2).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64))))
    (hdivWord : fullDivN3QuotientWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b2).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n3_stack_spec_within_word_noNop_callableOwnPost
      bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2nz
      hshift_nz halign hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Unified-bound wrapper for the n=3 no-NOP DIV callable surface whose
    precondition keeps `x1` outside the scratch bundle. -/
theorem evm_div_n3_stack_spec_within_word_noNop_preNoX1_callableOwnPost_uni
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : isTrialN3_j1 bltu_1 a3 b1 b2)
    (hbltu_0 : isTrialN3_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b2).1).toNat % 64))
      ((b1 <<< (((clzResult b2).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b2 <<< (((clzResult b2).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
      ((b3 <<< (((clzResult b2).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64))))
    (hdivWord : fullDivN3QuotientWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult b2).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ (signExtend12 4095 : Word))) := by
  exact cpsTripleWithin_mono_nSteps (by decide)
    (evm_div_n3_stack_spec_within_word_noNop_preNoX1_callableOwnPost
      bltu_1 bltu_0 sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2nz
      hshift_nz halign hbltu_1 hbltu_0 hcarry2 hdivWord)

/-- Single named exact-`x1` DIV stack spec over `divCode_noNop`. -/
theorem evm_div_stack_spec_exact_x1_noNop (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (branch : DivStackSpecCase base a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        branch.x9 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostNoX1 sp a b ** (.x9 ↦ᵣ branch.returnX1)) := by
  cases branch with
  | bzero v1 v2 hbz =>
      exact evm_div_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni
        sp base a b v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz
  | n1Full bltu_3 bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1z hshift_nz halign
      hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge =>
      exact evm_div_n1_stack_spec_within_word_exact_x1_noNop_uni
        bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2z hb1z hshift_nz halign
        hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge
  | n2Full bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1nz hshift_nz halign
      hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge =>
      exact evm_div_n2_stack_spec_within_word_exact_x1_noNop_uni
        bltu_2 bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2z hb1nz hshift_nz halign
        hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge
  | n3Full bltu_1 bltu_0 hbnz hb3z hb2nz hshift_nz halign
      hbltu_1 hbltu_0 hcarry2 hmulsub hge =>
      exact evm_div_n3_stack_spec_within_word_exact_x1_noNop_uni
        bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2nz hshift_nz halign
        hbltu_1 hbltu_0 hcarry2 hmulsub hge

/-- Single named no-NOP DIV stack spec over the dispatcher branch certificate,
    weakened to the callable public post plus caller-owned `x1` and exact `x9`. -/
theorem evm_div_stack_spec_noNop_callableOwnPost (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (branch : DivStackSpecCase base a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPre sp a b
        branch.x9 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ branch.returnX9)) := by
  cases branch with
  | bzero v1 v2 hbz =>
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (divStackDispatchPostNoX1_weaken_callable_own_x1_frame_x9 sp a b v1)
        (evm_div_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni
          sp base a b v1 v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz)
  | n1Full bltu_3 bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1z hshift_nz halign
      hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge =>
      have hdivWord :=
        fullDivN1QuotientWord_eq_div_of_limbs_mulsub_overestimate
          bltu_3 bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
          hbnz hmulsub hge
      exact evm_div_n1_stack_spec_within_word_noNop_callableOwnPost_uni
        bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2z hb1z hshift_nz halign
        hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord
  | n2Full bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1nz hshift_nz halign
      hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge =>
      have hdivWord :=
        fullDivN2QuotientWord_eq_div_of_limbs_mulsub_overestimate
          bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
          hbnz hmulsub hge
      exact evm_div_n2_stack_spec_within_word_noNop_callableOwnPost_uni
        bltu_2 bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2z hb1nz hshift_nz halign
        hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord
  | n3Full bltu_1 bltu_0 hbnz hb3z hb2nz hshift_nz halign
      hbltu_1 hbltu_0 hcarry2 hmulsub hge =>
      have hdivWord :=
        fullDivN3QuotientWord_eq_div_of_limbs_mulsub_overestimate
          bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl hbnz hmulsub hge
      exact evm_div_n3_stack_spec_within_word_noNop_callableOwnPost_uni
        bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2nz hshift_nz halign
        hbltu_1 hbltu_0 hcarry2 hdivWord

/-- Single named no-NOP DIV stack spec over the dispatcher branch certificate
    from the callable-ready precondition shape. This keeps `x1` outside the
    scratch bundle on entry, and exposes the callable public post with
    caller-owned `x1` plus exact `x9`. -/
theorem evm_div_stack_spec_noNop_preNoX1_callableOwnPost
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (branch : DivStackSpecCase base a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        branch.x9 raVal branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ branch.returnX9)) := by
  cases branch with
  | bzero v1 v2 hbz =>
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (divStackDispatchPostCallable_exact_x1_weaken_own_x1_frame_x9
          sp a b raVal v1)
        (evm_div_bzero_stack_spec_within_dispatch_noNop_callable_uni
          sp base a b v1 raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz)
  | n1Full bltu_3 bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1z hshift_nz halign
      hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge =>
      have hdivWord :=
        fullDivN1QuotientWord_eq_div_of_limbs_mulsub_overestimate
          bltu_3 bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
          hbnz hmulsub hge
      exact evm_div_n1_stack_spec_within_word_noNop_preNoX1_callableOwnPost_uni
        bltu_3 bltu_2 bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2z hb1z hshift_nz halign
        hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord
  | n2Full bltu_2 bltu_1 bltu_0 hbnz hb3z hb2z hb1nz hshift_nz halign
      hbltu_2 hbltu_1 hbltu_0 hcarry2 hmulsub hge =>
      have hdivWord :=
        fullDivN2QuotientWord_eq_div_of_limbs_mulsub_overestimate
          bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
          hbnz hmulsub hge
      exact evm_div_n2_stack_spec_within_word_noNop_preNoX1_callableOwnPost_uni
        bltu_2 bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2z hb1nz hshift_nz halign
        hbltu_2 hbltu_1 hbltu_0 hcarry2 hdivWord
  | n3Full bltu_1 bltu_0 hbnz hb3z hb2nz hshift_nz halign
      hbltu_1 hbltu_0 hcarry2 hmulsub hge =>
      have hdivWord :=
        fullDivN3QuotientWord_eq_div_of_limbs_mulsub_overestimate
          bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl hbnz hmulsub hge
      exact evm_div_n3_stack_spec_within_word_noNop_preNoX1_callableOwnPost_uni
        bltu_1 bltu_0 sp base a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0 raVal
        rfl rfl rfl rfl rfl rfl rfl rfl
        hbnz hb3z hb2nz hshift_nz halign
        hbltu_1 hbltu_0 hcarry2 hdivWord

/-- Zero-divisor branch of the no-NOP DIV dispatcher from the callable-ready
    precondition shape, preserving exact caller-framed `x1` and `x9`. -/
theorem evm_div_stack_spec_bzero_noNop_preNoX1_callableExactPost
    (sp base : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  exact evm_div_bzero_stack_spec_within_dispatch_noNop_callable_uni
    sp base a b x9Val raVal v2 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz

/-- Zero-divisor branch of the no-NOP DIV dispatcher from the callable
    precondition shape, preserving exact caller-framed `x1` with no `x9`
    frame in either the precondition or postcondition. -/
theorem evm_div_stack_spec_bzero_noNop_preCallable_callableExactX1Post
    (sp base : Word) (a b : EvmWord)
    (raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  exact evm_div_bzero_stack_spec_within_dispatch_noNop_callable_x1_uni
    sp base a b raVal v2 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz

end EvmAsm.Evm64
