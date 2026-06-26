/-
  EvmAsm.Evm64.MulMod.ProductLayoutSpec

  Public product-layout spec for MULMOD.
-/

import EvmAsm.Evm64.MulMod.ProductLayoutCall15
import EvmAsm.Evm64.MulMod.ProductLayoutHighTargets

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Scratch registers clobbered by `evm_mulmod_product_layout`.

    The public layout spec keeps `x12` precise through
    `evmMulModProductLayoutPost`; the remaining caller-save registers are
    released as owned scratch. -/
@[irreducible]
def evmMulModProductLayoutScratchPost : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x8 ** regOwn .x9 **
  regOwn .x10 ** regOwn .x11 ** regOwn .x13 ** regOwn .x14

/-- Exact scratch-register values after the final product-layout call. -/
@[irreducible]
def evmMulModProductLayoutExactScratchPost (a b : EvmWord) : Assertion :=
  (.x5 ↦ᵣ a.getLimbN 3) **
  (.x6 ↦ᵣ b.getLimbN 3) **
  (.x7 ↦ᵣ mulModAddPartialLoProduct (a.getLimbN 3) (b.getLimbN 3)) **
  (.x8 ↦ᵣ mulModAddPartialHiProduct (a.getLimbN 3) (b.getLimbN 3)) **
  (.x9 ↦ᵣ mulModProductLayoutCall14P152 a b) **
  (.x10 ↦ᵣ mulModAddPartialHiCarry (mulModProductLayoutCall14P152 a b)
    (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3)) **
  (.x11 ↦ᵣ mulModAddPartialHiValue (mulModProductLayoutCall14P152 a b)
    (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3)) **
  (.x13 ↦ᵣ mulModAddPartialHiBaseCarry (mulModProductLayoutCall14P152 a b)
    (a.getLimbN 3) (b.getLimbN 3)) **
  (.x14 ↦ᵣ mulModAddPartialHiCarryFromLo (mulModProductLayoutCall14P152 a b)
    (mulModProductLayoutCall14P144 a b) (a.getLimbN 3) (b.getLimbN 3))

/-- Exact scratch values imply abstract scratch ownership. -/
theorem evmMulModProductLayoutExactScratchPost_to_scratchPost (a b : EvmWord) :
    ∀ h, evmMulModProductLayoutExactScratchPost a b h →
      evmMulModProductLayoutScratchPost h := by
  intro h hp
  unfold evmMulModProductLayoutExactScratchPost at hp
  unfold evmMulModProductLayoutScratchPost
  exact sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x8)
          (sepConj_mono (regIs_implies_regOwn .x9)
            (sepConj_mono (regIs_implies_regOwn .x10)
              (sepConj_mono (regIs_implies_regOwn .x11)
                (sepConj_mono (regIs_implies_regOwn .x13)
                  (regIs_implies_regOwn .x14)))))))) h hp

/-- Product-layout spec with exact scratch-register values. -/
theorem evm_mulmod_product_layout_exact_scratch_spec_within
    (sp base : Word) (a b n : EvmWord)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 440
      base (base + 1760) (evm_mulmod_product_layout_code base)
      (evmMulModProductLayoutPre sp a b n p0 p1 p2 p3 p4 p5 p6 p7 **
       ((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) **
        (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
        (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old)))
      (evmMulModProductLayoutPost sp a b n ** evmMulModProductLayoutExactScratchPost a b) := by
  have hCall15 := evm_mulmod_product_layout_zero_call15_spec_within sp base a b n
    p0 p1 p2 p3 p4 p5 p6 p7
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old
  refine cpsTripleWithin_weaken
    (P := evmMulModProductLayoutPre sp a b n p0 p1 p2 p3 p4 p5 p6 p7 **
      ((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) **
       (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
       (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old)))
    (Q := evmMulModProductLayoutZeroCall15Post sp a b n)
    (P' := evmMulModProductLayoutPre sp a b n p0 p1 p2 p3 p4 p5 p6 p7 **
      ((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) **
       (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
       (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old)))
    (Q' := evmMulModProductLayoutPost sp a b n ** evmMulModProductLayoutExactScratchPost a b)
    (fun _ hp => hp)
    (fun _ hq => ?_)
    ?_
  · unfold evmMulModProductLayoutZeroCall15Post evmMulModProductLayoutCall15Frame at hq
    rw [evmMulModProductLayoutPost_unfold]
    unfold evmMulModProductLayoutExactScratchPost
    simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
      signExtend12_32, signExtend12_40] at hq ⊢
    simp only [
      show signExtend12 (48 : BitVec 12) = (48 : Word) by decide,
      show signExtend12 (56 : BitVec 12) = (56 : Word) by decide,
      show signExtend12 (3936 : BitVec 12) = (18446744073709551456 : Word) by decide,
      show signExtend12 (3944 : BitVec 12) = (18446744073709551464 : Word) by decide,
      show signExtend12 (3952 : BitVec 12) = (18446744073709551472 : Word) by decide,
      show signExtend12 (3960 : BitVec 12) = (18446744073709551480 : Word) by decide,
      show signExtend12 (3968 : BitVec 12) = (18446744073709551488 : Word) by decide,
      show signExtend12 (3976 : BitVec 12) = (18446744073709551496 : Word) by decide,
      show signExtend12 (3984 : BitVec 12) = (18446744073709551504 : Word) by decide,
      show signExtend12 (3992 : BitVec 12) = (18446744073709551512 : Word) by decide] at hq ⊢
    rw [show sp + (0 : Word) = sp by bv_omega] at hq
    rw [mulModProductLayoutCall00P96_eq_mul_limb0,
      mulModProductLayoutCall02P104_eq_mul_limb1,
      mulModProductLayoutCall05P112_eq_mul_limb2,
      mulModProductLayoutCall09P120_eq_mul_limb3,
      mulModProductLayoutCall12P128_eq_mulHigh_getLimbN_zero,
      mulModProductLayoutCall14P136_eq_mulHigh_getLimbN_one] at hq
    rw [mulModProductLayoutCall15P144Value_eq_mulHigh_getLimbN_two] at hq
    rw [mulModProductLayoutCall15P152Value_eq_mulHigh_getLimbN_three] at hq ⊢
    simp only [sepConj_assoc'] at hq ⊢
    xperm_hyp hq
  · norm_num at hCall15
    simpa using hCall15

/-- Public product-layout spec: the product window contains the low limbs of
    `a * b` followed by the high limbs of the full 512-bit product. -/
theorem evm_mulmod_product_layout_spec_within
    (sp base : Word) (a b n : EvmWord)
    (p0 p1 p2 p3 p4 p5 p6 p7 : Word)
    (x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old : Word) :
    cpsTripleWithin 440
      base (base + 1760) (evm_mulmod_product_layout_code base)
      (evmMulModProductLayoutPre sp a b n p0 p1 p2 p3 p4 p5 p6 p7 **
       ((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) ** (.x8 ↦ᵣ x8Old) **
        (.x9 ↦ᵣ x9Old) ** (.x10 ↦ᵣ x10Old) ** (.x11 ↦ᵣ x11Old) **
        (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old)))
      (evmMulModProductLayoutPost sp a b n ** evmMulModProductLayoutScratchPost) := by
  refine cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hq => sepConj_mono_right
      (evmMulModProductLayoutExactScratchPost_to_scratchPost a b) _ hq)
    ?_
  exact evm_mulmod_product_layout_exact_scratch_spec_within sp base a b n
    p0 p1 p2 p3 p4 p5 p6 p7
    x5Old x6Old x7Old x8Old x9Old x10Old x11Old x13Old x14Old

end EvmAsm.Evm64
