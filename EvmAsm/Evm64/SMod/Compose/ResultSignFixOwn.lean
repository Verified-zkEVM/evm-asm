/-
  EvmAsm.Evm64.SMod.Compose.ResultSignFixOwn

  SMOD-local wrappers for the shared result-sign-fix block. The SMOD wrapper
  preserves the dividend/result sign in x13 across the MOD callable, so these
  assertions intentionally differ from the SDIV x8-shaped result-sign-fix
  assertions.
-/

import EvmAsm.Evm64.SDiv.LimbSpec
import EvmAsm.Evm64.SMod.Compose.BaseCode
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64.Tactics

@[irreducible]
def smodResultSignFixPre (sp sign maskOld valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x13 ↦ᵣ sign) **
  (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
  ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
  ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
  ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
  ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)

theorem smodResultSignFixPre_unfold
    {sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    smodResultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x13 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
       ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
       ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
       ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) := by
  delta smodResultSignFixPre
  rfl

@[irreducible]
def smodResultSignFixPost (sp sign limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x13 ↦ᵣ sign) **
  (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
  ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
  ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
  ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
  ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ sum3)

theorem smodResultSignFixPost_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    smodResultSignFixPost sp sign limb0 limb1 limb2 limb3 =
      (let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (limb3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x13 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
       ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
       ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
       ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ sum3)) := by
  delta smodResultSignFixPost
  rfl

theorem smodResultSignFixPost_pcFree
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3).pcFree := by
  rw [smodResultSignFixPost_unfold]
  dsimp only
  pcFree

instance pcFreeInst_smodResultSignFixPost
    (sp sign limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3) :=
  ⟨smodResultSignFixPost_pcFree⟩

@[irreducible]
def smodResultSignFixPreOwnX10 (sp sign valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  (((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x13 ↦ᵣ sign)) **
    (.x7 ↦ᵣ valueOld)) ** (.x11 ↦ᵣ carryOld)) **
    ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
    ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
    ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
    ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) **
    EvmAsm.Rv64.regOwn .x10

theorem smodResultSignFixPreOwnX10_unfold
    {sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    smodResultSignFixPreOwnX10 sp sign valueOld carryOld
        limb0 limb1 limb2 limb3 =
      ((((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x13 ↦ᵣ sign)) **
        (.x7 ↦ᵣ valueOld)) ** (.x11 ↦ᵣ carryOld)) **
        ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
        ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
        ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
        ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) **
        EvmAsm.Rv64.regOwn .x10) := by
  delta smodResultSignFixPreOwnX10
  rfl

@[irreducible]
def smodResultSignFixPreOwnX10X7 (sp sign carryOld
    limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  (((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x13 ↦ᵣ sign)) **
    (.x11 ↦ᵣ carryOld)) **
    ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
    ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
    ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
    ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) **
    EvmAsm.Rv64.regOwn .x10) ** EvmAsm.Rv64.regOwn .x7

theorem smodResultSignFixPreOwnX10X7_unfold
    {sp sign carryOld limb0 limb1 limb2 limb3 : Word} :
    smodResultSignFixPreOwnX10X7 sp sign carryOld limb0 limb1 limb2 limb3 =
      ((((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x13 ↦ᵣ sign)) **
        (.x11 ↦ᵣ carryOld)) **
        ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
        ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
        ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
        ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) **
        EvmAsm.Rv64.regOwn .x10) ** EvmAsm.Rv64.regOwn .x7) := by
  delta smodResultSignFixPreOwnX10X7
  rfl

@[irreducible]
def smodResultSignFixPreOwnScratch
    (sp sign limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  (((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x13 ↦ᵣ sign)) **
    ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
    ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
    ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
    ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) **
    EvmAsm.Rv64.regOwn .x10) ** EvmAsm.Rv64.regOwn .x7) ** EvmAsm.Rv64.regOwn .x11

theorem smodResultSignFixPreOwnScratch_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    smodResultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3 =
      ((((((((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp)) ** (.x13 ↦ᵣ sign)) **
        ((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ limb0)) **
        ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ limb1)) **
        ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ limb2)) **
        ((sp + EvmAsm.Rv64.signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) **
        EvmAsm.Rv64.regOwn .x10) ** EvmAsm.Rv64.regOwn .x7) **
        EvmAsm.Rv64.regOwn .x11) := by
  delta smodResultSignFixPreOwnScratch
  rfl

theorem smodResultSignFixPreOwnScratch_pcFree
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    (smodResultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3).pcFree := by
  rw [smodResultSignFixPreOwnScratch_unfold]
  pcFree

instance pcFreeInst_smodResultSignFixPreOwnScratch
    (sp sign limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (smodResultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3) :=
  ⟨smodResultSignFixPreOwnScratch_pcFree⟩

theorem resultSignFix_spec_in_smodCode
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (smodCode base)
      (smodResultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [smodResultSignFixPre_unfold, smodResultSignFixPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x13 .x10 .x7 .x11 0 8 16 24
          (base + resultSignFixOff)) a = some i →
        (smodCode base) a = some i := by
    intro a i h
    exact smodCode_resultSignFix_sub (base := base) a i
      (by simpa [resultSignFixCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x13 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + resultSignFixOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono hSpec

theorem resultSignFix_spec_in_smodCodeV4
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (smodCodeV4 base)
      (smodResultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [smodResultSignFixPre_unfold, smodResultSignFixPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x13 .x10 .x7 .x11 0 8 16 24
          (base + resultSignFixOff)) a = some i →
        (smodCodeV4 base) a = some i := by
    intro a i h
    exact smodCodeV4_resultSignFix_sub (base := base) a i
      (by simpa [resultSignFixCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x13 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + resultSignFixOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono hSpec

theorem resultSignFix_regOwn_x10_spec_in_smodCodeV4
    (sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (smodCodeV4 base)
      (smodResultSignFixPreOwnX10 sp sign valueOld carryOld
        limb0 limb1 limb2 limb3)
      (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [smodResultSignFixPreOwnX10_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro maskOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [smodResultSignFixPre_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_spec_in_smodCodeV4 sp sign maskOld valueOld carryOld
      limb0 limb1 limb2 limb3 base)

theorem resultSignFix_regOwn_x10_x7_spec_in_smodCodeV4
    (sp sign carryOld limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (smodCodeV4 base)
      (smodResultSignFixPreOwnX10X7 sp sign carryOld limb0 limb1 limb2 limb3)
      (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [smodResultSignFixPreOwnX10X7_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro valueOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [smodResultSignFixPreOwnX10_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_regOwn_x10_spec_in_smodCodeV4 sp sign valueOld carryOld
      limb0 limb1 limb2 limb3 base)

theorem resultSignFix_regOwn_scratch_spec_in_smodCodeV4
    (sp sign limb0 limb1 limb2 limb3 : Word) (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (smodCodeV4 base)
      (smodResultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3)
      (smodResultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [smodResultSignFixPreOwnScratch_unfold]
  apply EvmAsm.Rv64.cpsTripleWithin_of_forall_regIs_to_regOwn
  intro carryOld
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      rw [smodResultSignFixPreOwnX10X7_unfold]
      xperm_hyp hp)
    (fun _ hq => hq)
    (resultSignFix_regOwn_x10_x7_spec_in_smodCodeV4 sp sign carryOld
      limb0 limb1 limb2 limb3 base)

end EvmAsm.Evm64.SMod.Compose
