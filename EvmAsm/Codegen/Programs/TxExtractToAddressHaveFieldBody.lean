/-
  Extract HaveField body (idx 121+): MV t2; BEQ creation; LI/BNE len=20;
  creation path; copy leaves (compose residual).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressHaveField
import EvmAsm.Codegen.Programs.TxExtractToAddressEpilogue

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _)

abbrev AfterHaveMv : Word := E + 488
abbrev AfterHaveBeqzNt : Word := E + 492
abbrev CreationStart : Word := E + 536
abbrev AfterLi20 : Word := E + 496
abbrev AfterBne20Nt : Word := E + 500
abbrev AfterCreLi1 : Word := E + 540
abbrev AfterCreSd : Word := E + 544
abbrev AfterCreLi0 : Word := E + 548

private theorem add0 (w : Word) : w + (0 : Word) = w := by bv_omega

set_option maxRecDepth 8000 in
/-- `mv t2, a2` at HaveField. -/
theorem extractHaveMv (a2 t2Old : Word) :
    cpsTripleWithin 1 HaveField AfterHaveMv extractLinkedCode
      ((.x12 ↦ᵣ a2) ** (.x7 ↦ᵣ t2Old))
      ((.x12 ↦ᵣ a2) ** (.x7 ↦ᵣ a2)) := by
  have h := mv_spec_gen_within .x7 .x12 a2 t2Old HaveField (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E HaveField extractProg 121
        (.MV .x7 .x12) (by simp only [HaveField]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h
  rw [show (HaveField + 4 : Word) = AfterHaveMv from by
    simp only [HaveField, AfterHaveMv]; bv_omega] at he
  exact he

set_option maxRecDepth 8000 in
/-- `beqz t2, creation` not-taken when t2 ≠ 0. -/
theorem extractHaveBeqzNt (len : Word) (hne : len ≠ 0) :
    cpsTripleWithin 1 AfterHaveMv AfterHaveBeqzNt extractLinkedCode
      ((.x7 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x7 .x0 (48 : BitVec 13)
    len (0 : Word) AfterHaveMv
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterHaveMv extractProg 122
        (.BEQ .x7 .x0 (48 : BitVec 13)) (by simp only [AfterHaveMv]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hp).2 hne)
  rw [show (AfterHaveMv + 4 : Word) = AfterHaveBeqzNt from by
    simp only [AfterHaveMv, AfterHaveBeqzNt]; bv_omega] at hnt
  exact hnt

set_option maxRecDepth 8000 in
/-- `beqz t2, creation` taken when t2 = 0. -/
theorem extractHaveBeqzTaken :
    cpsTripleWithin 1 AfterHaveMv CreationStart extractLinkedCode
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x7 .x0 (48 : BitVec 13)
    (0 : Word) (0 : Word) AfterHaveMv
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterHaveMv extractProg 122
        (.BEQ .x7 .x0 (48 : BitVec 13)) (by simp only [AfterHaveMv]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have ht := cpsBranchWithin_takenStripPure2 hbrC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).1 hp).2)
  rw [show (AfterHaveMv + signExtend13 (48 : BitVec 13) : Word) = CreationStart from by
    simp only [AfterHaveMv, CreationStart, E]; decide] at ht
  exact ht

set_option maxRecDepth 8000 in
/-- `li t1, 20` after non-zero length. -/
theorem extractHaveLi20 (t1Old : Word) :
    cpsTripleWithin 1 AfterHaveBeqzNt AfterLi20 extractLinkedCode
      ((.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h := li_spec_gen_within .x6 t1Old (20 : Word) AfterHaveBeqzNt (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterHaveBeqzNt extractProg 123
        (.LI .x6 (20 : Word)) (by simp only [AfterHaveBeqzNt]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h
  rw [show (AfterHaveBeqzNt + 4 : Word) = AfterLi20 from by
    simp only [AfterHaveBeqzNt, AfterLi20]; bv_omega] at he
  exact cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) he

set_option maxRecDepth 8000 in
/-- `bne t2, t1, fail` not-taken when len = 20. -/
theorem extractHaveBne20Nt :
    cpsTripleWithin 1 AfterLi20 AfterBne20Nt extractLinkedCode
      ((.x7 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ (20 : Word)))
      ((.x7 ↦ᵣ (20 : Word)) ** (.x6 ↦ᵣ (20 : Word))) := by
  have hbr := bne_spec_gen_within .x7 .x6 (56 : BitVec 13)
    (20 : Word) (20 : Word) AfterLi20
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterLi20 extractProg 124
        (.BNE .x7 .x6 (56 : BitVec 13)) (by simp only [AfterLi20]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hp⟩ := hQt
    exact ((sepConj_pure_right _).1 hp).2 rfl)
  rw [show (AfterLi20 + 4 : Word) = AfterBne20Nt from by
    simp only [AfterLi20, AfterBne20Nt]; bv_omega] at hnt
  exact hnt

set_option maxRecDepth 8000 in
/-- Creation: `li t0, 1`. -/
theorem extractCreLi1 (t0Old : Word) :
    cpsTripleWithin 1 CreationStart AfterCreLi1 extractLinkedCode
      ((.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h := li_spec_gen_within .x5 t0Old (1 : Word) CreationStart (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E CreationStart extractProg 134
        (.LI .x5 (1 : Word)) (by simp only [CreationStart]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h
  rw [show (CreationStart + 4 : Word) = AfterCreLi1 from by
    simp only [CreationStart, AfterCreLi1]; bv_omega] at he
  exact cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) he

set_option maxRecDepth 8000 in
/-- Creation: `sd t0, 0(s3)` is_creation = 1. -/
theorem extractCreSd (isCreationPtr : Word) :
    cpsTripleWithin 1 AfterCreLi1 AfterCreSd extractLinkedCode
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** memOwn isCreationPtr)
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) **
        (isCreationPtr ↦ₘ (1 : Word))) := by
  have h := sd_spec_gen_own_within .x19 .x5 isCreationPtr (1 : Word)
    (0 : BitVec 12) AfterCreLi1
  simp only [signExtend12_0, add0] at h
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterCreLi1 extractProg 135
        (.SD .x19 .x5 (0 : BitVec 12)) (by simp only [AfterCreLi1]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h
  rw [show (AfterCreLi1 + 4 : Word) = AfterCreSd from by
    simp only [AfterCreLi1, AfterCreSd]; bv_omega] at he
  exact he

set_option maxRecDepth 8000 in
/-- Creation: `li a0, 0`. -/
theorem extractCreLi0 (a0Old : Word) :
    cpsTripleWithin 1 AfterCreSd AfterCreLi0 extractLinkedCode
      ((.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h := li_spec_gen_within .x10 a0Old (0 : Word) AfterCreSd (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterCreSd extractProg 136
        (.LI .x10 (0 : Word)) (by simp only [AfterCreSd]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h
  rw [show (AfterCreSd + 4 : Word) = AfterCreLi0 from by
    simp only [AfterCreSd, AfterCreLi0]; bv_omega] at he
  exact cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) he

set_option maxRecDepth 8000 in
/-- Creation: `j .Ltea_ret` (JAL x0 8) → EpiRestore. -/
theorem extractCreJalRet :
    cpsTripleWithin 1 AfterCreLi0 EpiRestore extractLinkedCode
      empAssertion empAssertion := by
  have hj := jal_x0_spec_gen_within (8 : BitVec 21) AfterCreLi0
  have ht : AfterCreLi0 + signExtend21 (8 : BitVec 21) = EpiRestore := by
    simp only [AfterCreLi0, EpiRestore, E]
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
    bv_omega
  rw [ht] at hj
  exact cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterCreLi0 extractProg 137
        (.JAL .x0 (8 : BitVec 21)) (by simp only [AfterCreLi0]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hj

set_option maxRecDepth 8000 in
/-- Creation path body: li1; sd; li0; j ret → EpiRestore.
    Flat matching midpoints; right-nested `seq_same_cr`. -/
theorem extractHaveCreation
    (isCreationPtr t0Old a0Old : Word) :
    cpsTripleWithin (1 + (1 + (1 + 1))) CreationStart EpiRestore extractLinkedCode
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) := by
  have h0F : cpsTripleWithin 1 CreationStart AfterCreLi1 extractLinkedCode
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr) := by
    have h := extractCreLi1 t0Old
    have hF := cpsTripleWithin_frameR
      ((.x19 ↦ᵣ isCreationPtr) ** (.x10 ↦ᵣ a0Old) ** memOwn isCreationPtr) (by pcf) h
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have h1F : cpsTripleWithin 1 AfterCreLi1 AfterCreSd extractLinkedCode
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) := by
    have h := extractCreSd isCreationPtr
    have hF := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word))) (by pcf) h
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have h2F : cpsTripleWithin 1 AfterCreSd AfterCreLi0 extractLinkedCode
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word)))
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) := by
    have h := extractCreLi0 a0Old
    have hF := cpsTripleWithin_frameR
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) **
        (isCreationPtr ↦ₘ (1 : Word))) (by pcf) h
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have h3F : cpsTripleWithin 1 AfterCreLi0 EpiRestore extractLinkedCode
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word)))
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) := by
    have h := extractCreJalRet
    have hF := cpsTripleWithin_frameR
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => by
      simpa only [sepConj_emp_left'] using hp) (fun _ hq => by
      simpa only [sepConj_emp_left'] using hq) hF
  exact cpsTripleWithin_seq_same_cr h0F
    (cpsTripleWithin_seq_same_cr h1F
      (cpsTripleWithin_seq_same_cr h2F h3F))

set_option maxRecDepth 8000 in
/-- HaveField → creation → EpiRestore (len=0). -/
theorem extractHaveFieldCreation
    (isCreationPtr t2Old t0Old a0Old : Word) :
    cpsTripleWithin (1 + (1 + (1 + (1 + (1 + 1))))) HaveField EpiRestore
      extractLinkedCode
      ((.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ t2Old) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      ((.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) := by
  have hmF : cpsTripleWithin 1 HaveField AfterHaveMv extractLinkedCode
      ((.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ t2Old) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      ((.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr) := by
    have h := extractHaveMv (0 : Word) t2Old
    have hF := cpsTripleWithin_frameR
      ((.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr) (by pcf) h
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have hbF : cpsTripleWithin 1 AfterHaveMv CreationStart extractLinkedCode
      ((.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      ((.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr) := by
    have h := extractHaveBeqzTaken
    have hF := cpsTripleWithin_frameR
      ((.x12 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) **
        (.x10 ↦ᵣ a0Old) ** memOwn isCreationPtr) (by pcf) h
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have hcF : cpsTripleWithin (1 + (1 + (1 + 1))) CreationStart EpiRestore
      extractLinkedCode
      ((.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      ((.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ isCreationPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (isCreationPtr ↦ₘ (1 : Word))) := by
    have h := extractHaveCreation isCreationPtr t0Old a0Old
    have hF := cpsTripleWithin_frameR
      ((.x12 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word))) (by pcf) h
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  exact cpsTripleWithin_seq_same_cr hmF
    (cpsTripleWithin_seq_same_cr hbF hcF)

set_option maxRecDepth 8000 in
/-- Copy path: `ld t0, 0(t6)`. -/
theorem extractCopyLd0 (contentPtr t0Old w0 : Word) :
    cpsTripleWithin 1 AfterBne20Nt (E + 504) extractLinkedCode
      ((.x31 ↦ᵣ contentPtr) ** (.x5 ↦ᵣ t0Old) ** (contentPtr ↦ₘ w0))
      ((.x31 ↦ᵣ contentPtr) ** (.x5 ↦ᵣ w0) ** (contentPtr ↦ₘ w0)) := by
  have h := ld_spec_gen_within .x5 .x31 contentPtr t0Old w0 (0 : BitVec 12)
    AfterBne20Nt (by decide)
  simp only [signExtend12_0, add0] at h
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterBne20Nt extractProg 125
        (.LD .x5 .x31 (0 : BitVec 12)) (by simp only [AfterBne20Nt]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h
  exact he

set_option maxRecDepth 8000 in
/-- Copy path: `sd t0, 0(s2)`. -/
theorem extractCopySd0 (toBuf w0 : Word) :
    cpsTripleWithin 1 (E + 504) (E + 508) extractLinkedCode
      ((.x18 ↦ᵣ toBuf) ** (.x5 ↦ᵣ w0) ** memOwn toBuf)
      ((.x18 ↦ᵣ toBuf) ** (.x5 ↦ᵣ w0) ** (toBuf ↦ₘ w0)) := by
  have h := sd_spec_gen_own_within .x18 .x5 toBuf w0 (0 : BitVec 12) (E + 504)
  simp only [signExtend12_0, add0] at h
  exact cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 504) extractProg 126
        (.SD .x18 .x5 (0 : BitVec 12)) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h

set_option maxRecDepth 8000 in
/-- Copy path: `ld t0, 8(t6)`. -/
theorem extractCopyLd8 (contentPtr w0 w1 : Word) :
    cpsTripleWithin 1 (E + 508) (E + 512) extractLinkedCode
      ((.x31 ↦ᵣ contentPtr) ** (.x5 ↦ᵣ w0) ** ((contentPtr + 8) ↦ₘ w1))
      ((.x31 ↦ᵣ contentPtr) ** (.x5 ↦ᵣ w1) ** ((contentPtr + 8) ↦ₘ w1)) := by
  have h := ld_spec_gen_within .x5 .x31 contentPtr w0 w1 (8 : BitVec 12)
    (E + 508) (by decide)
  simp only [signExtend12_8] at h
  exact cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 508) extractProg 127
        (.LD .x5 .x31 (8 : BitVec 12)) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h

set_option maxRecDepth 8000 in
/-- Copy path: `sd t0, 8(s2)`. -/
theorem extractCopySd8 (toBuf w1 : Word) :
    cpsTripleWithin 1 (E + 512) (E + 516) extractLinkedCode
      ((.x18 ↦ᵣ toBuf) ** (.x5 ↦ᵣ w1) ** memOwn (toBuf + 8))
      ((.x18 ↦ᵣ toBuf) ** (.x5 ↦ᵣ w1) ** ((toBuf + 8) ↦ₘ w1)) := by
  have h := sd_spec_gen_own_within .x18 .x5 toBuf w1 (8 : BitVec 12) (E + 512)
  simp only [signExtend12_8] at h
  exact cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 512) extractProg 128
        (.SD .x18 .x5 (8 : BitVec 12)) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h

set_option maxRecDepth 8000 in
/-- Copy path: `sd zero, 0(s3)` is_creation = 0. -/
theorem extractCopySdIsCre0 (isCreationPtr : Word) :
    cpsTripleWithin 1 (E + 524) (E + 528) extractLinkedCode
      ((.x19 ↦ᵣ isCreationPtr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn isCreationPtr)
      ((.x19 ↦ᵣ isCreationPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        (isCreationPtr ↦ₘ (0 : Word))) := by
  have h := sd_spec_gen_own_within .x19 .x0 isCreationPtr (0 : Word)
    (0 : BitVec 12) (E + 524)
  simp only [signExtend12_0, add0] at h
  exact cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 524) extractProg 131
        (.SD .x19 .x0 (0 : BitVec 12)) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h

set_option maxRecDepth 8000 in
/-- Copy path: `li a0, 0`. -/
theorem extractCopyLiA0 (a0Old : Word) :
    cpsTripleWithin 1 (E + 528) (E + 532) extractLinkedCode
      ((.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h := li_spec_gen_within .x10 a0Old (0 : Word) (E + 528) (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 528) extractProg 132
        (.LI .x10 (0 : Word)) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h
  exact cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) he

set_option maxRecDepth 8000 in
/-- Copy path: `j .Ltea_ret` (JAL x0 24) → EpiRestore. -/
theorem extractCopyJalRet :
    cpsTripleWithin 1 (E + 532) EpiRestore extractLinkedCode
      empAssertion empAssertion := by
  have hj := jal_x0_spec_gen_within (24 : BitVec 21) (E + 532)
  have ht : (E + 532 : Word) + signExtend21 (24 : BitVec 21) = EpiRestore := by
    simp only [EpiRestore, E]
    rw [show signExtend21 (24 : BitVec 21) = (24 : Word) from by decide]
    bv_omega
  rw [ht] at hj
  exact cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 532) extractProg 133
        (.JAL .x0 (24 : BitVec 21)) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hj

#print axioms extractHaveMv
#print axioms extractHaveBeqzNt
#print axioms extractHaveBeqzTaken
#print axioms extractHaveLi20
#print axioms extractHaveBne20Nt
#print axioms extractHaveCreation
#print axioms extractHaveFieldCreation
#print axioms extractCopyLd0
#print axioms extractCopySd0
#print axioms extractCopyJalRet

end EvmAsm.Codegen.TxExtractToAddressSpec
