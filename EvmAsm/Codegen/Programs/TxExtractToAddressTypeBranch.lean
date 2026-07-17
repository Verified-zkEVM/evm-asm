/-
  Extract body: type → field-index branch after save cursor (E+160).
  type 0 → legacy; type 1 → t1; else type 2/3/4.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNext

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen

abbrev AfterLi0 : Word := E + 164
abbrev LegacyStart : Word := E + 300
abbrev AfterBeqLegacyNt : Word := E + 168
abbrev AfterLi1 : Word := E + 172
abbrev T1Start : Word := E + 384
abbrev Type234Start : Word := E + 176

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

set_option maxRecDepth 8000 in
theorem extractTypeBrLi0 (t0Old : Word) :
    cpsTripleWithin 1 AfterSaveCursor AfterLi0 extractLinkedCode
      ((.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h := li_spec_gen_within .x5 t0Old (0 : Word) AfterSaveCursor (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterSaveCursor extractProg 40
        (.LI .x5 (0 : Word)) (by simp only [AfterSaveCursor]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h
  rw [show (AfterSaveCursor + 4 : Word) = AfterLi0 from by
    simp only [AfterSaveCursor, AfterLi0]; bv_omega] at he
  exact cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) he

set_option maxRecDepth 8000 in
theorem extractTypeBrLegacyTaken :
    cpsTripleWithin 1 AfterLi0 LegacyStart extractLinkedCode
      ((.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x20 .x5 (136 : BitVec 13)
    (0 : Word) (0 : Word) AfterLi0
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterLi0 extractProg 41
        (.BEQ .x20 .x5 (136 : BitVec 13)) (by simp only [AfterLi0]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have ht := cpsBranchWithin_takenStripPure2 hbrC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  rw [show (AfterLi0 + signExtend13 (136 : BitVec 13) : Word) = LegacyStart from by
    simp only [AfterLi0, LegacyStart, E]; decide] at ht
  exact ht

set_option maxRecDepth 8000 in
theorem extractTypeBrLegacyNt (typeW : Word) (hne : typeW ≠ 0) :
    cpsTripleWithin 1 AfterLi0 AfterBeqLegacyNt extractLinkedCode
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x20 .x5 (136 : BitVec 13)
    typeW (0 : Word) AfterLi0
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterLi0 extractProg 41
        (.BEQ .x20 .x5 (136 : BitVec 13)) (by simp only [AfterLi0]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hrest).2 hne)
  rw [show (AfterLi0 + 4 : Word) = AfterBeqLegacyNt from by
    simp only [AfterLi0, AfterBeqLegacyNt]; bv_omega] at hnt
  exact hnt

set_option maxRecDepth 8000 in
theorem extractTypeBrLi1 (t0Old : Word) :
    cpsTripleWithin 1 AfterBeqLegacyNt AfterLi1 extractLinkedCode
      ((.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h := li_spec_gen_within .x5 t0Old (1 : Word) AfterBeqLegacyNt (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterBeqLegacyNt extractProg 42
        (.LI .x5 (1 : Word)) (by simp only [AfterBeqLegacyNt]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h
  rw [show (AfterBeqLegacyNt + 4 : Word) = AfterLi1 from by
    simp only [AfterBeqLegacyNt, AfterLi1]; bv_omega] at he
  exact cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) he

set_option maxRecDepth 8000 in
theorem extractTypeBrT1Taken :
    cpsTripleWithin 1 AfterLi1 T1Start extractLinkedCode
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)))
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word))) := by
  have hbr := beq_spec_gen_within .x20 .x5 (212 : BitVec 13)
    (1 : Word) (1 : Word) AfterLi1
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterLi1 extractProg 43
        (.BEQ .x20 .x5 (212 : BitVec 13)) (by simp only [AfterLi1]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have ht := cpsBranchWithin_takenStripPure2 hbrC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  rw [show (AfterLi1 + signExtend13 (212 : BitVec 13) : Word) = T1Start from by
    simp only [AfterLi1, T1Start, E]; decide] at ht
  exact ht

set_option maxRecDepth 8000 in
theorem extractTypeBrT1Nt (typeW : Word) (hne : typeW ≠ 1) :
    cpsTripleWithin 1 AfterLi1 Type234Start extractLinkedCode
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)))
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word))) := by
  have hbr := beq_spec_gen_within .x20 .x5 (212 : BitVec 13)
    typeW (1 : Word) AfterLi1
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterLi1 extractProg 43
        (.BEQ .x20 .x5 (212 : BitVec 13)) (by simp only [AfterLi1]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hrest).2 hne)
  rw [show (AfterLi1 + 4 : Word) = Type234Start from by
    simp only [AfterLi1, Type234Start]; bv_omega] at hnt
  exact hnt

set_option maxRecDepth 8000 in
theorem extractTypeBranchLegacy (t0Old : Word) :
    cpsTripleWithin (1 + 1) AfterSaveCursor LegacyStart extractLinkedCode
      ((.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hli :=
    cpsTripleWithin_frameR (.x20 ↦ᵣ (0 : Word)) (by pcf) (extractTypeBrLi0 t0Old)
  have hb :=
    cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) extractTypeBrLegacyTaken
  have hli' : cpsTripleWithin 1 AfterSaveCursor AfterLi0 extractLinkedCode
      ((.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hli
  have hb' : cpsTripleWithin 1 AfterLi0 LegacyStart extractLinkedCode
      ((.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hb
  exact cpsTripleWithin_seq_same_cr hli' hb'

set_option maxRecDepth 8000 in
theorem extractTypeBranchT1 (t0Old : Word) :
    cpsTripleWithin (1 + (1 + (1 + 1))) AfterSaveCursor T1Start extractLinkedCode
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have s0 : cpsTripleWithin 1 AfterSaveCursor AfterLi0 extractLinkedCode
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (.x20 ↦ᵣ (1 : Word)) (by pcf) (extractTypeBrLi0 t0Old))
  have s1 : cpsTripleWithin 1 AfterLi0 AfterBeqLegacyNt extractLinkedCode
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf)
        (extractTypeBrLegacyNt (1 : Word) (by decide)))
  have s2 : cpsTripleWithin 1 AfterBeqLegacyNt AfterLi1 extractLinkedCode
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (.x20 ↦ᵣ (1 : Word)) (by pcf) (extractTypeBrLi1 (0 : Word)))
  have s3 : cpsTripleWithin 1 AfterLi1 T1Start extractLinkedCode
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) extractTypeBrT1Taken)
  exact cpsTripleWithin_seq_same_cr s0
    (cpsTripleWithin_seq_same_cr s1 (cpsTripleWithin_seq_same_cr s2 s3))

set_option maxRecDepth 8000 in
theorem extractTypeBranchType234 (typeW t0Old : Word)
    (hne0 : typeW ≠ 0) (hne1 : typeW ≠ 1) :
    cpsTripleWithin (1 + (1 + (1 + 1))) AfterSaveCursor Type234Start extractLinkedCode
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have s0 : cpsTripleWithin 1 AfterSaveCursor AfterLi0 extractLinkedCode
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ t0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (.x20 ↦ᵣ typeW) (by pcf) (extractTypeBrLi0 t0Old))
  have s1 : cpsTripleWithin 1 AfterLi0 AfterBeqLegacyNt extractLinkedCode
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf)
        (extractTypeBrLegacyNt typeW hne0))
  have s2 : cpsTripleWithin 1 AfterBeqLegacyNt AfterLi1 extractLinkedCode
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (.x20 ↦ᵣ typeW) (by pcf) (extractTypeBrLi1 (0 : Word)))
  have s3 : cpsTripleWithin 1 AfterLi1 Type234Start extractLinkedCode
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x20 ↦ᵣ typeW) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf)
        (extractTypeBrT1Nt typeW hne1))
  exact cpsTripleWithin_seq_same_cr s0
    (cpsTripleWithin_seq_same_cr s1 (cpsTripleWithin_seq_same_cr s2 s3))

#print axioms extractTypeBranchLegacy
#print axioms extractTypeBranchT1
#print axioms extractTypeBranchType234

end EvmAsm.Codegen.TxExtractToAddressSpec
