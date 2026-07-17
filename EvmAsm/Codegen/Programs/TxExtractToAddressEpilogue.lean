/-
  Frame restore epilogue for `tx_extract_to_address` (instr 139-149).

  loadSeq ra/s0–s7; ADDI sp,+80; JALR ret.
  Shared by success (a0=0) and fail (a0=1/2) paths.
-/

import EvmAsm.Codegen.Programs.TxExtractToAddressPrologue
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _)

/-- First LD of epilogue (instr index 139). -/
abbrev EpiRestore : Word := E + 556
abbrev EpiAddi : Word := E + 592
abbrev EpiJalr : Word := E + 596

theorem extractFrame_hne : ∀ p ∈ extractFrame, p.1 ≠ .x0 := by decide

set_option maxRecDepth 8000 in
/-- loadSeq + ADDI sp + JALR (instr 139-149). Exit at s.ra when ra is even. -/
theorem extractEpilogueRestore (sp0 spC : Word) (s cur : ExtractSaved)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 11 EpiRestore s.ra extractCode
      ((.x2 ↦ᵣ spC) ** regsAt extractFrame (extractSavedVals cur) **
        frameSlotsSaved extractFrame spC (extractSavedVals s))
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        frameSlotsSaved extractFrame spC (extractSavedVals s)) := by
  have hs0 := loadSeq_spec extractFrame spC (extractSavedVals s) (extractSavedVals cur)
    (E + 556) (by decide) extractFrame_hne
  have h_loadMono : ∀ a i,
      CodeReq.ofProg (E + 556) (loadProg extractFrame) a = some i →
        extractCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub E (E + 556) extractProg (loadProg extractFrame) 139
      (by bv_omega) (by rfl)
      (by rw [extract_length]; simp [extractFrame, loadProg])
      (by rw [extract_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_loadMono hs0
  rw [show E + 556 + BitVec.ofNat 64 (4 * extractFrame.length) = E + 592 from by
    simp [extractFrame]; bv_omega] at hs
  have ha0 := addi_spec_gen_same_within .x2 spC (80 : BitVec 12) (E + 592) (by decide)
  have hsp : spC + signExtend12 (80 : BitVec 12) = sp0 := by
    rw [hspC]
    rw [show signExtend12 (-80 : BitVec 12) = (-80 : Word) from by decide,
      show signExtend12 (80 : BitVec 12) = (80 : Word) from by decide]
    bv_omega
  rw [hsp] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (E + 592) extractProg 148
      (.ADDI .x2 .x2 (80 : BitVec 12))
      (by bv_omega)
      (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt extractFrame (extractSavedVals s) **
      frameSlotsSaved extractFrame spC (extractSavedVals s))
    (by pcf) ha
  have hload_addi := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hs haF
  have hpc : (E + 592 : Word) + 4 = E + 596 := by bv_omega
  rw [hpc] at hload_addi
  have hjalr0 := EvmAsm.Evm64.ret_spec_within' (E + 596) s.ra
  rw [hret] at hjalr0
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (E + 596) extractProg 149
      (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega)
      (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) hjalr0
  have hjalrF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
      (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      (Reg.x23 ↦ᵣ s.s7) **
      frameSlotsSaved extractFrame spC (extractSavedVals s))
    (by pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_extractFrame] at hp
    xperm_hyp hp) hload_addi hjalrF
  have hn : extractFrame.length + 1 + 1 = 11 := by simp [extractFrame]
  rw [hn] at hall
  change cpsTripleWithin 11 EpiRestore s.ra extractCode _ _
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Success epilogue: frame a0 through restore. -/
theorem extractEpilogueSuccess (sp0 spC : Word) (s cur : ExtractSaved) (a0v : Word)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 11 EpiRestore s.ra extractCode
      ((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ spC) **
        regsAt extractFrame (extractSavedVals cur) **
        frameSlotsSaved extractFrame spC (extractSavedVals s))
      ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (Reg.x23 ↦ᵣ s.s7) **
        frameSlotsSaved extractFrame spC (extractSavedVals s)) := by
  have h := extractEpilogueRestore sp0 spC s cur hspC hret
  have hF := cpsTripleWithin_frameR (.x10 ↦ᵣ a0v) (by exact pcFree_regIs) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms extractEpilogueRestore
#print axioms extractEpilogueSuccess

end EvmAsm.Codegen.TxExtractToAddressSpec
