/-
  Frame restore epilogue for `tx_intrinsic_state_gas` (instr 44-53).

  loadSeq ra/s0–s6; ADDI sp,+64; JALR ret.
  Shared by success (a0=0) and fail (a0=1/2) paths.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasPrologue
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

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

abbrev EpiRestore : Word := T + 176
abbrev EpiAddi : Word := T + 208
abbrev EpiJalr : Word := T + 212

theorem tisFrame_hne : ∀ p ∈ tisFrame, p.1 ≠ .x0 := by decide

set_option maxRecDepth 8000 in
/-- loadSeq + ADDI sp + JALR (instr 44-53). Exit at s.ra when ra is even. -/
theorem tisEpilogueRestore (sp0 spC : Word) (s cur : TisSaved)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 10 EpiRestore s.ra tisCode
      ((.x2 ↦ᵣ spC) ** regsAt tisFrame (tisSavedVals cur) **
        frameSlotsSaved tisFrame spC (tisSavedVals s))
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved tisFrame spC (tisSavedVals s)) := by
  have hs0 := loadSeq_spec tisFrame spC (tisSavedVals s) (tisSavedVals cur) (T + 176)
    (by decide) tisFrame_hne
  have h_loadMono : ∀ a i,
      CodeReq.ofProg (T + 176) (loadProg tisFrame) a = some i →
        tisCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub T (T + 176) tisProg (loadProg tisFrame) 44
      (by bv_omega) (by rfl)
      (by rw [tis_length]; simp [tisFrame, loadProg])
      (by rw [tis_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_loadMono hs0
  rw [show T + 176 + BitVec.ofNat 64 (4 * tisFrame.length) = T + 208 from by
    simp [tisFrame]; bv_omega] at hs
  have ha0 := addi_spec_gen_same_within .x2 spC (64 : BitVec 12) (T + 208) (by decide)
  have hsp : spC + signExtend12 (64 : BitVec 12) = sp0 := by
    rw [hspC]
    rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide,
      show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]
    bv_omega
  rw [hsp] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at T (T + 208) tisProg 52
      (.ADDI .x2 .x2 (64 : BitVec 12))
      (by bv_omega)
      (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt tisFrame (tisSavedVals s) ** frameSlotsSaved tisFrame spC (tisSavedVals s))
    (by pcf) ha
  have hload_addi := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hs haF
  have hpc : (T + 208 : Word) + 4 = T + 212 := by bv_omega
  rw [hpc] at hload_addi
  have hjalr0 := EvmAsm.Evm64.ret_spec_within' (T + 212) s.ra
  rw [hret] at hjalr0
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at T (T + 212) tisProg 53
      (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega)
      (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide)) hjalr0
  have hjalrF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
      (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      frameSlotsSaved tisFrame spC (tisSavedVals s))
    (by pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_tisFrame] at hp
    xperm_hyp hp) hload_addi hjalrF
  have hn : tisFrame.length + 1 + 1 = 10 := by simp [tisFrame]
  rw [hn] at hall
  change cpsTripleWithin 10 EpiRestore s.ra tisCode _ _
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Success epilogue: frame a0=0 through restore. -/
theorem tisEpilogueSuccess (sp0 spC : Word) (s cur : TisSaved) (a0v : Word)
    (hspC : spC = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 10 EpiRestore s.ra tisCode
      ((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ spC) **
        regsAt tisFrame (tisSavedVals cur) **
        frameSlotsSaved tisFrame spC (tisSavedVals s))
      ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        frameSlotsSaved tisFrame spC (tisSavedVals s)) := by
  have h := tisEpilogueRestore sp0 spC s cur hspC hret
  have hF := cpsTripleWithin_frameR (.x10 ↦ᵣ a0v) (by exact pcFree_regIs) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
