/-
  Teer frame restore epilogue (instr 730–744):
  loadSeq ra/s0–s11 (no a5); ADDI sp,+160; JALR ret.
  Entry at EpiRestore (E+2920). Shared by rolled/non-rolled paths after a0 set.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerPrologue
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBeq
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000

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

/-- Restore frame: ra + s0–s11 only (a5@104 left on stack; not reloaded). -/
def teerEpiFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16),
   (.x18, 24), (.x19, 32), (.x20, 40), (.x21, 48), (.x22, 56),
   (.x23, 64), (.x24, 72), (.x25, 80), (.x26, 88), (.x27, 96)]

theorem teerEpiFrame_length : teerEpiFrame.length = 13 := by decide

theorem teerEpiFrame_hne : ∀ p ∈ teerEpiFrame, p.1 ≠ .x0 := by decide

abbrev EpiRestore : Word := E + 2920
abbrev EpiAddi : Word := E + 2972
abbrev EpiJalr : Word := E + 2976

theorem regsAt_teerEpiFrame (s : TeerSaved) :
    regsAt teerEpiFrame (teerSavedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
        (.x27 ↦ᵣ s.s11)) := by
  simp [teerEpiFrame, regsAt, teerSavedVals, sepConj_emp_right']

theorem frameSlotsSaved_teerEpiFrame (spC : Word) (s : TeerSaved) :
    frameSlotsSaved teerEpiFrame spC (teerSavedVals s) =
      ((spC + signExtend12 (0 : BitVec 12) ↦ₘ s.ra) **
        (spC + signExtend12 (8 : BitVec 12) ↦ₘ s.s0) **
        (spC + signExtend12 (16 : BitVec 12) ↦ₘ s.s1) **
        (spC + signExtend12 (24 : BitVec 12) ↦ₘ s.s2) **
        (spC + signExtend12 (32 : BitVec 12) ↦ₘ s.s3) **
        (spC + signExtend12 (40 : BitVec 12) ↦ₘ s.s4) **
        (spC + signExtend12 (48 : BitVec 12) ↦ₘ s.s5) **
        (spC + signExtend12 (56 : BitVec 12) ↦ₘ s.s6) **
        (spC + signExtend12 (64 : BitVec 12) ↦ₘ s.s7) **
        (spC + signExtend12 (72 : BitVec 12) ↦ₘ s.s8) **
        (spC + signExtend12 (80 : BitVec 12) ↦ₘ s.s9) **
        (spC + signExtend12 (88 : BitVec 12) ↦ₘ s.s10) **
        (spC + signExtend12 (96 : BitVec 12) ↦ₘ s.s11)) := by
  simp [teerEpiFrame, frameSlotsSaved, teerSavedVals, sepConj_emp_right']

/-- loadSeq + ADDI sp,+160 + JALR (15 steps). Exit at s.ra when ra is even. -/
theorem teerEpilogueRestore (sp0 spC : Word) (s cur : TeerSaved)
    (hspC : spC = sp0 + signExtend12 (-160 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 15 EpiRestore s.ra teerCode
      ((.x2 ↦ᵣ spC) ** regsAt teerEpiFrame (teerSavedVals cur) **
        frameSlotsSaved teerEpiFrame spC (teerSavedVals s))
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
        (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
        frameSlotsSaved teerEpiFrame spC (teerSavedVals s)) := by
  have hs0 := loadSeq_spec teerEpiFrame spC (teerSavedVals s) (teerSavedVals cur)
    EpiRestore (by decide) teerEpiFrame_hne
  have h_loadMono : ∀ a i,
      CodeReq.ofProg EpiRestore (loadProg teerEpiFrame) a = some i →
        teerCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub E EpiRestore teerProg (loadProg teerEpiFrame) 730
      (by simp only [EpiRestore, E]; decide) (by rfl)
      (by rw [teer_length]; simp [teerEpiFrame, loadProg])
      (by rw [teer_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_loadMono hs0
  have hLoadEnd : EpiRestore + BitVec.ofNat 64 (4 * teerEpiFrame.length) = EpiAddi := by
    simp only [EpiRestore, EpiAddi, teerEpiFrame, List.length_cons, List.length_nil, E]
    decide
  rw [hLoadEnd] at hs
  have ha0 := addi_spec_gen_same_within .x2 spC (160 : BitVec 12) EpiAddi (by decide)
  have hsp : spC + signExtend12 (160 : BitVec 12) = sp0 := by
    rw [hspC]
    rw [show signExtend12 (-160 : BitVec 12) = (-160 : Word) from by decide,
      show signExtend12 (160 : BitVec 12) = (160 : Word) from by decide]
    bv_omega
  rw [hsp] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E EpiAddi teerProg 743
      (.ADDI .x2 .x2 (160 : BitVec 12))
      (by simp only [EpiAddi, E]; decide)
      (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt teerEpiFrame (teerSavedVals s) **
      frameSlotsSaved teerEpiFrame spC (teerSavedVals s))
    (by pcf) ha
  have hload_addi := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hs haF
  have hpc : (EpiAddi : Word) + 4 = EpiJalr := by
    simp only [EpiAddi, EpiJalr, E]; decide
  rw [hpc] at hload_addi
  have hjalr0 := EvmAsm.Evm64.ret_spec_within' EpiJalr s.ra
  rw [hret] at hjalr0
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E EpiJalr teerProg 744
      (.JALR .x0 .x1 (0 : BitVec 12))
      (by simp only [EpiJalr, E]; decide)
      (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide)) hjalr0
  have hjalrF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
      (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
      (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
      frameSlotsSaved teerEpiFrame spC (teerSavedVals s))
    (by pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_teerEpiFrame] at hp
    xperm_hyp hp) hload_addi hjalrF
  have hn : teerEpiFrame.length + 1 + 1 = 15 := by simp [teerEpiFrame]
  rw [hn] at hall
  change cpsTripleWithin 15 EpiRestore s.ra teerCode _ _
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-- Epilogue carrying a0 (return value) through restore. -/
theorem teerEpilogueRestore_a0 (sp0 spC : Word) (s cur : TeerSaved) (a0v : Word)
    (hspC : spC = sp0 + signExtend12 (-160 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 15 EpiRestore s.ra teerCode
      ((.x10 ↦ᵣ a0v) ** (.x2 ↦ᵣ spC) **
        regsAt teerEpiFrame (teerSavedVals cur) **
        frameSlotsSaved teerEpiFrame spC (teerSavedVals s))
      ((.x10 ↦ᵣ a0v) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
        (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
        frameSlotsSaved teerEpiFrame spC (teerSavedVals s)) := by
  have h := teerEpilogueRestore sp0 spC s cur hspC hret
  have hF := cpsTripleWithin_frameR (.x10 ↦ᵣ a0v) (by pcf) h
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms teerEpilogueRestore
#print axioms teerEpilogueRestore_a0

end EvmAsm.Codegen.TxEip7702TeerSpec
