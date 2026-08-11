/-
  EvmAsm.Codegen.Programs.ExecutionRequestsHashEpi

  Fail-join epilogue for `execution_requests_hash` (GH #11578 rescope):

    LI a0, 1                                  -- idx 120 @ B+480
    LD ra/s0–s11 from frame                   -- idx 121–132
    ADDI sp, +96                              -- idx 133
    JALR x0, ra, 0                            -- idx 134

  Shared by every reject arm that jumps to B+480. Pattern mirrors
  TxIntrinsicStateGasEpilogue (loadSeq + ADDI + JALR) with LI a0=1 framed.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.ExecutionRequestsHashEpi

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Evm64

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.execution_requests_hash
private abbrev erhProgL : List Instr := executionRequestsHash_prog

private theorem erhProgL_len : erhProgL.length = 135 := by
  simp only [erhProgL, executionRequestsHash_prog]; decide

private theorem erhProgL_bound : 4 * erhProgL.length < 2 ^ 64 := by
  rw [erhProgL_len]; norm_num

private abbrev erhCr : CodeReq := CodeReq.ofProg B erhProgL

/-- 12-slot frame: ra, s0–s11 (x8,x9,x18–x26). Matches RequestsHash.lean prologue. -/
def erhFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16),
   (.x18, 24), (.x19, 32), (.x20, 40), (.x21, 48), (.x22, 56),
   (.x23, 64), (.x24, 72), (.x25, 80), (.x26, 88)]

theorem erhFrame_length : erhFrame.length = 12 := by decide

theorem erhFrame_hne : ∀ p ∈ erhFrame, p.1 ≠ .x0 := by decide

structure ErhSaved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word
  s6 : Word
  s7 : Word
  s8 : Word
  s9 : Word
  s10 : Word

def erhSavedVals (s : ErhSaved) : Reg → Word
  | .x1  => s.ra
  | .x8  => s.s0
  | .x9  => s.s1
  | .x18 => s.s2
  | .x19 => s.s3
  | .x20 => s.s4
  | .x21 => s.s5
  | .x22 => s.s6
  | .x23 => s.s7
  | .x24 => s.s8
  | .x25 => s.s9
  | .x26 => s.s10
  | _ => 0

theorem regsAt_erhFrame (s : ErhSaved) :
    regsAt erhFrame (erhSavedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10)) := by
  simp [erhFrame, regsAt, erhSavedVals, sepConj_emp_right']

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

/-- Fail join: LI a0,1 @ B+480. -/
theorem erh_fail_li1 (v10old : Word) (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 1 (B + 480) (B + 484) erhCr
      ((.x10 ↦ᵣ v10old) ** A)
      ((.x10 ↦ᵣ (1 : Word)) ** A) := by
  have hli0 := li_spec_gen_within .x10 v10old (1 : Word) (B + 480) (by decide)
  have hli := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 480) erhProgL 120
      (.LI .x10 (1 : Word))
      (by bv_omega) (by rw [erhProgL_len]; decide) (by rfl) erhProgL_bound) hli0
  have hliF := cpsTripleWithin_frameR A hA hli
  rw [show (B + 480 : Word) + 4 = B + 484 from by decide] at hliF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hliF

/-- loadSeq + ADDI sp,+96 + JALR from B+484 (idx 121) → s.ra. -/
theorem erhEpilogueRestore (sp0 spC : Word) (s cur : ErhSaved)
    (hspC : spC = sp0 + signExtend12 (-96 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 14 (B + 484) s.ra erhCr
      ((.x2 ↦ᵣ spC) ** regsAt erhFrame (erhSavedVals cur) **
        frameSlotsSaved erhFrame spC (erhSavedVals s))
      ((.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
        (.x26 ↦ᵣ s.s10) **
        frameSlotsSaved erhFrame spC (erhSavedVals s)) := by
  have hs0 := loadSeq_spec erhFrame spC (erhSavedVals s) (erhSavedVals cur) (B + 484)
    (by decide) erhFrame_hne
  have h_loadMono : ∀ a i,
      CodeReq.ofProg (B + 484) (loadProg erhFrame) a = some i →
        erhCr a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub B (B + 484) erhProgL (loadProg erhFrame) 121
      (by bv_omega) (by rfl)
      (by rw [erhProgL_len]; simp [erhFrame, loadProg])
      erhProgL_bound a i h_mem
  have hs := cpsTripleWithin_extend_code h_loadMono hs0
  rw [show (B + 484 : Word) + BitVec.ofNat 64 (4 * erhFrame.length) = B + 532 from by
    simp [erhFrame]; bv_omega] at hs
  have ha0 := addi_spec_gen_same_within .x2 spC (96 : BitVec 12) (B + 532) (by decide)
  have hsp : spC + signExtend12 (96 : BitVec 12) = sp0 := by
    rw [hspC]
    rw [show signExtend12 (-96 : BitVec 12) = (-96 : Word) from by decide,
      show signExtend12 (96 : BitVec 12) = (96 : Word) from by decide]
    bv_omega
  rw [hsp] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 532) erhProgL 133
      (.ADDI .x2 .x2 (96 : BitVec 12))
      (by bv_omega)
      (by rw [erhProgL_len]; decide) rfl
      erhProgL_bound) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt erhFrame (erhSavedVals s) ** frameSlotsSaved erhFrame spC (erhSavedVals s))
    (by pcf) ha
  have hload_addi := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hs haF
  have hpc : (B + 532 : Word) + 4 = B + 536 := by decide
  rw [hpc] at hload_addi
  have hjalr0 := ret_spec_within' (B + 536) s.ra
  rw [hret] at hjalr0
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 536) erhProgL 134
      (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega)
      (by rw [erhProgL_len]; decide) rfl
      erhProgL_bound) hjalr0
  have hjalrF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
      (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
      (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
      (.x26 ↦ᵣ s.s10) **
      frameSlotsSaved erhFrame spC (erhSavedVals s))
    (by pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_erhFrame] at hp
    xperm_hyp hp) hload_addi hjalrF
  have hn : erhFrame.length + 1 + 1 = 14 := by simp [erhFrame]
  rw [hn] at hall
  change cpsTripleWithin 14 (B + 484) s.ra erhCr _ _
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-- Full fail join: LI a0,1 then restore+ret. Fuel 15. Exit at s.ra with a0=1. -/
theorem erh_fail_join (sp0 spC : Word) (s cur : ErhSaved) (v10old : Word)
    (hspC : spC = sp0 + signExtend12 (-96 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra) :
    cpsTripleWithin 15 (B + 480) s.ra erhCr
      ((.x10 ↦ᵣ v10old) ** (.x2 ↦ᵣ spC) **
        regsAt erhFrame (erhSavedVals cur) **
        frameSlotsSaved erhFrame spC (erhSavedVals s))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ s.ra) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
        (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
        (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
        (.x26 ↦ᵣ s.s10) **
        frameSlotsSaved erhFrame spC (erhSavedVals s)) := by
  let F : Assertion :=
    (.x2 ↦ᵣ spC) ** regsAt erhFrame (erhSavedVals cur) **
      frameSlotsSaved erhFrame spC (erhSavedVals s)
  have hli := erh_fail_li1 v10old F (by pcf)
  have hrest := erhEpilogueRestore sp0 spC s cur hspC hret
  have hrestF := cpsTripleWithin_frameR (.x10 ↦ᵣ (1 : Word)) (by exact pcFree_regIs) hrest
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hli hrestF
  have hn : 1 + 14 = 15 := rfl
  rw [hn] at hall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

end EvmAsm.Codegen.ExecutionRequestsHashEpi
