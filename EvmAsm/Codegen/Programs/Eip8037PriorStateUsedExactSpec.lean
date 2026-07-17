/-
  Fn.Spec for `eip8037_prior_state_used_exact` (43-instr sum leaf; a4gbr residual).

  ABI: a0 = prior tx count, a1 = out ptr.
  Success: a0=0 ∧ *out = pure prior-state sum (0 when prior=0).
  Fail: a0=1 (gates/overflow).

  No stack frame; leaf ret via JALR x0,x1,0.
  Globals: bsg_exact_state_ok, bvgr_runtime_count, bvgr_tx_state_gas[16],
  bv_tx_status_arr[16], bvgr_tx_exec_state_gas[16].
-/

import EvmAsm.Codegen.Programs.BlockVerdictGasGate
import EvmAsm.Codegen.Programs.Eip8037PriorStateUsedExactModel
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.Eip8037PriorStateUsedExactSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.Eip8037PriorStateUsedExactModel

abbrev P : Word := (GuestAddrs.eip8037_prior_state_used_exact : Word)
abbrev ExactOkAddr : Word := (GuestAddrs.bsg_exact_state_ok : Word)
abbrev RuntimeCountAddr : Word := (GuestAddrs.bvgr_runtime_count : Word)
abbrev TxStateGasAddr : Word := (GuestAddrs.bvgr_tx_state_gas : Word)
abbrev TxStatusAddr : Word := (GuestAddrs.bv_tx_status_arr : Word)
abbrev TxExecStateGasAddr : Word := (GuestAddrs.bvgr_tx_exec_state_gas : Word)

abbrev pseProg : Program := eip8037PriorStateUsedExact_prog

theorem pse_length : pseProg.length = 43 := by decide

def pseCode : CodeReq := CodeReq.ofProg P pseProg

/-- Exit PCs (byte offsets from P). -/
abbrev OkLi : Word := P + 156    -- instr 39 LI a0,0
abbrev OkRet : Word := P + 160   -- instr 40 JALR success
abbrev FailLi : Word := P + 164  -- instr 41 LI a0,1
abbrev FailRet : Word := P + 168 -- instr 42 JALR fail
abbrev LoopGuard : Word := P + 60 -- instr 15 BEQ i,n
abbrev StoreSum : Word := P + 152 -- instr 38 SD sum

/-- Success post: a0=0, *out=sum, ra preserved, hardwired x0. -/
def postOk (raIn outPtr sumW : Word) (scratch : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
    (outPtr ↦ₘ sumW) ** scratch ** (.x0 ↦ᵣ (0 : Word))

/-- Fail post: a0=1. -/
def postFail (raIn outPtr oldOut : Word) (scratch : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ outPtr) **
    (outPtr ↦ₘ oldOut) ** scratch ** (.x0 ↦ᵣ (0 : Word))

/-- Entry pre: ABI + out cell + ambient scratch + hardwired x0. -/
def entryPre (raIn priorW outPtr oldOut : Word) (scratch : Assertion) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
    (outPtr ↦ₘ oldOut) ** scratch ** (.x0 ↦ᵣ (0 : Word))

def nZeroSteps : Nat := 4

private theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se13_152 : signExtend13 (152 : BitVec 13) = (152 : Word) := by decide

private theorem P_plus_4_plus_152 : P + 4 + signExtend13 (152 : BitVec 13) = OkLi := by
  simp only [OkLi, P, GuestAddrs.eip8037_prior_state_used_exact, se13_152]
  decide

private theorem OkLi_plus_4 : OkLi + 4 = OkRet := by
  simp only [OkLi, OkRet, P, GuestAddrs.eip8037_prior_state_used_exact]; decide

set_option maxRecDepth 8000 in
/-- `prior=0`: zero *out, BEQ taken to ok, LI a0=0, ret. Matches pure model. -/
theorem eip8037PriorStateUsedExact_zero_spec_within
    (raIn outPtr oldOut : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin nZeroSteps P raIn pseCode
      (entryPre raIn (0 : Word) outPtr oldOut
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)))
      (postOk raIn outPtr (0 : Word)
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))) := by
  -- [0] SD x0, 0(x11)
  have haddr :
      outPtr + signExtend12 (0 : BitVec 12) = outPtr := by
    rw [se12_zero]; exact BitVec.add_zero outPtr
  have e0 :
      cpsTripleWithin 1 P (P + 4) pseCode
        ((.x11 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldOut))
        ((.x11 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (0 : Word))) := by
    have h0 := sd_spec_gen_within .x11 .x0 outPtr (0 : Word) oldOut
      (0 : BitVec 12) P
    rw [haddr] at h0
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at P P pseProg 0
        (.SD .x11 .x0 (0 : BitVec 12))
        (by decide) (by rw [pse_length]; decide) rfl
        (by rw [pse_length]; decide)) h0
  have e0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs) e0
  -- [1] BEQ x10, x0, +152 — taken (prior=0)
  have hbr := beq_spec_gen_within .x10 .x0 (152 : BitVec 13) (0 : Word) (0 : Word) (P + 4)
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at P (P + 4) pseProg 1
      (.BEQ .x10 .x0 (152 : BitVec 13))
      (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
      (by rw [pse_length]; decide) rfl
      (by rw [pse_length]; decide)) hbr
  have htk0 := cpsBranchWithin_takenStripPure2 hbrC (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have htk : cpsTripleWithin 1 (P + 4) OkLi pseCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
    rwa [P_plus_4_plus_152] at htk0
  have e1F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) htk
  -- [39] LI a0, 0
  have e39 :
      cpsTripleWithin 1 OkLi OkRet pseCode
        (.x10 ↦ᵣ (0 : Word)) (.x10 ↦ᵣ (0 : Word)) := by
    have h0 := li_spec_gen_within .x10 (0 : Word) (0 : Word) OkLi (by decide)
    have h0' : cpsTripleWithin 1 OkLi (OkLi + 4) pseCode
        (.x10 ↦ᵣ (0 : Word)) (.x10 ↦ᵣ (0 : Word)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P OkLi pseProg 39
          (.LI .x10 (0 : Word))
          (by simp only [OkLi, P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl
          (by rw [pse_length]; decide)) h0
    rwa [OkLi_plus_4] at h0'
  have e39F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e39
  -- [40] JALR x0, x1, 0 → raIn
  have hexit :
      ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
    have hadd : raIn + signExtend12 (0 : BitVec 12) = raIn := by
      rw [se12_zero]
      exact BitVec.add_zero raIn
    rw [hadd, hret]
  have e40 :
      cpsTripleWithin 1 OkRet raIn pseCode
        (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
    have h0 := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) OkRet
    rw [hexit] at h0
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at P OkRet pseProg 40
        (.JALR .x0 .x1 (0 : BitVec 12))
        (by simp only [OkRet, P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
        (by rw [pse_length]; decide) rfl
        (by rw [pse_length]; decide)) h0
  -- Frame for JALR ordered to match e39F post: x10 ** x1 ** rest
  -- so reshape is identity-ish after one xperm on the framed triple.
  have e40F0 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e40
  have e40F : cpsTripleWithin 1 OkRet raIn pseCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) e40F0
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e0F e1F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01 e39F
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c02 e40F
  change cpsTripleWithin (1 + 1 + 1 + 1) P raIn pseCode _ _ at c03
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp only [entryPre, nZeroSteps] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp only [postOk, nZeroSteps] at hq ⊢
      xperm_hyp hq) c03

#print axioms eip8037PriorStateUsedExact_zero_spec_within

end EvmAsm.Codegen.Eip8037PriorStateUsedExactSpec
