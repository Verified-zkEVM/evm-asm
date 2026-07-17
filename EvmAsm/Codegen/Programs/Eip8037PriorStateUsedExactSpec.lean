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
import EvmAsm.Rv64.LaResolve

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

/-! ## Shared exit tails -/

private theorem FailLi_plus_4 : FailLi + 4 = FailRet := by
  simp only [FailLi, FailRet, P, GuestAddrs.eip8037_prior_state_used_exact]; decide

private theorem P20_plus_144 : P + 20 + signExtend13 (144 : BitVec 13) = FailLi := by
  simp only [FailLi, P, GuestAddrs.eip8037_prior_state_used_exact]
  decide

private theorem P36_plus_128 : P + 36 + signExtend13 (128 : BitVec 13) = FailLi := by
  simp only [FailLi, P, GuestAddrs.eip8037_prior_state_used_exact]
  decide

private theorem P44_plus_120 : P + 44 + signExtend13 (120 : BitVec 13) = FailLi := by
  simp only [FailLi, P, GuestAddrs.eip8037_prior_state_used_exact]
  decide

set_option maxRecDepth 8000 in
/-- Fail tail: LI a0=1; JALR. Preserves `*out` (still the entry old or zeroed). -/
theorem pseFailRet_spec
    (raIn outPtr outVal : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 2 FailLi raIn pseCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ v5) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ outVal) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
      (postFail raIn outPtr outVal
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))) := by
  have e41 :
      cpsTripleWithin 1 FailLi FailRet pseCode
        (.x10 ↦ᵣ v5) (.x10 ↦ᵣ (1 : Word)) := by
    have h0 := li_spec_gen_within .x10 v5 (1 : Word) FailLi (by decide)
    have h0' : cpsTripleWithin 1 FailLi (FailLi + 4) pseCode
        (.x10 ↦ᵣ v5) (.x10 ↦ᵣ (1 : Word)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P FailLi pseProg 41
          (.LI .x10 (1 : Word))
          (by simp only [FailLi, P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl
          (by rw [pse_length]; decide)) h0
    rwa [FailLi_plus_4] at h0'
  have e41F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ outVal) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e41
  have hexit :
      ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
    have hadd : raIn + signExtend12 (0 : BitVec 12) = raIn := by
      rw [se12_zero]; exact BitVec.add_zero raIn
    rw [hadd, hret]
  have e42 :
      cpsTripleWithin 1 FailRet raIn pseCode
        (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
    have h0 := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) FailRet
    rw [hexit] at h0
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at P FailRet pseProg 42
        (.JALR .x0 .x1 (0 : BitVec 12))
        (by simp only [FailRet, P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
        (by rw [pse_length]; decide) rfl
        (by rw [pse_length]; decide)) h0
  have e42F0 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ outVal) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e42
  have e42F : cpsTripleWithin 1 FailRet raIn pseCode
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ outVal) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ outVal) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) e42F0
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e41F e42F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      dsimp only [postFail] at hq ⊢
      xperm_hyp hq) c

set_option maxRecDepth 8000 in
/-- Success tail: LI a0=0; JALR. -/
theorem pseOkRet_spec
    (raIn outPtr sumW : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 2 OkLi raIn pseCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ v5) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ sumW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
      (postOk raIn outPtr sumW
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))) := by
  have e39 :
      cpsTripleWithin 1 OkLi OkRet pseCode
        (.x10 ↦ᵣ v5) (.x10 ↦ᵣ (0 : Word)) := by
    have h0 := li_spec_gen_within .x10 v5 (0 : Word) OkLi (by decide)
    have h0' : cpsTripleWithin 1 OkLi (OkLi + 4) pseCode
        (.x10 ↦ᵣ v5) (.x10 ↦ᵣ (0 : Word)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P OkLi pseProg 39
          (.LI .x10 (0 : Word))
          (by simp only [OkLi, P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl
          (by rw [pse_length]; decide)) h0
    rwa [OkLi_plus_4] at h0'
  have e39F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ sumW) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e39
  have hexit :
      ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
    have hadd : raIn + signExtend12 (0 : BitVec 12) = raIn := by
      rw [se12_zero]; exact BitVec.add_zero raIn
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
  have e40F0 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ sumW) **
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
        (outPtr ↦ₘ sumW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ sumW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) e40F0
  have c := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e39F e40F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      dsimp only [postOk] at hq ⊢
      xperm_hyp hq) c

/-! ## `la` materializations for gate globals -/

private theorem pseLaExactOk (v : Word) :
    cpsTripleWithin 2 (P + 8) (P + 16) pseCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ ExactOkAddr) := by
  have hau := CodeReq.ofProg_mem_at P (P + 8) pseProg 2
    (.AUIPC .x5 (Codegen.laHi GuestAddrs.bsg_exact_state_ok
      (GuestAddrs.eip8037_prior_state_used_exact + 8)))
    (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
    (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)
  have had := CodeReq.ofProg_mem_at P (P + 12) pseProg 3
    (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.bsg_exact_state_ok
      (GuestAddrs.eip8037_prior_state_used_exact + 8)))
    (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
    (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)
  have h := la_materialize_within .x5 v (P + 8) ExactOkAddr
    (by decide)
    (by simp only [P, ExactOkAddr, GuestAddrs.eip8037_prior_state_used_exact,
          GuestAddrs.bsg_exact_state_ok]; decide)
    hau had
  rwa [show (P + 8 : Word) + 8 = P + 16 from by
    simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide] at h

private theorem pseLaRuntime (v : Word) :
    cpsTripleWithin 2 (P + 24) (P + 32) pseCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ RuntimeCountAddr) := by
  have hau := CodeReq.ofProg_mem_at P (P + 24) pseProg 6
    (.AUIPC .x5 (Codegen.laHi GuestAddrs.bvgr_runtime_count
      (GuestAddrs.eip8037_prior_state_used_exact + 24)))
    (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
    (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)
  have had := CodeReq.ofProg_mem_at P (P + 28) pseProg 7
    (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.bvgr_runtime_count
      (GuestAddrs.eip8037_prior_state_used_exact + 24)))
    (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
    (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)
  have h := la_materialize_within .x5 v (P + 24) RuntimeCountAddr
    (by decide)
    (by simp only [P, RuntimeCountAddr, GuestAddrs.eip8037_prior_state_used_exact,
          GuestAddrs.bvgr_runtime_count]; decide)
    hau had
  rwa [show (P + 24 : Word) + 8 = P + 32 from by
    simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide] at h

/-! ## Gate fail: exact_ok = 0 (after prior ≠ 0) -/

set_option maxRecDepth 8000 in
/-- From P (entry) with prior≠0 and *exact_ok=0: zero out, fall through BEQ,
    load exact_ok=0, take fail branch, ret a0=1. -/
theorem eip8037PriorStateUsedExact_exactOkFail_spec_within
    (raIn priorW outPtr oldOut : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hprior : priorW ≠ (0 : Word)) :
    cpsTripleWithin 8 P raIn pseCode
      (entryPre raIn priorW outPtr oldOut
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (ExactOkAddr ↦ₘ (0 : Word))))
      (postFail raIn outPtr (0 : Word)
        ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (ExactOkAddr ↦ₘ (0 : Word)))) := by
  -- [0] SD zero *out
  have haddr : outPtr + signExtend12 (0 : BitVec 12) = outPtr := by
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
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ (0 : Word)))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e0
  -- [1] BEQ prior,0 — ntaken
  have hbr := beq_spec_gen_within .x10 .x0 (152 : BitVec 13) priorW (0 : Word) (P + 4)
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at P (P + 4) pseProg 1
      (.BEQ .x10 .x0 (152 : BitVec 13))
      (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
      (by rw [pse_length]; decide) rfl
      (by rw [pse_length]; decide)) hbr
  have hnt0 := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hprior)
  have hnt : cpsTripleWithin 1 (P + 4) (P + 8) pseCode
      ((.x10 ↦ᵣ priorW) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ priorW) ** (.x0 ↦ᵣ (0 : Word))) := by
    rwa [show (P + 4 : Word) + 4 = P + 8 from by
      simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide] at hnt0
  have e1F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ (0 : Word)))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) hnt
  -- [2-3] la exact_ok
  have e23F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ (0 : Word)))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) (pseLaExactOk v5)
  -- [4] LD x5,0(x5) — same-reg load exact_ok=0
  have e4 :
      cpsTripleWithin 1 (P + 16) (P + 20) pseCode
        ((.x5 ↦ᵣ ExactOkAddr) ** (ExactOkAddr ↦ₘ (0 : Word)))
        ((.x5 ↦ᵣ (0 : Word)) ** (ExactOkAddr ↦ₘ (0 : Word))) := by
    have haddrE : ExactOkAddr + signExtend12 (0 : BitVec 12) = ExactOkAddr := by
      rw [se12_zero]; exact BitVec.add_zero ExactOkAddr
    have h0 := ld_spec_gen_same_within .x5 ExactOkAddr (0 : Word)
      (0 : BitVec 12) (P + 16) (by decide)
    rw [haddrE] at h0
    have h0' : cpsTripleWithin 1 (P + 16) ((P + 16) + 4) pseCode
        ((.x5 ↦ᵣ ExactOkAddr) ** (ExactOkAddr ↦ₘ (0 : Word)))
        ((.x5 ↦ᵣ (0 : Word)) ** (ExactOkAddr ↦ₘ (0 : Word))) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 16) pseProg 4
          (.LD .x5 .x5 (0 : BitVec 12))
          (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl
          (by rw [pse_length]; decide)) h0
    rwa [show (P + 16 : Word) + 4 = P + 20 from by
      simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide] at h0'
  have e4F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e4
  -- [5] BEQ x5,x0 taken → FailLi
  have hbr5 := beq_spec_gen_within .x5 .x0 (144 : BitVec 13) (0 : Word) (0 : Word) (P + 20)
  have hbr5C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at P (P + 20) pseProg 5
      (.BEQ .x5 .x0 (144 : BitVec 13))
      (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
      (by rw [pse_length]; decide) rfl
      (by rw [pse_length]; decide)) hbr5
  have htk5_0 := cpsBranchWithin_takenStripPure2 hbr5C (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have htk5 : cpsTripleWithin 1 (P + 20) FailLi pseCode
      ((.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
    rwa [P20_plus_144] at htk5_0
  have e5F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ (0 : Word)))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) htk5
  -- Fail ret: a0 was priorW, LI overwrites to 1; frame ExactOkAddr through.
  have eFail' : cpsTripleWithin 2 FailLi raIn pseCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (ExactOkAddr ↦ₘ (0 : Word)))
      (postFail raIn outPtr (0 : Word)
        ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (ExactOkAddr ↦ₘ (0 : Word)))) := by
    have e41 :
        cpsTripleWithin 1 FailLi FailRet pseCode
          (.x10 ↦ᵣ priorW) (.x10 ↦ᵣ (1 : Word)) := by
      have h0 := li_spec_gen_within .x10 priorW (1 : Word) FailLi (by decide)
      have h0' : cpsTripleWithin 1 FailLi (FailLi + 4) pseCode
          (.x10 ↦ᵣ priorW) (.x10 ↦ᵣ (1 : Word)) :=
        cpsTripleWithin_extend_code
          (CodeReq.ofProg_mem_at P FailLi pseProg 41
            (.LI .x10 (1 : Word))
            (by simp only [FailLi, P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
            (by rw [pse_length]; decide) rfl
            (by rw [pse_length]; decide)) h0
      rwa [FailLi_plus_4] at h0'
    have e41F := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (ExactOkAddr ↦ₘ (0 : Word)))
      (by
        repeat' first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_memIs) e41
    have hexit :
        ((raIn + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)) = raIn := by
      have hadd : raIn + signExtend12 (0 : BitVec 12) = raIn := by
        rw [se12_zero]; exact BitVec.add_zero raIn
      rw [hadd, hret]
    have e42 :
        cpsTripleWithin 1 FailRet raIn pseCode
          (.x1 ↦ᵣ raIn) (.x1 ↦ᵣ raIn) := by
      have h0 := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) FailRet
      rw [hexit] at h0
      exact cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P FailRet pseProg 42
          (.JALR .x0 .x1 (0 : BitVec 12))
          (by simp only [FailRet, P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl
          (by rw [pse_length]; decide)) h0
    have e42F0 := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (ExactOkAddr ↦ₘ (0 : Word)))
      (by
        repeat' first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_memIs) e42
    have e42F : cpsTripleWithin 1 FailRet raIn pseCode
        ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
          (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (ExactOkAddr ↦ₘ (0 : Word)))
        ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
          (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (ExactOkAddr ↦ₘ (0 : Word))) :=
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) e42F0
    have c := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) e41F e42F
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        dsimp only [postFail] at hq ⊢
        xperm_hyp hq) c
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e0F e1F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01 e23F
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c02 e4F
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c03 e5F
  have c05 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c04 eFail'
  change cpsTripleWithin (1 + 1 + 2 + 1 + 1 + 2) P raIn pseCode _ _ at c05
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp only [entryPre] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp only [postFail] at hq ⊢
      xperm_hyp hq) c05

#print axioms eip8037PriorStateUsedExact_exactOkFail_spec_within
#print axioms pseFailRet_spec
#print axioms pseOkRet_spec

/-! ## Gate success → LoopGuard (prior≠0, gates hold) -/

/-- Loop-entry regs after gates: n=prior, i=0, sum=0; *out already zeroed. -/
def loopEntry
    (raIn priorW outPtr exactOkW runtimeW : Word)
    (v28 v29 v30 v31 : Word) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
    (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
    (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW)

def nGateSteps : Nat := 15

private theorem P36_plus_4 : P + 36 + 4 = P + 40 := by
  simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide
private theorem P40_plus_4 : P + 40 + 4 = P + 44 := by
  simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide
private theorem P44_plus_4 : P + 44 + 4 = P + 48 := by
  simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide
private theorem P48_plus_4 : P + 48 + 4 = P + 52 := by
  simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide
private theorem P52_plus_4 : P + 52 + 4 = P + 56 := by
  simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide
private theorem P56_plus_4 : P + 56 + 4 = LoopGuard := by
  simp only [LoopGuard, P, GuestAddrs.eip8037_prior_state_used_exact]; decide
private theorem P32_plus_4 : P + 32 + 4 = P + 36 := by
  simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide
private theorem P20_plus_4 : P + 20 + 4 = P + 24 := by
  simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide
private theorem P16_plus_4 : P + 16 + 4 = P + 20 := by
  simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide
private theorem P8_plus_8 : P + 8 + 8 = P + 16 := by
  simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide
private theorem P4_plus_4 : P + 4 + 4 = P + 8 := by
  simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide

set_option maxRecDepth 8000 in
/-- Entry → LoopGuard under prior≠0 and gate hyps (exactOk≠0, runtime≥prior, prior≤16). -/
theorem eip8037PriorStateUsedExact_gatesToLoop_spec_within
    (raIn priorW outPtr oldOut exactOkW runtimeW : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (hprior : priorW ≠ (0 : Word))
    (hexact : exactOkW ≠ (0 : Word))
    (hruntime : ¬ BitVec.ult runtimeW priorW)
    (hpriorLe16 : ¬ BitVec.ult (16 : Word) priorW) :
    cpsTripleWithin nGateSteps P LoopGuard pseCode
      (entryPre raIn priorW outPtr oldOut
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW)))
      (loopEntry raIn priorW outPtr exactOkW runtimeW v28 v29 v30 v31) := by
  -- [0] SD
  have haddr : outPtr + signExtend12 (0 : BitVec 12) = outPtr := by
    rw [se12_zero]; exact BitVec.add_zero outPtr
  have e0 :
      cpsTripleWithin 1 P (P + 4) pseCode
        ((.x11 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldOut))
        ((.x11 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (0 : Word))) := by
    have h0 := sd_spec_gen_within .x11 .x0 outPtr (0 : Word) oldOut (0 : BitVec 12) P
    rw [haddr] at h0
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at P P pseProg 0 (.SD .x11 .x0 (0 : BitVec 12))
        (by decide) (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
  have e0F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e0
  -- [1] BEQ prior ntaken
  have hbr := beq_spec_gen_within .x10 .x0 (152 : BitVec 13) priorW (0 : Word) (P + 4)
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at P (P + 4) pseProg 1 (.BEQ .x10 .x0 (152 : BitVec 13))
      (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
      (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr
  have hnt0 := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hprior)
  have hnt : cpsTripleWithin 1 (P + 4) (P + 8) pseCode
      ((.x10 ↦ᵣ priorW) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ priorW) ** (.x0 ↦ᵣ (0 : Word))) := by
    rwa [P4_plus_4] at hnt0
  have e1F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) hnt
  -- [2-3] la exact_ok
  have e23F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) (pseLaExactOk v5)
  -- [4] LD exact_ok
  have haddrE : ExactOkAddr + signExtend12 (0 : BitVec 12) = ExactOkAddr := by
    rw [se12_zero]; exact BitVec.add_zero ExactOkAddr
  have e4 :
      cpsTripleWithin 1 (P + 16) (P + 20) pseCode
        ((.x5 ↦ᵣ ExactOkAddr) ** (ExactOkAddr ↦ₘ exactOkW))
        ((.x5 ↦ᵣ exactOkW) ** (ExactOkAddr ↦ₘ exactOkW)) := by
    have h0 := ld_spec_gen_same_within .x5 ExactOkAddr exactOkW
      (0 : BitVec 12) (P + 16) (by decide)
    rw [haddrE] at h0
    have h0' : cpsTripleWithin 1 (P + 16) ((P + 16) + 4) pseCode
        ((.x5 ↦ᵣ ExactOkAddr) ** (ExactOkAddr ↦ₘ exactOkW))
        ((.x5 ↦ᵣ exactOkW) ** (ExactOkAddr ↦ₘ exactOkW)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 16) pseProg 4 (.LD .x5 .x5 (0 : BitVec 12))
          (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [P16_plus_4] at h0'
  have e4F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e4
  -- [5] BEQ exact_ok ntaken
  have hbr5 := beq_spec_gen_within .x5 .x0 (144 : BitVec 13) exactOkW (0 : Word) (P + 20)
  have hbr5C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at P (P + 20) pseProg 5 (.BEQ .x5 .x0 (144 : BitVec 13))
      (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
      (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr5
  have hnt5_0 := cpsBranchWithin_ntakenStripPure2 hbr5C (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hexact)
  have hnt5 : cpsTripleWithin 1 (P + 20) (P + 24) pseCode
      ((.x5 ↦ᵣ exactOkW) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ exactOkW) ** (.x0 ↦ᵣ (0 : Word))) := by
    rwa [P20_plus_4] at hnt5_0
  have e5F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) hnt5
  -- [6-7] la runtime
  have e67F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) (pseLaRuntime exactOkW)
  -- [8] LD runtime
  have haddrR : RuntimeCountAddr + signExtend12 (0 : BitVec 12) = RuntimeCountAddr := by
    rw [se12_zero]; exact BitVec.add_zero RuntimeCountAddr
  have e8 :
      cpsTripleWithin 1 (P + 32) (P + 36) pseCode
        ((.x5 ↦ᵣ RuntimeCountAddr) ** (RuntimeCountAddr ↦ₘ runtimeW))
        ((.x5 ↦ᵣ runtimeW) ** (RuntimeCountAddr ↦ₘ runtimeW)) := by
    have h0 := ld_spec_gen_same_within .x5 RuntimeCountAddr runtimeW
      (0 : BitVec 12) (P + 32) (by decide)
    rw [haddrR] at h0
    have h0' : cpsTripleWithin 1 (P + 32) ((P + 32) + 4) pseCode
        ((.x5 ↦ᵣ RuntimeCountAddr) ** (RuntimeCountAddr ↦ₘ runtimeW))
        ((.x5 ↦ᵣ runtimeW) ** (RuntimeCountAddr ↦ₘ runtimeW)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 32) pseProg 8 (.LD .x5 .x5 (0 : BitVec 12))
          (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [P32_plus_4] at h0'
  have e8F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e8
  -- [9] BLTU runtime,prior ntaken
  have hbr9 := bltu_spec_gen_within .x5 .x10 (128 : BitVec 13) runtimeW priorW (P + 36)
  have hbr9C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at P (P + 36) pseProg 9 (.BLTU .x5 .x10 (128 : BitVec 13))
      (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
      (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr9
  have hnt9_0 := cpsBranchWithin_ntakenStripPure2 hbr9C (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hruntime)
  have hnt9 : cpsTripleWithin 1 (P + 36) (P + 40) pseCode
      ((.x5 ↦ᵣ runtimeW) ** (.x10 ↦ᵣ priorW))
      ((.x5 ↦ᵣ runtimeW) ** (.x10 ↦ᵣ priorW)) := by
    rwa [P36_plus_4] at hnt9_0
  have e9F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) hnt9
  -- [10] LI x5,16
  have e10 :
      cpsTripleWithin 1 (P + 40) (P + 44) pseCode
        (.x5 ↦ᵣ runtimeW) (.x5 ↦ᵣ (16 : Word)) := by
    have h0 := li_spec_gen_within .x5 runtimeW (16 : Word) (P + 40) (by decide)
    have h0' : cpsTripleWithin 1 (P + 40) ((P + 40) + 4) pseCode
        (.x5 ↦ᵣ runtimeW) (.x5 ↦ᵣ (16 : Word)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 40) pseProg 10 (.LI .x5 (16 : Word))
          (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [P40_plus_4] at h0'
  have e10F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e10
  -- [11] BLTU 16,prior ntaken
  have hbr11 := bltu_spec_gen_within .x5 .x10 (120 : BitVec 13) (16 : Word) priorW (P + 44)
  have hbr11C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at P (P + 44) pseProg 11 (.BLTU .x5 .x10 (120 : BitVec 13))
      (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
      (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr11
  have hnt11_0 := cpsBranchWithin_ntakenStripPure2 hbr11C (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hpriorLe16)
  have hnt11 : cpsTripleWithin 1 (P + 44) (P + 48) pseCode
      ((.x5 ↦ᵣ (16 : Word)) ** (.x10 ↦ᵣ priorW))
      ((.x5 ↦ᵣ (16 : Word)) ** (.x10 ↦ᵣ priorW)) := by
    rwa [P44_plus_4] at hnt11_0
  have e11F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) hnt11
  -- [12] MV x5,x10 → n=prior
  have e12 :
      cpsTripleWithin 1 (P + 48) (P + 52) pseCode
        ((.x10 ↦ᵣ priorW) ** (.x5 ↦ᵣ (16 : Word)))
        ((.x10 ↦ᵣ priorW) ** (.x5 ↦ᵣ priorW)) := by
    have h0 := mv_spec_gen_within .x5 .x10 priorW (16 : Word) (P + 48) (by decide)
    have h0' : cpsTripleWithin 1 (P + 48) ((P + 48) + 4) pseCode
        ((.x10 ↦ᵣ priorW) ** (.x5 ↦ᵣ (16 : Word)))
        ((.x10 ↦ᵣ priorW) ** (.x5 ↦ᵣ priorW)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 48) pseProg 12 (.MV .x5 .x10)
          (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [P48_plus_4] at h0'
  have e12F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e12
  -- [13] LI x6,0
  have e13 :
      cpsTripleWithin 1 (P + 52) (P + 56) pseCode
        (.x6 ↦ᵣ v6) (.x6 ↦ᵣ (0 : Word)) := by
    have h0 := li_spec_gen_within .x6 v6 (0 : Word) (P + 52) (by decide)
    have h0' : cpsTripleWithin 1 (P + 52) ((P + 52) + 4) pseCode
        (.x6 ↦ᵣ v6) (.x6 ↦ᵣ (0 : Word)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 52) pseProg 13 (.LI .x6 (0 : Word))
          (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [P52_plus_4] at h0'
  have e13F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x7 ↦ᵣ v7) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e13
  -- [14] LI x7,0
  have e14 :
      cpsTripleWithin 1 (P + 56) LoopGuard pseCode
        (.x7 ↦ᵣ v7) (.x7 ↦ᵣ (0 : Word)) := by
    have h0 := li_spec_gen_within .x7 v7 (0 : Word) (P + 56) (by decide)
    have h0' : cpsTripleWithin 1 (P + 56) ((P + 56) + 4) pseCode
        (.x7 ↦ᵣ v7) (.x7 ↦ᵣ (0 : Word)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 56) pseProg 14 (.LI .x7 (0 : Word))
          (by simp only [P, GuestAddrs.eip8037_prior_state_used_exact]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [P56_plus_4] at h0'
  have e14F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ (0 : Word)) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e14
  -- compose
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 e23F
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 e4F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 e5F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 e67F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 e8F
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 e9F
  have c08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c07 e10F
  have c09 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c08 e11F
  have c10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c09 e12F
  have c11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c10 e13F
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c11 e14F
  change cpsTripleWithin
    (1+1+2+1+1+2+1+1+1+1+1+1+1) P LoopGuard pseCode _ _ at c12
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp only [entryPre, nGateSteps] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp only [loopEntry, nGateSteps] at hq ⊢
      xperm_hyp hq) c12

#print axioms eip8037PriorStateUsedExact_gatesToLoop_spec_within

end EvmAsm.Codegen.Eip8037PriorStateUsedExactSpec
