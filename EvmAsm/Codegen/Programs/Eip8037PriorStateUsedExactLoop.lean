/-
  Loop + exit for `eip8037_prior_state_used_exact` (a4gbr residual leaf).
-/

import EvmAsm.Codegen.Programs.Eip8037PriorStateUsedExactSpec
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.Eip8037PriorStateUsedExactLoop

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.Eip8037PriorStateUsedExactSpec
open EvmAsm.Codegen.Eip8037PriorStateUsedExactModel
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom
   shiftLeft3_ofNat)

abbrev P : Word := Eip8037PriorStateUsedExactSpec.P
abbrev pseProg : Program := Eip8037PriorStateUsedExactSpec.pseProg
abbrev pseCode : CodeReq := Eip8037PriorStateUsedExactSpec.pseCode
abbrev LoopGuard : Word := Eip8037PriorStateUsedExactSpec.LoopGuard
abbrev StoreSum : Word := Eip8037PriorStateUsedExactSpec.StoreSum
abbrev OkLi : Word := Eip8037PriorStateUsedExactSpec.OkLi
abbrev OkRet : Word := Eip8037PriorStateUsedExactSpec.OkRet
abbrev FailLi : Word := Eip8037PriorStateUsedExactSpec.FailLi
abbrev TxStateGasAddr : Word := Eip8037PriorStateUsedExactSpec.TxStateGasAddr
abbrev TxStatusAddr : Word := Eip8037PriorStateUsedExactSpec.TxStatusAddr
abbrev TxExecStateGasAddr : Word := Eip8037PriorStateUsedExactSpec.TxExecStateGasAddr
abbrev ExactOkAddr : Word := Eip8037PriorStateUsedExactSpec.ExactOkAddr
abbrev RuntimeCountAddr : Word := Eip8037PriorStateUsedExactSpec.RuntimeCountAddr

theorem pse_length : pseProg.length = 43 := Eip8037PriorStateUsedExactSpec.pse_length

private theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se13_92 : signExtend13 (92 : BitVec 13) = (92 : Word) := by decide

private theorem LoopGuard_plus_92 :
    LoopGuard + signExtend13 (92 : BitVec 13) = StoreSum := by
  simp only [LoopGuard, StoreSum, se13_92]; decide

private theorem StoreSum_plus_4 : StoreSum + 4 = OkLi := by
  simp only [StoreSum, OkLi]; decide

private theorem OkLi_plus_4 : OkLi + 4 = OkRet := by
  simp only [OkLi, OkRet]; decide

/-- Ambient globals framed through the loop (read-only). -/
def loopGlobals (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat) : Assertion :=
  (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW) **
    wordArray TxStateGasAddr stateGas **
    wordArray TxStatusAddr status **
    wordArray TxExecStateGasAddr execGas

theorem pcFree_loopGlobals (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat) :
    (loopGlobals exactOkW runtimeW stateGas status execGas).pcFree := by
  unfold loopGlobals
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_memIs
    | exact pcFree_wordArray _ _

/-- Loop invariant at LoopGuard: i ≤ n, sum = priorPrefixExact ... i as Word. -/
def LoopInv
    (raIn priorW outPtr sumW iW : Word)
    (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (v28 v29 v30 v31 : Word) : Assertion :=
  (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
    (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumW) **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
    loopGlobals exactOkW runtimeW stateGas status execGas

set_option maxRecDepth 8000 in
/-- Guard taken (i=n): BEQ → StoreSum, SD sum, OkRet. -/
theorem pseLoopExitOk
    (raIn priorW outPtr sumW : Word)
    (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (v28 v29 v30 v31 : Word)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 4 LoopGuard raIn pseCode
      (LoopInv raIn priorW outPtr sumW priorW exactOkW runtimeW
        stateGas status execGas v28 v29 v30 v31)
      (postOk raIn outPtr sumW
        ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          loopGlobals exactOkW runtimeW stateGas status execGas)) := by
  have hGpf : (loopGlobals exactOkW runtimeW stateGas status execGas).pcFree :=
    pcFree_loopGlobals exactOkW runtimeW stateGas status execGas
  -- [15] BEQ i,n taken
  have hbr := beq_spec_gen_within .x6 .x5 (92 : BitVec 13) priorW priorW LoopGuard
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at P LoopGuard pseProg 15
      (.BEQ .x6 .x5 (92 : BitVec 13))
      (by simp only [LoopGuard]; decide)
      (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr
  have htk0 := cpsBranchWithin_takenStripPure2 hbrC (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have htk : cpsTripleWithin 1 LoopGuard StoreSum pseCode
      ((.x6 ↦ᵣ priorW) ** (.x5 ↦ᵣ priorW))
      ((.x6 ↦ᵣ priorW) ** (.x5 ↦ᵣ priorW)) := by
    rwa [LoopGuard_plus_92] at htk0
  have e15F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x7 ↦ᵣ sumW) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) htk
  -- [38] SD sum *out
  have haddr : outPtr + signExtend12 (0 : BitVec 12) = outPtr := by
    rw [se12_zero]; exact BitVec.add_zero outPtr
  have e38 :
      cpsTripleWithin 1 StoreSum OkLi pseCode
        ((.x11 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ (0 : Word)))
        ((.x11 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ sumW)) := by
    have h0 := sd_spec_gen_within .x11 .x7 outPtr sumW (0 : Word)
      (0 : BitVec 12) StoreSum
    rw [haddr] at h0
    have h0' : cpsTripleWithin 1 StoreSum (StoreSum + 4) pseCode
        ((.x11 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ (0 : Word)))
        ((.x11 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) ** (outPtr ↦ₘ sumW)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P StoreSum pseProg 38
          (.SD .x11 .x7 (0 : BitVec 12))
          (by simp only [StoreSum]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [StoreSum_plus_4] at h0'
  have e38F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs) e38
  -- Ok ret: a0 was priorW
  have eOk :
      cpsTripleWithin 2 OkLi raIn pseCode
        ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
          (outPtr ↦ₘ sumW) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          loopGlobals exactOkW runtimeW stateGas status execGas)
        (postOk raIn outPtr sumW
          ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
            (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
            loopGlobals exactOkW runtimeW stateGas status execGas)) := by
    have e39 :
        cpsTripleWithin 1 OkLi OkRet pseCode
          (.x10 ↦ᵣ priorW) (.x10 ↦ᵣ (0 : Word)) := by
      have h0 := li_spec_gen_within .x10 priorW (0 : Word) OkLi (by decide)
      have h0' : cpsTripleWithin 1 OkLi (OkLi + 4) pseCode
          (.x10 ↦ᵣ priorW) (.x10 ↦ᵣ (0 : Word)) :=
        cpsTripleWithin_extend_code
          (CodeReq.ofProg_mem_at P OkLi pseProg 39 (.LI .x10 (0 : Word))
            (by simp only [OkLi]; decide)
            (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
      rwa [OkLi_plus_4] at h0'
    have e39F := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ sumW) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        loopGlobals exactOkW runtimeW stateGas status execGas)
      (by
        repeat' first
          | exact hGpf
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
          (by simp only [OkRet]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    have e40F0 := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (outPtr ↦ₘ sumW) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        loopGlobals exactOkW runtimeW stateGas status execGas)
      (by
        repeat' first
          | exact hGpf
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_memIs) e40
    have e40F : cpsTripleWithin 1 OkRet raIn pseCode
        ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
          (outPtr ↦ₘ sumW) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          loopGlobals exactOkW runtimeW stateGas status execGas)
        ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ outPtr) **
          (outPtr ↦ₘ sumW) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          loopGlobals exactOkW runtimeW stateGas status execGas) :=
      cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) e40F0
    have c := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) e39F e40F
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        dsimp only [postOk] at hq ⊢
        xperm_hyp hq) c
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e15F e38F
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01 eOk
  change cpsTripleWithin (1 + 1 + 2) LoopGuard raIn pseCode _ _ at c02
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp only [LoopInv] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c02

#print axioms pseLoopExitOk

end EvmAsm.Codegen.Eip8037PriorStateUsedExactLoop
