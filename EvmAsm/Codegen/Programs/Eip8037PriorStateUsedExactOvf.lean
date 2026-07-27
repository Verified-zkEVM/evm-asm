/-
  Mid-loop overflow fail paths for `eip8037_prior_state_used_exact`.

  Program overflow sites:
    Instr 22 BLTU x31,x7 +76 at P+88  → FailLi (after state_gas ADD)
    Instr 34 BLTU x31,x7 +28 at P+136 → FailLi (after exec_gas ADD)

  On overflow: a0=1, *out stays 0. Classical-3 only.
-/
import EvmAsm.Codegen.Programs.Eip8037PriorStateUsedExactIter
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.Eip8037PriorStateUsedExactOvf

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.Eip8037PriorStateUsedExactModel
open EvmAsm.Codegen.Eip8037PriorStateUsedExactSpec
open EvmAsm.Codegen.Eip8037PriorStateUsedExactLoop
open EvmAsm.Codegen.Eip8037PriorStateUsedExactIter
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom
   shiftLeft3_ofNat)

abbrev P : Word := Eip8037PriorStateUsedExactLoop.P
abbrev pseProg : Program := Eip8037PriorStateUsedExactLoop.pseProg
abbrev pseCode : CodeReq := Eip8037PriorStateUsedExactLoop.pseCode
abbrev LoopGuard : Word := Eip8037PriorStateUsedExactLoop.LoopGuard
abbrev LoopBody : Word := Eip8037PriorStateUsedExactLoop.LoopBody
abbrev AfterSlli : Word := Eip8037PriorStateUsedExactLoop.AfterSlli
abbrev AfterLaState : Word := Eip8037PriorStateUsedExactLoop.AfterLaState
abbrev TxStateGasAddr : Word := Eip8037PriorStateUsedExactLoop.TxStateGasAddr
abbrev TxStatusAddr : Word := Eip8037PriorStateUsedExactLoop.TxStatusAddr
abbrev TxExecStateGasAddr : Word := Eip8037PriorStateUsedExactLoop.TxExecStateGasAddr
abbrev FailLi : Word := Eip8037PriorStateUsedExactSpec.FailLi

theorem pse_length : pseProg.length = 43 := Eip8037PriorStateUsedExactLoop.pse_length

private theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

private theorem AfterLaState_plus_4 : AfterLaState + 4 = P + 80 := by
  simp only [AfterLaState, P]; decide
private theorem P80_plus_4 : (P + 80 : Word) + 4 = P + 84 := by simp only [P]; decide
private theorem P84_plus_4 : (P + 84 : Word) + 4 = P + 88 := by simp only [P]; decide
private theorem P88_plus_4 : (P + 88 : Word) + 4 = P + 92 := by simp only [P]; decide

private theorem ofNat_add_wrap (s g : Nat)
    (hs : s < 2 ^ 64) (hg : g < 2 ^ 64) :
    BitVec.ofNat 64 s + BitVec.ofNat 64 g =
      BitVec.ofNat 64 ((s + g) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hg]
  exact (Nat.mod_eq_of_lt (Nat.mod_lt (s + g) (by decide : 0 < 2 ^ 64))).symm

/-- Detect u64 wrap as Prop: ofNat s + ofNat g ult ofNat s when s+g ≥ 2^64. -/
private theorem ult_add_of_overflow (s g : Nat)
    (hs : s < 2 ^ 64) (hg : g < 2 ^ 64) (hov : 2 ^ 64 ≤ s + g) :
    BitVec.ult (BitVec.ofNat 64 s + BitVec.ofNat 64 g) (BitVec.ofNat 64 s) := by
  have hwrap : (s + g) % 2 ^ 64 = s + g - 2 ^ 64 := by
    have : s + g < 2 * 2 ^ 64 := by omega
    omega
  have hlt_s : (s + g) % 2 ^ 64 < s := by
    rw [hwrap]; omega
  have heq := ofNat_add_wrap s g hs hg
  rw [heq]
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hs,
    Nat.mod_eq_of_lt (Nat.mod_lt (s + g) (by decide : 0 < 2 ^ 64))]
  exact hlt_s

set_option maxRecDepth 8000 in
/-- State-gas overflow fail: LoopGuard → postFail in 10 steps when
    2^64 ≤ sum + stateGas[i]. BLTU taken before status is loaded. -/
theorem pseIterStateOvf
    (raIn priorW outPtr : Word)
    (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (i sum : Nat)
    (v28 v29 v30 v31 : Word)
    (hi : i < stateGas.length)
    (hs : sum < 2 ^ 64)
    (hg : stateGas[i] < 2 ^ 64)
    (hov : 2 ^ 64 ≤ sum + stateGas[i])
    (hne : BitVec.ofNat 64 i ≠ priorW)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    let iW := BitVec.ofNat 64 i
    let sumW := BitVec.ofNat 64 sum
    let offW := BitVec.ofNat 64 (8 * i)
    let gasW := BitVec.ofNat 64 stateGas[i]
    let sumW' := sumW + gasW
    cpsTripleWithin 10 LoopGuard raIn pseCode
      (LoopInv raIn priorW outPtr sumW iW exactOkW runtimeW
        stateGas status execGas v28 v29 v30 v31)
      (postFail raIn outPtr (0 : Word)
        ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumW) **
          (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxStateGasAddr + offW)) **
          (.x30 ↦ᵣ gasW) ** (.x31 ↦ᵣ sumW') **
          loopGlobals exactOkW runtimeW stateGas status execGas)) := by
  intro iW sumW offW gasW sumW'
  have hGpf : (loopGlobals exactOkW runtimeW stateGas status execGas).pcFree :=
    pcFree_loopGlobals exactOkW runtimeW stateGas status execGas
  have hoff : iW <<< 3 = offW := by
    simpa [iW, offW] using shiftLeft3_ofNat i
  have hUlt : BitVec.ult sumW' sumW := by
    simpa [sumW, sumW', gasW] using ult_add_of_overflow sum stateGas[i] hs hg hov
  have hsplit := wordArray_split TxStateGasAddr stateGas i hi
  have haddrState :
      TxStateGasAddr + BitVec.ofNat 64 (8 * i) = TxStateGasAddr + offW := by
    simp only [offW]
  -- 1. guard ntaken
  have hguard := pseLoopGuardNtaken raIn priorW outPtr sumW iW exactOkW runtimeW
    stateGas status execGas v28 v29 v30 v31 hne
  -- 2. SLLI x28 = 8*i
  have e16 :
      cpsTripleWithin 1 LoopBody AfterSlli pseCode
        ((.x6 ↦ᵣ iW) ** (.x28 ↦ᵣ v28))
        ((.x6 ↦ᵣ iW) ** (.x28 ↦ᵣ offW)) := by
    have h0 := slli_spec_gen_within .x28 .x6 v28 iW (3 : BitVec 6) LoopBody (by decide)
    have h0' : cpsTripleWithin 1 LoopBody (LoopBody + 4) pseCode
        ((.x6 ↦ᵣ iW) ** (.x28 ↦ᵣ v28))
        ((.x6 ↦ᵣ iW) ** (.x28 ↦ᵣ (iW <<< 3))) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P LoopBody pseProg 16
          (.SLLI .x28 .x6 (3 : BitVec 6))
          (by simp only [LoopBody]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    have h0'' : cpsTripleWithin 1 LoopBody AfterSlli pseCode
        ((.x6 ↦ᵣ iW) ** (.x28 ↦ᵣ v28))
        ((.x6 ↦ᵣ iW) ** (.x28 ↦ᵣ (iW <<< 3))) := by
      rwa [show LoopBody + 4 = AfterSlli from by simp only [LoopBody, AfterSlli]; decide] at h0'
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by rw [← hoff]; exact hq) h0''
  have e16F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW) **
      (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e16
  -- 3. la state → x29
  have eLa := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumW) **
      (.x28 ↦ᵣ offW) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) (pseLaStateGas v29)
  -- 4. ADD x29 += x28
  have e19 :
      cpsTripleWithin 1 AfterLaState (P + 80) pseCode
        ((.x29 ↦ᵣ TxStateGasAddr) ** (.x28 ↦ᵣ offW))
        ((.x29 ↦ᵣ (TxStateGasAddr + offW)) ** (.x28 ↦ᵣ offW)) := by
    have h0 := add_spec_gen_rd_eq_rs1_within .x29 .x28 TxStateGasAddr offW AfterLaState (by decide)
    have h0' : cpsTripleWithin 1 AfterLaState (AfterLaState + 4) pseCode
        ((.x29 ↦ᵣ TxStateGasAddr) ** (.x28 ↦ᵣ offW))
        ((.x29 ↦ᵣ (TxStateGasAddr + offW)) ** (.x28 ↦ᵣ offW)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P AfterLaState pseProg 19
          (.ADD .x29 .x29 .x28)
          (by simp only [AfterLaState]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [AfterLaState_plus_4] at h0'
  have e19F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumW) **
      (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e19
  -- 5. LD state cell
  have e20core :
      cpsTripleWithin 1 (P + 80) (P + 84) pseCode
        ((.x29 ↦ᵣ (TxStateGasAddr + offW)) ** (.x30 ↦ᵣ v30) **
          ((TxStateGasAddr + offW) ↦ₘ gasW))
        ((.x29 ↦ᵣ (TxStateGasAddr + offW)) ** (.x30 ↦ᵣ gasW) **
          ((TxStateGasAddr + offW) ↦ₘ gasW)) := by
    have haddr : (TxStateGasAddr + offW) + signExtend12 (0 : BitVec 12) =
        TxStateGasAddr + offW := by
      rw [se12_zero]; exact BitVec.add_zero _
    have h0 := ld_spec_gen_within .x30 .x29 (TxStateGasAddr + offW) v30
      gasW (0 : BitVec 12) (P + 80) (by decide)
    rw [haddr] at h0
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at P (P + 80) pseProg 20
        (.LD .x30 .x29 (0 : BitVec 12))
        (by simp only [P]; decide)
        (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
  have e20F0 := cpsTripleWithin_frameR
    (wordArrayFrom TxStateGasAddr 0 (stateGas.take i) **
      wordArrayFrom TxStateGasAddr (i + 1) (stateGas.drop (i + 1)) **
      wordArray TxStatusAddr status **
      wordArray TxExecStateGasAddr execGas **
      loopGlobalsCore exactOkW runtimeW **
      (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumW) **
      (.x28 ↦ᵣ offW) ** (.x31 ↦ᵣ v31))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact pcFree_wordArray _ _
        | exact pcFree_wordArrayFrom _ _ _) e20core
  have e20F : cpsTripleWithin 1 (P + 80) (P + 84) pseCode
      ((.x29 ↦ᵣ (TxStateGasAddr + offW)) ** (.x30 ↦ᵣ v30) **
        (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumW) **
        (.x28 ↦ᵣ offW) ** (.x31 ↦ᵣ v31) **
        loopGlobals exactOkW runtimeW stateGas status execGas)
      ((.x29 ↦ᵣ (TxStateGasAddr + offW)) ** (.x30 ↦ᵣ gasW) **
        (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumW) **
        (.x28 ↦ᵣ offW) ** (.x31 ↦ᵣ v31) **
        loopGlobals exactOkW runtimeW stateGas status execGas) := by
    refine cpsTripleWithin_weaken ?_ ?_ e20F0
    · intro s hp
      have hp' := hp
      rw [loopGlobals_eq, hsplit, haddrState] at hp'
      xperm_hyp hp'
    · intro s hq
      have hq' := hq
      rw [loopGlobals_eq, hsplit, haddrState]
      xperm_hyp hq'
  -- 6. ADD x31 = sum + gas  (args: rd rs1 rs2 v_rs1 v_rs2 v_rd_old)
  have e21 :
      cpsTripleWithin 1 (P + 84) (P + 88) pseCode
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ gasW) ** (.x31 ↦ᵣ v31))
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ gasW) ** (.x31 ↦ᵣ sumW')) := by
    have h0 := add_spec_gen_within .x31 .x7 .x30 sumW gasW v31 (P + 84) (by decide)
    have h0' : cpsTripleWithin 1 (P + 84) (P + 84 + 4) pseCode
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ gasW) ** (.x31 ↦ᵣ v31))
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ gasW) ** (.x31 ↦ᵣ (sumW + gasW))) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 84) pseProg 21
          (.ADD .x31 .x7 .x30)
          (by simp only [P]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    have h0'' : cpsTripleWithin 1 (P + 84) (P + 88) pseCode
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ gasW) ** (.x31 ↦ᵣ v31))
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ gasW) ** (.x31 ↦ᵣ (sumW + gasW))) := by
      rwa [P84_plus_4] at h0'
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by simpa [sumW'] using hq) h0''
  have e21F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) **
      (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxStateGasAddr + offW)) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e21
  -- 7. BLTU taken → FailLi (offset is BitVec 13)
  have e22tk : cpsTripleWithin 1 (P + 88) FailLi pseCode
      ((.x31 ↦ᵣ sumW') ** (.x7 ↦ᵣ sumW))
      ((.x31 ↦ᵣ sumW') ** (.x7 ↦ᵣ sumW)) := by
    have hbr := bltu_spec_gen_within .x31 .x7 (76 : BitVec 13) sumW' sumW (P + 88)
    have hbrC := cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at P (P + 88) pseProg 22
        (.BLTU .x31 .x7 (76 : BitVec 13))
        (by simp only [P]; decide)
        (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr
    have htk0 := cpsBranchWithin_takenStripPure2 hbrC (fun _ hq => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hq
      exact ((sepConj_pure_right _).1 hrest).2 hUlt)
    have hpc : (P + 88) + signExtend13 (76 : BitVec 13) = FailLi := by
      simp only [P, FailLi]; decide
    rwa [hpc] at htk0
  have e22tkF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) **
      (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxStateGasAddr + offW)) **
      (.x30 ↦ᵣ gasW) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e22tk
  -- 8-9. fail ret; x10 and x5 both priorW (pseFailRet pins both as v5)
  have eFail :=
    pseFailRet_spec raIn outPtr (0 : Word)
      priorW iW sumW offW (TxStateGasAddr + offW) gasW sumW' hret
  have eFailF := cpsTripleWithin_frameR
    (loopGlobals exactOkW runtimeW stateGas status execGas)
    (by exact hGpf) eFail
  -- Compose (seq_perm_same_cr: hperm Q1→Q2, h1, h2)
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp only [LoopInv] at hp; xperm_hyp hp) hguard e16F
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 eLa
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 e19F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 e20F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 e21F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 e22tkF
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 eFailF
  change cpsTripleWithin (1+1+2+1+1+1+1+2) LoopGuard raIn pseCode _ _ at c07
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp only [LoopInv] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by
      dsimp only [postFail] at hq ⊢
      xperm_hyp hq) c07

#print axioms pseIterStateOvf

end EvmAsm.Codegen.Eip8037PriorStateUsedExactOvf
