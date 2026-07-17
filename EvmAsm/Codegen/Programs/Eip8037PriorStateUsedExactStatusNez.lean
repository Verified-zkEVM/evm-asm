/-
  Status≠0 one-iter for `eip8037_prior_state_used_exact` (exec gas path).
-/

import EvmAsm.Codegen.Programs.Eip8037PriorStateUsedExactIter
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.Eip8037PriorStateUsedExactStatusNez

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.Eip8037PriorStateUsedExactModel
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
abbrev AfterMvSum : Word := Eip8037PriorStateUsedExactLoop.AfterMvSum
abbrev AfterLaStatus : Word := Eip8037PriorStateUsedExactLoop.AfterLaStatus
abbrev AfterLdStatus : Word := Eip8037PriorStateUsedExactLoop.AfterLdStatus
abbrev AfterStatusSkip : Word := Eip8037PriorStateUsedExactLoop.AfterStatusSkip
abbrev AfterIncr : Word := Eip8037PriorStateUsedExactLoop.AfterIncr
abbrev AfterStatusBne : Word := Eip8037PriorStateUsedExactLoop.AfterStatusBne
abbrev AfterLaExec : Word := Eip8037PriorStateUsedExactLoop.AfterLaExec
abbrev TxStateGasAddr : Word := Eip8037PriorStateUsedExactLoop.TxStateGasAddr
abbrev TxStatusAddr : Word := Eip8037PriorStateUsedExactLoop.TxStatusAddr
abbrev TxExecStateGasAddr : Word := Eip8037PriorStateUsedExactLoop.TxExecStateGasAddr

theorem pse_length : pseProg.length = 43 := Eip8037PriorStateUsedExactLoop.pse_length

private theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_one : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se13_32 : signExtend13 (32 : BitVec 13) = (32 : Word) := by decide
private theorem se21_m88 : signExtend21 (-88 : BitVec 21) = BitVec.ofInt 64 (-88) := by decide

private theorem ofNat_addi1 (i : Nat) :
    BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 (i + 1) := by
  rw [se12_one, BitVec.ofNat_add]; rfl

private theorem ofNat_add_lt (a b : Nat) (h : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  have ha : a < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right a b) h
  have hb : b < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left b a) h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt h]

private theorem not_ult_add (s g : Nat) (h : s + g < 2 ^ 64) :
    ¬BitVec.ult (BitVec.ofNat 64 (s + g)) (BitVec.ofNat 64 s) := by
  have hs : s < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right s g) h
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt h]
  omega

private theorem AfterLdStatus_plus_4 : AfterLdStatus + 4 = AfterStatusBne := by
  simp only [AfterLdStatus, AfterStatusBne]; decide
private theorem AfterLaExec_plus_4 : AfterLaExec + 4 = P + 128 := by
  simp only [AfterLaExec, P]; decide
private theorem AfterLaState_plus_4 : AfterLaState + 4 = P + 80 := by
  simp only [AfterLaState, P]; decide
private theorem AfterLaStatus_plus_4 : AfterLaStatus + 4 = P + 108 := by
  simp only [AfterLaStatus, P]; decide
private theorem AfterStatusSkip_plus_4 : AfterStatusSkip + 4 = AfterIncr := by
  simp only [AfterStatusSkip, AfterIncr]; decide
private theorem AfterIncr_back :
    AfterIncr + signExtend21 (-88 : BitVec 21) = LoopGuard := by
  simp only [AfterIncr, LoopGuard, se21_m88]
  decide
private theorem P80_plus_4 : (P + 80 : Word) + 4 = P + 84 := by simp only [P]; decide
private theorem P84_plus_4 : (P + 84 : Word) + 4 = P + 88 := by simp only [P]; decide
private theorem P88_plus_4 : (P + 88 : Word) + 4 = P + 92 := by simp only [P]; decide
private theorem P92_plus_4 : (P + 92 : Word) + 4 = AfterMvSum := by
  simp only [AfterMvSum, P]; decide
private theorem P108_plus_4 : (P + 108 : Word) + 4 = AfterLdStatus := by
  simp only [AfterLdStatus, P]; decide
private theorem P128_plus_4 : (P + 128 : Word) + 4 = P + 132 := by simp only [P]; decide
private theorem P132_plus_4 : (P + 132 : Word) + 4 = P + 136 := by simp only [P]; decide
private theorem P136_plus_4 : (P + 136 : Word) + 4 = P + 140 := by simp only [P]; decide
private theorem P140_plus_4 : (P + 140 : Word) + 4 = AfterStatusSkip := by
  simp only [AfterStatusSkip, P]; decide

set_option maxRecDepth 8000 in
/-- Status≠0 one-iter: LoopGuard → LoopGuard, sum+=state+exec, i+=1.
    Requires status[i]≠0 and no u64 overflow on state or exec adds. -/
theorem pseIterStatusNez
    (raIn priorW outPtr : Word)
    (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (i sum : Nat)
    (v28 v29 v30 v31 : Word)
    (hi : i < stateGas.length)
    (hstat : i < status.length)
    (hexec : i < execGas.length)
    (hstatNe : status[i] ≠ 0)
    (hstatBound : status[i] < 2 ^ 64)
    (hno : sum + stateGas[i] < 2 ^ 64)
    (hnoE : sum + stateGas[i] + execGas[i] < 2 ^ 64)
    (hne : BitVec.ofNat 64 i ≠ priorW) :
    let iW := BitVec.ofNat 64 i
    let sumW := BitVec.ofNat 64 sum
    let sumW' := BitVec.ofNat 64 (sum + stateGas[i] + execGas[i])
    let iW' := BitVec.ofNat 64 (i + 1)
    let offW := BitVec.ofNat 64 (8 * i)
    cpsTripleWithin 23 LoopGuard LoopGuard pseCode
      (LoopInv raIn priorW outPtr sumW iW exactOkW runtimeW
        stateGas status execGas v28 v29 v30 v31)
      (LoopInv raIn priorW outPtr sumW' iW' exactOkW runtimeW
        stateGas status execGas offW
          (TxExecStateGasAddr + offW) (BitVec.ofNat 64 execGas[i]) sumW') := by
  intro iW sumW sumW' iW' offW
  let sumS := BitVec.ofNat 64 (sum + stateGas[i])
  have hGpf : (loopGlobals exactOkW runtimeW stateGas status execGas).pcFree :=
    pcFree_loopGlobals exactOkW runtimeW stateGas status execGas
  have hsumAdd : sumW + BitVec.ofNat 64 stateGas[i] = sumS := by
    simpa [sumW, sumS] using ofNat_add_lt sum stateGas[i] hno
  have hnoUlt : ¬BitVec.ult sumS sumW := by
    simpa [sumW, sumS] using not_ult_add sum stateGas[i] hno
  have hsumAddE : sumS + BitVec.ofNat 64 execGas[i] = sumW' := by
    simpa [sumS, sumW'] using ofNat_add_lt (sum + stateGas[i]) execGas[i] hnoE
  have hnoUltE : ¬BitVec.ult sumW' sumS := by
    simpa [sumS, sumW'] using not_ult_add (sum + stateGas[i]) execGas[i] hnoE
  have hoff : iW <<< 3 = offW := by
    simpa [iW, offW] using shiftLeft3_ofNat i
  have hstatW : BitVec.ofNat 64 status[i] ≠ (0 : Word) := by
    intro heq
    have hmod : status[i] % 2 ^ 64 = 0 := by
      have := congrArg BitVec.toNat heq
      simpa [BitVec.toNat_ofNat, BitVec.toNat_zero] using this
    have : status[i] = 0 := by
      have := Nat.mod_eq_of_lt hstatBound
      omega
    exact hstatNe this
  have hsplit := wordArray_split TxStateGasAddr stateGas i hi
  have hsplitS := wordArray_split TxStatusAddr status i hstat
  have haddrState :
      TxStateGasAddr + BitVec.ofNat 64 (8 * i) = TxStateGasAddr + offW := by
    simp only [offW]
  have haddrStatus :
      TxStatusAddr + BitVec.ofNat 64 (8 * i) = TxStatusAddr + offW := by
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
  -- 3. la state → x29 = TxStateGasAddr
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
          ((TxStateGasAddr + offW) ↦ₘ BitVec.ofNat 64 stateGas[i]))
        ((.x29 ↦ᵣ (TxStateGasAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) **
          ((TxStateGasAddr + offW) ↦ₘ BitVec.ofNat 64 stateGas[i])) := by
    have haddr : (TxStateGasAddr + offW) + signExtend12 (0 : BitVec 12) =
        TxStateGasAddr + offW := by
      rw [se12_zero]; exact BitVec.add_zero _
    have h0 := ld_spec_gen_within .x30 .x29 (TxStateGasAddr + offW) v30
      (BitVec.ofNat 64 stateGas[i]) (0 : BitVec 12) (P + 80) (by decide)
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
      ((.x29 ↦ᵣ (TxStateGasAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) **
        (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumW) **
        (.x28 ↦ᵣ offW) ** (.x31 ↦ᵣ v31) **
        loopGlobals exactOkW runtimeW stateGas status execGas) := by
    refine cpsTripleWithin_weaken ?_ ?_ e20F0
    · intro _ hp
      have hp' := hp
      rw [loopGlobals_eq, hsplit, haddrState] at hp'
      xperm_hyp hp'
    · intro _ hq
      have hq' := hq
      rw [loopGlobals_eq, hsplit, haddrState]
      xperm_hyp hq'
  -- 6. ADD x31 = sum + state
  have e21 :
      cpsTripleWithin 1 (P + 84) (P + 88) pseCode
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) ** (.x31 ↦ᵣ v31))
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) ** (.x31 ↦ᵣ sumS)) := by
    have h0 := add_spec_gen_within .x31 .x7 .x30 sumW (BitVec.ofNat 64 stateGas[i]) v31
      (P + 84) (by decide)
    have h0' : cpsTripleWithin 1 (P + 84) (P + 84 + 4) pseCode
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) ** (.x31 ↦ᵣ v31))
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) **
          (.x31 ↦ᵣ (sumW + BitVec.ofNat 64 stateGas[i]))) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 84) pseProg 21
          (.ADD .x31 .x7 .x30)
          (by simp only [P]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    have h0'' : cpsTripleWithin 1 (P + 84) (P + 88) pseCode
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) ** (.x31 ↦ᵣ v31))
        ((.x7 ↦ᵣ sumW) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) **
          (.x31 ↦ᵣ (sumW + BitVec.ofNat 64 stateGas[i]))) := by
      rwa [P84_plus_4] at h0'
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by rw [← hsumAdd]; exact hq) h0''
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
  -- 7. BLTU overflow ntaken
  have e22 :
      cpsTripleWithin 1 (P + 88) (P + 92) pseCode
        ((.x31 ↦ᵣ sumS) ** (.x7 ↦ᵣ sumW))
        ((.x31 ↦ᵣ sumS) ** (.x7 ↦ᵣ sumW)) := by
    have hbr := bltu_spec_gen_within .x31 .x7 (76 : BitVec 13) sumS sumW (P + 88)
    have hbrC := cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at P (P + 88) pseProg 22
        (.BLTU .x31 .x7 (76 : BitVec 13))
        (by simp only [P]; decide)
        (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr
    have hnt0 := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hq => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hq
      exact absurd ((sepConj_pure_right _).1 hrest).2 hnoUlt)
    rwa [P88_plus_4] at hnt0
  have e22F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) **
      (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxStateGasAddr + offW)) **
      (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e22
  -- 8. MV x7, x31
  have e23 :
      cpsTripleWithin 1 (P + 92) AfterMvSum pseCode
        ((.x31 ↦ᵣ sumS) ** (.x7 ↦ᵣ sumW))
        ((.x31 ↦ᵣ sumS) ** (.x7 ↦ᵣ sumS)) := by
    have h0 := mv_spec_gen_within .x7 .x31 sumS sumW (P + 92) (by decide)
    have h0' : cpsTripleWithin 1 (P + 92) (P + 92 + 4) pseCode
        ((.x31 ↦ᵣ sumS) ** (.x7 ↦ᵣ sumW))
        ((.x31 ↦ᵣ sumS) ** (.x7 ↦ᵣ sumS)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 92) pseProg 23
          (.MV .x7 .x31)
          (by simp only [P]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [P92_plus_4] at h0'
  have e23F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) **
      (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxStateGasAddr + offW)) **
      (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e23
  -- 9. la status
  have eLaSt := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
      (.x28 ↦ᵣ offW) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) **
      (.x31 ↦ᵣ sumS) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs)
    (pseLaStatus (TxStateGasAddr + offW))
  -- 10. ADD x29 += x28
  have e26 :
      cpsTripleWithin 1 AfterLaStatus (P + 108) pseCode
        ((.x29 ↦ᵣ TxStatusAddr) ** (.x28 ↦ᵣ offW))
        ((.x29 ↦ᵣ (TxStatusAddr + offW)) ** (.x28 ↦ᵣ offW)) := by
    have h0 := add_spec_gen_rd_eq_rs1_within .x29 .x28 TxStatusAddr offW AfterLaStatus (by decide)
    have h0' : cpsTripleWithin 1 AfterLaStatus (AfterLaStatus + 4) pseCode
        ((.x29 ↦ᵣ TxStatusAddr) ** (.x28 ↦ᵣ offW))
        ((.x29 ↦ᵣ (TxStatusAddr + offW)) ** (.x28 ↦ᵣ offW)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P AfterLaStatus pseProg 26
          (.ADD .x29 .x29 .x28)
          (by simp only [AfterLaStatus]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [AfterLaStatus_plus_4] at h0'
  have e26F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
      (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) ** (.x31 ↦ᵣ sumS) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e26
  -- 11. LD status
  have e27core :
      cpsTripleWithin 1 (P + 108) AfterLdStatus pseCode
        ((.x29 ↦ᵣ (TxStatusAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) **
          ((TxStatusAddr + offW) ↦ₘ BitVec.ofNat 64 status[i]))
        ((.x29 ↦ᵣ (TxStatusAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 status[i]) **
          ((TxStatusAddr + offW) ↦ₘ BitVec.ofNat 64 status[i])) := by
    have haddr : (TxStatusAddr + offW) + signExtend12 (0 : BitVec 12) =
        TxStatusAddr + offW := by
      rw [se12_zero]; exact BitVec.add_zero _
    have h0 := ld_spec_gen_within .x30 .x29 (TxStatusAddr + offW)
      (BitVec.ofNat 64 stateGas[i]) (BitVec.ofNat 64 status[i])
      (0 : BitVec 12) (P + 108) (by decide)
    rw [haddr] at h0
    have h0' : cpsTripleWithin 1 (P + 108) (P + 108 + 4) pseCode
        ((.x29 ↦ᵣ (TxStatusAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) **
          ((TxStatusAddr + offW) ↦ₘ BitVec.ofNat 64 status[i]))
        ((.x29 ↦ᵣ (TxStatusAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 status[i]) **
          ((TxStatusAddr + offW) ↦ₘ BitVec.ofNat 64 status[i])) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 108) pseProg 27
          (.LD .x30 .x29 (0 : BitVec 12))
          (by simp only [P]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [P108_plus_4] at h0'
  have e27F0 := cpsTripleWithin_frameR
    (wordArrayFrom TxStatusAddr 0 (status.take i) **
      wordArrayFrom TxStatusAddr (i + 1) (status.drop (i + 1)) **
      wordArray TxStateGasAddr stateGas **
      wordArray TxExecStateGasAddr execGas **
      loopGlobalsCore exactOkW runtimeW **
      (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
      (.x28 ↦ᵣ offW) ** (.x31 ↦ᵣ sumS))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact pcFree_wordArray _ _
        | exact pcFree_wordArrayFrom _ _ _) e27core
  have e27F : cpsTripleWithin 1 (P + 108) AfterLdStatus pseCode
      ((.x29 ↦ᵣ (TxStatusAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 stateGas[i]) **
        (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
        (.x28 ↦ᵣ offW) ** (.x31 ↦ᵣ sumS) **
        loopGlobals exactOkW runtimeW stateGas status execGas)
      ((.x29 ↦ᵣ (TxStatusAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 status[i]) **
        (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
        (.x28 ↦ᵣ offW) ** (.x31 ↦ᵣ sumS) **
        loopGlobals exactOkW runtimeW stateGas status execGas) := by
    refine cpsTripleWithin_weaken ?_ ?_ e27F0
    · intro _ hp
      have hp' := hp
      rw [loopGlobals_eq, hsplitS, haddrStatus] at hp'
      xperm_hyp hp'
    · intro _ hq
      have hq' := hq
      rw [loopGlobals_eq, hsplitS, haddrStatus]
      xperm_hyp hq'
  have hsplitE := wordArray_split TxExecStateGasAddr execGas i hexec
  have haddrExec :
      TxExecStateGasAddr + BitVec.ofNat 64 (8 * i) = TxExecStateGasAddr + offW := by
    simp only [offW]
  -- 12. BEQ status=0 ntaken (status ≠ 0)
  have e28 :
      cpsTripleWithin 1 AfterLdStatus AfterStatusBne pseCode
        ((.x30 ↦ᵣ BitVec.ofNat 64 status[i]) ** (.x0 ↦ᵣ (0 : Word)))
        ((.x30 ↦ᵣ BitVec.ofNat 64 status[i]) ** (.x0 ↦ᵣ (0 : Word))) := by
    have hbr := beq_spec_gen_within .x30 .x0 (32 : BitVec 13)
      (BitVec.ofNat 64 status[i]) (0 : Word) AfterLdStatus
    have hbrC := cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at P AfterLdStatus pseProg 28
        (.BEQ .x30 .x0 (32 : BitVec 13))
        (by simp only [AfterLdStatus]; decide)
        (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr
    have hnt0 := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hq => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hq
      exact absurd ((sepConj_pure_right _).1 hrest).2 hstatW)
    rwa [AfterLdStatus_plus_4] at hnt0
  have e28F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
      (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxStatusAddr + offW)) **
      (.x31 ↦ᵣ sumS) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e28
  -- 13. la exec
  have eLaEx := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
      (.x28 ↦ᵣ offW) ** (.x30 ↦ᵣ BitVec.ofNat 64 status[i]) **
      (.x31 ↦ᵣ sumS) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs)
    (pseLaExec (TxStatusAddr + offW))
  -- 14. ADD x29 += x28
  have e31 :
      cpsTripleWithin 1 AfterLaExec (P + 128) pseCode
        ((.x29 ↦ᵣ TxExecStateGasAddr) ** (.x28 ↦ᵣ offW))
        ((.x29 ↦ᵣ (TxExecStateGasAddr + offW)) ** (.x28 ↦ᵣ offW)) := by
    have h0 := add_spec_gen_rd_eq_rs1_within .x29 .x28 TxExecStateGasAddr offW AfterLaExec (by decide)
    have h0' : cpsTripleWithin 1 AfterLaExec (AfterLaExec + 4) pseCode
        ((.x29 ↦ᵣ TxExecStateGasAddr) ** (.x28 ↦ᵣ offW))
        ((.x29 ↦ᵣ (TxExecStateGasAddr + offW)) ** (.x28 ↦ᵣ offW)) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P AfterLaExec pseProg 31
          (.ADD .x29 .x29 .x28)
          (by simp only [AfterLaExec]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [AfterLaExec_plus_4] at h0'
  have e31F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
      (.x30 ↦ᵣ BitVec.ofNat 64 status[i]) ** (.x31 ↦ᵣ sumS) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e31
  -- 15. LD exec cell
  have e32core :
      cpsTripleWithin 1 (P + 128) (P + 132) pseCode
        ((.x29 ↦ᵣ (TxExecStateGasAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 status[i]) **
          ((TxExecStateGasAddr + offW) ↦ₘ BitVec.ofNat 64 execGas[i]))
        ((.x29 ↦ᵣ (TxExecStateGasAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) **
          ((TxExecStateGasAddr + offW) ↦ₘ BitVec.ofNat 64 execGas[i])) := by
    have haddr : (TxExecStateGasAddr + offW) + signExtend12 (0 : BitVec 12) =
        TxExecStateGasAddr + offW := by
      rw [se12_zero]; exact BitVec.add_zero _
    have h0 := ld_spec_gen_within .x30 .x29 (TxExecStateGasAddr + offW)
      (BitVec.ofNat 64 status[i]) (BitVec.ofNat 64 execGas[i])
      (0 : BitVec 12) (P + 128) (by decide)
    rw [haddr] at h0
    have h0' : cpsTripleWithin 1 (P + 128) (P + 128 + 4) pseCode
        ((.x29 ↦ᵣ (TxExecStateGasAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 status[i]) **
          ((TxExecStateGasAddr + offW) ↦ₘ BitVec.ofNat 64 execGas[i]))
        ((.x29 ↦ᵣ (TxExecStateGasAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) **
          ((TxExecStateGasAddr + offW) ↦ₘ BitVec.ofNat 64 execGas[i])) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 128) pseProg 32
          (.LD .x30 .x29 (0 : BitVec 12))
          (by simp only [P]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [P128_plus_4] at h0'
  have e32F0 := cpsTripleWithin_frameR
    (wordArrayFrom TxExecStateGasAddr 0 (execGas.take i) **
      wordArrayFrom TxExecStateGasAddr (i + 1) (execGas.drop (i + 1)) **
      wordArray TxStateGasAddr stateGas **
      wordArray TxStatusAddr status **
      loopGlobalsCore exactOkW runtimeW **
      (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
      (.x28 ↦ᵣ offW) ** (.x31 ↦ᵣ sumS))
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact pcFree_wordArray _ _
        | exact pcFree_wordArrayFrom _ _ _) e32core
  have e32F : cpsTripleWithin 1 (P + 128) (P + 132) pseCode
      ((.x29 ↦ᵣ (TxExecStateGasAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 status[i]) **
        (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
        (.x28 ↦ᵣ offW) ** (.x31 ↦ᵣ sumS) **
        loopGlobals exactOkW runtimeW stateGas status execGas)
      ((.x29 ↦ᵣ (TxExecStateGasAddr + offW)) ** (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) **
        (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
        (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) ** (.x7 ↦ᵣ sumS) **
        (.x28 ↦ᵣ offW) ** (.x31 ↦ᵣ sumS) **
        loopGlobals exactOkW runtimeW stateGas status execGas) := by
    refine cpsTripleWithin_weaken ?_ ?_ e32F0
    · intro _ hp
      have hp' := hp
      rw [loopGlobals_eq, hsplitE, haddrExec] at hp'
      xperm_hyp hp'
    · intro _ hq
      have hq' := hq
      rw [loopGlobals_eq, hsplitE, haddrExec]
      xperm_hyp hq'
  -- 16. ADD x31 = sumS + exec
  have e33 :
      cpsTripleWithin 1 (P + 132) (P + 136) pseCode
        ((.x7 ↦ᵣ sumS) ** (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) ** (.x31 ↦ᵣ sumS))
        ((.x7 ↦ᵣ sumS) ** (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) ** (.x31 ↦ᵣ sumW')) := by
    have h0 := add_spec_gen_within .x31 .x7 .x30 sumS (BitVec.ofNat 64 execGas[i]) sumS
      (P + 132) (by decide)
    have h0' : cpsTripleWithin 1 (P + 132) (P + 132 + 4) pseCode
        ((.x7 ↦ᵣ sumS) ** (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) ** (.x31 ↦ᵣ sumS))
        ((.x7 ↦ᵣ sumS) ** (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) **
          (.x31 ↦ᵣ (sumS + BitVec.ofNat 64 execGas[i]))) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 132) pseProg 33
          (.ADD .x31 .x7 .x30)
          (by simp only [P]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    have h0'' : cpsTripleWithin 1 (P + 132) (P + 136) pseCode
        ((.x7 ↦ᵣ sumS) ** (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) ** (.x31 ↦ᵣ sumS))
        ((.x7 ↦ᵣ sumS) ** (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) **
          (.x31 ↦ᵣ (sumS + BitVec.ofNat 64 execGas[i]))) := by
      rwa [P132_plus_4] at h0'
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by rw [← hsumAddE]; exact hq) h0''
  have e33F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) **
      (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxExecStateGasAddr + offW)) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e33
  -- 17. BLTU overflow ntaken on exec add
  have e34 :
      cpsTripleWithin 1 (P + 136) (P + 140) pseCode
        ((.x31 ↦ᵣ sumW') ** (.x7 ↦ᵣ sumS))
        ((.x31 ↦ᵣ sumW') ** (.x7 ↦ᵣ sumS)) := by
    have hbr := bltu_spec_gen_within .x31 .x7 (28 : BitVec 13) sumW' sumS (P + 136)
    have hbrC := cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at P (P + 136) pseProg 34
        (.BLTU .x31 .x7 (28 : BitVec 13))
        (by simp only [P]; decide)
        (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) hbr
    have hnt0 := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hq => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hq
      exact absurd ((sepConj_pure_right _).1 hrest).2 hnoUltE)
    rwa [P136_plus_4] at hnt0
  have e34F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) **
      (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxExecStateGasAddr + offW)) **
      (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e34
  -- 18. MV x7, x31
  have e35 :
      cpsTripleWithin 1 (P + 140) AfterStatusSkip pseCode
        ((.x31 ↦ᵣ sumW') ** (.x7 ↦ᵣ sumS))
        ((.x31 ↦ᵣ sumW') ** (.x7 ↦ᵣ sumW')) := by
    have h0 := mv_spec_gen_within .x7 .x31 sumW' sumS (P + 140) (by decide)
    have h0' : cpsTripleWithin 1 (P + 140) (P + 140 + 4) pseCode
        ((.x31 ↦ᵣ sumW') ** (.x7 ↦ᵣ sumS))
        ((.x31 ↦ᵣ sumW') ** (.x7 ↦ᵣ sumW')) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P (P + 140) pseProg 35
          (.MV .x7 .x31)
          (by simp only [P]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [P140_plus_4] at h0'
  have e35F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW) **
      (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxExecStateGasAddr + offW)) **
      (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e35
  -- 19. ADDI i++
  have e36 :
      cpsTripleWithin 1 AfterStatusSkip AfterIncr pseCode
        (.x6 ↦ᵣ iW) (.x6 ↦ᵣ iW') := by
    have h0 := addi_spec_gen_same_within .x6 iW (1 : BitVec 12) AfterStatusSkip (by decide)
    have h0' : cpsTripleWithin 1 AfterStatusSkip (AfterStatusSkip + 4) pseCode
        (.x6 ↦ᵣ iW) (.x6 ↦ᵣ (iW + signExtend12 (1 : BitVec 12))) :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P AfterStatusSkip pseProg 36
          (.ADDI .x6 .x6 (1 : BitVec 12))
          (by simp only [AfterStatusSkip]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    have h0'' : cpsTripleWithin 1 AfterStatusSkip AfterIncr pseCode
        (.x6 ↦ᵣ iW) (.x6 ↦ᵣ (iW + signExtend12 (1 : BitVec 12))) := by
      rwa [AfterStatusSkip_plus_4] at h0'
    exact cpsTripleWithin_weaken (fun _ hp => hp)
      (fun _ hq => by
        have hadd : iW + signExtend12 (1 : BitVec 12) = iW' := by
          simpa [iW, iW'] using ofNat_addi1 i
        rw [hadd] at hq
        exact hq) h0''
  have e36F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x7 ↦ᵣ sumW') **
      (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxExecStateGasAddr + offW)) **
      (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) ** (.x31 ↦ᵣ sumW') **
      loopGlobals exactOkW runtimeW stateGas status execGas)
    (by
      repeat' first
        | exact hGpf
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs) e36
  -- 20. JAL back
  have e37 :
      cpsTripleWithin 1 AfterIncr LoopGuard pseCode
        empAssertion empAssertion := by
    have h0 := jal_x0_spec_gen_within (-88 : BitVec 21) AfterIncr
    have h0' : cpsTripleWithin 1 AfterIncr
        (AfterIncr + signExtend21 (-88 : BitVec 21)) pseCode
        empAssertion empAssertion :=
      cpsTripleWithin_extend_code
        (CodeReq.ofProg_mem_at P AfterIncr pseProg 37
          (.JAL .x0 (-88 : BitVec 21))
          (by simp only [AfterIncr]; decide)
          (by rw [pse_length]; decide) rfl (by rw [pse_length]; decide)) h0
    rwa [AfterIncr_back] at h0'
  let ambientExit : Assertion :=
    (.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ priorW) ** (.x11 ↦ᵣ outPtr) **
      (outPtr ↦ₘ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ iW') ** (.x7 ↦ᵣ sumW') **
      (.x28 ↦ᵣ offW) ** (.x29 ↦ᵣ (TxExecStateGasAddr + offW)) **
      (.x30 ↦ᵣ BitVec.ofNat 64 execGas[i]) ** (.x31 ↦ᵣ sumW') **
      loopGlobals exactOkW runtimeW stateGas status execGas
  have hAmbPf : ambientExit.pcFree := by
    dsimp only [ambientExit]
    repeat' first
      | exact hGpf
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
  have e37F0 := cpsTripleWithin_frameR ambientExit hAmbPf e37
  have e37F : cpsTripleWithin 1 AfterIncr LoopGuard pseCode
      ambientExit ambientExit := by
    refine cpsTripleWithin_weaken ?_ ?_ e37F0
    · intro s hp
      exact (sepConj_emp_left' ambientExit).symm ▸ hp
    · intro s hq
      exact (sepConj_emp_left' ambientExit) ▸ hq
  -- Compose
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp only [LoopInv] at hp; xperm_hyp hp) hguard e16F
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 eLa
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 e19F
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 e20F
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 e21F
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 e22F
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 e23F
  have c08 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c07 eLaSt
  have c09 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c08 e26F
  have c10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c09 e27F
  have c11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c10 e28F
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c11 eLaEx
  have c13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 e31F
  have c14 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c13 e32F
  have c15 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c14 e33F
  have c16 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c15 e34F
  have c17 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c16 e35F
  have c18 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c17 e36F
  have c19 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by dsimp only [ambientExit] at hp ⊢; xperm_hyp hp) c18 e37F
  -- 13 prefix + 1 bne + 2 la + 1 add + 1 ld + 1 add + 1 bltu + 1 mv + 1 addi + 1 jal = 23
  change cpsTripleWithin (1+1+2+1+1+1+1+1+2+1+1+1+2+1+1+1+1+1+1+1) LoopGuard LoopGuard pseCode _ _ at c19
  exact cpsTripleWithin_weaken
    (fun _ hp => by dsimp only [LoopInv] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by
      dsimp only [LoopInv, ambientExit] at hq ⊢
      xperm_hyp hq) c19


#print axioms pseIterStatusNez

end EvmAsm.Codegen.Eip8037PriorStateUsedExactStatusNez
