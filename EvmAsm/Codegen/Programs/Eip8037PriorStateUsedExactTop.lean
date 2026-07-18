/-
  Top-level success specs for `eip8037_prior_state_used_exact`.
-/

import EvmAsm.Codegen.Programs.Eip8037PriorStateUsedExactInduct
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.Eip8037PriorStateUsedExactTop

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.Eip8037PriorStateUsedExactModel
open EvmAsm.Codegen.Eip8037PriorStateUsedExactSpec
open EvmAsm.Codegen.Eip8037PriorStateUsedExactLoop
open EvmAsm.Codegen.Eip8037PriorStateUsedExactInduct
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec (wordArray pcFree_wordArray)

abbrev P : Word := Eip8037PriorStateUsedExactSpec.P
abbrev pseCode : CodeReq := Eip8037PriorStateUsedExactSpec.pseCode
abbrev LoopGuard : Word := Eip8037PriorStateUsedExactSpec.LoopGuard
abbrev ExactOkAddr : Word := Eip8037PriorStateUsedExactSpec.ExactOkAddr
abbrev RuntimeCountAddr : Word := Eip8037PriorStateUsedExactSpec.RuntimeCountAddr
abbrev TxStateGasAddr : Word := Eip8037PriorStateUsedExactSpec.TxStateGasAddr
abbrev TxStatusAddr : Word := Eip8037PriorStateUsedExactSpec.TxStatusAddr
abbrev TxExecStateGasAddr : Word := Eip8037PriorStateUsedExactSpec.TxExecStateGasAddr

/-- Arrays framed across gates (read-only). -/
def arrayAmbient (stateGas status execGas : List Nat) : Assertion :=
  wordArray TxStateGasAddr stateGas **
    wordArray TxStatusAddr status **
    wordArray TxExecStateGasAddr execGas

theorem pcFree_arrayAmbient (stateGas status execGas : List Nat) :
    (arrayAmbient stateGas status execGas).pcFree := by
  unfold arrayAmbient
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_wordArray _ _

theorem prior_ne_zero_ofNat (n : Nat) (hn : n ≠ 0) (hn64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ (0 : Word) := by
  intro heq
  have := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at this
  exact hn this

/-- Pure model alignment under the success hyps. -/
theorem priorExactResult_of_success
    (exactOkW runtimeW priorW : Word)
    (stateGas status execGas : List Nat)
    (n finalSum : Nat)
    (hnW : priorW = BitVec.ofNat 64 n)
    (hn0 : n ≠ 0)
    (hn16 : n ≤ 16)
    (hexact : exactOkW ≠ (0 : Word))
    (hruntime : ¬ BitVec.ult runtimeW priorW)
    (hfinal : priorPrefixExact stateGas status execGas n = some finalSum) :
    priorExactResult exactOkW.toNat runtimeW.toNat n
      stateGas status execGas = some finalSum := by
  have hn64 : n < 2 ^ 64 := Nat.lt_of_le_of_lt hn16 (by decide : (16 : Nat) < 2 ^ 64)
  have hgatesB : priorGatesOkB exactOkW.toNat runtimeW.toNat n = true := by
    simp only [priorGatesOkB, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_, ?_⟩, hn16⟩
    · intro heq
      apply hexact
      apply BitVec.eq_of_toNat_eq
      simp [heq]
    · have hnot : ¬ runtimeW.toNat < priorW.toNat := by
        intro hlt
        apply hruntime
        exact BitVec.ult_iff_toNat_lt.mpr hlt
      have hge : runtimeW.toNat ≥ priorW.toNat := Nat.le_of_not_gt hnot
      have hp : priorW.toNat = n := by
        rw [hnW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
      simpa [hp] using hge
  simp only [priorExactResult, hn0, hgatesB, hfinal]
  -- residual: if False then … else if true=false then … else some finalSum
  simp

def nSuccessSteps (n : Nat) : Nat := nGateSteps + nLoopFrom n

set_option maxRecDepth 8000 in
/-- Success path: prior≠0, gates hold, prefixExact succeeds → a0=0 *out=finalSum.
    Pure model: see `priorExactResult_of_success`. -/
theorem eip8037PriorStateUsedExact_success_spec_within
    (raIn priorW outPtr oldOut exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (n finalSum : Nat)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (hnW : priorW = BitVec.ofNat 64 n)
    (hn0 : n ≠ 0)
    (hn16 : n ≤ 16)
    (hexact : exactOkW ≠ (0 : Word))
    (hruntime : ¬ BitVec.ult runtimeW priorW)
    (hpriorLe16 : ¬ BitVec.ult (16 : Word) priorW)
    (hfinal : priorPrefixExact stateGas status execGas n = some finalSum)
    (hAllState : n ≤ stateGas.length)
    (hAllStat : n ≤ status.length)
    (hAllExec : n ≤ execGas.length)
    (hAllStatBound : ∀ j < n, status[j]! < 2 ^ 64)
    (hAllNoOvf : ∀ j < n,
      ∀ s, priorPrefixExact stateGas status execGas j = some s →
        s + priorCell stateGas status execGas j < 2 ^ 64)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    let finalW := BitVec.ofNat 64 finalSum
    ∃ v28' v29' v30' v31',
      cpsTripleWithin (nSuccessSteps n) P raIn pseCode
        (entryPre raIn priorW outPtr oldOut
          ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
            (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
            (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW) **
            arrayAmbient stateGas status execGas))
        (postOk raIn outPtr finalW
          ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ finalW) **
            (.x28 ↦ᵣ v28') ** (.x29 ↦ᵣ v29') ** (.x30 ↦ᵣ v30') ** (.x31 ↦ᵣ v31') **
            loopGlobals exactOkW runtimeW stateGas status execGas)) := by
  intro finalW
  have hn64 : n < 2 ^ 64 := Nat.lt_of_le_of_lt hn16 (by decide : (16 : Nat) < 2 ^ 64)
  have hprior : priorW ≠ (0 : Word) := by
    rw [hnW]; exact prior_ne_zero_ofNat n hn0 hn64
  have hgates := eip8037PriorStateUsedExact_gatesToLoop_spec_within
    raIn priorW outPtr oldOut exactOkW runtimeW
    v5 v6 v7 v28 v29 v30 v31 hprior hexact hruntime hpriorLe16
  have hgatesF := cpsTripleWithin_frameR
    (arrayAmbient stateGas status execGas)
    (pcFree_arrayAmbient stateGas status execGas) hgates
  have hgates' : cpsTripleWithin nGateSteps P LoopGuard pseCode
      (entryPre raIn priorW outPtr oldOut
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW) **
          arrayAmbient stateGas status execGas))
      (LoopInv raIn priorW outPtr (0 : Word) (0 : Word) exactOkW runtimeW
        stateGas status execGas v28 v29 v30 v31) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [entryPre] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        -- hq: loopEntry ** arrays; goal: LoopInv0
        unfold loopEntry arrayAmbient at hq
        unfold LoopInv loopGlobals
        xperm_hyp hq) hgatesF
  obtain ⟨v28', v29', v30', v31', hloop⟩ :=
    pseLoop raIn priorW outPtr exactOkW runtimeW
      stateGas status execGas n finalSum v28 v29 v30 v31
      hnW hn16 hfinal hAllState hAllStat hAllExec hAllStatBound hAllNoOvf hret
  have hcomp := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => hp) hgates' hloop
  refine ⟨v28', v29', v30', v31', ?_⟩
  simpa [nSuccessSteps] using hcomp

#print axioms eip8037PriorStateUsedExact_success_spec_within

set_option maxRecDepth 8000 in
/-- Zero prior with ambient arrays/globals framed. -/
theorem eip8037PriorStateUsedExact_zero_top_spec_within
    (raIn outPtr oldOut : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (stateGas status execGas : List Nat)
    (exactOkW runtimeW : Word)
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin nZeroSteps P raIn pseCode
      (entryPre raIn (0 : Word) outPtr oldOut
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW) **
          arrayAmbient stateGas status execGas))
      (postOk raIn outPtr (0 : Word)
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
          (ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW) **
          arrayAmbient stateGas status execGas)) := by
  have h0 := eip8037PriorStateUsedExact_zero_spec_within
    raIn outPtr oldOut v5 v6 v7 v28 v29 v30 v31 hret
  have h0F := cpsTripleWithin_frameR
    ((ExactOkAddr ↦ₘ exactOkW) ** (RuntimeCountAddr ↦ₘ runtimeW) **
      arrayAmbient stateGas status execGas)
    (by
      unfold arrayAmbient
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_memIs
        | exact pcFree_wordArray _ _) h0
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp only [entryPre] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      dsimp only [postOk] at hq ⊢
      xperm_hyp hq) h0F

#print axioms eip8037PriorStateUsedExact_zero_top_spec_within

end EvmAsm.Codegen.Eip8037PriorStateUsedExactTop
