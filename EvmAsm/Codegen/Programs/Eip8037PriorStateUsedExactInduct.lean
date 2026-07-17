/-
  Loop induction + success top path for `eip8037_prior_state_used_exact`.
-/

import EvmAsm.Codegen.Programs.Eip8037PriorStateUsedExactStatusNez
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.SAsm.DualReadByteScan

namespace EvmAsm.Codegen.Eip8037PriorStateUsedExactInduct

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.Eip8037PriorStateUsedExactModel
open EvmAsm.Codegen.Eip8037PriorStateUsedExactSpec
open EvmAsm.Codegen.Eip8037PriorStateUsedExactLoop
open EvmAsm.Codegen.Eip8037PriorStateUsedExactIter
open EvmAsm.Codegen.Eip8037PriorStateUsedExactStatusNez

abbrev LoopGuard : Word := Eip8037PriorStateUsedExactLoop.LoopGuard
abbrev pseCode : CodeReq := Eip8037PriorStateUsedExactLoop.pseCode

def nOneIterSteps : Nat := 23

def nLoopFrom : Nat → Nat
  | 0 => 4
  | r + 1 => nOneIterSteps + nLoopFrom r

private theorem getElem_bang (as : List Nat) (i : Nat) (h : i < as.length) :
    as[i]! = as[i] := getElem!_pos as i h

theorem priorCell_of_status0 (stateGas status execGas : List Nat) (i : Nat)
    (hstat : i < status.length) (h0 : status[i] = 0) (hi : i < stateGas.length) :
    priorCell stateGas status execGas i = stateGas[i] := by
  simp only [priorCell, getElem_bang status i hstat, h0, ↓reduceIte,
    getElem_bang stateGas i hi, Nat.add_zero]

theorem priorCell_of_statusNez (stateGas status execGas : List Nat) (i : Nat)
    (hstat : i < status.length) (hne : status[i] ≠ 0)
    (hi : i < stateGas.length) (hexec : i < execGas.length) :
    priorCell stateGas status execGas i = stateGas[i] + execGas[i] := by
  simp only [priorCell, getElem_bang status i hstat, hne, ↓reduceIte,
    getElem_bang stateGas i hi, getElem_bang execGas i hexec]

theorem priorPrefixExact_eq_prefix (stateGas status execGas : List Nat)
    (k s : Nat) (h : priorPrefixExact stateGas status execGas k = some s) :
    s = priorPrefix stateGas status execGas k := by
  induction k generalizing s with
  | zero =>
    simp only [priorPrefixExact, priorPrefix] at h ⊢
    injection h with h; exact h.symm
  | succ k ih =>
    simp only [priorPrefixExact] at h
    split at h
    · contradiction
    · next t ht =>
      simp only [add64?] at h
      split at h
      · next hlt =>
        injection h with heq
        have iht := ih t ht
        simp only [priorPrefix, iht] at heq ⊢
        exact heq.symm
      · contradiction

theorem ofNat_ne_of_lt (i n : Nat) (hi : i < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 i ≠ BitVec.ofNat 64 n := by
  intro heq
  have hi' : i < 2 ^ 64 := Nat.lt_trans hi hn
  have := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hn] at this
  omega

set_option maxRecDepth 8000 in
theorem pseIterOne
    (raIn priorW outPtr : Word)
    (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (i sum : Nat)
    (v28 v29 v30 v31 : Word)
    (hi : i < stateGas.length)
    (hstat : i < status.length)
    (hexec : i < execGas.length)
    (hstatBound : status[i] < 2 ^ 64)
    (hno : sum + priorCell stateGas status execGas i < 2 ^ 64)
    (hne : BitVec.ofNat 64 i ≠ priorW) :
    ∃ v28' v29' v30' v31',
      cpsTripleWithin nOneIterSteps LoopGuard LoopGuard pseCode
        (LoopInv raIn priorW outPtr (BitVec.ofNat 64 sum) (BitVec.ofNat 64 i)
          exactOkW runtimeW stateGas status execGas v28 v29 v30 v31)
        (LoopInv raIn priorW outPtr
          (BitVec.ofNat 64 (sum + priorCell stateGas status execGas i))
          (BitVec.ofNat 64 (i + 1)) exactOkW runtimeW
          stateGas status execGas v28' v29' v30' v31') := by
  by_cases hst : status[i] = 0
  · have hcell := priorCell_of_status0 stateGas status execGas i hstat hst hi
    have hno' : sum + stateGas[i] < 2 ^ 64 := by simpa [hcell] using hno
    have htrip := pseIterStatus0 raIn priorW outPtr exactOkW runtimeW
      stateGas status execGas i sum v28 v29 v30 v31 hi hstat hst hno' hne
    refine ⟨BitVec.ofNat 64 (8 * i),
      Eip8037PriorStateUsedExactLoop.TxStatusAddr + BitVec.ofNat 64 (8 * i),
      (0 : Word),
      BitVec.ofNat 64 (sum + stateGas[i]), ?_⟩
    have hle : 16 ≤ nOneIterSteps := by unfold nOneIterSteps; omega
    have htrip' := cpsTripleWithin_mono_nSteps hle htrip
    -- goal post sum uses priorCell; leaf uses stateGas[i]
    rw [hcell]
    exact htrip'
  · have hcell := priorCell_of_statusNez stateGas status execGas i hstat hst hi hexec
    have hnoS : sum + stateGas[i] < 2 ^ 64 := by
      have : stateGas[i] ≤ priorCell stateGas status execGas i := by
        simp only [hcell]; omega
      omega
    have hnoE : sum + stateGas[i] + execGas[i] < 2 ^ 64 := by
      have : sum + priorCell stateGas status execGas i =
          sum + stateGas[i] + execGas[i] := by
        simp only [hcell, Nat.add_assoc]
      simpa [this] using hno
    have htrip := pseIterStatusNez raIn priorW outPtr exactOkW runtimeW
      stateGas status execGas i sum v28 v29 v30 v31 hi hstat hexec hst hstatBound
      hnoS hnoE hne
    refine ⟨BitVec.ofNat 64 (8 * i),
      Eip8037PriorStateUsedExactLoop.TxExecStateGasAddr + BitVec.ofNat 64 (8 * i),
      BitVec.ofNat 64 execGas[i],
      BitVec.ofNat 64 (sum + stateGas[i] + execGas[i]), ?_⟩
    -- goal: ofNat (sum + priorCell) = ofNat (sum + (state+exec))
    -- leaf: ofNat (sum + state + exec)
    have hassoc : sum + stateGas[i] + execGas[i] =
        sum + (stateGas[i] + execGas[i]) := by omega
    rw [hcell, ← hassoc]
    exact htrip

set_option maxRecDepth 8000 in
theorem pseLoopFrom
    (raIn priorW outPtr : Word)
    (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (n : Nat)
    (hnW : priorW = BitVec.ofNat 64 n)
    (hn16 : n ≤ 16)
    (hAllState : n ≤ stateGas.length)
    (hAllStat : n ≤ status.length)
    (hAllExec : n ≤ execGas.length)
    (hAllStatBound : ∀ j < n, status[j]! < 2 ^ 64)
    (hAllNoOvf : ∀ j < n,
      ∀ s, priorPrefixExact stateGas status execGas j = some s →
        s + priorCell stateGas status execGas j < 2 ^ 64)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (fuel i sum : Nat)
    (v28 v29 v30 v31 : Word)
    (hfuel : n - i ≤ fuel)
    (hi : i ≤ n)
    (hsum : priorPrefixExact stateGas status execGas i = some sum) :
    let sumW := BitVec.ofNat 64 sum
    let iW := BitVec.ofNat 64 i
    let finalSum := priorPrefix stateGas status execGas n
    let finalW := BitVec.ofNat 64 finalSum
    ∃ v28' v29' v30' v31',
      cpsTripleWithin (nLoopFrom (n - i)) LoopGuard raIn pseCode
        (LoopInv raIn priorW outPtr sumW iW exactOkW runtimeW
          stateGas status execGas v28 v29 v30 v31)
        (postOk raIn outPtr finalW
          ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ finalW) **
            (.x28 ↦ᵣ v28') ** (.x29 ↦ᵣ v29') ** (.x30 ↦ᵣ v30') ** (.x31 ↦ᵣ v31') **
            loopGlobals exactOkW runtimeW stateGas status execGas)) := by
  intro sumW iW finalSum finalW
  induction fuel generalizing i sum v28 v29 v30 v31 with
  | zero =>
    have hni : n - i = 0 := Nat.le_zero.mp hfuel
    have hi_eq : i = n := by omega
    have hsumEq : sum = finalSum := by
      rw [hi_eq] at hsum
      -- finalSum := priorPrefix ... n
      exact priorPrefixExact_eq_prefix stateGas status execGas n sum hsum
    refine ⟨v28, v29, v30, v31, ?_⟩
    have hexit := pseLoopExitOk raIn priorW outPtr (BitVec.ofNat 64 sum)
      exactOkW runtimeW stateGas status execGas v28 v29 v30 v31 hret
    have hiW : BitVec.ofNat 64 n = priorW := hnW.symm
    have hexit' : cpsTripleWithin 4 LoopGuard raIn pseCode
        (LoopInv raIn priorW outPtr (BitVec.ofNat 64 sum) (BitVec.ofNat 64 n)
          exactOkW runtimeW stateGas status execGas v28 v29 v30 v31)
        (postOk raIn outPtr (BitVec.ofNat 64 sum)
          ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ BitVec.ofNat 64 sum) **
            (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
            loopGlobals exactOkW runtimeW stateGas status execGas)) := by
      simpa [hiW] using hexit
    have hgoal : cpsTripleWithin 4 LoopGuard raIn pseCode
        (LoopInv raIn priorW outPtr sumW iW exactOkW runtimeW
          stateGas status execGas v28 v29 v30 v31)
        (postOk raIn outPtr finalW
          ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ finalW) **
            (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
            loopGlobals exactOkW runtimeW stateGas status execGas)) := by
      simpa [sumW, iW, finalW, hsumEq, hi_eq] using hexit'
    simpa [nLoopFrom, hni] using hgoal
  | succ fuel ih =>
    by_cases hdone : i = n
    · -- exit without subst: rewrite with hdone
      have hsumEq : sum = finalSum := by
        rw [hdone] at hsum
        exact priorPrefixExact_eq_prefix stateGas status execGas n sum hsum
      refine ⟨v28, v29, v30, v31, ?_⟩
      have hexit := pseLoopExitOk raIn priorW outPtr (BitVec.ofNat 64 sum)
        exactOkW runtimeW stateGas status execGas v28 v29 v30 v31 hret
      have hiW : BitVec.ofNat 64 n = priorW := hnW.symm
      have hexit' : cpsTripleWithin 4 LoopGuard raIn pseCode
          (LoopInv raIn priorW outPtr (BitVec.ofNat 64 sum) (BitVec.ofNat 64 n)
            exactOkW runtimeW stateGas status execGas v28 v29 v30 v31)
          (postOk raIn outPtr (BitVec.ofNat 64 sum)
            ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ BitVec.ofNat 64 sum) **
              (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
              loopGlobals exactOkW runtimeW stateGas status execGas)) := by
        simpa [hiW] using hexit
      have hgoal : cpsTripleWithin 4 LoopGuard raIn pseCode
          (LoopInv raIn priorW outPtr sumW iW exactOkW runtimeW
            stateGas status execGas v28 v29 v30 v31)
          (postOk raIn outPtr finalW
            ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ finalW) **
              (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
              loopGlobals exactOkW runtimeW stateGas status execGas)) := by
        simpa [sumW, iW, finalW, hsumEq, hdone] using hexit'
      simpa [hdone, Nat.sub_self, nLoopFrom] using hgoal
    · have hilt : i < n := Nat.lt_of_le_of_ne hi hdone
      have hiS : i < stateGas.length := Nat.lt_of_lt_of_le hilt hAllState
      have hiSt : i < status.length := Nat.lt_of_lt_of_le hilt hAllStat
      have hiE : i < execGas.length := Nat.lt_of_lt_of_le hilt hAllExec
      have hstatBound : status[i] < 2 ^ 64 := by
        have := hAllStatBound i hilt
        rwa [getElem_bang status i hiSt] at this
      have hno : sum + priorCell stateGas status execGas i < 2 ^ 64 :=
        hAllNoOvf i hilt sum hsum
      have hn64 : n < 2 ^ 64 := Nat.lt_of_le_of_lt hn16 (by decide : (16 : Nat) < 2 ^ 64)
      have hne : BitVec.ofNat 64 i ≠ priorW := by
        rw [hnW]; exact ofNat_ne_of_lt i n hilt hn64
      obtain ⟨v28a, v29a, v30a, v31a, hiter⟩ :=
        pseIterOne raIn priorW outPtr exactOkW runtimeW
          stateGas status execGas i sum v28 v29 v30 v31
          hiS hiSt hiE hstatBound hno hne
      have hsum' : priorPrefixExact stateGas status execGas (i + 1) =
          some (sum + priorCell stateGas status execGas i) := by
        simp only [priorPrefixExact, hsum, add64?, if_pos hno]
      have hfuel' : n - (i + 1) ≤ fuel := by omega
      have hi' : i + 1 ≤ n := Nat.succ_le_of_lt hilt
      obtain ⟨v28b, v29b, v30b, v31b, htail⟩ :=
        ih (i + 1) (sum + priorCell stateGas status execGas i)
          v28a v29a v30a v31a hfuel' hi' hsum'
      refine ⟨v28b, v29b, v30b, v31b, ?_⟩
      have hcomp := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => hp) hiter htail
      have hsteps : nOneIterSteps + nLoopFrom (n - (i + 1)) = nLoopFrom (n - i) := by
        have : n - i = (n - (i + 1)) + 1 := by omega
        rw [this, nLoopFrom]
      simpa [hsteps] using hcomp

set_option maxRecDepth 8000 in
theorem pseLoop
    (raIn priorW outPtr : Word)
    (exactOkW runtimeW : Word)
    (stateGas status execGas : List Nat)
    (n finalSum : Nat)
    (v28 v29 v30 v31 : Word)
    (hnW : priorW = BitVec.ofNat 64 n)
    (hn16 : n ≤ 16)
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
      cpsTripleWithin (nLoopFrom n) LoopGuard raIn pseCode
        (LoopInv raIn priorW outPtr (0 : Word) (0 : Word) exactOkW runtimeW
          stateGas status execGas v28 v29 v30 v31)
        (postOk raIn outPtr finalW
          ((.x5 ↦ᵣ priorW) ** (.x6 ↦ᵣ priorW) ** (.x7 ↦ᵣ finalW) **
            (.x28 ↦ᵣ v28') ** (.x29 ↦ᵣ v29') ** (.x30 ↦ᵣ v30') ** (.x31 ↦ᵣ v31') **
            loopGlobals exactOkW runtimeW stateGas status execGas)) := by
  intro finalW
  have hsum0 : priorPrefixExact stateGas status execGas 0 = some 0 := rfl
  have hfeq : finalSum = priorPrefix stateGas status execGas n :=
    priorPrefixExact_eq_prefix stateGas status execGas n finalSum hfinal
  obtain ⟨v28', v29', v30', v31', h⟩ :=
    pseLoopFrom raIn priorW outPtr exactOkW runtimeW
      stateGas status execGas n hnW hn16
      hAllState hAllStat hAllExec hAllStatBound hAllNoOvf hret
      n 0 0 v28 v29 v30 v31 (by omega) (by omega) hsum0
  refine ⟨v28', v29', v30', v31', ?_⟩
  -- finalW = ofNat finalSum; h has ofNat (priorPrefix) = ofNat finalSum via hfeq
  simpa [Nat.sub_zero, ← hfeq] using h

#print axioms pseLoop

end EvmAsm.Codegen.Eip8037PriorStateUsedExactInduct
