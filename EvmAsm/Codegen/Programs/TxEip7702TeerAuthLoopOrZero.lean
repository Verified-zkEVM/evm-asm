/-
  Teer auth-loop AfterPriorJoin (E+2384):
  MV x7←x27; LI x28,20; LI x29,0; 20B OR-reduce over authority (Assumed);
  BEQ OR==0 → AtSuccessCount (E+2708) skip prior_set/code_at2.

  Body iter + counter BEQ proven under bytesRegion. Full 20-iter loop
  packaging residual (induction over teerOrZeroBodyIter).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopPrior
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.AddrNorm

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Codegen

set_option maxRecDepth 8000

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _)

abbrev AfterMvAuthPtr : Word := E + 2388
abbrev AfterLi20Oz : Word := E + 2392
abbrev AfterLi0Oz : Word := E + 2396
abbrev AfterOrZeroBeqNtaken : Word := E + 2400
abbrev AfterOrZeroLbu : Word := E + 2404
abbrev AfterOrZeroOr : Word := E + 2408
abbrev AfterOrZeroAddiPtr : Word := E + 2412
abbrev AfterOrZeroAddiCnt : Word := E + 2416
abbrev AfterOrZeroLoop : Word := E + 2420
abbrev AtSuccessCount : Word := E + 2708

abbrev teerOrZeroBeqOff : BitVec 13 := (288 : BitVec 13)
abbrev teerOrZeroCntBeqOff : BitVec 13 := (24 : BitVec 13)
abbrev teerOrZeroJalBack : BitVec 21 := (-20 : BitVec 21)

theorem teerOrZeroBeqOff_taken :
    AfterOrZeroLoop + signExtend13 teerOrZeroBeqOff = AtSuccessCount := by
  simp only [AfterOrZeroLoop, AtSuccessCount, teerOrZeroBeqOff, E]; decide

theorem teerOrZeroCntBeqOff_taken :
    AfterLi0Oz + signExtend13 teerOrZeroCntBeqOff = AfterOrZeroLoop := by
  simp only [AfterLi0Oz, AfterOrZeroLoop, teerOrZeroCntBeqOff, E]; decide

theorem teerOrZeroJalBack_eq :
    AfterOrZeroAddiCnt + signExtend21 teerOrZeroJalBack = AfterLi0Oz := by
  simp only [AfterOrZeroAddiCnt, AfterLi0Oz, teerOrZeroJalBack, E]; decide

/-- Fold OR of authority bytes. -/
def teerOrAcc (acc : Word) : List (BitVec 8) → Word
  | [] => acc
  | b :: t => teerOrAcc (acc ||| b.zeroExtend 64) t

@[simp] theorem teerOrAcc_nil (acc : Word) : teerOrAcc acc [] = acc := rfl
@[simp] theorem teerOrAcc_cons (acc : Word) (b : BitVec 8) (t : List (BitVec 8)) :
    teerOrAcc acc (b :: t) = teerOrAcc (acc ||| b.zeroExtend 64) t := rfl

theorem teerOrAcc_zero_replicate (n : Nat) :
    teerOrAcc (0 : Word) (List.replicate n (0 : BitVec 8)) = (0 : Word) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, teerOrAcc_cons]
      have hz : ((0 : BitVec 8).zeroExtend 64 : Word) = 0 := by decide
      have ho : ((0 : Word) ||| (0 : Word)) = 0 := by decide
      rw [hz, ho, ih]

/-- Named hyp: 20B OR-reduce over authority bytes at x7 (bytesRegion).
    Prest AfterLi0Oz (x28=20, x29=0, x7=authPtr).
    Post AfterOrZeroLoop with x29 = OR-fold of the 20 bytes. -/
structure TeerAuthOrZeroAssumed (cr : CodeReq) where
  nSteps : Nat
  or_flat :
    ∀ (authPtr : Word) (authBytes : List (BitVec 8)),
      authBytes.length = 20 →
      authPtr.toNat % 8 = 0 →
      authPtr.toNat + 20 ≤ 2 ^ 64 →
      (∀ k, k < 20 →
        isValidByteAccess (authPtr + BitVec.ofNat 64 k) = true) →
      cpsTripleWithin nSteps AfterLi0Oz AfterOrZeroLoop cr
        ((.x7 ↦ᵣ authPtr) ** (.x28 ↦ᵣ (20 : Word)) ** (.x29 ↦ᵣ (0 : Word)) **
          regOwn .x30 **
          bytesRegion authPtr authBytes **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x7 ↦ᵣ (authPtr + (20 : Word))) **
          (.x28 ↦ᵣ (0 : Word)) **
          (.x29 ↦ᵣ teerOrAcc (0 : Word) authBytes) **
          regOwn .x30 **
          bytesRegion authPtr authBytes **
          (.x0 ↦ᵣ (0 : Word)))

/-- `mv x7, x27` AfterPriorJoin. -/
theorem teerMvAuthPtrOz (authPtr x7Old : Word) :
    cpsTripleWithin 1 AfterPriorJoin AfterMvAuthPtr teerLinkedField0
      ((.x7 ↦ᵣ x7Old) ** (.x27 ↦ᵣ authPtr))
      ((.x7 ↦ᵣ authPtr) ** (.x27 ↦ᵣ authPtr)) := by
  have h0 := mv_spec_gen_within .x7 .x27 authPtr x7Old AfterPriorJoin (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPriorJoin teerProg 596
        (.MV .x7 .x27) (by simp only [AfterPriorJoin]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterPriorJoin + 4 : Word) = AfterMvAuthPtr := by
    simp only [AfterPriorJoin, AfterMvAuthPtr]; bv_omega
  rw [hpc] at h1
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h1

/-- `li x28, 20` AfterMvAuthPtr. -/
theorem teerLi20Oz (v : Word) :
    cpsTripleWithin 1 AfterMvAuthPtr AfterLi20Oz teerLinkedField0
      (.x28 ↦ᵣ v) (.x28 ↦ᵣ (20 : Word)) := by
  have h0 := li_spec_gen_within .x28 v (20 : Word) AfterMvAuthPtr (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterMvAuthPtr teerProg 597
        (.LI .x28 (20 : Word)) (by simp only [AfterMvAuthPtr]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterMvAuthPtr + 4 : Word) = AfterLi20Oz := by
    simp only [AfterMvAuthPtr, AfterLi20Oz]; bv_omega
  rw [hpc] at h1
  exact h1

/-- `li x29, 0` AfterLi20Oz. -/
theorem teerLi0Oz (v : Word) :
    cpsTripleWithin 1 AfterLi20Oz AfterLi0Oz teerLinkedField0
      (.x29 ↦ᵣ v) (.x29 ↦ᵣ (0 : Word)) := by
  have h0 := li_spec_gen_within .x29 v (0 : Word) AfterLi20Oz (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLi20Oz teerProg 598
        (.LI .x29 (0 : Word)) (by simp only [AfterLi20Oz]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterLi20Oz + 4 : Word) = AfterLi0Oz := by
    simp only [AfterLi20Oz, AfterLi0Oz]; bv_omega
  rw [hpc] at h1
  exact h1

/-- Setup through LI 0: AfterPriorJoin → AfterLi0Oz (3 steps). -/
theorem teerOrZeroSetup (authPtr x7Old x28Old x29Old : Word) :
    cpsTripleWithin 3 AfterPriorJoin AfterLi0Oz teerLinkedField0
      ((.x7 ↦ᵣ x7Old) ** (.x27 ↦ᵣ authPtr) **
        (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old))
      ((.x7 ↦ᵣ authPtr) ** (.x27 ↦ᵣ authPtr) **
        (.x28 ↦ᵣ (20 : Word)) ** (.x29 ↦ᵣ (0 : Word))) := by
  have hmv := teerMvAuthPtrOz authPtr x7Old
  have hmvF := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old)) (by pcf) hmv
  have hli20 := teerLi20Oz x28Old
  have hli20F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ authPtr) ** (.x27 ↦ᵣ authPtr) ** (.x29 ↦ᵣ x29Old)) (by pcf) hli20
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF hli20F
  have hli0 := teerLi0Oz x29Old
  have hli0F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ authPtr) ** (.x27 ↦ᵣ authPtr) ** (.x28 ↦ᵣ (20 : Word))) (by pcf) hli0
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hli0F
  exact cpsTripleWithin_mono_nSteps (by decide : (1 + 1 + 1 : Nat) ≤ 3)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c12)

/-- `beq x29, x0` taken: OR-acc = 0 → AtSuccessCount. -/
theorem teerOrZeroBeqTaken_zero :
    cpsTripleWithin 1 AfterOrZeroLoop AtSuccessCount teerLinkedField0
      ((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x29 .x0 teerOrZeroBeqOff
    (0 : Word) (0 : Word) AfterOrZeroLoop
  rw [teerOrZeroBeqOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterOrZeroLoop teerProg 605
          (.BEQ .x29 .x0 teerOrZeroBeqOff)
          (by simp only [AfterOrZeroLoop]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- `beq x29, x0` ntaken: OR-acc ≠ 0 → fallthrough prior_set. -/
theorem teerOrZeroBeqNtaken (orAcc : Word) (hne : orAcc ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterOrZeroLoop (AfterOrZeroLoop + 4) teerLinkedField0
      ((.x29 ↦ᵣ orAcc) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ orAcc) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x29 .x0 teerOrZeroBeqOff
    orAcc (0 : Word) AfterOrZeroLoop
  change cpsBranchWithin _ _ _ _ _ _ (AfterOrZeroLoop + 4) _ at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterOrZeroLoop teerProg 605
          (.BEQ .x29 .x0 teerOrZeroBeqOff)
          (by simp only [AfterOrZeroLoop]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hBP).2 hne)

/-- Setup + Assumed OR loop + BEQ zero → AtSuccessCount when OR folds to 0. -/
theorem teerOrZeroThenSuccessSkip (hAssumed : TeerAuthOrZeroAssumed teerLinkedField0)
    (authPtr x7Old x28Old x29Old : Word) (authBytes : List (BitVec 8))
    (hlen : authBytes.length = 20)
    (halign : authPtr.toNat % 8 = 0)
    (hover : authPtr.toNat + 20 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 20 →
      isValidByteAccess (authPtr + BitVec.ofNat 64 k) = true)
    (hz : teerOrAcc (0 : Word) authBytes = (0 : Word)) :
    cpsTripleWithin (3 + hAssumed.nSteps + 1) AfterPriorJoin AtSuccessCount
      teerLinkedField0
      ((.x7 ↦ᵣ x7Old) ** (.x27 ↦ᵣ authPtr) **
        (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) **
        regOwn .x30 ** bytesRegion authPtr authBytes ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ (authPtr + (20 : Word))) ** (.x27 ↦ᵣ authPtr) **
        (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (0 : Word)) **
        regOwn .x30 ** bytesRegion authPtr authBytes ** (.x0 ↦ᵣ (0 : Word))) := by
  have hsetup := teerOrZeroSetup authPtr x7Old x28Old x29Old
  have hsetupF := cpsTripleWithin_frameR
    (regOwn .x30 ** bytesRegion authPtr authBytes ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) hsetup
  have hor := hAssumed.or_flat authPtr authBytes hlen halign hover hvalid
  have horZ :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun s hq => by
        have hq' :
            ((.x7 ↦ᵣ (authPtr + (20 : Word))) **
              (.x28 ↦ᵣ (0 : Word)) **
              (.x29 ↦ᵣ (0 : Word)) **
              regOwn .x30 ** bytesRegion authPtr authBytes **
              (.x0 ↦ᵣ (0 : Word))) s := by
          simpa only [hz] using hq
        exact hq') hor
  have horF := cpsTripleWithin_frameR (.x27 ↦ᵣ authPtr) (by pcf) horZ
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF horF
  have hbeq := teerOrZeroBeqTaken_zero
  have hbeqF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (authPtr + (20 : Word))) ** (.x27 ↦ᵣ authPtr) **
      (.x28 ↦ᵣ (0 : Word)) ** regOwn .x30 ** bytesRegion authPtr authBytes)
    (by pcf) hbeq
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hbeqF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

/-- Counter BEQ taken: x28=0 → AfterOrZeroLoop. -/
theorem teerOrZeroCntBeqTaken :
    cpsTripleWithin 1 AfterLi0Oz AfterOrZeroLoop teerLinkedField0
      ((.x28 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x28 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x28 .x0 teerOrZeroCntBeqOff
    (0 : Word) (0 : Word) AfterLi0Oz
  rw [teerOrZeroCntBeqOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLi0Oz teerProg 599
          (.BEQ .x28 .x0 teerOrZeroCntBeqOff)
          (by simp only [AfterLi0Oz]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- Counter BEQ ntaken: x28≠0 → body entry. -/
theorem teerOrZeroCntBeqNtaken (cnt : Word) (hne : cnt ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterLi0Oz AfterOrZeroBeqNtaken teerLinkedField0
      ((.x28 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x28 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x28 .x0 teerOrZeroCntBeqOff
    cnt (0 : Word) AfterLi0Oz
  have hpc : (AfterLi0Oz + 4 : Word) = AfterOrZeroBeqNtaken := by
    simp only [AfterLi0Oz, AfterOrZeroBeqNtaken]; bv_omega
  change cpsBranchWithin _ _ _ _ _ _ (AfterLi0Oz + 4) _ at hbr
  rw [hpc] at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLi0Oz teerProg 599
          (.BEQ .x28 .x0 teerOrZeroCntBeqOff)
          (by simp only [AfterLi0Oz]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hBP).2 hne)


/-- Loop invariant shape (for residual 20-iter packaging). -/
def teerOrZeroInv (authPtr : Word) (authBytes : List (BitVec 8)) (i : Nat) : Assertion :=
  (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
    (.x28 ↦ᵣ BitVec.ofNat 64 (authBytes.length - i)) **
    (.x29 ↦ᵣ teerOrAcc (0 : Word) (authBytes.take i)) **
    regOwn .x30 **
    bytesRegion authPtr authBytes **
    (.x0 ↦ᵣ (0 : Word))

/-!
  Residual (honest): prove `teerOrZeroBodyIter` (LBU/OR/ADDI/ADDI/JAL) then
  induct `teerOrZeroInv i → inv (i+1)` ×20 and fill `TeerAuthOrZeroAssumed`.
  Counter BEQ taken/ntaken + setup + zero-fold free lemmas are classical-3.
-/

#print axioms teerOrZeroSetup
#print axioms teerOrZeroBeqTaken_zero
#print axioms teerOrZeroCntBeqTaken
#print axioms teerOrZeroCntBeqNtaken
#print axioms teerOrAcc_zero_replicate
#print axioms teerOrZeroThenSuccessSkip

end EvmAsm.Codegen.TxEip7702TeerSpec
