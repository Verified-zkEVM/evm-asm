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
open EvmAsm.Rv64.AddrNorm (se12_1)

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
    Prest/post match `teerOrZeroInv` association (x28/x0 left for BEQ frame).
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
        (((.x28 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x7 ↦ᵣ authPtr) ** (.x29 ↦ᵣ (0 : Word)) **
            regOwn .x30 ** bytesRegion authPtr authBytes))
        (((.x28 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x7 ↦ᵣ (authPtr + (20 : Word))) **
            (.x29 ↦ᵣ teerOrAcc (0 : Word) authBytes) **
            regOwn .x30 ** bytesRegion authPtr authBytes))

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
  -- Setup post is flat; reshape to Assumed prest (nested x28/x0 left) + x27.
  have hsetupN :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun s hq => by
        change
          ((((.x28 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
            ((.x7 ↦ᵣ authPtr) ** (.x29 ↦ᵣ (0 : Word)) **
              regOwn .x30 ** bytesRegion authPtr authBytes)) **
            (.x27 ↦ᵣ authPtr)) s
        xperm_hyp hq) hsetupF
  have hor := hAssumed.or_flat authPtr authBytes hlen halign hover hvalid
  have horZ :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun s hq => by
        -- Assumed post nested → flat with x29=0 via hz
        change
          ((.x7 ↦ᵣ (authPtr + (20 : Word))) **
            (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (0 : Word)) **
            regOwn .x30 ** bytesRegion authPtr authBytes **
            (.x0 ↦ᵣ (0 : Word))) s
        have hq' :
            (((.x28 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
              ((.x7 ↦ᵣ (authPtr + (20 : Word))) **
                (.x29 ↦ᵣ (0 : Word)) **
                regOwn .x30 ** bytesRegion authPtr authBytes)) s := by
          simpa only [hz] using hq
        xperm_hyp hq') hor
  have horF := cpsTripleWithin_frameR (.x27 ↦ᵣ authPtr) (by pcf) horZ
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupN horF
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


/-- Loop invariant at AfterLi0Oz after `i` bytes consumed.
    x28/x0 left for BEQ framing; remaining ambient right. -/
def teerOrZeroInv (authPtr : Word) (authBytes : List (BitVec 8)) (i : Nat) : Assertion :=
  ((.x28 ↦ᵣ BitVec.ofNat 64 (authBytes.length - i)) ** (.x0 ↦ᵣ (0 : Word))) **
    ((.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
      (.x29 ↦ᵣ teerOrAcc (0 : Word) (authBytes.take i)) **
      regOwn .x30 **
      bytesRegion authPtr authBytes)

/-- Ambient half of inv (everything except counter+x0). -/
def teerOrZeroInvAmb (authPtr : Word) (authBytes : List (BitVec 8)) (i : Nat) : Assertion :=
  (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) **
    (.x29 ↦ᵣ teerOrAcc (0 : Word) (authBytes.take i)) **
    regOwn .x30 **
    bytesRegion authPtr authBytes

private theorem teerOrZeroInv_eq (authPtr : Word) (authBytes : List (BitVec 8)) (i : Nat) :
    teerOrZeroInv authPtr authBytes i =
      (((.x28 ↦ᵣ BitVec.ofNat 64 (authBytes.length - i)) ** (.x0 ↦ᵣ (0 : Word))) **
        teerOrZeroInvAmb authPtr authBytes i) := rfl


private theorem teer_word_ofNat_add_one (i : Nat) :
    BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 i + (1 : Word) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

private theorem teer_ofNat_zero_eq : (BitVec.ofNat 64 0 : Word) = 0 := rfl

private theorem teer_add_ofNat_zero (x : Word) : x + BitVec.ofNat 64 0 = x := by
  change x + (0 : Word) = x
  exact BitVec.add_zero x

/-- `ofNat (n+1) + se12(-1) = ofNat n` (dual ParentHeaderMemcmp.cnt_step_down). -/
private theorem teer_cnt_step (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  have e1 : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + (1 : Word) := by
    rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  rw [e1, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
      BitVec.add_assoc, show (1 : Word) + (-1 : Word) = 0 from by decide]
  exact BitVec.add_zero _

/-- `ofNat k + se12(-1) = ofNat (k-1)` for `0 < k`. -/
private theorem teer_cnt_pred (k : Nat) (hk : 0 < k) :
    BitVec.ofNat 64 k + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 (k - 1) := by
  have hk' : k = (k - 1) + 1 := by omega
  rw [hk']; exact teer_cnt_step (k - 1)

private theorem teerOrAcc_take_succ' (bs : List (BitVec 8)) (i : Nat) (hi : i < bs.length) :
    teerOrAcc (0 : Word) (bs.take (i + 1)) =
      teerOrAcc (0 : Word) (bs.take i) ||| (bs[i]'hi).zeroExtend 64 := by
  have h1 : bs.take (i + 1) = bs.take i ++ [bs[i]'hi] :=
    List.take_succ_eq_append_getElem (l := bs) (i := i) hi
  rw [h1]
  have hfold : ∀ (a : Word) (l : List (BitVec 8)) (b : BitVec 8),
      teerOrAcc a (l ++ [b]) = teerOrAcc a l ||| b.zeroExtend 64 := by
    intro a l b
    induction l generalizing a with
    | nil => simp [teerOrAcc_cons, teerOrAcc_nil]
    | cons x xs ih =>
        simp only [List.cons_append, teerOrAcc_cons]
        exact ih (a ||| x.zeroExtend 64)
  exact hfold 0 (bs.take i) (bs[i]'hi)

/-- Body LBU+OR+ADDI+ADDI (4 steps). -/
theorem teerOrZeroBody4
    (authPtr acc byteOld cnt : Word) (authBytes : List (BitVec 8)) (i : Nat)
    (halign : authPtr.toNat % 8 = 0) (hi : i < authBytes.length)
    (hover : authPtr.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (authPtr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 4 AfterOrZeroBeqNtaken AfterOrZeroAddiCnt teerLinkedField0
      ((.x29 ↦ᵣ acc) ** (.x30 ↦ᵣ byteOld) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes)
      ((.x29 ↦ᵣ (acc ||| (authBytes[i]'hi).zeroExtend 64)) **
        (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
        bytesRegion authPtr authBytes) := by
  set byteZext := (authBytes[i]'hi).zeroExtend 64
  have lbu_raw := bytesRegion_lbu_within .x30 .x7 authPtr byteOld AfterOrZeroBeqNtaken
    authBytes i (by decide) halign hi hover hvalid
  have s1 : cpsTripleWithin 1 AfterOrZeroBeqNtaken AfterOrZeroLbu teerLinkedField0
      ((.x29 ↦ᵣ acc) ** (.x30 ↦ᵣ byteOld) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes)
      ((.x29 ↦ᵣ acc) ** (.x30 ↦ᵣ byteZext) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes) := by
    have h0 := cpsTripleWithin_frameR ((.x29 ↦ᵣ acc) ** (.x28 ↦ᵣ cnt)) (by pcf) lbu_raw
    have h1 := cpsTripleWithin_extend_code
      (fun a i' hi' => teerField0_mono_teer a i'
        (CodeReq.ofProg_mem_at E AfterOrZeroBeqNtaken teerProg 600
          (.LBU .x30 .x7 (0 : BitVec 12))
          (by simp only [AfterOrZeroBeqNtaken]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterOrZeroBeqNtaken + 4 : Word) = AfterOrZeroLbu := by
      simp only [AfterOrZeroBeqNtaken, AfterOrZeroLbu]; bv_omega
    rw [hpc] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1
  have or_raw := or_spec_gen_rd_eq_rs1_within .x29 .x30 acc byteZext AfterOrZeroLbu (by nofun)
  have s2 : cpsTripleWithin 1 AfterOrZeroLbu AfterOrZeroOr teerLinkedField0
      ((.x29 ↦ᵣ acc) ** (.x30 ↦ᵣ byteZext) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes)
      ((.x29 ↦ᵣ (acc ||| byteZext)) ** (.x30 ↦ᵣ byteZext) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes) := by
    have h0 := cpsTripleWithin_frameR
      ((.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes) (by pcf) or_raw
    have h1 := cpsTripleWithin_extend_code
      (fun a i' hi' => teerField0_mono_teer a i'
        (CodeReq.ofProg_mem_at E AfterOrZeroLbu teerProg 601
          (.OR .x29 .x29 .x30)
          (by simp only [AfterOrZeroLbu]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterOrZeroLbu + 4 : Word) = AfterOrZeroOr := by
      simp only [AfterOrZeroLbu, AfterOrZeroOr]; bv_omega
    rw [hpc] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1
  have addi_ptr_raw := addi_spec_gen_same_within .x7 (authPtr + BitVec.ofNat 64 i)
    1 AfterOrZeroOr (by nofun)
  have hptr : (authPtr + BitVec.ofNat 64 i) + (1 : Word) =
      authPtr + BitVec.ofNat 64 (i + 1) := by
    rw [teer_word_ofNat_add_one i]; bv_omega
  have s3 : cpsTripleWithin 1 AfterOrZeroOr AfterOrZeroAddiPtr teerLinkedField0
      ((.x29 ↦ᵣ (acc ||| byteZext)) ** (.x30 ↦ᵣ byteZext) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes)
      ((.x29 ↦ᵣ (acc ||| byteZext)) ** (.x30 ↦ᵣ byteZext) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes) := by
    have h0 := cpsTripleWithin_frameR
      ((.x29 ↦ᵣ (acc ||| byteZext)) ** (.x30 ↦ᵣ byteZext) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes) (by pcf) addi_ptr_raw
    have h1 := cpsTripleWithin_extend_code
      (fun a i' hi' => teerField0_mono_teer a i'
        (CodeReq.ofProg_mem_at E AfterOrZeroOr teerProg 602
          (.ADDI .x7 .x7 (1 : BitVec 12))
          (by simp only [AfterOrZeroOr]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterOrZeroOr + 4 : Word) = AfterOrZeroAddiPtr := by
      simp only [AfterOrZeroOr, AfterOrZeroAddiPtr]; bv_omega
    rw [hpc, se12_1] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun s hq => by
        have hq2 :
            ((.x29 ↦ᵣ (acc ||| byteZext)) ** (.x30 ↦ᵣ byteZext) **
              (.x28 ↦ᵣ cnt) ** bytesRegion authPtr authBytes **
              (.x7 ↦ᵣ ((authPtr + BitVec.ofNat 64 i) + (1 : Word)))) s := by
          xperm_hyp hq
        have hq3 :
            ((.x29 ↦ᵣ (acc ||| byteZext)) ** (.x30 ↦ᵣ byteZext) **
              (.x28 ↦ᵣ cnt) ** bytesRegion authPtr authBytes **
              (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1)))) s := by
          simpa only [hptr] using hq2
        xperm_hyp hq3) h1
  have addi_cnt_raw := addi_spec_gen_same_within .x28 cnt (-1) AfterOrZeroAddiPtr (by nofun)
  have s4 : cpsTripleWithin 1 AfterOrZeroAddiPtr AfterOrZeroAddiCnt teerLinkedField0
      ((.x29 ↦ᵣ (acc ||| byteZext)) ** (.x30 ↦ᵣ byteZext) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes)
      ((.x29 ↦ᵣ (acc ||| byteZext)) ** (.x30 ↦ᵣ byteZext) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
        bytesRegion authPtr authBytes) := by
    have h0 := cpsTripleWithin_frameR
      ((.x29 ↦ᵣ (acc ||| byteZext)) ** (.x30 ↦ᵣ byteZext) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        bytesRegion authPtr authBytes) (by pcf) addi_cnt_raw
    have h1 := cpsTripleWithin_extend_code
      (fun a i' hi' => teerField0_mono_teer a i'
        (CodeReq.ofProg_mem_at E AfterOrZeroAddiPtr teerProg 603
          (.ADDI .x28 .x28 (-1 : BitVec 12))
          (by simp only [AfterOrZeroAddiPtr]; bv_omega)
          (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i' hi')) h0
    have hpc : (AfterOrZeroAddiPtr + 4 : Word) = AfterOrZeroAddiCnt := by
      simp only [AfterOrZeroAddiPtr, AfterOrZeroAddiCnt]; bv_omega
    rw [hpc] at h1
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 s2
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 s3
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 s4

#print axioms teerOrZeroBody4
#print axioms teer_cnt_pred
#print axioms teerOrAcc_take_succ'

/-- Body4 with x30 owned (regOwn). Post keeps concrete x30 value. -/
theorem teerOrZeroBody4_own
    (authPtr acc cnt : Word) (authBytes : List (BitVec 8)) (i : Nat)
    (halign : authPtr.toNat % 8 = 0) (hi : i < authBytes.length)
    (hover : authPtr.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (authPtr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 4 AfterOrZeroBeqNtaken AfterOrZeroAddiCnt teerLinkedField0
      (((.x29 ↦ᵣ acc) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) ** (.x28 ↦ᵣ cnt) **
        bytesRegion authPtr authBytes) ** regOwn .x30)
      ((.x29 ↦ᵣ (acc ||| (authBytes[i]'hi).zeroExtend 64)) **
        (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x28 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
        bytesRegion authPtr authBytes **
        (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64))) := by
  exact cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x30)
    (P := (.x29 ↦ᵣ acc) **
      (.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 i)) ** (.x28 ↦ᵣ cnt) **
      bytesRegion authPtr authBytes)
    (fun byteOld =>
      cpsTripleWithin_weaken
        (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq)
        (teerOrZeroBody4 authPtr acc byteOld cnt authBytes i
          halign hi hover hvalid))

/-- JAL x0 -20: AfterOrZeroAddiCnt → AfterLi0Oz. -/
theorem teerOrZeroJalBackTrip (P : Assertion) (hpc : P.pcFree) :
    cpsTripleWithin 1 AfterOrZeroAddiCnt AfterLi0Oz teerLinkedField0 P P := by
  have h0 := jal_x0_spec_gen_within teerOrZeroJalBack AfterOrZeroAddiCnt
  rw [teerOrZeroJalBack_eq] at h0
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterOrZeroAddiCnt teerProg 604
        (.JAL .x0 teerOrZeroJalBack)
        (by simp only [AfterOrZeroAddiCnt]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) h0
  have h2 := cpsTripleWithin_frameR P hpc h1
  exact cpsTripleWithin_weaken
    (fun s hp => (sepConj_emp_left _).2 hp)
    (fun s hq => (sepConj_emp_left _).1 hq) h2

/-- One full iteration: BEQ ntaken + body4 + JAL → inv i → inv (i+1). -/
theorem teerOrZeroBodyIter
    (authPtr : Word) (authBytes : List (BitVec 8)) (i : Nat)
    (hlen : authBytes.length = 20)
    (halign : authPtr.toNat % 8 = 0)
    (hi : i < authBytes.length)
    (hover : authPtr.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (authPtr + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 6 AfterLi0Oz AfterLi0Oz teerLinkedField0
      (teerOrZeroInv authPtr authBytes i)
      (teerOrZeroInv authPtr authBytes (i + 1)) := by
  set acc := teerOrAcc (0 : Word) (authBytes.take i)
  set cnt := BitVec.ofNat 64 (authBytes.length - i)
  have hne : cnt ≠ (0 : Word) := by
    intro hc
    have hlt : authBytes.length - i < 2 ^ 64 := by omega
    have ht : cnt.toNat = authBytes.length - i := by
      simp only [cnt, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
    have ht0 : (0 : Word).toNat = 0 := rfl
    simp only [hc] at ht
    rw [ht0] at ht
    omega
  have amb := teerOrZeroInvAmb authPtr authBytes i
  -- BEQ ntaken framed: leaf (x28**x0) frame amb
  have hbneF : cpsTripleWithin 1 AfterLi0Oz AfterOrZeroBeqNtaken teerLinkedField0
      (teerOrZeroInv authPtr authBytes i)
      (((.x28 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) ** teerOrZeroInvAmb authPtr authBytes i) := by
    have h0 := cpsTripleWithin_frameR (teerOrZeroInvAmb authPtr authBytes i)
      (by simp only [teerOrZeroInvAmb]; pcf)
      (teerOrZeroCntBeqNtaken cnt hne)
    exact cpsTripleWithin_weaken
      (fun s hp => by
        change (((.x28 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) **
          teerOrZeroInvAmb authPtr authBytes i) s
        dsimp only [teerOrZeroInv, cnt] at hp
        exact hp)
      (fun _ hq => hq) h0
  -- reshape amb to body4_own prest + x0 through body
  -- body4_own prest: (x29**x7**x28**blob)**regOwn x30
  -- amb: x7**x29**regOwn x30**blob
  -- full after bne: (x28**x0)**amb
  have hbodyF : cpsTripleWithin 4 AfterOrZeroBeqNtaken AfterOrZeroAddiCnt teerLinkedField0
      (((.x28 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word))) ** teerOrZeroInvAmb authPtr authBytes i)
      (((.x28 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
          (.x29 ↦ᵣ (acc ||| (authBytes[i]'hi).zeroExtend 64)) **
          (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
          bytesRegion authPtr authBytes)) := by
    have hraw := teerOrZeroBody4_own authPtr acc cnt authBytes i
      halign hi hover hvalid
    -- frame x0; reorder prest/post
    have h0 := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) hraw
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        -- goal prest: (x28**x0)**(x7**x29**regOwn x30**blob)
        -- h0 prest: ((x29**x7**x28**blob)**regOwn x30)**x0
        dsimp only [teerOrZeroInvAmb, acc] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        dsimp only [acc] at hq ⊢
        xperm_hyp hq) h0
  have hjal := teerOrZeroJalBackTrip
    (((.x28 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word))) **
      ((.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
        (.x29 ↦ᵣ (acc ||| (authBytes[i]'hi).zeroExtend 64)) **
        (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
        bytesRegion authPtr authBytes))
    (by pcf)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbneF hbodyF
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hjal
  have hcnt : cnt + signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 (authBytes.length - (i + 1)) := by
    have hk : 0 < authBytes.length - i := by omega
    simp only [cnt]
    have hrem : authBytes.length - (i + 1) = (authBytes.length - i) - 1 := by omega
    rw [hrem, teer_cnt_pred (authBytes.length - i) hk]
  have hacc : acc ||| (authBytes[i]'hi).zeroExtend 64 =
      teerOrAcc (0 : Word) (authBytes.take (i + 1)) :=
    (teerOrAcc_take_succ' authBytes i hi).symm
  -- Post after jal: (x28'**x0)**(x7'**x29'**x30↦byte**blob)
  -- Target inv (i+1): (x28'**x0)**(x7'**x29'**regOwn x30**blob)
  have hpost :
      ∀ s,
        (((.x28 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
            (.x29 ↦ᵣ (acc ||| (authBytes[i]'hi).zeroExtend 64)) **
            (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
            bytesRegion authPtr authBytes)) s →
        teerOrZeroInv authPtr authBytes (i + 1) s := by
    intro s hq
    have hq1 :
        (((.x28 ↦ᵣ BitVec.ofNat 64 (authBytes.length - (i + 1))) **
            (.x0 ↦ᵣ (0 : Word))) **
          ((.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
            (.x29 ↦ᵣ teerOrAcc (0 : Word) (authBytes.take (i + 1))) **
            (.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
            bytesRegion authPtr authBytes)) s := by
      simpa only [hcnt, hacc] using hq
    -- mono x30↦ → regOwn inside right half via reassoc
    have hq2 :
        (((.x28 ↦ᵣ BitVec.ofNat 64 (authBytes.length - (i + 1))) **
            (.x0 ↦ᵣ (0 : Word))) **
          ((.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
            (.x29 ↦ᵣ teerOrAcc (0 : Word) (authBytes.take (i + 1))) **
            regOwn .x30 **
            bytesRegion authPtr authBytes)) s := by
      refine sepConj_mono_right ?_ s hq1
      intro sR hR
      -- hR: x7 ** x29 ** x30↦ ** blob  →  x7 ** x29 ** regOwn ** blob
      have hR1 :
          (((.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
              (.x29 ↦ᵣ teerOrAcc (0 : Word) (authBytes.take (i + 1)))) **
            ((.x30 ↦ᵣ ((authBytes[i]'hi).zeroExtend 64)) **
              bytesRegion authPtr authBytes)) sR := by
        xperm_hyp hR
      have hR2 :
          (((.x7 ↦ᵣ (authPtr + BitVec.ofNat 64 (i + 1))) **
              (.x29 ↦ᵣ teerOrAcc (0 : Word) (authBytes.take (i + 1)))) **
            (regOwn .x30 ** bytesRegion authPtr authBytes)) sR :=
        sepConj_mono_right
          (fun s2 h2 =>
            sepConj_mono_left (regIs_implies_regOwn .x30) s2 h2) sR hR1
      xperm_hyp hR2
    simpa only [teerOrZeroInv, teerOrZeroInvAmb] using hq2
  exact cpsTripleWithin_weaken (fun _ hp => hp) hpost c2

/-- Loop with remaining fuel `k` starting at index `20-k`. -/
theorem teerOrZeroLoop_fuel
    (authPtr : Word) (authBytes : List (BitVec 8)) (k : Nat)
    (hlen : authBytes.length = 20)
    (halign : authPtr.toNat % 8 = 0)
    (hk : k ≤ 20)
    (hvalid_all : ∀ j, j < 20 →
      isValidByteAccess (authPtr + BitVec.ofNat 64 j) = true)
    (hover_all : authPtr.toNat + 20 ≤ 2 ^ 64) :
    cpsTripleWithin (6 * k + 1) AfterLi0Oz AfterOrZeroLoop teerLinkedField0
      (teerOrZeroInv authPtr authBytes (20 - k))
      (teerOrZeroInv authPtr authBytes 20) := by
  induction k with
  | zero =>
      -- inv 20: cnt=0; BEQ taken
      have h0 := cpsTripleWithin_frameR
        (teerOrZeroInvAmb authPtr authBytes 20)
        (by simp only [teerOrZeroInvAmb]; pcf)
        teerOrZeroCntBeqTaken
      exact cpsTripleWithin_weaken
        (fun s hp => by
          change (((.x28 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
            teerOrZeroInvAmb authPtr authBytes 20) s
          dsimp only [teerOrZeroInv] at hp
          simpa only [Nat.sub_zero, hlen, Nat.sub_self, teer_ofNat_zero_eq] using hp)
        (fun s hq => by
          change teerOrZeroInv authPtr authBytes 20 s
          dsimp only [teerOrZeroInv]
          simpa only [hlen, Nat.sub_self, teer_ofNat_zero_eq] using hq)
        (by simpa only [Nat.mul_zero, Nat.zero_add] using h0)
  | succ m ih =>
      have hm : m ≤ 20 := by omega
      have hi : 20 - (m + 1) < authBytes.length := by omega
      have hover : authPtr.toNat + (20 - (m + 1)) < 2 ^ 64 := by omega
      have hvalid := hvalid_all (20 - (m + 1)) (by omega)
      have hstep := teerOrZeroBodyIter authPtr authBytes (20 - (m + 1))
        hlen halign hi hover hvalid
      have hidx : (20 - (m + 1)) + 1 = 20 - m := by omega
      have hstep' : cpsTripleWithin 6 AfterLi0Oz AfterLi0Oz teerLinkedField0
          (teerOrZeroInv authPtr authBytes (20 - (m + 1)))
          (teerOrZeroInv authPtr authBytes (20 - m)) := by
        simpa only [hidx] using hstep
      have hrest := ih hm
      have hseq := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hstep' hrest
      have hn : 6 + (6 * m + 1) = 6 * (m + 1) + 1 := by omega
      simpa only [hn] using hseq

/-- Full 20-iter OR-reduce under inv shape: AfterLi0Oz → AfterOrZeroLoop. -/
theorem teerOrZeroLoop20
    (authPtr : Word) (authBytes : List (BitVec 8))
    (hlen : authBytes.length = 20)
    (halign : authPtr.toNat % 8 = 0)
    (hover : authPtr.toNat + 20 ≤ 2 ^ 64)
    (hvalid : ∀ k, k < 20 →
      isValidByteAccess (authPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 121 AfterLi0Oz AfterOrZeroLoop teerLinkedField0
      (teerOrZeroInv authPtr authBytes 0)
      (teerOrZeroInv authPtr authBytes 20) := by
  have hloop := teerOrZeroLoop_fuel authPtr authBytes 20 hlen halign (by omega) hvalid hover
  have hn : 6 * 20 + 1 = 121 := by decide
  simpa only [Nat.sub_self, hn] using hloop

/-- Assumed prest (nested) → `teerOrZeroInv 0` under `hlen`. -/
private theorem teerOrZeroAssumedPre_to_inv0
    (authPtr : Word) (authBytes : List (BitVec 8))
    (hlen : authBytes.length = 20) :
    ∀ s,
      (((.x28 ↦ᵣ (20 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x7 ↦ᵣ authPtr) ** (.x29 ↦ᵣ (0 : Word)) **
          regOwn .x30 ** bytesRegion authPtr authBytes)) s →
      teerOrZeroInv authPtr authBytes 0 s := by
  intro s hp
  dsimp only [teerOrZeroInv, teerOrZeroInvAmb]
  -- goal: ((x28↦ofNat(len-0) ** x0↦0) ** (x7↦auth+0 ** x29↦orAcc 0 [] ** ...))
  have h20 : BitVec.ofNat 64 20 = (20 : Word) := rfl
  simpa only [hlen, Nat.sub_zero, List.take_zero, teerOrAcc_nil, teer_add_ofNat_zero, h20]
    using hp

/-- `teerOrZeroInv 20` → Assumed post under `hlen`. -/
private theorem teerOrZeroInv20_to_assumedPost
    (authPtr : Word) (authBytes : List (BitVec 8))
    (hlen : authBytes.length = 20) :
    ∀ s, teerOrZeroInv authPtr authBytes 20 s →
      (((.x28 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x7 ↦ᵣ (authPtr + (20 : Word))) **
          (.x29 ↦ᵣ teerOrAcc (0 : Word) authBytes) **
          regOwn .x30 ** bytesRegion authPtr authBytes)) s := by
  intro s hq
  dsimp only [teerOrZeroInv, teerOrZeroInvAmb] at hq
  have htake : authBytes.take 20 = authBytes :=
    List.take_of_length_le (by omega)
  have h20 : BitVec.ofNat 64 20 = (20 : Word) := rfl
  simpa only [hlen, Nat.sub_self, teer_ofNat_zero_eq, htake, h20] using hq

/-- Fill TeerAuthOrZeroAssumed under teerLinkedField0. -/
def teerAuthOrZeroAssumed_teerLinked : TeerAuthOrZeroAssumed teerLinkedField0 where
  nSteps := 121
  or_flat := fun authPtr authBytes hlen halign hover hvalid =>
    cpsTripleWithin_weaken
      (teerOrZeroAssumedPre_to_inv0 authPtr authBytes hlen)
      (teerOrZeroInv20_to_assumedPost authPtr authBytes hlen)
      (teerOrZeroLoop20 authPtr authBytes hlen halign hover hvalid)

#print axioms teerOrZeroBody4_own
#print axioms teerOrZeroJalBackTrip
#print axioms teerOrZeroBodyIter
#print axioms teerOrZeroLoop_fuel
#print axioms teerOrZeroLoop20
#print axioms teerAuthOrZeroAssumed_teerLinked
#print axioms teerOrZeroThenSuccessSkip

end EvmAsm.Codegen.TxEip7702TeerSpec
