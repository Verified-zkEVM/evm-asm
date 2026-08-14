/-
  EvmAsm.Codegen.Programs.Secp256k1FieldReduceOnceNSAsm

  Final branch merge and whole-frame CPS proof for `secf_reduce_once`.
-/

import EvmAsm.Codegen.Programs.Secp256k1FieldReduceOnceNSAsmSupport

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1FieldReduceOnceNSAsm

#guard secfReduceOnceN_prog.length = 32

private theorem cmpFlag_ne_zero_reduce (xs orig : List (BitVec 8))
    (hflag : cmpFlagWordN xs ≠ (0 : Word)) :
    reduceOnceNFlag xs = (0 : Word) ∧ reduceOnceNBytes xs orig = xs := by
  unfold cmpFlagWordN reduceOnceNFlag reduceOnceNBytes at *
  by_cases hlt : beBytesToNat xs < beBytesToNat secfNBytes
  · simp [hlt]
  · simp [hlt] at hflag

private theorem cmpFlag_eq_zero_reduce (xs orig : List (BitVec 8))
    (hflag : cmpFlagWordN xs = (0 : Word)) :
    reduceOnceNFlag xs = (1 : Word) ∧
      reduceOnceNBytes xs orig = U256SubBeSAsm.u256SubBeBytes xs secfNBytes orig := by
  unfold cmpFlagWordN reduceOnceNFlag reduceOnceNBytes at *
  by_cases hlt : beBytesToNat xs < beBytesToNat secfNBytes
  · simp [hlt] at hflag
  · simp [hlt]


private def copyBranchPostFrame (src dst flag : Word) (xs orig : List (BitVec 8)) : Assertion :=
  (((.x6 : Reg) ↦ᵣ flag) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜flag ≠ 0⌝ **
    ((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) **
    ((.x11 : Reg) ↦ᵣ (GuestAddrs.secf_n_be : Word)) **
    ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
    ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once_n + 48 : Word)) **
    ((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
    regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    bytesRegion src xs ** globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
    ((GuestAddrs.secf_cmp : Word) ↦ₘ flag) **
    (bytesRegion dst orig ** regOwns highScratch))

private def copyArmPreFrame (src dst flag : Word) (xs orig : List (BitVec 8)) : Assertion :=
  (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) **
    ((.x11 : Reg) ↦ᵣ (GuestAddrs.secf_n_be : Word)) **
    ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once_n + 48 : Word)) **
    regOwns copyScratch ** bytesRegion src xs ** bytesRegion dst orig **
    (⌜flag ≠ 0⌝ ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
      ((GuestAddrs.secf_cmp : Word) ↦ₘ flag)))

private theorem copyBranch_to_copyPre (src dst flag : Word) (xs orig : List (BitVec 8)) :
    ∀ h, copyBranchPostFrame src dst flag xs orig h → copyArmPreFrame src dst flag xs orig h := by
  intro h hp
  unfold copyBranchPostFrame at hp
  unfold copyArmPreFrame
  have hp1 : (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secf_n_be : Word)) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once_n + 48 : Word)) **
        ((((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
          ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwns highScratch)) **
        bytesRegion src xs ** bytesRegion dst orig **
        (⌜flag ≠ 0⌝ ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
          ((GuestAddrs.secf_cmp : Word) ↦ₘ flag))) h := by
    xperm_hyp hp
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left
      (branchScratch_to_copyScratch (GuestAddrs.secf_cmp : Word) flag (GuestAddrs.secf_cmp : Word))))))) h hp1



private def subBranchPostFrame (src dst flag : Word) (xs orig : List (BitVec 8)) : Assertion :=
  (((.x6 : Reg) ↦ᵣ flag) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜flag = 0⌝ **
    ((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) **
    ((.x11 : Reg) ↦ᵣ (GuestAddrs.secf_n_be : Word)) **
    ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
    ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once_n + 48 : Word)) **
    ((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
    regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    bytesRegion src xs ** globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
    ((GuestAddrs.secf_cmp : Word) ↦ₘ flag) **
    (bytesRegion dst orig ** regOwns highScratch))

private def subArmPreFrame (src dst flag : Word) (xs orig : List (BitVec 8)) : Assertion :=
  (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) **
    ((.x11 : Reg) ↦ᵣ (GuestAddrs.secf_n_be : Word)) **
    ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
    ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once_n + 48 : Word)) **
    regOwns subScratch ** bytesRegion dst orig ** bytesRegion src xs **
    globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
    (⌜flag = 0⌝ ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((GuestAddrs.secf_cmp : Word) ↦ₘ flag)))

private theorem subBranch_to_subPre (src dst flag : Word) (xs orig : List (BitVec 8)) :
    ∀ h, subBranchPostFrame src dst flag xs orig h → subArmPreFrame src dst flag xs orig h := by
  intro h hp
  unfold subBranchPostFrame at hp
  unfold subArmPreFrame
  have hp1 : (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (GuestAddrs.secf_n_be : Word)) **
        ((.x12 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) **
        ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once_n + 48 : Word)) **
        ((((.x5 : Reg) ↦ᵣ (GuestAddrs.secf_cmp : Word)) ** ((.x6 : Reg) ↦ᵣ flag) **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwns highScratch)) **
        bytesRegion dst orig ** bytesRegion src xs **
        globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
        (⌜flag = 0⌝ ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((GuestAddrs.secf_cmp : Word) ↦ₘ flag))) h := by
    xperm_hyp hp
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (branchScratch_to_subScratch (GuestAddrs.secf_cmp : Word) flag))))))) h hp1




private def reduceCallerPre (src dst v12 : Word) (xs orig : List (BitVec 8)) : Assertion :=
  (((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) ** ((.x12 : Reg) ↦ᵣ v12) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    bytesRegion src xs ** globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
    memOwn (GuestAddrs.secf_cmp : Word) **
    (bytesRegion dst orig ** regOwns highScratch))

private theorem reduceCmpBranchFramed_spec (src dst ret v8 v9 v12 : Word)
    (xs orig : List (BitVec 8))
    (hlenX : xs.length = 32)
    (halignX : src.toNat % 8 = 0)
    (hovX : src.toNat + 32 < 2 ^ 64)
    (hvalidX : ∀ k, k < 32 → isValidByteAccess (src + BitVec.ofNat 64 k) = true) :
    cpsBranchWithin 307 (GuestAddrs.secf_reduce_once_n + 16 : Word) secfReduceOnceNCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs **
        globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
        memOwn (GuestAddrs.secf_cmp : Word) **
        (bytesRegion dst orig ** regOwns highScratch))
      (GuestAddrs.secf_reduce_once_n + 92 : Word)
      (copyBranchPostFrame src dst (cmpFlagWordN xs) xs orig)
      (GuestAddrs.secf_reduce_once_n + 64 : Word)
      (subBranchPostFrame src dst (cmpFlagWordN xs) xs orig) := by
  have hbr0 := ltSetupCallLoadBranch_spec src dst ret v8 v9 v12 xs hlenX halignX hovX hvalidX
  have hbrF := cpsBranchWithin_frameR (bytesRegion dst orig ** regOwns highScratch) (by pcf) hbr0
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      unfold copyBranchPostFrame cmpFlagWordN
      xperm_hyp hq)
    (fun _ hq => by
      unfold subBranchPostFrame cmpFlagWordN
      xperm_hyp hq) hbrF

private def reduceCallerPost (src dst : Word) (xs orig : List (BitVec 8)) : Assertion :=
  (((.x10 : Reg) ↦ᵣ reduceOnceNFlag xs) ** regOwns retScratch **
    bytesRegion dst (reduceOnceNBytes xs orig) ** bytesRegion src xs **
    globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((GuestAddrs.secf_cmp : Word) ↦ₘ cmpFlagWordN xs)))

private def reduceJoinPost (src dst : Word) (xs orig : List (BitVec 8)) : Assertion :=
  (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) ** regOwn .x1 **
    reduceCallerPost src dst xs orig)

private def copyArmPostFrame (src dst : Word) (xs : List (BitVec 8)) : Assertion :=
  (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
    ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once_n + 104 : Word)) **
    ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch **
    bytesRegion src xs ** bytesRegion dst xs **
    (⌜cmpFlagWordN xs ≠ 0⌝ ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
      ((GuestAddrs.secf_cmp : Word) ↦ₘ cmpFlagWordN xs)))

private def subArmPostFrame (src dst : Word) (xs orig : List (BitVec 8)) : Assertion :=
  (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
    ((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once_n + 84 : Word)) **
    ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regOwns retScratch **
    bytesRegion dst (U256SubBeSAsm.u256SubBeBytes xs secfNBytes orig) **
    bytesRegion src xs ** globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
    (⌜cmpFlagWordN xs = 0⌝ ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((GuestAddrs.secf_cmp : Word) ↦ₘ cmpFlagWordN xs)))

private theorem copyPost_to_reducePost (src dst : Word) (xs orig : List (BitVec 8)) :
    ∀ h, copyArmPostFrame src dst xs h → reduceJoinPost src dst xs orig h := by
  intro h hp
  unfold copyArmPostFrame at hp
  unfold reduceJoinPost
  extract_pure_deep hp
  obtain ⟨hflag, hp⟩ := hp
  have hred := cmpFlag_ne_zero_reduce xs orig hflag
  have hp1 : (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once_n + 104 : Word)) **
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch **
        bytesRegion src xs ** bytesRegion dst xs **
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
          ((GuestAddrs.secf_cmp : Word) ↦ₘ cmpFlagWordN xs)))) h := by
    xperm_hyp hp
  have hp2 : (regOwn .x1 **
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** regOwns retScratch **
        bytesRegion src xs ** bytesRegion dst xs **
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
          ((GuestAddrs.secf_cmp : Word) ↦ₘ cmpFlagWordN xs)))) h := by
    exact sepConj_mono_left
      (regIs_to_regOwn .x1 (GuestAddrs.secf_reduce_once_n + 104 : Word)) h hp1
  unfold reduceCallerPost
  rw [hred.1, hred.2]
  xperm_hyp hp2


private theorem copyBranchToReduceJoin_spec (src dst : Word)
    (xs orig : List (BitVec 8))
    (hlenX : xs.length = 32) (hlenOrig : orig.length = 32) :
    cpsTripleWithin ((2 + (1 + 9)) + 1)
      (GuestAddrs.secf_reduce_once_n + 92 : Word)
      (GuestAddrs.secf_reduce_once_n + 108 : Word) secfReduceOnceNCr
      (copyBranchPostFrame src dst (cmpFlagWordN xs) xs orig)
      (reduceJoinPost src dst xs orig) := by
  have hcopy0 := copyArm_spec src dst (GuestAddrs.secf_reduce_once_n + 48 : Word)
    (0 : Word) (GuestAddrs.secf_n_be : Word) xs orig hlenX hlenOrig
  have hcopyF := cpsTripleWithin_frameR
    (⌜cmpFlagWordN xs ≠ 0⌝ ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
      ((GuestAddrs.secf_cmp : Word) ↦ₘ cmpFlagWordN xs)) (by pcf) hcopy0
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hcopyF
  · have hp1 := copyBranch_to_copyPre src dst (cmpFlagWordN xs) xs orig h hp
    unfold copyArmPreFrame at hp1
    xperm_hyp hp1
  · have hq1 : copyArmPostFrame src dst xs h := by
      unfold copyArmPostFrame
      xperm_hyp hq
    exact copyPost_to_reducePost src dst xs orig h hq1

private theorem subPost_to_reducePost (src dst : Word) (xs orig : List (BitVec 8)) :
    ∀ h, subArmPostFrame src dst xs orig h → reduceJoinPost src dst xs orig h := by
  intro h hp
  unfold subArmPostFrame at hp
  unfold reduceJoinPost
  extract_pure_deep hp
  obtain ⟨hflag, hp⟩ := hp
  have hred := cmpFlag_eq_zero_reduce xs orig hflag
  have hp1 : (((.x1 : Reg) ↦ᵣ (GuestAddrs.secf_reduce_once_n + 84 : Word)) **
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regOwns retScratch **
        bytesRegion dst (U256SubBeSAsm.u256SubBeBytes xs secfNBytes orig) **
        bytesRegion src xs ** globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((GuestAddrs.secf_cmp : Word) ↦ₘ cmpFlagWordN xs)))) h := by
    xperm_hyp hp
  have hp2 : (regOwn .x1 **
      (((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        ((.x10 : Reg) ↦ᵣ (1 : Word)) ** regOwns retScratch **
        bytesRegion dst (U256SubBeSAsm.u256SubBeBytes xs secfNBytes orig) **
        bytesRegion src xs ** globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((GuestAddrs.secf_cmp : Word) ↦ₘ cmpFlagWordN xs)))) h := by
    exact sepConj_mono_left
      (regIs_to_regOwn .x1 (GuestAddrs.secf_reduce_once_n + 84 : Word)) h hp1
  unfold reduceCallerPost
  rw [hred.1, hred.2]
  xperm_hyp hp2




private theorem subBranchToReduceJoin_spec (src dst : Word)
    (xs orig : List (BitVec 8))
    (hroX : Region.wf ⟨src, xs⟩)
    (hrwDst : RwRegion.wf ⟨dst, 32⟩)
    (hlenX : xs.length = 32) (hlenOrig : orig.length = 32)
    (hovX : src.toNat + 32 < 2 ^ 64)
    (hovDst : dst.toNat + 32 < 2 ^ 64)
    (hdisjX : src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat)
    (hdisjP : (GuestAddrs.secf_n_be : Word).toNat + 32 ≤ dst.toNat ∨
      dst.toNat + 32 ≤ (GuestAddrs.secf_n_be : Word).toNat) :
    cpsTripleWithin ((4 + (1 + ((U256SubBeSAsm.u256SubBeFn src
        (GuestAddrs.secf_n_be : Word) dst xs secfNBytes orig).body.steps + 1))) + 2)
      (GuestAddrs.secf_reduce_once_n + 64 : Word)
      (GuestAddrs.secf_reduce_once_n + 108 : Word) secfReduceOnceNCr
      (subBranchPostFrame src dst (cmpFlagWordN xs) xs orig)
      (reduceJoinPost src dst xs orig) := by
  have hsub0 := subArm_spec src dst (GuestAddrs.secf_reduce_once_n + 48 : Word)
    (0 : Word) (GuestAddrs.secf_n_be : Word) (GuestAddrs.secf_cmp : Word)
    xs orig hroX hrwDst hlenX hlenOrig hovX hovDst hdisjX hdisjP
  have hsubF := cpsTripleWithin_frameR
    (⌜cmpFlagWordN xs = 0⌝ ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((GuestAddrs.secf_cmp : Word) ↦ₘ cmpFlagWordN xs)) (by pcf) hsub0
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hsubF
  · have hp1 := subBranch_to_subPre src dst (cmpFlagWordN xs) xs orig h hp
    unfold subArmPreFrame at hp1
    xperm_hyp hp1
  · have hq1 : subArmPostFrame src dst xs orig h := by
      unfold subArmPostFrame
      xperm_hyp hq
    exact subPost_to_reducePost src dst xs orig h hq1


private theorem reduceBodyBranch_spec (src dst ret v8 v9 v12 : Word)
    (xs orig : List (BitVec 8))
    (hroX : Region.wf ⟨src, xs⟩)
    (hrwDst : RwRegion.wf ⟨dst, 32⟩)
    (hlenX : xs.length = 32) (hlenOrig : orig.length = 32)
    (halignX : src.toNat % 8 = 0)
    (hovX : src.toNat + 32 < 2 ^ 64)
    (hvalidX : ∀ k, k < 32 → isValidByteAccess (src + BitVec.ofNat 64 k) = true)
    (hovDst : dst.toNat + 32 < 2 ^ 64)
    (hdisjX : src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat)
    (hdisjP : (GuestAddrs.secf_n_be : Word).toNat + 32 ≤ dst.toNat ∨
      dst.toNat + 32 ≤ (GuestAddrs.secf_n_be : Word).toNat) :
    cpsTripleWithin (307 + (((2 + (1 + 9)) + 1) +
        ((4 + (1 + ((U256SubBeSAsm.u256SubBeFn src
        (GuestAddrs.secf_n_be : Word) dst xs secfNBytes orig).body.steps + 1))) + 2)))
      (GuestAddrs.secf_reduce_once_n + 16 : Word)
      (GuestAddrs.secf_reduce_once_n + 108 : Word) secfReduceOnceNCr
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        bytesRegion src xs **
        globalConst (GuestAddrs.secf_n_be : Word) secfNBytes **
        memOwn (GuestAddrs.secf_cmp : Word) **
        (bytesRegion dst orig ** regOwns highScratch))
      (reduceJoinPost src dst xs orig) := by
  have hbr := reduceCmpBranchFramed_spec src dst ret v8 v9 v12 xs orig
    hlenX halignX hovX hvalidX
  have hcopy0 := copyBranchToReduceJoin_spec src dst xs orig hlenX hlenOrig
  have hcopy : cpsTripleWithin (((2 + (1 + 9)) + 1) +
        ((4 + (1 + ((U256SubBeSAsm.u256SubBeFn src
        (GuestAddrs.secf_n_be : Word) dst xs secfNBytes orig).body.steps + 1))) + 2))
      (GuestAddrs.secf_reduce_once_n + 92 : Word)
      (GuestAddrs.secf_reduce_once_n + 108 : Word) secfReduceOnceNCr
      (copyBranchPostFrame src dst (cmpFlagWordN xs) xs orig)
      (reduceJoinPost src dst xs orig) := by
    exact cpsTripleWithin_mono_nSteps (by omega) hcopy0
  have hsub0 := subBranchToReduceJoin_spec src dst xs orig hroX hrwDst hlenX hlenOrig
    hovX hovDst hdisjX hdisjP
  have hsub : cpsTripleWithin (((2 + (1 + 9)) + 1) +
        ((4 + (1 + ((U256SubBeSAsm.u256SubBeFn src
        (GuestAddrs.secf_n_be : Word) dst xs secfNBytes orig).body.steps + 1))) + 2))
      (GuestAddrs.secf_reduce_once_n + 64 : Word)
      (GuestAddrs.secf_reduce_once_n + 108 : Word) secfReduceOnceNCr
      (subBranchPostFrame src dst (cmpFlagWordN xs) xs orig)
      (reduceJoinPost src dst xs orig) := by
    exact cpsTripleWithin_mono_nSteps (by omega) hsub0
  exact cpsBranchWithin_merge_same_cr hbr hcopy hsub


private theorem reduceRestoreTail_spec (sp0 ret src dst s0 s1 : Word)
    (xs orig : List (BitVec 8))
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (secfReduceOnceNFrame.length + 1 + 1)
      (GuestAddrs.secf_reduce_once_n + 108 : Word) ret secfReduceOnceNCr
      (((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12))) **
        frameSlotsSaved secfReduceOnceNFrame (sp0 + signExtend12 (-32 : BitVec 12))
          (secfReduceOnceNVals ret s0 s1) **
        reduceJoinPost src dst xs orig)
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt secfReduceOnceNFrame (secfReduceOnceNVals ret s0 s1) **
        frameSlotsSaved secfReduceOnceNFrame (sp0 + signExtend12 (-32 : BitVec 12))
          (secfReduceOnceNVals ret s0 s1) **
        reduceCallerPost src dst xs orig) := by
  set newSp := sp0 + signExtend12 (-32 : BitVec 12) with hnewSp
  have hcore : cpsTripleWithin (secfReduceOnceNFrame.length + 1 + 1)
      (GuestAddrs.secf_reduce_once_n + 108 : Word) ret secfReduceOnceNCr
      (((((.x2 : Reg) ↦ᵣ newSp) **
        frameSlotsSaved secfReduceOnceNFrame newSp (secfReduceOnceNVals ret s0 s1) **
        ((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        reduceCallerPost src dst xs orig) ** regOwn .x1))
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt secfReduceOnceNFrame (secfReduceOnceNVals ret s0 s1) **
        frameSlotsSaved secfReduceOnceNFrame newSp (secfReduceOnceNVals ret s0 s1) **
        reduceCallerPost src dst xs orig) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x1)
      (P := (((.x2 : Reg) ↦ᵣ newSp) **
        frameSlotsSaved secfReduceOnceNFrame newSp (secfReduceOnceNVals ret s0 s1) **
        ((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst) **
        reduceCallerPost src dst xs orig))
      (Q := (((.x2 : Reg) ↦ᵣ sp0) ** regsAt secfReduceOnceNFrame (secfReduceOnceNVals ret s0 s1) **
        frameSlotsSaved secfReduceOnceNFrame newSp (secfReduceOnceNVals ret s0 s1) **
        reduceCallerPost src dst xs orig)) ?_
    intro v1
    have hload0 := loadSeq_spec secfReduceOnceNFrame newSp
      (secfReduceOnceNVals ret s0 s1) (secfReduceOnceNVals v1 src dst)
      (GuestAddrs.secf_reduce_once_n + 108 : Word) (by decide) (by decide)
    have hload := liftCode (cr' := secfReduceOnceNCr) hload0
      (by unfold secfReduceOnceNCr; code_mem)
    rw [show (GuestAddrs.secf_reduce_once_n + 108 : Word) + BitVec.ofNat 64 (4 * secfReduceOnceNFrame.length) =
        (GuestAddrs.secf_reduce_once_n + 120 : Word) from by decide] at hload
    have hloadF := cpsTripleWithin_frameR (reduceCallerPost src dst xs orig) (by pcf) hload
    have hdealloc0 := addi_spec_gen_same_within .x2 newSp (32 : BitVec 12)
      (GuestAddrs.secf_reduce_once_n + 120 : Word) (by decide)
    rw [show newSp + signExtend12 (32 : BitVec 12) = sp0 from by
        rw [hnewSp]
        exact sext_frameRestore sp0 (-32 : BitVec 12) (32 : BitVec 12) (by decide)] at hdealloc0
    have hdealloc := liftCode (cr' := secfReduceOnceNCr) hdealloc0
      (by unfold secfReduceOnceNCr; code_mem)
    rw [show (GuestAddrs.secf_reduce_once_n + 120 : Word) + 4 =
        (GuestAddrs.secf_reduce_once_n + 124 : Word) from by decide] at hdealloc
    have hdeallocF := cpsTripleWithin_frameR
      (regsAt secfReduceOnceNFrame (secfReduceOnceNVals ret s0 s1) **
        frameSlotsSaved secfReduceOnceNFrame newSp (secfReduceOnceNVals ret s0 s1) **
        reduceCallerPost src dst xs orig) (by pcf) hdealloc
    have hret0 := EvmAsm.Evm64.ret_spec_within' (GuestAddrs.secf_reduce_once_n + 124 : Word) ret
    rw [halign] at hret0
    have hret := liftCode (cr' := secfReduceOnceNCr) hret0
      (by unfold secfReduceOnceNCr; code_mem)
    have hretF := cpsTripleWithin_frameR
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12))]
          (secfReduceOnceNVals ret s0 s1) **
        frameSlotsSaved secfReduceOnceNFrame newSp (secfReduceOnceNVals ret s0 s1) **
        reduceCallerPost src dst xs orig) (by pcf) hret
    have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
        xperm_hyp hp) hloadF hdeallocF
    have hReg : regsAt secfReduceOnceNFrame (secfReduceOnceNVals ret s0 s1) =
        (((.x1 : Reg) ↦ᵣ ret) ** regsAt [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12))]
          (secfReduceOnceNVals ret s0 s1)) := by
      simp only [secfReduceOnceNFrame, regsAt, secfReduceOnceNVals, List.foldr_cons,
        List.foldr_nil, sepConj_emp_right']
    rw [hReg] at h12
    have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12 hretF
    have hRegV : regsAt secfReduceOnceNFrame (secfReduceOnceNVals v1 src dst) =
        (((.x1 : Reg) ↦ᵣ v1) ** ((.x8 : Reg) ↦ᵣ src) ** ((.x9 : Reg) ↦ᵣ dst)) := by
      simp only [secfReduceOnceNFrame, regsAt, secfReduceOnceNVals, List.foldr_cons,
        List.foldr_nil, sepConj_emp_right']
    exact cpsTripleWithin_weaken (fun _ hp => by
        rw [hRegV]
        xperm_hyp hp)
      (fun _ hq => by
        rw [hReg]
        xperm_hyp hq) h123
  exact cpsTripleWithin_weaken (fun h hp => by
      unfold reduceJoinPost at hp
      rw [hnewSp]
      xperm_hyp hp)
    (fun h hq => by
      rw [hnewSp] at hq
      xperm_hyp hq) hcore


theorem secfReduceOnceNFrame_spec (sp0 ret src dst s0 s1 v12 : Word)
    (xs orig : List (BitVec 8))
    (hroX : Region.wf ⟨src, xs⟩)
    (hrwDst : RwRegion.wf ⟨dst, 32⟩)
    (hlenX : xs.length = 32) (hlenOrig : orig.length = 32)
    (halignX : src.toNat % 8 = 0)
    (hovX : src.toNat + 32 < 2 ^ 64)
    (hvalidX : ∀ k, k < 32 → isValidByteAccess (src + BitVec.ofNat 64 k) = true)
    (hovDst : dst.toNat + 32 < 2 ^ 64)
    (hdisjX : src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat)
    (hdisjP : (GuestAddrs.secf_n_be : Word).toNat + 32 ≤ dst.toNat ∨
      dst.toNat + 32 ≤ (GuestAddrs.secf_n_be : Word).toNat)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (1 + secfReduceOnceNFrame.length +
        (307 + (((2 + (1 + 9)) + 1) +
          ((4 + (1 + ((U256SubBeSAsm.u256SubBeFn src
            (GuestAddrs.secf_n_be : Word) dst xs secfNBytes orig).body.steps + 1))) + 2))) +
        (secfReduceOnceNFrame.length + 1 + 1))
      (GuestAddrs.secf_reduce_once_n : Word) ret secfReduceOnceNCr
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt secfReduceOnceNFrame (secfReduceOnceNVals ret s0 s1) **
        frameSlotsOwn secfReduceOnceNFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
        reduceCallerPre src dst v12 xs orig)
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt secfReduceOnceNFrame (secfReduceOnceNVals ret s0 s1) **
        frameSlotsSaved secfReduceOnceNFrame (sp0 + signExtend12 (-32 : BitVec 12))
          (secfReduceOnceNVals ret s0 s1) **
        reduceCallerPost src dst xs orig) := by
  set newSp := sp0 + signExtend12 (-32 : BitVec 12) with hnewSp
  have halloc0 := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12)
    (GuestAddrs.secf_reduce_once_n : Word) (by decide)
  rw [← hnewSp] at halloc0
  have halloc := liftCode (cr' := secfReduceOnceNCr) halloc0
    (by unfold secfReduceOnceNCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once_n : Word) + 4 =
      (GuestAddrs.secf_reduce_once_n + 4 : Word) from by decide] at halloc
  have hallocF := cpsTripleWithin_frameR
    (regsAt secfReduceOnceNFrame (secfReduceOnceNVals ret s0 s1) **
      frameSlotsOwn secfReduceOnceNFrame newSp ** reduceCallerPre src dst v12 xs orig) (by pcf) halloc
  have hstore0 := storeSeq_spec secfReduceOnceNFrame newSp (secfReduceOnceNVals ret s0 s1)
    (GuestAddrs.secf_reduce_once_n + 4 : Word) (by decide)
  have hstore := liftCode (cr' := secfReduceOnceNCr) hstore0
    (by unfold secfReduceOnceNCr; code_mem)
  rw [show (GuestAddrs.secf_reduce_once_n + 4 : Word) + BitVec.ofNat 64 (4 * secfReduceOnceNFrame.length) =
      (GuestAddrs.secf_reduce_once_n + 16 : Word) from by decide] at hstore
  have hstoreF := cpsTripleWithin_frameR (reduceCallerPre src dst v12 xs orig) (by pcf) hstore
  have hbody0 := reduceBodyBranch_spec src dst ret s0 s1 v12 xs orig hroX hrwDst hlenX hlenOrig
    halignX hovX hvalidX hovDst hdisjX hdisjP
  have hbodyF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
      frameSlotsSaved secfReduceOnceNFrame newSp (secfReduceOnceNVals ret s0 s1)) (by pcf) hbody0
  have htail := reduceRestoreTail_spec sp0 ret src dst s0 s1 xs orig halignRet
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hallocF hstoreF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      unfold reduceCallerPre at hp
      simp only [secfReduceOnceNFrame, regsAt, secfReduceOnceNVals, List.foldr_cons,
        List.foldr_nil, sepConj_emp_right'] at hp ⊢
      xperm_hyp hp) h12 hbodyF
  have h1234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h123 htail
  exact cpsTripleWithin_weaken (fun _ hp => by
      rw [hnewSp]
      xperm_hyp hp)
    (fun _ hq => by
      rw [hnewSp]
      xperm_hyp hq) h1234


end Secp256k1FieldReduceOnceNSAsm

end EvmAsm.Codegen
