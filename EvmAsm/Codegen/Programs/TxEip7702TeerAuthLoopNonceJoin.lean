/-
  Teer auth-loop after bal_nonce status=0:
  AfterBalNonceBeq0 (E+2016) MV x6←a1 (nonce) + authority/sender setup +
  20B cmp (Assumed) + prior_count add + BNE match → AfterNonceEq (E+2096).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBalNonce
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopRecoverCall
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
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

abbrev AfterMvNonce : Word := E + 2020
abbrev AfterLaAuthNj : Word := E + 2028
abbrev AfterLaSenderNj : Word := E + 2036
abbrev AfterLi20Nj : Word := E + 2040
/-- After `addi x6,x6,1` (E+2072); prior_count la starts here. -/
abbrev AfterAuthSenderInc : Word := E + 2076
abbrev AfterLaPriorNj : Word := E + 2084
abbrev AfterLdPriorNj : Word := E + 2088
abbrev AfterAddPriorNj : Word := E + 2092
abbrev AfterLdNonceScratchNj : Word := E + 2096
abbrev AfterNonceEq : Word := E + 2100

def SenderAddr : Word := BitVec.ofNat 64 GuestAddrs.bv_stx_sender_addr

private theorem se12_zero_nj : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_144_nj : signExtend12 (144 : BitVec 12) = (144 : Word) := by decide

/-- Named hyp: authority==sender 20B cmp loop + `addi x6,x6,1`.
    Prest at AfterLi20Nj (x29=20, x7=AuthorityAddr, x28=SenderAddr).
    Post at AfterAuthSenderInc with x6 = nonceVal+1. -/
structure TeerAuthSenderMatchAssumed (cr : CodeReq) where
  nSteps : Nat
  match_flat :
    ∀ (nonceVal : Word),
      cpsTripleWithin nSteps AfterLi20Nj AfterAuthSenderInc cr
        ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ AuthorityAddr) ** (.x28 ↦ᵣ SenderAddr) **
          (.x29 ↦ᵣ (20 : Word)) **
          regOwn .x30 ** regOwn .x31 **
          memOwn AuthorityAddr ** memOwn SenderAddr **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x6 ↦ᵣ (nonceVal + (1 : Word))) **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 **
          memOwn AuthorityAddr ** memOwn SenderAddr **
          (.x0 ↦ᵣ (0 : Word)))

/-- `mv x6, x11` AfterBalNonceBeq0 → AfterMvNonce. -/
theorem teerMvNonceFromA1 (nonceVal x6Old : Word) :
    cpsTripleWithin 1 AfterBalNonceBeq0 AfterMvNonce teerLinkedField0
      ((.x6 ↦ᵣ x6Old) ** (.x11 ↦ᵣ nonceVal))
      ((.x6 ↦ᵣ nonceVal) ** (.x11 ↦ᵣ nonceVal)) := by
  have h0 := mv_spec_gen_within .x6 .x11 nonceVal x6Old AfterBalNonceBeq0 (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterBalNonceBeq0 teerProg 504
        (.MV .x6 .x11) (by simp only [AfterBalNonceBeq0]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterBalNonceBeq0 + 4 : Word) = AfterMvNonce := by
    simp only [AfterBalNonceBeq0, AfterMvNonce]; bv_omega
  rw [hpc] at h1
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h1

/-- `la x7, teer_authority` AfterMvNonce. -/
theorem teerLaAuthNj (v : Word) :
    cpsTripleWithin 2 AfterMvNonce AfterLaAuthNj teerLinkedField0
      (.x7 ↦ᵣ v) (.x7 ↦ᵣ AuthorityAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterMvNonce
      (.AUIPC .x7 (Codegen.laHi GuestAddrs.teer_authority
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2020)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterMvNonce teerProg 505
        (.AUIPC .x7 (Codegen.laHi GuestAddrs.teer_authority
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2020)))
        (by simp only [AfterMvNonce]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2024)
      (.ADDI .x7 .x7 (Codegen.laLo GuestAddrs.teer_authority
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2020)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2024) teerProg 506
        (.ADDI .x7 .x7 (Codegen.laLo GuestAddrs.teer_authority
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2020)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x7 v AfterMvNonce AuthorityAddr
    (by decide) (by decide) hau had
  have hpc : (AfterMvNonce : Word) + 8 = AfterLaAuthNj := by
    simp only [AfterMvNonce, AfterLaAuthNj]; bv_omega
  rw [hpc] at h
  exact h

/-- `la x28, bv_stx_sender_addr` AfterLaAuthNj. -/
theorem teerLaSenderNj (v : Word) :
    cpsTripleWithin 2 AfterLaAuthNj AfterLaSenderNj teerLinkedField0
      (.x28 ↦ᵣ v) (.x28 ↦ᵣ SenderAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterLaAuthNj
      (.AUIPC .x28 (Codegen.laHi GuestAddrs.bv_stx_sender_addr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2028)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaAuthNj teerProg 507
        (.AUIPC .x28 (Codegen.laHi GuestAddrs.bv_stx_sender_addr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2028)))
        (by simp only [AfterLaAuthNj]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2032)
      (.ADDI .x28 .x28 (Codegen.laLo GuestAddrs.bv_stx_sender_addr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2028)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2032) teerProg 508
        (.ADDI .x28 .x28 (Codegen.laLo GuestAddrs.bv_stx_sender_addr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2028)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x28 v AfterLaAuthNj SenderAddr
    (by decide) (by decide) hau had
  have hpc : (AfterLaAuthNj : Word) + 8 = AfterLaSenderNj := by
    simp only [AfterLaAuthNj, AfterLaSenderNj]; bv_omega
  rw [hpc] at h
  exact h

/-- `li x29, 20` AfterLaSenderNj → AfterLi20Nj. -/
theorem teerLi20Nj (vOld : Word) :
    cpsTripleWithin 1 AfterLaSenderNj AfterLi20Nj teerLinkedField0
      (.x29 ↦ᵣ vOld) (.x29 ↦ᵣ (20 : Word)) := by
  have h0 := li_spec_gen_within .x29 vOld (20 : Word) AfterLaSenderNj (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaSenderNj teerProg 509
        (.LI .x29 (20 : Word)) (by simp only [AfterLaSenderNj]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterLaSenderNj + 4 : Word) = AfterLi20Nj := by
    simp only [AfterLaSenderNj, AfterLi20Nj]; bv_omega
  rw [hpc] at h1
  exact h1

/-- MV + la authority + la sender + li 20. -/
theorem teerNonceJoinSetup
    (nonceVal x6Old x7Old x28Old x29Old : Word) :
    cpsTripleWithin 6 AfterBalNonceBeq0 AfterLi20Nj teerLinkedField0
      ((.x6 ↦ᵣ x6Old) ** (.x11 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old))
      ((.x6 ↦ᵣ nonceVal) ** (.x11 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ AuthorityAddr) ** (.x28 ↦ᵣ SenderAddr) **
        (.x29 ↦ᵣ (20 : Word))) := by
  have hmv := teerMvNonceFromA1 nonceVal x6Old
  have hmvF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old)) (by pcf) hmv
  have hla0 := teerLaAuthNj x7Old
  have hla0F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ nonceVal) ** (.x11 ↦ᵣ nonceVal) **
      (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old)) (by pcf) hla0
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF hla0F
  have hla1 := teerLaSenderNj x28Old
  have hla1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ nonceVal) ** (.x11 ↦ᵣ nonceVal) **
      (.x7 ↦ᵣ AuthorityAddr) ** (.x29 ↦ᵣ x29Old)) (by pcf) hla1
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hla1F
  have hli := teerLi20Nj x29Old
  have hliF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ nonceVal) ** (.x11 ↦ᵣ nonceVal) **
      (.x7 ↦ᵣ AuthorityAddr) ** (.x28 ↦ᵣ SenderAddr)) (by pcf) hli
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hliF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c23

/-- Setup + Assumed 20B match → AfterAuthSenderInc with x6 = nonceVal+1. -/
theorem teerNonceJoinThroughMatch
    (asm : TeerAuthSenderMatchAssumed teerLinkedField0)
    (nonceVal x6Old x7Old x28Old x29Old : Word) :
    cpsTripleWithin (6 + asm.nSteps) AfterBalNonceBeq0 AfterAuthSenderInc teerLinkedField0
      ((.x6 ↦ᵣ x6Old) ** (.x11 ↦ᵣ nonceVal) **
        (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) **
        regOwn .x30 ** regOwn .x31 **
        memOwn AuthorityAddr ** memOwn SenderAddr **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ (nonceVal + (1 : Word))) ** (.x11 ↦ᵣ nonceVal) **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        memOwn AuthorityAddr ** memOwn SenderAddr **
        (.x0 ↦ᵣ (0 : Word))) := by
  have hsetup := teerNonceJoinSetup nonceVal x6Old x7Old x28Old x29Old
  have hsetupF := cpsTripleWithin_frameR
    (regOwn .x30 ** regOwn .x31 **
      memOwn AuthorityAddr ** memOwn SenderAddr ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) hsetup
  have hmatch := asm.match_flat nonceVal
  have hmatchF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ nonceVal)) (by pcf) hmatch
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsetupF hmatchF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c

/-- `la x7, teer_prior_count` AfterAuthSenderInc. -/
theorem teerLaPriorNj (v : Word) :
    cpsTripleWithin 2 AfterAuthSenderInc AfterLaPriorNj teerLinkedField0
      (.x7 ↦ᵣ v) (.x7 ↦ᵣ PriorCountAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterAuthSenderInc
      (.AUIPC .x7 (Codegen.laHi GuestAddrs.teer_prior_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2076)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthSenderInc teerProg 519
        (.AUIPC .x7 (Codegen.laHi GuestAddrs.teer_prior_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2076)))
        (by simp only [AfterAuthSenderInc]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2080)
      (.ADDI .x7 .x7 (Codegen.laLo GuestAddrs.teer_prior_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2076)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2080) teerProg 520
        (.ADDI .x7 .x7 (Codegen.laLo GuestAddrs.teer_prior_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2076)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x7 v AfterAuthSenderInc PriorCountAddr
    (by decide) (by decide) hau had
  have hpc : (AfterAuthSenderInc : Word) + 8 = AfterLaPriorNj := by
    simp only [AfterAuthSenderInc, AfterLaPriorNj]; bv_omega
  rw [hpc] at h
  exact h

/-- `ld x7, 0(x7)` prior_count. -/
theorem teerLdPriorNj (prior : Word) :
    cpsTripleWithin 1 AfterLaPriorNj AfterLdPriorNj teerLinkedField0
      ((.x7 ↦ᵣ PriorCountAddr) ** (PriorCountAddr ↦ₘ prior))
      ((.x7 ↦ᵣ prior) ** (PriorCountAddr ↦ₘ prior)) := by
  have h0 := ld_spec_gen_same_within .x7 PriorCountAddr prior (0 : BitVec 12)
    AfterLaPriorNj (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaPriorNj teerProg 521
        (.LD .x7 .x7 (0 : BitVec 12)) (by simp only [AfterLaPriorNj]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have h2 : cpsTripleWithin 1 AfterLaPriorNj (AfterLaPriorNj + 4) teerLinkedField0
      ((.x7 ↦ᵣ PriorCountAddr) ** (PriorCountAddr ↦ₘ prior))
      ((.x7 ↦ᵣ prior) ** (PriorCountAddr ↦ₘ prior)) := by
    convert h1 using 1 <;> simp only [se12_zero_nj]
  have hpc : (AfterLaPriorNj + 4 : Word) = AfterLdPriorNj := by
    simp only [AfterLaPriorNj, AfterLdPriorNj]; bv_omega
  rw [hpc] at h2
  exact h2

/-- `add x6, x6, x7` expected = nonce+1+prior. -/
theorem teerAddPriorNj (expected prior : Word) :
    cpsTripleWithin 1 AfterLdPriorNj AfterAddPriorNj teerLinkedField0
      ((.x6 ↦ᵣ expected) ** (.x7 ↦ᵣ prior))
      ((.x6 ↦ᵣ (expected + prior)) ** (.x7 ↦ᵣ prior)) := by
  have h0 := add_spec_gen_rd_eq_rs1_within .x6 .x7 expected prior AfterLdPriorNj (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLdPriorNj teerProg 522
        (.ADD .x6 .x6 .x7) (by simp only [AfterLdPriorNj]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterLdPriorNj + 4 : Word) = AfterAddPriorNj := by
    simp only [AfterLdPriorNj, AfterAddPriorNj]; bv_omega
  rw [hpc] at h1
  exact h1

/-- `ld x7, 144(sp)` auth nonce scratch. -/
theorem teerLdNonceScratchNj (spVal nonceScratch x7Old : Word) :
    cpsTripleWithin 1 AfterAddPriorNj AfterLdNonceScratchNj teerLinkedField0
      ((.x2 ↦ᵣ spVal) ** (.x7 ↦ᵣ x7Old) **
        ((spVal + (144 : Word)) ↦ₘ nonceScratch))
      ((.x2 ↦ᵣ spVal) ** (.x7 ↦ᵣ nonceScratch) **
        ((spVal + (144 : Word)) ↦ₘ nonceScratch)) := by
  have h0 := ld_spec_gen_within .x7 .x2 spVal x7Old nonceScratch
    (144 : BitVec 12) AfterAddPriorNj (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAddPriorNj teerProg 523
        (.LD .x7 .x2 (144 : BitVec 12)) (by simp only [AfterAddPriorNj]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have h1' : cpsTripleWithin 1 AfterAddPriorNj (AfterAddPriorNj + 4) teerLinkedField0
      ((.x2 ↦ᵣ spVal) ** (.x7 ↦ᵣ x7Old) **
        ((spVal + (144 : Word)) ↦ₘ nonceScratch))
      ((.x2 ↦ᵣ spVal) ** (.x7 ↦ᵣ nonceScratch) **
        ((spVal + (144 : Word)) ↦ₘ nonceScratch)) := by
    simpa only [se12_144_nj] using h1
  have hpc : (AfterAddPriorNj + 4 : Word) = AfterLdNonceScratchNj := by
    simp only [AfterAddPriorNj, AfterLdNonceScratchNj]; bv_omega
  rw [hpc] at h1'
  exact h1'

abbrev teerNonceEqBneOff : BitVec 13 := (-252 : BitVec 13)

/-- `bne x6, x7` ntaken when equal → AfterNonceEq. -/
theorem teerNonceEqBneNtaken (v : Word) :
    cpsTripleWithin 1 AfterLdNonceScratchNj AfterNonceEq teerLinkedField0
      ((.x6 ↦ᵣ v) ** (.x7 ↦ᵣ v))
      ((.x6 ↦ᵣ v) ** (.x7 ↦ᵣ v)) := by
  have hbr := bne_spec_gen_within .x6 .x7 teerNonceEqBneOff v v AfterLdNonceScratchNj
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLdNonceScratchNj teerProg 524
        (.BNE .x6 .x7 teerNonceEqBneOff)
        (by simp only [AfterLdNonceScratchNj]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterLdNonceScratchNj + 4 = AfterNonceEq := by
    simp only [AfterLdNonceScratchNj, AfterNonceEq]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- prior_count load+add+nonce scratch BNE eq: AfterAuthSenderInc → AfterNonceEq. -/
theorem teerNoncePriorCheck
    (expected prior nonceScratch spVal x7Old : Word)
    (heq : expected + prior = nonceScratch) :
    cpsTripleWithin 6 AfterAuthSenderInc AfterNonceEq teerLinkedField0
      ((.x7 ↦ᵣ x7Old) ** (.x6 ↦ᵣ expected) ** (.x2 ↦ᵣ spVal) **
        (PriorCountAddr ↦ₘ prior) **
        ((spVal + (144 : Word)) ↦ₘ nonceScratch))
      (((.x6 ↦ᵣ (expected + prior)) ** (.x7 ↦ᵣ nonceScratch)) **
        (.x2 ↦ᵣ spVal) ** (PriorCountAddr ↦ₘ prior) **
        ((spVal + (144 : Word)) ↦ₘ nonceScratch)) := by
  have hla := teerLaPriorNj x7Old
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ expected) ** (.x2 ↦ᵣ spVal) **
      (PriorCountAddr ↦ₘ prior) **
      ((spVal + (144 : Word)) ↦ₘ nonceScratch)) (by pcf) hla
  have hld0 := teerLdPriorNj prior
  have hld0F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ expected) ** (.x2 ↦ᵣ spVal) **
      ((spVal + (144 : Word)) ↦ₘ nonceScratch)) (by pcf) hld0
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hld0F
  have hadd := teerAddPriorNj expected prior
  have haddF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spVal) ** (PriorCountAddr ↦ₘ prior) **
      ((spVal + (144 : Word)) ↦ₘ nonceScratch)) (by pcf) hadd
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 haddF
  have hld1 := teerLdNonceScratchNj spVal nonceScratch prior
  have hld1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (expected + prior)) ** (PriorCountAddr ↦ₘ prior)) (by pcf) hld1
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hld1F
  have hbne : cpsTripleWithin 1 AfterLdNonceScratchNj AfterNonceEq teerLinkedField0
      ((.x6 ↦ᵣ (expected + prior)) ** (.x7 ↦ᵣ nonceScratch))
      ((.x6 ↦ᵣ (expected + prior)) ** (.x7 ↦ᵣ nonceScratch)) := by
    simpa only [heq] using teerNonceEqBneNtaken (expected + prior)
  have hbneF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spVal) ** (PriorCountAddr ↦ₘ prior) **
      ((spVal + (144 : Word)) ↦ₘ nonceScratch)) (by pcf) hbne
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 hbneF
  exact cpsTripleWithin_mono_nSteps (by decide : (2 + 1 + 1 + 1 + 1 : Nat) ≤ 6) c34

#print axioms teerMvNonceFromA1
#print axioms teerLaAuthNj
#print axioms teerLaSenderNj
#print axioms teerLi20Nj
#print axioms teerNonceJoinSetup
#print axioms teerNonceJoinThroughMatch
#print axioms teerLaPriorNj
#print axioms teerLdPriorNj
#print axioms teerAddPriorNj
#print axioms teerLdNonceScratchNj
#print axioms teerNonceEqBneNtaken
#print axioms teerNoncePriorCheck

end EvmAsm.Codegen.TxEip7702TeerSpec
