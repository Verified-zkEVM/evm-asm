/-
  Teer auth-loop nonce-max check + recover setup:
  MV t1,a0; LI t2,-1; BEQ t1,t2 skip; SD nonce,144(sp);
  MV a0,s9; LD a1,136(sp); la a2,teer_authority; la a3,teer_recover_scratch
  → AtRecover (E+936).
  AfterAuthNonceBne (E+896) → AtRecover (E+936) on nonce≠max path.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopNonce
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopChain
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

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

/-- After `mv t1, a0` (stash nonce). -/
abbrev AfterNonceMv : Word := E + 900

/-- After `li t2, -1`. -/
abbrev AfterNonceLi : Word := E + 904

/-- After `beq t1, t2` not-taken (nonce ≠ max). -/
abbrev AfterNonceBeqNtaken : Word := E + 908

/-- After `sd t1, 144(sp)`. -/
abbrev AfterNonceSd : Word := E + 912

/-- After `mv a0, s9` (content base for recover). -/
abbrev AfterRecoverMvA0 : Word := E + 916

/-- After `ld a1, 136(sp)`. -/
abbrev AfterRecoverLdA1 : Word := E + 920

/-- After `la a2, teer_authority`. -/
abbrev AfterLaAuthority : Word := E + 928

/-- JAL recover site. -/
abbrev AtRecover : Word := E + 936

abbrev LinkRecover : Word := E + 940

abbrev teerNonceBeqOff : BitVec 13 := (940 : BitVec 13)

def AuthorityAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_authority
def RecoverScratchAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_recover_scratch

theorem teerNonceBeqOff_taken :
    AfterNonceLi + signExtend13 teerNonceBeqOff = AtChainMismatch := by
  simp only [AfterNonceLi, AtChainMismatch, teerNonceBeqOff, E]; decide

private theorem se12_144 :
    signExtend12 (144 : BitVec 12) = (144 : Word) := by decide

private theorem se12_136_rec :
    signExtend12 (136 : BitVec 12) = (136 : Word) := by decide

/-- `mv t1, a0` — stash nonce value. -/
theorem teerNonceMvT1 (nonceVal t1Old : Word) :
    cpsTripleWithin 1 AfterAuthNonceBne AfterNonceMv teerLinkedField0
      ((.x10 ↦ᵣ nonceVal) ** (.x6 ↦ᵣ t1Old))
      ((.x10 ↦ᵣ nonceVal) ** (.x6 ↦ᵣ nonceVal)) := by
  have h0 := mv_spec_gen_within .x6 .x10 nonceVal t1Old AfterAuthNonceBne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthNonceBne teerProg 224
        (.MV .x6 .x10) (by simp only [AfterAuthNonceBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthNonceBne + 4 : Word) = AfterNonceMv := by
    simp only [AfterAuthNonceBne, AfterNonceMv]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `li t2, -1`. -/
theorem teerNonceLiMax (t2Old : Word) :
    cpsTripleWithin 1 AfterNonceMv AfterNonceLi teerLinkedField0
      (.x7 ↦ᵣ t2Old) (.x7 ↦ᵣ (-1 : Word)) := by
  have h0 := li_spec_gen_within .x7 t2Old (-1 : Word) AfterNonceMv (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterNonceMv teerProg 225
        (.LI .x7 (-1 : Word)) (by simp only [AfterNonceMv]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterNonceMv + 4 : Word) = AfterNonceLi := by
    simp only [AfterNonceMv, AfterNonceLi]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `beq t1, t2` taken: nonce = max → AtChainMismatch (skip item). -/
theorem teerNonceBeqMaxTaken :
    cpsTripleWithin 1 AfterNonceLi AtChainMismatch teerLinkedField0
      ((.x6 ↦ᵣ (-1 : Word)) ** (.x7 ↦ᵣ (-1 : Word)))
      ((.x6 ↦ᵣ (-1 : Word)) ** (.x7 ↦ᵣ (-1 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x7 teerNonceBeqOff
    (-1 : Word) (-1 : Word) AfterNonceLi
  rw [teerNonceBeqOff_taken] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterNonceLi teerProg 226
          (.BEQ .x6 .x7 teerNonceBeqOff)
          (by simp only [AfterNonceLi]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- `beq t1, t2` not-taken: nonce ≠ max → AfterNonceBeqNtaken. -/
theorem teerNonceBeqMaxNtaken (nonceVal : Word) (hne : nonceVal ≠ (-1 : Word)) :
    cpsTripleWithin 1 AfterNonceLi AfterNonceBeqNtaken teerLinkedField0
      ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (-1 : Word)))
      ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (-1 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x7 teerNonceBeqOff
    nonceVal (-1 : Word) AfterNonceLi
  change cpsBranchWithin _ _ _ _ _ _ AfterNonceBeqNtaken _ at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterNonceLi teerProg 226
          (.BEQ .x6 .x7 teerNonceBeqOff)
          (by simp only [AfterNonceLi]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hBP).2)

/-- `sd t1, 144(sp)` — store nonce into frame scratch. -/
theorem teerNonceSd (spC nonceVal : Word) :
    cpsTripleWithin 1 AfterNonceBeqNtaken AfterNonceSd teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x6 ↦ᵣ nonceVal) **
        memOwn (spC + (144 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x6 ↦ᵣ nonceVal) **
        memOwn (spC + (144 : Word))) := by
  have h0 := sd_spec_gen_own_within .x2 .x6 spC nonceVal (144 : BitVec 12)
    AfterNonceBeqNtaken
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterNonceBeqNtaken teerProg 227
        (.SD .x2 .x6 (144 : BitVec 12))
        (by simp only [AfterNonceBeqNtaken]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) h0
  have h2 : cpsTripleWithin 1 AfterNonceBeqNtaken (AfterNonceBeqNtaken + 4)
      teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x6 ↦ᵣ nonceVal) ** memOwn (spC + (144 : Word)))
      ((.x2 ↦ᵣ spC) ** (.x6 ↦ᵣ nonceVal) ** ((spC + (144 : Word)) ↦ₘ nonceVal)) := by
    simpa only [se12_144] using h1
  have h3 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2
  have hpc : (AfterNonceBeqNtaken + 4 : Word) = AfterNonceSd := by
    simp only [AfterNonceBeqNtaken, AfterNonceSd]; bv_omega
  rw [hpc] at h3
  exact h3

/-- Nonce ≠ max path: MV + LI + BEQ ntaken + SD → AfterNonceSd. -/
theorem teerNonceOk_neMax (nonceVal t1Old t2Old spC : Word)
    (hne : nonceVal ≠ (-1 : Word)) :
    cpsTripleWithin 4 AfterAuthNonceBne AfterNonceSd teerLinkedField0
      ((.x10 ↦ᵣ nonceVal) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x2 ↦ᵣ spC) ** memOwn (spC + (144 : Word)))
      ((.x10 ↦ᵣ nonceVal) ** (.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (-1 : Word)) **
        (.x2 ↦ᵣ spC) ** memOwn (spC + (144 : Word))) := by
  have h0 := teerNonceMvT1 nonceVal t1Old
  have h0F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ t2Old) ** (.x2 ↦ᵣ spC) ** memOwn (spC + (144 : Word))) (by pcf) h0
  have h1 := teerNonceLiMax t2Old
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nonceVal) ** (.x6 ↦ᵣ nonceVal) ** (.x2 ↦ᵣ spC) **
      memOwn (spC + (144 : Word))) (by pcf) h1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h2 := teerNonceBeqMaxNtaken nonceVal hne
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nonceVal) ** (.x2 ↦ᵣ spC) ** memOwn (spC + (144 : Word))) (by pcf) h2
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h2F
  have h3 := teerNonceSd spC nonceVal
  have h3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (-1 : Word))) (by pcf) h3
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 h3F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c23

/-- `mv a0, s9` — content base for recover. -/
theorem teerRecoverMvA0 (content a0Old : Word) :
    cpsTripleWithin 1 AfterNonceSd AfterRecoverMvA0 teerLinkedField0
      ((.x25 ↦ᵣ content) ** (.x10 ↦ᵣ a0Old))
      ((.x25 ↦ᵣ content) ** (.x10 ↦ᵣ content)) := by
  have h0 := mv_spec_gen_within .x10 .x25 content a0Old AfterNonceSd (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterNonceSd teerProg 228
        (.MV .x10 .x25) (by simp only [AfterNonceSd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterNonceSd + 4 : Word) = AfterRecoverMvA0 := by
    simp only [AfterNonceSd, AfterRecoverMvA0]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `ld a1, 136(sp)` — content length. -/
theorem teerRecoverLdA1 (spC lenW a1Old : Word) :
    cpsTripleWithin 1 AfterRecoverMvA0 AfterRecoverLdA1 teerLinkedField0
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ a1Old) ** ((spC + (136 : Word)) ↦ₘ lenW))
      ((.x2 ↦ᵣ spC) ** (.x11 ↦ᵣ lenW) ** ((spC + (136 : Word)) ↦ₘ lenW)) := by
  have h0 := ld_spec_gen_within .x11 .x2 spC a1Old lenW
    (136 : BitVec 12) AfterRecoverMvA0 (by decide)
  rw [show spC + signExtend12 (136 : BitVec 12) = spC + (136 : Word) from by
    rw [se12_136_rec]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterRecoverMvA0 teerProg 229
        (.LD .x11 .x2 (136 : BitVec 12))
        (by simp only [AfterRecoverMvA0]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterRecoverMvA0 + 4 : Word) = AfterRecoverLdA1 := by
    simp only [AfterRecoverMvA0, AfterRecoverLdA1]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `la a2, teer_authority` at AfterRecoverLdA1 → AfterLaAuthority. -/
theorem teerLaAuthority (v : Word) :
    cpsTripleWithin 2 AfterRecoverLdA1 AfterLaAuthority teerLinkedField0
      (.x12 ↦ᵣ v) (.x12 ↦ᵣ AuthorityAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterRecoverLdA1
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_authority
        (GuestAddrs.tx_eip7702_existing_authority_refund + 920)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterRecoverLdA1 teerProg 230
        (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_authority
          (GuestAddrs.tx_eip7702_existing_authority_refund + 920)))
        (by simp only [AfterRecoverLdA1]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 924)
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_authority
        (GuestAddrs.tx_eip7702_existing_authority_refund + 920)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 924) teerProg 231
        (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_authority
          (GuestAddrs.tx_eip7702_existing_authority_refund + 920)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x12 v AfterRecoverLdA1 AuthorityAddr
    (by decide) (by decide) hau had
  rw [show (AfterRecoverLdA1 : Word) + 8 = AfterLaAuthority from by
    simp only [AfterRecoverLdA1, AfterLaAuthority]; bv_omega] at h
  exact h

/-- `la a3, teer_recover_scratch` at AfterLaAuthority → AtRecover. -/
theorem teerLaRecoverScratch (v : Word) :
    cpsTripleWithin 2 AfterLaAuthority AtRecover teerLinkedField0
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ RecoverScratchAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterLaAuthority
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.teer_recover_scratch
        (GuestAddrs.tx_eip7702_existing_authority_refund + 928)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaAuthority teerProg 232
        (.AUIPC .x13 (Codegen.laHi GuestAddrs.teer_recover_scratch
          (GuestAddrs.tx_eip7702_existing_authority_refund + 928)))
        (by simp only [AfterLaAuthority]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 932)
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.teer_recover_scratch
        (GuestAddrs.tx_eip7702_existing_authority_refund + 928)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 932) teerProg 233
        (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.teer_recover_scratch
          (GuestAddrs.tx_eip7702_existing_authority_refund + 928)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x13 v AfterLaAuthority RecoverScratchAddr
    (by decide) (by decide) hau had
  rw [show (AfterLaAuthority : Word) + 8 = AtRecover from by
    simp only [AfterLaAuthority, AtRecover]; bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Recover ABI setup: AfterNonceSd → AtRecover (MV/LD/la×2). -/
theorem teerRecoverSetup
    (content lenW a0Old a1Old v12 v13 spC : Word) :
    cpsTripleWithin 6 AfterNonceSd AtRecover teerLinkedField0
      ((.x25 ↦ᵣ content) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x2 ↦ᵣ spC) **
        ((spC + (136 : Word)) ↦ₘ lenW))
      ((.x25 ↦ᵣ content) ** (.x10 ↦ᵣ content) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ AuthorityAddr) ** (.x13 ↦ᵣ RecoverScratchAddr) **
        (.x2 ↦ᵣ spC) ** ((spC + (136 : Word)) ↦ₘ lenW)) := by
  have hm := teerRecoverMvA0 content a0Old
  have hmF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x2 ↦ᵣ spC) **
      ((spC + (136 : Word)) ↦ₘ lenW)) (by pcf) hm
  have hl := teerRecoverLdA1 spC lenW a1Old
  have hlF := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ content) ** (.x10 ↦ᵣ content) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13))
    (by pcf) hl
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmF hlF
  have ha := teerLaAuthority v12
  have haF := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ content) ** (.x10 ↦ᵣ content) ** (.x11 ↦ᵣ lenW) **
      (.x13 ↦ᵣ v13) ** (.x2 ↦ᵣ spC) ** ((spC + (136 : Word)) ↦ₘ lenW)) (by pcf) ha
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 haF
  have hs := teerLaRecoverScratch v13
  have hsF := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ content) ** (.x10 ↦ᵣ content) ** (.x11 ↦ᵣ lenW) **
      (.x12 ↦ᵣ AuthorityAddr) ** (.x2 ↦ᵣ spC) **
      ((spC + (136 : Word)) ↦ₘ lenW)) (by pcf) hs
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hsF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c23

set_option maxRecDepth 8000 in
/-- Nonce ≠ max + recover setup: AfterAuthNonceBne → AtRecover. -/
theorem teerNonceOkThenRecoverSetup
    (nonceVal t1Old t2Old content lenW a1Old v12 v13 spC : Word)
    (hne : nonceVal ≠ (-1 : Word)) :
    cpsTripleWithin 10 AfterAuthNonceBne AtRecover teerLinkedField0
      ((.x10 ↦ᵣ nonceVal) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x25 ↦ᵣ content) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x2 ↦ᵣ spC) ** memOwn (spC + (144 : Word)) **
        ((spC + (136 : Word)) ↦ₘ lenW))
      ((.x10 ↦ᵣ content) ** (.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (-1 : Word)) **
        (.x25 ↦ᵣ content) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ AuthorityAddr) **
        (.x13 ↦ᵣ RecoverScratchAddr) ** (.x2 ↦ᵣ spC) **
        memOwn (spC + (144 : Word)) ** ((spC + (136 : Word)) ↦ₘ lenW)) := by
  have hN := teerNonceOk_neMax nonceVal t1Old t2Old spC hne
  have hNF := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ content) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
      ((spC + (136 : Word)) ↦ₘ lenW)) (by pcf) hN
  have hS := teerRecoverSetup content lenW nonceVal a1Old v12 v13 spC
  have hSF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ nonceVal) ** (.x7 ↦ᵣ (-1 : Word)) **
      memOwn (spC + (144 : Word))) (by pcf) hS
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hNF hSF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

#print axioms teerNonceMvT1
#print axioms teerNonceLiMax
#print axioms teerNonceBeqMaxTaken
#print axioms teerNonceBeqMaxNtaken
#print axioms teerNonceSd
#print axioms teerNonceOk_neMax
#print axioms teerRecoverMvA0
#print axioms teerRecoverLdA1
#print axioms teerLaAuthority
#print axioms teerLaRecoverScratch
#print axioms teerRecoverSetup
#print axioms teerNonceOkThenRecoverSetup

end EvmAsm.Codegen.TxEip7702TeerSpec
