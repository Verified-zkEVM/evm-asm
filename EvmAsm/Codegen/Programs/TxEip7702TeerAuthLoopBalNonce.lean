/-
  Teer auth-loop bal_account_nonce_before_index setup + Call(Assumed) + BEQ status0:
  AtSvfTxCountSkip (E+1848) → AfterBalNonceBeq0 (E+2016) when status=0.

  ABI: a0=acct_ptr, a1=acct_len, a2=saved a5 from 104(sp) (bai/index).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopCahsrPrefix
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

abbrev AfterLaAcctPtrBn : Word := E + 1856
abbrev AfterLdAcctPtrBn : Word := E + 1860
abbrev AfterLaAcctLenBn : Word := E + 1868
abbrev AfterLdAcctLenBn : Word := E + 1872
abbrev AfterLdBaiBn : Word := E + 1876
abbrev AtBalNonce : Word := E + 1876
abbrev LinkBalNonce : Word := E + 1880
abbrev AfterBalNonceBeqNtaken : Word := E + 1884
abbrev AfterBalNonceBeq0 : Word := E + 2016

abbrev BalNonceEntry : Word :=
  BitVec.ofNat 64 GuestAddrs.bal_account_nonce_before_index

def balNonceJalOff : BitVec 21 :=
  jalOff GuestAddrs.bal_account_nonce_before_index
    (GuestAddrs.tx_eip7702_existing_authority_refund + 1876)

abbrev teerBalNonceBeqOff : BitVec 13 := (136 : BitVec 13)

theorem balNonceJalOff_resolves :
    AtBalNonce + signExtend21 balNonceJalOff = BalNonceEntry := by
  simp only [AtBalNonce, BalNonceEntry, balNonceJalOff, E]; decide

theorem teerBalNonceBeqOff_taken :
    LinkBalNonce + signExtend13 teerBalNonceBeqOff = AfterBalNonceBeq0 := by
  simp only [LinkBalNonce, AfterBalNonceBeq0, teerBalNonceBeqOff, E]; decide

private theorem se12_zero_bn : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_104_bn : signExtend12 (104 : BitVec 12) = (104 : Word) := by decide

/-- Named hyp for bal_account_nonce_before_index status-0 path. -/
structure TeerBalNonceAssumed (cr : CodeReq) where
  entry : Word
  nSteps : Nat
  success_flat :
    ∀ (ret acctPtr acctLenW bai : Word),
      (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin nSteps entry ret cr
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ acctPtr) ** (.x11 ↦ᵣ acctLenW) ** (.x12 ↦ᵣ bai) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))

def teerBalNonceCalleeP (acctPtr acctLenW bai : Word) : Assertion :=
  (.x10 ↦ᵣ acctPtr) ** (.x11 ↦ᵣ acctLenW) ** (.x12 ↦ᵣ bai) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

def teerBalNonceCalleeQ : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem teerBalNonceCalleeP_pcFree (acctPtr acctLenW bai : Word) :
    (teerBalNonceCalleeP acctPtr acctLenW bai).pcFree := by
  unfold teerBalNonceCalleeP; pcf

/-- `la x5, teer_acct_ptr` AtSvfTxCountSkip. -/
theorem teerLaAcctPtrBn (v : Word) :
    cpsTripleWithin 2 AtSvfTxCountSkip AfterLaAcctPtrBn teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ AcctPtrAddr) := by
  have hau : ∀ a i, CodeReq.singleton AtSvfTxCountSkip
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_acct_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1848)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtSvfTxCountSkip teerProg 462
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_acct_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1848)))
        (by simp only [AtSvfTxCountSkip]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1852)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_acct_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1848)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1852) teerProg 463
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_acct_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1848)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AtSvfTxCountSkip AcctPtrAddr
    (by decide) (by decide) hau had
  rw [show (AtSvfTxCountSkip : Word) + 8 = AfterLaAcctPtrBn from by
    simp only [AtSvfTxCountSkip, AfterLaAcctPtrBn]; bv_omega] at h
  exact h

/-- `ld a0, 0(x5)` acct_ptr. -/
theorem teerLdAcctPtrBn (acctPtr a0Old : Word) :
    cpsTripleWithin 1 AfterLaAcctPtrBn AfterLdAcctPtrBn teerLinkedField0
      ((.x5 ↦ᵣ AcctPtrAddr) ** (.x10 ↦ᵣ a0Old) ** (AcctPtrAddr ↦ₘ acctPtr))
      ((.x5 ↦ᵣ AcctPtrAddr) ** (.x10 ↦ᵣ acctPtr) ** (AcctPtrAddr ↦ₘ acctPtr)) := by
  have h0 := ld_spec_gen_within .x10 .x5 AcctPtrAddr a0Old acctPtr
    (0 : BitVec 12) AfterLaAcctPtrBn (by decide)
  rw [show AcctPtrAddr + signExtend12 (0 : BitVec 12) = AcctPtrAddr from by
    rw [se12_zero_bn]; exact BitVec.add_zero AcctPtrAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaAcctPtrBn teerProg 464
        (.LD .x10 .x5 (0 : BitVec 12))
        (by simp only [AfterLaAcctPtrBn]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLaAcctPtrBn + 4 = AfterLdAcctPtrBn := by
    simp only [AfterLaAcctPtrBn, AfterLdAcctPtrBn]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `la x5, teer_acct_len`. -/
theorem teerLaAcctLenBn (v : Word) :
    cpsTripleWithin 2 AfterLdAcctPtrBn AfterLaAcctLenBn teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ AcctLenAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterLdAcctPtrBn
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_acct_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1860)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLdAcctPtrBn teerProg 465
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_acct_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1860)))
        (by simp only [AfterLdAcctPtrBn]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1864)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_acct_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1860)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1864) teerProg 466
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_acct_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1860)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterLdAcctPtrBn AcctLenAddr
    (by decide) (by decide) hau had
  rw [show (AfterLdAcctPtrBn : Word) + 8 = AfterLaAcctLenBn from by
    simp only [AfterLdAcctPtrBn, AfterLaAcctLenBn]; bv_omega] at h
  exact h

/-- `ld a1, 0(x5)` acct_len. -/
theorem teerLdAcctLenBn (acctLenW a1Old : Word) :
    cpsTripleWithin 1 AfterLaAcctLenBn AfterLdAcctLenBn teerLinkedField0
      ((.x5 ↦ᵣ AcctLenAddr) ** (.x11 ↦ᵣ a1Old) ** (AcctLenAddr ↦ₘ acctLenW))
      ((.x5 ↦ᵣ AcctLenAddr) ** (.x11 ↦ᵣ acctLenW) ** (AcctLenAddr ↦ₘ acctLenW)) := by
  have h0 := ld_spec_gen_within .x11 .x5 AcctLenAddr a1Old acctLenW
    (0 : BitVec 12) AfterLaAcctLenBn (by decide)
  rw [show AcctLenAddr + signExtend12 (0 : BitVec 12) = AcctLenAddr from by
    rw [se12_zero_bn]; exact BitVec.add_zero AcctLenAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaAcctLenBn teerProg 467
        (.LD .x11 .x5 (0 : BitVec 12))
        (by simp only [AfterLaAcctLenBn]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLaAcctLenBn + 4 = AfterLdAcctLenBn := by
    simp only [AfterLaAcctLenBn, AfterLdAcctLenBn]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `ld a2, 104(sp)` saved a5 / bai. -/
theorem teerLdBaiBn (spVal bai a2Old : Word) :
    cpsTripleWithin 1 AfterLdAcctLenBn AfterLdBaiBn teerLinkedField0
      ((.x2 ↦ᵣ spVal) ** (.x12 ↦ᵣ a2Old) ** ((spVal + (104 : Word)) ↦ₘ bai))
      ((.x2 ↦ᵣ spVal) ** (.x12 ↦ᵣ bai) ** ((spVal + (104 : Word)) ↦ₘ bai)) := by
  have h0 := ld_spec_gen_within .x12 .x2 spVal a2Old bai
    (104 : BitVec 12) AfterLdAcctLenBn (by decide)
  rw [show spVal + signExtend12 (104 : BitVec 12) = spVal + (104 : Word) from by
    rw [se12_104_bn]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLdAcctLenBn teerProg 468
        (.LD .x12 .x2 (104 : BitVec 12))
        (by simp only [AfterLdAcctLenBn]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLdAcctLenBn + 4 = AfterLdBaiBn := by
    simp only [AfterLdAcctLenBn, AfterLdBaiBn]; bv_omega
  rw [hpc] at e0
  exact e0

set_option maxRecDepth 8000 in
/-- Load acct_ptr/len + bai from sp+104: AtSvfTxCountSkip → AtBalNonce. -/
theorem teerBalNonceSetup
    (spVal acctPtr acctLenW bai t0Old a0Old a1Old a2Old : Word) :
    cpsTripleWithin 7 AtSvfTxCountSkip AtBalNonce teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x2 ↦ᵣ spVal) **
        (AcctPtrAddr ↦ₘ acctPtr) ** (AcctLenAddr ↦ₘ acctLenW) **
        ((spVal + (104 : Word)) ↦ₘ bai))
      ((.x5 ↦ᵣ AcctLenAddr) ** (.x10 ↦ᵣ acctPtr) ** (.x11 ↦ᵣ acctLenW) **
        (.x12 ↦ᵣ bai) ** (.x2 ↦ᵣ spVal) **
        (AcctPtrAddr ↦ₘ acctPtr) ** (AcctLenAddr ↦ₘ acctLenW) **
        ((spVal + (104 : Word)) ↦ₘ bai)) := by
  have hla0 := teerLaAcctPtrBn t0Old
  have hla0F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x2 ↦ᵣ spVal) **
      (AcctPtrAddr ↦ₘ acctPtr) ** (AcctLenAddr ↦ₘ acctLenW) **
      ((spVal + (104 : Word)) ↦ₘ bai)) (by pcf) hla0
  have hld0 := teerLdAcctPtrBn acctPtr a0Old
  have hld0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x2 ↦ᵣ spVal) **
      (AcctLenAddr ↦ₘ acctLenW) ** ((spVal + (104 : Word)) ↦ₘ bai)) (by pcf) hld0
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla0F hld0F
  have hla1 := teerLaAcctLenBn AcctPtrAddr
  have hla1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ acctPtr) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x2 ↦ᵣ spVal) **
      (AcctPtrAddr ↦ₘ acctPtr) ** (AcctLenAddr ↦ₘ acctLenW) **
      ((spVal + (104 : Word)) ↦ₘ bai)) (by pcf) hla1
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hla1F
  have hld1 := teerLdAcctLenBn acctLenW a1Old
  have hld1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ acctPtr) ** (.x12 ↦ᵣ a2Old) ** (.x2 ↦ᵣ spVal) **
      (AcctPtrAddr ↦ₘ acctPtr) ** ((spVal + (104 : Word)) ↦ₘ bai)) (by pcf) hld1
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hld1F
  have hld2 := teerLdBaiBn spVal bai a2Old
  have hld2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ AcctLenAddr) ** (.x10 ↦ᵣ acctPtr) ** (.x11 ↦ᵣ acctLenW) **
      (AcctPtrAddr ↦ₘ acctPtr) ** (AcctLenAddr ↦ₘ acctLenW)) (by pcf) hld2
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 hld2F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c34

set_option maxRecDepth 8000 in
/-- JAL bal_nonce under TeerBalNonceAssumed → LinkBalNonce. -/
theorem teerBalNonceCall
    (asm : TeerBalNonceAssumed teerLinkedField0)
    (hentry : asm.entry = BalNonceEntry)
    (acctPtr acctLenW bai old1 : Word) :
    cpsTripleWithin (1 + asm.nSteps) AtBalNonce LinkBalNonce teerLinkedField0
      ((.x1 ↦ᵣ old1) ** teerBalNonceCalleeP acctPtr acctLenW bai)
      ((.x1 ↦ᵣ LinkBalNonce) ** teerBalNonceCalleeQ) := by
  have hret : (LinkBalNonce &&& ~~~(1 : Word)) = LinkBalNonce := by
    simp only [LinkBalNonce, E]; decide
  have hcallee0 := asm.success_flat LinkBalNonce acctPtr acctLenW bai hret
  have hcallee0' : cpsTripleWithin asm.nSteps asm.entry LinkBalNonce teerLinkedField0
      ((.x1 ↦ᵣ LinkBalNonce) ** teerBalNonceCalleeP acctPtr acctLenW bai)
      ((.x1 ↦ᵣ LinkBalNonce) ** teerBalNonceCalleeQ) := by
    unfold teerBalNonceCalleeP teerBalNonceCalleeQ
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcallee : cpsTripleWithin asm.nSteps BalNonceEntry LinkBalNonce teerLinkedField0
      ((.x1 ↦ᵣ LinkBalNonce) ** teerBalNonceCalleeP acctPtr acctLenW bai)
      ((.x1 ↦ᵣ LinkBalNonce) ** teerBalNonceCalleeQ) := by
    rw [← hentry]; exact hcallee0'
  have hcall := callWithin_spec AtBalNonce BalNonceEntry old1 balNonceJalOff
    asm.nSteps balNonceJalOff_resolves
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtBalNonce teerProg 469
        (.JAL .x1 balNonceJalOff) (by simp only [AtBalNonce]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerBalNonceCalleeP_pcFree acctPtr acctLenW bai)
    hcallee
  rw [show (AtBalNonce + 4 : Word) = LinkBalNonce from by
    simp only [AtBalNonce, LinkBalNonce]; bv_omega] at hcall
  exact hcall

/-- `beq a0, x0` taken: status 0 → AfterBalNonceBeq0. -/
theorem teerBalNonceBeqTaken_zero :
    cpsTripleWithin 1 LinkBalNonce AfterBalNonceBeq0 teerLinkedField0
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x10 .x0 teerBalNonceBeqOff
    (0 : Word) (0 : Word) LinkBalNonce
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkBalNonce teerProg 470
        (.BEQ .x10 .x0 teerBalNonceBeqOff)
        (by simp only [LinkBalNonce]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have ht := cpsBranchWithin_takenStripPure2 hbrC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  rw [teerBalNonceBeqOff_taken] at ht
  exact ht

#print axioms teerLaAcctPtrBn
#print axioms teerLdAcctPtrBn
#print axioms teerLaAcctLenBn
#print axioms teerLdAcctLenBn
#print axioms teerLdBaiBn
#print axioms teerBalNonceSetup
#print axioms teerBalNonceCall
#print axioms teerBalNonceBeqTaken_zero

end EvmAsm.Codegen.TxEip7702TeerSpec

