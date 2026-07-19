/-
  Teer auth-loop bal_account_nonstorage_finals setup + Call(Assumed) + BNE ok:
  AfterBalFindBne (E+1156) → AfterBalFinalsBne (E+1196).

  ABI: a0=acct_ptr cell load, a1=acct_len cell load, a2=teer_finals out block.
  Leaf partially verified elsewhere; TeerBalFinalsAssumed is the named hyp here.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBalFind
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

abbrev AfterLaAcctPtrLd : Word := E + 1164
abbrev AfterLdAcctPtr : Word := E + 1168
abbrev AfterLaAcctLenLd : Word := E + 1176
abbrev AfterLdAcctLen : Word := E + 1180
abbrev AfterLaFinals : Word := E + 1188
abbrev AtBalFinals : Word := E + 1188
abbrev LinkBalFinals : Word := E + 1192
abbrev AfterBalFinalsBne : Word := E + 1196

def FinalsAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_finals

abbrev BalFinalsEntry : Word :=
  BitVec.ofNat 64 GuestAddrs.bal_account_nonstorage_finals

def balFinalsJalOff : BitVec 21 :=
  jalOff GuestAddrs.bal_account_nonstorage_finals
    (GuestAddrs.tx_eip7702_existing_authority_refund + 1188)

abbrev teerBalFinalsBneOff : BitVec 13 := (1656 : BitVec 13)

theorem balFinalsJalOff_resolves :
    AtBalFinals + signExtend21 balFinalsJalOff = BalFinalsEntry := by
  simp only [AtBalFinals, BalFinalsEntry, balFinalsJalOff, E]; decide

private theorem se12_zero_bf : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- Named hyp for bal_finals status-0 path. Posts `x5 ↦ 0` for following la. -/
structure TeerBalFinalsAssumed (cr : CodeReq) where
  entry : Word
  nSteps : Nat
  success_flat :
    ∀ (ret acctPtr acctLenW : Word),
      (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin nSteps entry ret cr
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ acctPtr) ** (.x11 ↦ᵣ acctLenW) **
          (.x12 ↦ᵣ FinalsAddr) **
          memOwn FinalsAddr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
          memOwn FinalsAddr **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))

def teerBalFinalsCalleeP (acctPtr acctLenW : Word) : Assertion :=
  (.x10 ↦ᵣ acctPtr) ** (.x11 ↦ᵣ acctLenW) **
  (.x12 ↦ᵣ FinalsAddr) **
  memOwn FinalsAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

def teerBalFinalsCalleeQ : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
  memOwn FinalsAddr **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem teerBalFinalsCalleeP_pcFree (acctPtr acctLenW : Word) :
    (teerBalFinalsCalleeP acctPtr acctLenW).pcFree := by
  unfold teerBalFinalsCalleeP; pcf

/-- `la x5, teer_acct_ptr` AfterBalFindBne. -/
theorem teerLaAcctPtrLoad (v : Word) :
    cpsTripleWithin 2 AfterBalFindBne AfterLaAcctPtrLd teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ AcctPtrAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterBalFindBne
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_acct_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1156)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterBalFindBne teerProg 289
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_acct_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1156)))
        (by simp only [AfterBalFindBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1160)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_acct_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1156)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1160) teerProg 290
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_acct_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1156)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterBalFindBne AcctPtrAddr
    (by decide) (by decide) hau had
  rw [show (AfterBalFindBne : Word) + 8 = AfterLaAcctPtrLd from by
    simp only [AfterBalFindBne, AfterLaAcctPtrLd]; bv_omega] at h
  exact h

/-- `ld a0, 0(x5)` acct_ptr value. -/
theorem teerLdAcctPtr (acctPtr a0Old : Word) :
    cpsTripleWithin 1 AfterLaAcctPtrLd AfterLdAcctPtr teerLinkedField0
      ((.x5 ↦ᵣ AcctPtrAddr) ** (.x10 ↦ᵣ a0Old) ** (AcctPtrAddr ↦ₘ acctPtr))
      ((.x5 ↦ᵣ AcctPtrAddr) ** (.x10 ↦ᵣ acctPtr) **
        (AcctPtrAddr ↦ₘ acctPtr)) := by
  have h0 := ld_spec_gen_within .x10 .x5 AcctPtrAddr a0Old acctPtr
    (0 : BitVec 12) AfterLaAcctPtrLd (by decide)
  rw [show AcctPtrAddr + signExtend12 (0 : BitVec 12) = AcctPtrAddr from by
    rw [se12_zero_bf]; exact BitVec.add_zero AcctPtrAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaAcctPtrLd teerProg 291
        (.LD .x10 .x5 (0 : BitVec 12))
        (by simp only [AfterLaAcctPtrLd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLaAcctPtrLd + 4 = AfterLdAcctPtr := by
    simp only [AfterLaAcctPtrLd, AfterLdAcctPtr]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `la x5, teer_acct_len`. -/
theorem teerLaAcctLenLoad (v : Word) :
    cpsTripleWithin 2 AfterLdAcctPtr AfterLaAcctLenLd teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ AcctLenAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterLdAcctPtr
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_acct_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1168)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLdAcctPtr teerProg 292
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_acct_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1168)))
        (by simp only [AfterLdAcctPtr]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1172)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_acct_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1168)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1172) teerProg 293
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_acct_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1168)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterLdAcctPtr AcctLenAddr
    (by decide) (by decide) hau had
  rw [show (AfterLdAcctPtr : Word) + 8 = AfterLaAcctLenLd from by
    simp only [AfterLdAcctPtr, AfterLaAcctLenLd]; bv_omega] at h
  exact h

/-- `ld a1, 0(x5)` acct_len value. -/
theorem teerLdAcctLen (acctLenW a1Old : Word) :
    cpsTripleWithin 1 AfterLaAcctLenLd AfterLdAcctLen teerLinkedField0
      ((.x5 ↦ᵣ AcctLenAddr) ** (.x11 ↦ᵣ a1Old) ** (AcctLenAddr ↦ₘ acctLenW))
      ((.x5 ↦ᵣ AcctLenAddr) ** (.x11 ↦ᵣ acctLenW) **
        (AcctLenAddr ↦ₘ acctLenW)) := by
  have h0 := ld_spec_gen_within .x11 .x5 AcctLenAddr a1Old acctLenW
    (0 : BitVec 12) AfterLaAcctLenLd (by decide)
  rw [show AcctLenAddr + signExtend12 (0 : BitVec 12) = AcctLenAddr from by
    rw [se12_zero_bf]; exact BitVec.add_zero AcctLenAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaAcctLenLd teerProg 294
        (.LD .x11 .x5 (0 : BitVec 12))
        (by simp only [AfterLaAcctLenLd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLaAcctLenLd + 4 = AfterLdAcctLen := by
    simp only [AfterLaAcctLenLd, AfterLdAcctLen]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `la a2, teer_finals`. -/
theorem teerLaFinals (v : Word) :
    cpsTripleWithin 2 AfterLdAcctLen AtBalFinals teerLinkedField0
      (.x12 ↦ᵣ v) (.x12 ↦ᵣ FinalsAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterLdAcctLen
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_finals
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1180)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLdAcctLen teerProg 295
        (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_finals
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1180)))
        (by simp only [AfterLdAcctLen]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1184)
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_finals
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1180)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1184) teerProg 296
        (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_finals
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1180)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x12 v AfterLdAcctLen FinalsAddr
    (by decide) (by decide) hau had
  rw [show (AfterLdAcctLen : Word) + 8 = AtBalFinals from by
    simp only [AfterLdAcctLen, AtBalFinals]; bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Load acct_ptr/len + la finals: AfterBalFindBne → AtBalFinals. -/
theorem teerBalFinalsSetup
    (acctPtr acctLenW t0Old a0Old a1Old a2Old : Word) :
    cpsTripleWithin 8 AfterBalFindBne AtBalFinals teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        (.x12 ↦ᵣ a2Old) **
        (AcctPtrAddr ↦ₘ acctPtr) ** (AcctLenAddr ↦ₘ acctLenW))
      ((.x5 ↦ᵣ AcctLenAddr) ** (.x10 ↦ᵣ acctPtr) ** (.x11 ↦ᵣ acctLenW) **
        (.x12 ↦ᵣ FinalsAddr) **
        (AcctPtrAddr ↦ₘ acctPtr) ** (AcctLenAddr ↦ₘ acctLenW)) := by
  have hla0 := teerLaAcctPtrLoad t0Old
  have hla0F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
      (AcctPtrAddr ↦ₘ acctPtr) ** (AcctLenAddr ↦ₘ acctLenW)) (by pcf) hla0
  have hld0 := teerLdAcctPtr acctPtr a0Old
  have hld0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (AcctLenAddr ↦ₘ acctLenW))
    (by pcf) hld0
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla0F hld0F
  have hla1 := teerLaAcctLenLoad AcctPtrAddr
  have hla1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ acctPtr) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
      (AcctPtrAddr ↦ₘ acctPtr) ** (AcctLenAddr ↦ₘ acctLenW)) (by pcf) hla1
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hla1F
  have hld1 := teerLdAcctLen acctLenW a1Old
  have hld1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ acctPtr) ** (.x12 ↦ᵣ a2Old) ** (AcctPtrAddr ↦ₘ acctPtr))
    (by pcf) hld1
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hld1F
  have hla2 := teerLaFinals a2Old
  have hla2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ AcctLenAddr) ** (.x10 ↦ᵣ acctPtr) ** (.x11 ↦ᵣ acctLenW) **
      (AcctPtrAddr ↦ₘ acctPtr) ** (AcctLenAddr ↦ₘ acctLenW)) (by pcf) hla2
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 hla2F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c34

set_option maxRecDepth 8000 in
/-- JAL bal_finals under TeerBalFinalsAssumed → LinkBalFinals. -/
theorem teerBalFinalsCall
    (asm : TeerBalFinalsAssumed teerLinkedField0)
    (hentry : asm.entry = BalFinalsEntry)
    (acctPtr acctLenW old1 : Word) :
    cpsTripleWithin (1 + asm.nSteps) AtBalFinals LinkBalFinals teerLinkedField0
      ((.x1 ↦ᵣ old1) ** teerBalFinalsCalleeP acctPtr acctLenW)
      ((.x1 ↦ᵣ LinkBalFinals) ** teerBalFinalsCalleeQ) := by
  have hret : (LinkBalFinals &&& ~~~(1 : Word)) = LinkBalFinals := by
    simp only [LinkBalFinals, E]; decide
  have hcallee0 := asm.success_flat LinkBalFinals acctPtr acctLenW hret
  have hcallee0' : cpsTripleWithin asm.nSteps asm.entry LinkBalFinals teerLinkedField0
      ((.x1 ↦ᵣ LinkBalFinals) ** teerBalFinalsCalleeP acctPtr acctLenW)
      ((.x1 ↦ᵣ LinkBalFinals) ** teerBalFinalsCalleeQ) := by
    unfold teerBalFinalsCalleeP teerBalFinalsCalleeQ
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcallee : cpsTripleWithin asm.nSteps BalFinalsEntry LinkBalFinals teerLinkedField0
      ((.x1 ↦ᵣ LinkBalFinals) ** teerBalFinalsCalleeP acctPtr acctLenW)
      ((.x1 ↦ᵣ LinkBalFinals) ** teerBalFinalsCalleeQ) := by
    rw [← hentry]; exact hcallee0'
  have hcall := callWithin_spec AtBalFinals BalFinalsEntry old1 balFinalsJalOff
    asm.nSteps balFinalsJalOff_resolves
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtBalFinals teerProg 297
        (.JAL .x1 balFinalsJalOff) (by simp only [AtBalFinals]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerBalFinalsCalleeP_pcFree acctPtr acctLenW)
    hcallee
  rw [show (AtBalFinals + 4 : Word) = LinkBalFinals from by
    simp only [AtBalFinals, LinkBalFinals]; bv_omega] at hcall
  exact hcall

/-- BNE a0,x0 ok after bal_finals (status 0) → AfterBalFinalsBne. -/
theorem teerBalFinalsBneOk :
    cpsTripleWithin 1 LinkBalFinals AfterBalFinalsBne teerLinkedField0
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 teerBalFinalsBneOff
    (0 : Word) (0 : Word) LinkBalFinals
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkBalFinals teerProg 298
        (.BNE .x10 .x0 teerBalFinalsBneOff)
        (by simp only [LinkBalFinals]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkBalFinals + 4 = AfterBalFinalsBne := by
    simp only [LinkBalFinals, AfterBalFinalsBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

#print axioms teerLaAcctPtrLoad
#print axioms teerLdAcctPtr
#print axioms teerLaAcctLenLoad
#print axioms teerLdAcctLen
#print axioms teerLaFinals
#print axioms teerBalFinalsSetup
#print axioms teerBalFinalsCall
#print axioms teerBalFinalsBneOk

end EvmAsm.Codegen.TxEip7702TeerSpec
