/-
  Teer auth-loop bal_find_account_by_address setup + Call(Assumed) + BNE ok:
  AtBalFindSetup (E+1116) → AfterBalFindBne (E+1156).

  ABI: a0=balPtr(s2), a1=balLen(s3), a2=authority, a3=acct_ptr, a4=acct_len.
  bal_find leaf unproven; TeerBalFindAssumed.success_flat is the named hyp.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopSuccessTable
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

abbrev AfterBalFindMvA0 : Word := E + 1120
abbrev AfterBalFindMvA1 : Word := E + 1124
abbrev AfterLaAuthBal : Word := E + 1132
abbrev AfterLaAcctPtr : Word := E + 1140
abbrev AtBalFind : Word := E + 1148
abbrev LinkBalFind : Word := E + 1152
abbrev AfterBalFindBne : Word := E + 1156

def AcctPtrAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_acct_ptr
def AcctLenAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_acct_len

abbrev BalFindEntry : Word :=
  BitVec.ofNat 64 GuestAddrs.bal_find_account_by_address

def balFindJalOff : BitVec 21 :=
  jalOff GuestAddrs.bal_find_account_by_address
    (GuestAddrs.tx_eip7702_existing_authority_refund + 1148)

abbrev teerBalFindBneOff : BitVec 13 := (324 : BitVec 13)

theorem balFindJalOff_resolves :
    AtBalFind + signExtend21 balFindJalOff = BalFindEntry := by
  simp only [AtBalFind, BalFindEntry, balFindJalOff, E]; decide

/-- Named hyp for unproven bal_find leaf (status-0 found path).
    Posts `x5 ↦ 0` so following `la x5, acct_*` has a concrete old value. -/
structure TeerBalFindAssumed (cr : CodeReq) where
  entry : Word
  nSteps : Nat
  success_flat :
    ∀ (ret balPtr balLenW : Word),
      (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin nSteps entry ret cr
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ balPtr) ** (.x11 ↦ᵣ balLenW) **
          (.x12 ↦ᵣ AuthorityAddr) ** (.x13 ↦ᵣ AcctPtrAddr) **
          (.x14 ↦ᵣ AcctLenAddr) **
          memOwn AuthorityAddr ** memOwn AcctPtrAddr ** memOwn AcctLenAddr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
          memOwn AuthorityAddr ** memOwn AcctPtrAddr ** memOwn AcctLenAddr **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))

def teerBalFindCalleeP (balPtr balLenW : Word) : Assertion :=
  (.x10 ↦ᵣ balPtr) ** (.x11 ↦ᵣ balLenW) **
  (.x12 ↦ᵣ AuthorityAddr) ** (.x13 ↦ᵣ AcctPtrAddr) **
  (.x14 ↦ᵣ AcctLenAddr) **
  memOwn AuthorityAddr ** memOwn AcctPtrAddr ** memOwn AcctLenAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

def teerBalFindCalleeQ : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
  memOwn AuthorityAddr ** memOwn AcctPtrAddr ** memOwn AcctLenAddr **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem teerBalFindCalleeP_pcFree (balPtr balLenW : Word) :
    (teerBalFindCalleeP balPtr balLenW).pcFree := by
  unfold teerBalFindCalleeP; pcf

/-- `mv a0, s2` balPtr. -/
theorem teerBalFindMvA0 (balPtr a0Old : Word) :
    cpsTripleWithin 1 AtBalFindSetup AfterBalFindMvA0 teerLinkedField0
      ((.x18 ↦ᵣ balPtr) ** (.x10 ↦ᵣ a0Old))
      ((.x18 ↦ᵣ balPtr) ** (.x10 ↦ᵣ balPtr)) := by
  have h0 := mv_spec_gen_within .x10 .x18 balPtr a0Old AtBalFindSetup (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtBalFindSetup teerProg 279
        (.MV .x10 .x18) (by simp only [AtBalFindSetup]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AtBalFindSetup + 4 : Word) = AfterBalFindMvA0 := by
    simp only [AtBalFindSetup, AfterBalFindMvA0]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a1, s3` balLen. -/
theorem teerBalFindMvA1 (balLenW a1Old : Word) :
    cpsTripleWithin 1 AfterBalFindMvA0 AfterBalFindMvA1 teerLinkedField0
      ((.x19 ↦ᵣ balLenW) ** (.x11 ↦ᵣ a1Old))
      ((.x19 ↦ᵣ balLenW) ** (.x11 ↦ᵣ balLenW)) := by
  have h0 := mv_spec_gen_within .x11 .x19 balLenW a1Old AfterBalFindMvA0 (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterBalFindMvA0 teerProg 280
        (.MV .x11 .x19) (by simp only [AfterBalFindMvA0]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterBalFindMvA0 + 4 : Word) = AfterBalFindMvA1 := by
    simp only [AfterBalFindMvA0, AfterBalFindMvA1]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `la a2, teer_authority`. -/
theorem teerLaAuthorityBal (v : Word) :
    cpsTripleWithin 2 AfterBalFindMvA1 AfterLaAuthBal teerLinkedField0
      (.x12 ↦ᵣ v) (.x12 ↦ᵣ AuthorityAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterBalFindMvA1
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_authority
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1124)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterBalFindMvA1 teerProg 281
        (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_authority
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1124)))
        (by simp only [AfterBalFindMvA1]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1128)
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_authority
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1124)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1128) teerProg 282
        (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_authority
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1124)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x12 v AfterBalFindMvA1 AuthorityAddr
    (by decide) (by decide) hau had
  rw [show (AfterBalFindMvA1 : Word) + 8 = AfterLaAuthBal from by
    simp only [AfterBalFindMvA1, AfterLaAuthBal]; bv_omega] at h
  exact h

/-- `la a3, teer_acct_ptr`. -/
theorem teerLaAcctPtr (v : Word) :
    cpsTripleWithin 2 AfterLaAuthBal AfterLaAcctPtr teerLinkedField0
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ AcctPtrAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterLaAuthBal
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.teer_acct_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1132)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaAuthBal teerProg 283
        (.AUIPC .x13 (Codegen.laHi GuestAddrs.teer_acct_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1132)))
        (by simp only [AfterLaAuthBal]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1136)
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.teer_acct_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1132)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1136) teerProg 284
        (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.teer_acct_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1132)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x13 v AfterLaAuthBal AcctPtrAddr
    (by decide) (by decide) hau had
  rw [show (AfterLaAuthBal : Word) + 8 = AfterLaAcctPtr from by
    simp only [AfterLaAuthBal, AfterLaAcctPtr]; bv_omega] at h
  exact h

/-- `la a4, teer_acct_len`. -/
theorem teerLaAcctLen (v : Word) :
    cpsTripleWithin 2 AfterLaAcctPtr AtBalFind teerLinkedField0
      (.x14 ↦ᵣ v) (.x14 ↦ᵣ AcctLenAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterLaAcctPtr
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.teer_acct_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1140)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaAcctPtr teerProg 285
        (.AUIPC .x14 (Codegen.laHi GuestAddrs.teer_acct_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1140)))
        (by simp only [AfterLaAcctPtr]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1144)
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.teer_acct_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1140)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1144) teerProg 286
        (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.teer_acct_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1140)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x14 v AfterLaAcctPtr AcctLenAddr
    (by decide) (by decide) hau had
  rw [show (AfterLaAcctPtr : Word) + 8 = AtBalFind from by
    simp only [AfterLaAcctPtr, AtBalFind]; bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Setup ABI for bal_find: AtBalFindSetup → AtBalFind. -/
theorem teerBalFindSetup (balPtr balLenW a0Old a1Old a2Old a3Old a4Old : Word) :
    cpsTripleWithin 8 AtBalFindSetup AtBalFind teerLinkedField0
      ((.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x13 ↦ᵣ a3Old) ** (.x14 ↦ᵣ a4Old))
      ((.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) **
        (.x10 ↦ᵣ balPtr) ** (.x11 ↦ᵣ balLenW) **
        (.x12 ↦ᵣ AuthorityAddr) ** (.x13 ↦ᵣ AcctPtrAddr) **
        (.x14 ↦ᵣ AcctLenAddr)) := by
  have hm0 := teerBalFindMvA0 balPtr a0Old
  have hm0F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ balLenW) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
      (.x13 ↦ᵣ a3Old) ** (.x14 ↦ᵣ a4Old)) (by pcf) hm0
  have hm1 := teerBalFindMvA1 balLenW a1Old
  have hm1F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ balPtr) ** (.x10 ↦ᵣ balPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x13 ↦ᵣ a3Old) ** (.x14 ↦ᵣ a4Old)) (by pcf) hm1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hm0F hm1F
  have hla2 := teerLaAuthorityBal a2Old
  have hla2F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x10 ↦ᵣ balPtr) **
      (.x11 ↦ᵣ balLenW) ** (.x13 ↦ᵣ a3Old) ** (.x14 ↦ᵣ a4Old)) (by pcf) hla2
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hla2F
  have hla3 := teerLaAcctPtr a3Old
  have hla3F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x10 ↦ᵣ balPtr) **
      (.x11 ↦ᵣ balLenW) ** (.x12 ↦ᵣ AuthorityAddr) ** (.x14 ↦ᵣ a4Old))
    (by pcf) hla3
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hla3F
  have hla4 := teerLaAcctLen a4Old
  have hla4F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x10 ↦ᵣ balPtr) **
      (.x11 ↦ᵣ balLenW) ** (.x12 ↦ᵣ AuthorityAddr) ** (.x13 ↦ᵣ AcctPtrAddr))
    (by pcf) hla4
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 hla4F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c34

set_option maxRecDepth 8000 in
/-- JAL bal_find under TeerBalFindAssumed → LinkBalFind. -/
theorem teerBalFindCall
    (asm : TeerBalFindAssumed teerLinkedField0)
    (hentry : asm.entry = BalFindEntry)
    (balPtr balLenW old1 : Word) :
    cpsTripleWithin (1 + asm.nSteps) AtBalFind LinkBalFind teerLinkedField0
      ((.x1 ↦ᵣ old1) ** teerBalFindCalleeP balPtr balLenW)
      ((.x1 ↦ᵣ LinkBalFind) ** teerBalFindCalleeQ) := by
  have hret : (LinkBalFind &&& ~~~(1 : Word)) = LinkBalFind := by
    simp only [LinkBalFind, E]; decide
  have hcallee0 := asm.success_flat LinkBalFind balPtr balLenW hret
  have hcallee0' : cpsTripleWithin asm.nSteps asm.entry LinkBalFind teerLinkedField0
      ((.x1 ↦ᵣ LinkBalFind) ** teerBalFindCalleeP balPtr balLenW)
      ((.x1 ↦ᵣ LinkBalFind) ** teerBalFindCalleeQ) := by
    unfold teerBalFindCalleeP teerBalFindCalleeQ
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcallee : cpsTripleWithin asm.nSteps BalFindEntry LinkBalFind teerLinkedField0
      ((.x1 ↦ᵣ LinkBalFind) ** teerBalFindCalleeP balPtr balLenW)
      ((.x1 ↦ᵣ LinkBalFind) ** teerBalFindCalleeQ) := by
    rw [← hentry]; exact hcallee0'
  have hcall := callWithin_spec AtBalFind BalFindEntry old1 balFindJalOff asm.nSteps
    balFindJalOff_resolves
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtBalFind teerProg 287
        (.JAL .x1 balFindJalOff) (by simp only [AtBalFind]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerBalFindCalleeP_pcFree balPtr balLenW)
    hcallee
  rw [show (AtBalFind + 4 : Word) = LinkBalFind from by
    simp only [AtBalFind, LinkBalFind]; bv_omega] at hcall
  exact hcall

/-- BNE a0,x0 ok after bal_find (status 0 = found) → AfterBalFindBne. -/
theorem teerBalFindBneOk :
    cpsTripleWithin 1 LinkBalFind AfterBalFindBne teerLinkedField0
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 teerBalFindBneOff
    (0 : Word) (0 : Word) LinkBalFind
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkBalFind teerProg 288
        (.BNE .x10 .x0 teerBalFindBneOff)
        (by simp only [LinkBalFind]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkBalFind + 4 = AfterBalFindBne := by
    simp only [LinkBalFind, AfterBalFindBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

#print axioms teerBalFindMvA0
#print axioms teerBalFindMvA1
#print axioms teerLaAuthorityBal
#print axioms teerLaAcctPtr
#print axioms teerLaAcctLen
#print axioms teerBalFindSetup
#print axioms teerBalFindCall
#print axioms teerBalFindBneOk

end EvmAsm.Codegen.TxEip7702TeerSpec
