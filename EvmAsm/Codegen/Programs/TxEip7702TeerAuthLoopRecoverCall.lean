/-
  Teer auth-loop recover call under named Assumed + BNE ok + prior_* zero:
  AtRecover (E+936) → AfterPriorSetFlagZero (E+968).
  Recover leaf unproven; TeerRecoverAssumed.success_flat is the named hyp.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopRecover
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic

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

abbrev RecoverEntry : Word :=
  BitVec.ofNat 64 GuestAddrs.eip7702_authorization_recover_address

abbrev AfterRecoverBne : Word := E + 944
abbrev AfterPriorCountLa : Word := E + 952
abbrev AfterPriorCountZero : Word := E + 956
abbrev AfterPriorSetFlagLa : Word := E + 964
abbrev AfterPriorSetFlagZero : Word := E + 968

def PriorCountAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_prior_count
def PriorSetFlagAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_prior_set_flag

def recoverJalOff : BitVec 21 :=
  jalOff GuestAddrs.eip7702_authorization_recover_address
    (GuestAddrs.tx_eip7702_existing_authority_refund + 936)

abbrev teerRecoverBneOff : BitVec 13 := (904 : BitVec 13)

theorem recoverJalOff_resolves :
    AtRecover + signExtend21 recoverJalOff = RecoverEntry := by
  simp only [AtRecover, RecoverEntry, recoverJalOff, E]; decide

theorem teerRecoverBneOff_taken :
    LinkRecover + signExtend13 teerRecoverBneOff = AtChainMismatch := by
  simp only [LinkRecover, AtChainMismatch, teerRecoverBneOff, E]; decide

/-- Named hyp for unproven recover leaf (status-0 path).
    Posts `x5 ↦ 0` so the following `la x5, prior_*` has a concrete old value. -/
structure TeerRecoverAssumed (cr : CodeReq) where
  entry : Word
  nSteps : Nat
  success_flat :
    ∀ (ret authPtr authLenW : Word),
      (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin nSteps entry ret cr
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ authPtr) ** (.x11 ↦ᵣ authLenW) **
          (.x12 ↦ᵣ AuthorityAddr) ** (.x13 ↦ᵣ RecoverScratchAddr) **
          memOwn AuthorityAddr ** memOwn RecoverScratchAddr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
          memOwn AuthorityAddr ** memOwn RecoverScratchAddr **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))

def teerRecoverCalleeP (authPtr authLenW : Word) : Assertion :=
  (.x10 ↦ᵣ authPtr) ** (.x11 ↦ᵣ authLenW) **
  (.x12 ↦ᵣ AuthorityAddr) ** (.x13 ↦ᵣ RecoverScratchAddr) **
  memOwn AuthorityAddr ** memOwn RecoverScratchAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

def teerRecoverCalleeQ : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
  memOwn AuthorityAddr ** memOwn RecoverScratchAddr **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem teerRecoverCalleeP_pcFree (authPtr authLenW : Word) :
    (teerRecoverCalleeP authPtr authLenW).pcFree := by
  unfold teerRecoverCalleeP; pcf

set_option maxRecDepth 8000 in
/-- JAL recover under TeerRecoverAssumed → LinkRecover. -/
theorem teerRecoverCall
    (asm : TeerRecoverAssumed teerLinkedField0)
    (hentry : asm.entry = RecoverEntry)
    (authPtr authLenW old1 : Word) :
    cpsTripleWithin (1 + asm.nSteps) AtRecover LinkRecover teerLinkedField0
      ((.x1 ↦ᵣ old1) ** teerRecoverCalleeP authPtr authLenW)
      ((.x1 ↦ᵣ LinkRecover) ** teerRecoverCalleeQ) := by
  have hret : (LinkRecover &&& ~~~(1 : Word)) = LinkRecover := by
    simp only [LinkRecover, E]; decide
  have hcallee0 := asm.success_flat LinkRecover authPtr authLenW hret
  have hcallee0' : cpsTripleWithin asm.nSteps asm.entry LinkRecover teerLinkedField0
      ((.x1 ↦ᵣ LinkRecover) ** teerRecoverCalleeP authPtr authLenW)
      ((.x1 ↦ᵣ LinkRecover) ** teerRecoverCalleeQ) := by
    unfold teerRecoverCalleeP teerRecoverCalleeQ
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcallee : cpsTripleWithin asm.nSteps RecoverEntry LinkRecover teerLinkedField0
      ((.x1 ↦ᵣ LinkRecover) ** teerRecoverCalleeP authPtr authLenW)
      ((.x1 ↦ᵣ LinkRecover) ** teerRecoverCalleeQ) := by
    rw [← hentry]; exact hcallee0'
  have hcall := callWithin_spec AtRecover RecoverEntry old1 recoverJalOff asm.nSteps
    recoverJalOff_resolves
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtRecover teerProg 234
        (.JAL .x1 recoverJalOff) (by simp only [AtRecover]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerRecoverCalleeP_pcFree authPtr authLenW)
    hcallee
  rw [show (AtRecover + 4 : Word) = LinkRecover from by
    simp only [AtRecover, LinkRecover]; bv_omega] at hcall
  exact hcall

/-- BNE a0,x0 ok after recover (status 0) → AfterRecoverBne. -/
theorem teerRecoverBneOk :
    cpsTripleWithin 1 LinkRecover AfterRecoverBne teerLinkedField0
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 teerRecoverBneOff
    (0 : Word) (0 : Word) LinkRecover
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkRecover teerProg 235
        (.BNE .x10 .x0 teerRecoverBneOff)
        (by simp only [LinkRecover]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkRecover + 4 = AfterRecoverBne := by
    simp only [LinkRecover, AfterRecoverBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `la x5, teer_prior_count` AfterRecoverBne → AfterPriorCountLa. -/
theorem teerLaPriorCount (v : Word) :
    cpsTripleWithin 2 AfterRecoverBne AfterPriorCountLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ PriorCountAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterRecoverBne
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_prior_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 944)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterRecoverBne teerProg 236
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_prior_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 944)))
        (by simp only [AfterRecoverBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 948)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_prior_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 944)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 948) teerProg 237
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_prior_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 944)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterRecoverBne PriorCountAddr
    (by decide) (by decide) hau had
  rw [show (AfterRecoverBne : Word) + 8 = AfterPriorCountLa from by
    simp only [AfterRecoverBne, AfterPriorCountLa]; bv_omega] at h
  exact h

private theorem addr_add_off0 (a : Word) :
    a + signExtend12 (0 : BitVec 12) = a := by
  simp [signExtend12]

private theorem teerSdZeroAt (addr pc : Word)
    (hmem : ∀ a i, CodeReq.singleton pc (.SD .x5 .x0 (0 : BitVec 12)) a = some i →
      teerLinkedField0 a = some i) :
    cpsTripleWithin 1 pc (pc + 4) teerLinkedField0
      ((.x5 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn addr)
      ((.x5 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn addr) := by
  have heq := addr_add_off0 addr
  have h0 := sd_spec_gen_own_within .x5 .x0 addr (0 : Word) (0 : BitVec 12) pc
  have h1 := cpsTripleWithin_extend_code hmem h0
  have h2 : cpsTripleWithin 1 pc (pc + 4) teerLinkedField0
      ((.x5 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn addr)
      ((.x5 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** (addr ↦ₘ (0 : Word))) := by
    convert h1 using 1 <;> simp only [heq]
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2

/-- `sd x0, 0(x5)` prior_count. -/
theorem teerSdPriorCountZero (v5 : Word) (hv : v5 = PriorCountAddr) :
    cpsTripleWithin 1 AfterPriorCountLa AfterPriorCountZero teerLinkedField0
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn PriorCountAddr)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn PriorCountAddr) := by
  subst hv
  have h := teerSdZeroAt PriorCountAddr AfterPriorCountLa
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPriorCountLa teerProg 238
        (.SD .x5 .x0 (0 : BitVec 12)) (by simp only [AfterPriorCountLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi))
  rw [show (AfterPriorCountLa + 4 : Word) = AfterPriorCountZero from by
    simp only [AfterPriorCountLa, AfterPriorCountZero]; bv_omega] at h
  exact h

/-- `la x5, teer_prior_set_flag`. -/
theorem teerLaPriorSetFlag (v : Word) :
    cpsTripleWithin 2 AfterPriorCountZero AfterPriorSetFlagLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ PriorSetFlagAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterPriorCountZero
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_prior_set_flag
        (GuestAddrs.tx_eip7702_existing_authority_refund + 956)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPriorCountZero teerProg 239
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_prior_set_flag
          (GuestAddrs.tx_eip7702_existing_authority_refund + 956)))
        (by simp only [AfterPriorCountZero]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 960)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_prior_set_flag
        (GuestAddrs.tx_eip7702_existing_authority_refund + 956)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 960) teerProg 240
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_prior_set_flag
          (GuestAddrs.tx_eip7702_existing_authority_refund + 956)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterPriorCountZero PriorSetFlagAddr
    (by decide) (by decide) hau had
  rw [show (AfterPriorCountZero : Word) + 8 = AfterPriorSetFlagLa from by
    simp only [AfterPriorCountZero, AfterPriorSetFlagLa]; bv_omega] at h
  exact h

/-- `sd x0, 0(x5)` prior_set_flag. -/
theorem teerSdPriorSetFlagZero (v5 : Word) (hv : v5 = PriorSetFlagAddr) :
    cpsTripleWithin 1 AfterPriorSetFlagLa AfterPriorSetFlagZero teerLinkedField0
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn PriorSetFlagAddr)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn PriorSetFlagAddr) := by
  subst hv
  have h := teerSdZeroAt PriorSetFlagAddr AfterPriorSetFlagLa
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPriorSetFlagLa teerProg 241
        (.SD .x5 .x0 (0 : BitVec 12)) (by simp only [AfterPriorSetFlagLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi))
  rw [show (AfterPriorSetFlagLa + 4 : Word) = AfterPriorSetFlagZero from by
    simp only [AfterPriorSetFlagLa, AfterPriorSetFlagZero]; bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Zero prior_count + prior_set_flag: AfterRecoverBne → AfterPriorSetFlagZero.
    Pre requires `x5 ↦ v` (e.g. `0` from recover Assumed post). -/
theorem teerPriorZeros (v5 : Word) :
    cpsTripleWithin 6 AfterRecoverBne AfterPriorSetFlagZero teerLinkedField0
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn PriorCountAddr ** memOwn PriorSetFlagAddr)
      ((.x5 ↦ᵣ PriorSetFlagAddr) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn PriorCountAddr ** memOwn PriorSetFlagAddr) := by
  have hla0 := teerLaPriorCount v5
  have hla0F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** memOwn PriorCountAddr ** memOwn PriorSetFlagAddr)
    (by pcf) hla0
  have hsd0 := teerSdPriorCountZero PriorCountAddr rfl
  have hsd0F := cpsTripleWithin_frameR (memOwn PriorSetFlagAddr) (by pcf) hsd0
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla0F hsd0F
  have hla1 := teerLaPriorSetFlag PriorCountAddr
  have hla1F := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** memOwn PriorCountAddr ** memOwn PriorSetFlagAddr)
    (by pcf) hla1
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hla1F
  have hsd1 := teerSdPriorSetFlagZero PriorSetFlagAddr rfl
  have hsd1F := cpsTripleWithin_frameR (memOwn PriorCountAddr) (by pcf) hsd1
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hsd1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c23

#print axioms teerRecoverCall
#print axioms teerRecoverBneOk
#print axioms teerLaPriorCount
#print axioms teerSdPriorCountZero
#print axioms teerLaPriorSetFlag
#print axioms teerSdPriorSetFlagZero
#print axioms teerPriorZeros

end EvmAsm.Codegen.TxEip7702TeerSpec
