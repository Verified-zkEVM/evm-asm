/-
  Teer auth-loop post-finals: zero teer_acct_absent + load records_ptr +
  empty-records skip:
  AfterBalFinalsBne (E+1196) → AtSvfTxCount (E+1276) when records_ptr = 0.

  Path: la/sd teer_acct_absent=0; la/ld teer_records_ptr; beq x5,x0 taken (off 56).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopBalFinals
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

abbrev AfterAcctAbsentLa : Word := E + 1204
abbrev AfterAcctAbsentZero : Word := E + 1208
abbrev AfterRecordsLa : Word := E + 1216
abbrev AfterRecordsLd : Word := E + 1220
/-- BEQ taken: records_ptr = 0 → skip bfa scale → svf_tx_count. -/
abbrev AtSvfTxCount : Word := E + 1276
abbrev AfterRecordsBeqNtaken : Word := AfterRecordsLd + 4

def AcctAbsentAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_acct_absent
def RecordsPtrAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_records_ptr

abbrev teerRecordsBeqOff : BitVec 13 := (56 : BitVec 13)

theorem teerRecordsBeqOff_taken :
    AfterRecordsLd + signExtend13 teerRecordsBeqOff = AtSvfTxCount := by
  simp only [AfterRecordsLd, AtSvfTxCount, teerRecordsBeqOff, E]; decide

private theorem se12_zero_aa : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

private theorem addr_add_off0_aa (a : Word) :
    a + signExtend12 (0 : BitVec 12) = a := by
  simp [signExtend12]

/-- `la x7, teer_acct_absent` AfterBalFinalsBne → AfterAcctAbsentLa. -/
theorem teerLaAcctAbsent (v : Word) :
    cpsTripleWithin 2 AfterBalFinalsBne AfterAcctAbsentLa teerLinkedField0
      (.x7 ↦ᵣ v) (.x7 ↦ᵣ AcctAbsentAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterBalFinalsBne
      (.AUIPC .x7 (Codegen.laHi GuestAddrs.teer_acct_absent
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1196)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterBalFinalsBne teerProg 299
        (.AUIPC .x7 (Codegen.laHi GuestAddrs.teer_acct_absent
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1196)))
        (by simp only [AfterBalFinalsBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1200)
      (.ADDI .x7 .x7 (Codegen.laLo GuestAddrs.teer_acct_absent
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1196)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1200) teerProg 300
        (.ADDI .x7 .x7 (Codegen.laLo GuestAddrs.teer_acct_absent
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1196)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x7 v AfterBalFinalsBne AcctAbsentAddr
    (by decide) (by decide) hau had
  rw [show (AfterBalFinalsBne : Word) + 8 = AfterAcctAbsentLa from by
    simp only [AfterBalFinalsBne, AfterAcctAbsentLa]; bv_omega] at h
  exact h

private theorem teerSdZeroAtX7 (addr pc : Word)
    (hmem : ∀ a i, CodeReq.singleton pc (.SD .x7 .x0 (0 : BitVec 12)) a = some i →
      teerLinkedField0 a = some i) :
    cpsTripleWithin 1 pc (pc + 4) teerLinkedField0
      ((.x7 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn addr)
      ((.x7 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn addr) := by
  have heq := addr_add_off0_aa addr
  have h0 := sd_spec_gen_own_within .x7 .x0 addr (0 : Word) (0 : BitVec 12) pc
  have h1 := cpsTripleWithin_extend_code hmem h0
  have h2 : cpsTripleWithin 1 pc (pc + 4) teerLinkedField0
      ((.x7 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn addr)
      ((.x7 ↦ᵣ addr) ** (.x0 ↦ᵣ (0 : Word)) ** (addr ↦ₘ (0 : Word))) := by
    convert h1 using 1 <;> simp only [heq]
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2

/-- `sd x0, 0(x7)` into teer_acct_absent. -/
theorem teerSdAcctAbsentZero (v7 : Word) (hv : v7 = AcctAbsentAddr) :
    cpsTripleWithin 1 AfterAcctAbsentLa AfterAcctAbsentZero teerLinkedField0
      ((.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn AcctAbsentAddr)
      ((.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn AcctAbsentAddr) := by
  subst hv
  have h := teerSdZeroAtX7 AcctAbsentAddr AfterAcctAbsentLa
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAcctAbsentLa teerProg 301
        (.SD .x7 .x0 (0 : BitVec 12)) (by simp only [AfterAcctAbsentLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi))
  rw [show (AfterAcctAbsentLa + 4 : Word) = AfterAcctAbsentZero from by
    simp only [AfterAcctAbsentLa, AfterAcctAbsentZero]; bv_omega] at h
  exact h

/-- `la x5, teer_records_ptr` AfterAcctAbsentZero → AfterRecordsLa. -/
theorem teerLaRecordsPtr (v : Word) :
    cpsTripleWithin 2 AfterAcctAbsentZero AfterRecordsLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ RecordsPtrAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterAcctAbsentZero
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_records_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1208)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAcctAbsentZero teerProg 302
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_records_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1208)))
        (by simp only [AfterAcctAbsentZero]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1212)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_records_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1208)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1212) teerProg 303
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_records_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1208)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterAcctAbsentZero RecordsPtrAddr
    (by decide) (by decide) hau had
  rw [show (AfterAcctAbsentZero : Word) + 8 = AfterRecordsLa from by
    simp only [AfterAcctAbsentZero, AfterRecordsLa]; bv_omega] at h
  exact h

/-- `ld x5, 0(x5)` records_ptr value (rd = rs1). -/
theorem teerLdRecordsPtr (recordsPtr : Word) :
    cpsTripleWithin 1 AfterRecordsLa AfterRecordsLd teerLinkedField0
      ((.x5 ↦ᵣ RecordsPtrAddr) ** (RecordsPtrAddr ↦ₘ recordsPtr))
      ((.x5 ↦ᵣ recordsPtr) ** (RecordsPtrAddr ↦ₘ recordsPtr)) := by
  have h0 := ld_spec_gen_same_within .x5 RecordsPtrAddr recordsPtr
    (0 : BitVec 12) AfterRecordsLa (by decide)
  rw [show RecordsPtrAddr + signExtend12 (0 : BitVec 12) = RecordsPtrAddr from by
    rw [se12_zero_aa]; exact BitVec.add_zero RecordsPtrAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterRecordsLa teerProg 304
        (.LD .x5 .x5 (0 : BitVec 12))
        (by simp only [AfterRecordsLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterRecordsLa + 4 = AfterRecordsLd := by
    simp only [AfterRecordsLa, AfterRecordsLd]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `beq x5, x0` taken: records_ptr = 0 → AtSvfTxCount. -/
theorem teerRecordsBeqTaken (recordsPtr : Word) (heq : recordsPtr = (0 : Word)) :
    cpsTripleWithin 1 AfterRecordsLd AtSvfTxCount teerLinkedField0
      ((.x5 ↦ᵣ recordsPtr) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ recordsPtr) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x5 .x0 teerRecordsBeqOff recordsPtr (0 : Word)
    AfterRecordsLd
  rw [teerRecordsBeqOff_taken] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterRecordsLd teerProg 305
          (.BEQ .x5 .x0 teerRecordsBeqOff)
          (by simp only [AfterRecordsLd]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 heq)

theorem teerRecordsBeqTaken_zero :
    cpsTripleWithin 1 AfterRecordsLd AtSvfTxCount teerLinkedField0
      ((.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
  teerRecordsBeqTaken (0 : Word) rfl

/-- `beq x5, x0` not-taken: records_ptr ≠ 0 → scale path. -/
theorem teerRecordsBeqNtaken (recordsPtr : Word) (hne : recordsPtr ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterRecordsLd AfterRecordsBeqNtaken teerLinkedField0
      ((.x5 ↦ᵣ recordsPtr) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ recordsPtr) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x5 .x0 teerRecordsBeqOff recordsPtr (0 : Word)
    AfterRecordsLd
  change cpsBranchWithin _ _ _ _ _ _ AfterRecordsBeqNtaken _ at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterRecordsLd teerProg 305
          (.BEQ .x5 .x0 teerRecordsBeqOff)
          (by simp only [AfterRecordsLd]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hBP).2)

/-- Zero acct_absent: AfterBalFinalsBne → AfterAcctAbsentZero. -/
theorem teerAcctAbsentZero (v7 : Word) :
    cpsTripleWithin 3 AfterBalFinalsBne AfterAcctAbsentZero teerLinkedField0
      ((.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn AcctAbsentAddr)
      ((.x7 ↦ᵣ AcctAbsentAddr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn AcctAbsentAddr) := by
  have hla := teerLaAcctAbsent v7
  have hlaF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** memOwn AcctAbsentAddr) (by pcf) hla
  have hsd := teerSdAcctAbsentZero AcctAbsentAddr rfl
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hsd
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c

/-- Load records_ptr (no BEQ): AfterAcctAbsentZero → AfterRecordsLd. -/
theorem teerRecordsLoad (recordsPtr t0Old : Word) :
    cpsTripleWithin 3 AfterAcctAbsentZero AfterRecordsLd teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (RecordsPtrAddr ↦ₘ recordsPtr))
      ((.x5 ↦ᵣ recordsPtr) ** (RecordsPtrAddr ↦ₘ recordsPtr)) := by
  have hla := teerLaRecordsPtr t0Old
  have hlaF := cpsTripleWithin_frameR (RecordsPtrAddr ↦ₘ recordsPtr) (by pcf) hla
  have hld := teerLdRecordsPtr recordsPtr
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hld
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c

set_option maxRecDepth 8000 in
/-- Empty records: zero absent + load records=0 + BEQ taken → AtSvfTxCount. -/
theorem teerRecordsEmptySkip (v5 v7 : Word) :
    cpsTripleWithin 7 AfterBalFinalsBne AtSvfTxCount teerLinkedField0
      ((.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn AcctAbsentAddr ** (RecordsPtrAddr ↦ₘ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ AcctAbsentAddr) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn AcctAbsentAddr ** (RecordsPtrAddr ↦ₘ (0 : Word))) := by
  have hzero := teerAcctAbsentZero v7
  have hzeroF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (RecordsPtrAddr ↦ₘ (0 : Word))) (by pcf) hzero
  have hload := teerRecordsLoad (0 : Word) v5
  have hloadF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ AcctAbsentAddr) ** (.x0 ↦ᵣ (0 : Word)) ** memOwn AcctAbsentAddr)
    (by pcf) hload
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hzeroF hloadF
  have hbeq := teerRecordsBeqTaken_zero
  have hbeqF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ AcctAbsentAddr) ** memOwn AcctAbsentAddr **
      (RecordsPtrAddr ↦ₘ (0 : Word))) (by pcf) hbeq
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hbeqF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

#print axioms teerLaAcctAbsent
#print axioms teerSdAcctAbsentZero
#print axioms teerLaRecordsPtr
#print axioms teerLdRecordsPtr
#print axioms teerRecordsBeqTaken_zero
#print axioms teerRecordsBeqNtaken
#print axioms teerAcctAbsentZero
#print axioms teerRecordsLoad
#print axioms teerRecordsEmptySkip

end EvmAsm.Codegen.TxEip7702TeerSpec
