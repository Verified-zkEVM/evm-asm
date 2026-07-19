/-
  Teer: after walk_next cycle5 ok, store recipient content ptr/len.
  AfterWalkNext5Bne (E+348): SUB x30,a0,a2; la/sd teer_recipient_ptr;
  la/sd teer_recipient_len; MV s8,a0 → AfterRecipientSave (E+380).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxEip7702TeerSpec
import EvmAsm.Codegen.Programs.TxEip7702TeerType
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNextSkip
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

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

abbrev RecipientPtrAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_recipient_ptr
abbrev RecipientLenAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_recipient_len

/-- After SUB at E+348. -/
abbrev AfterRecipientSub : Word := E + 352
/-- After la/sd recipient_ptr (3 instr). -/
abbrev AfterRecipientPtrStore : Word := E + 364
/-- After la/sd recipient_len (3 instr). -/
abbrev AfterRecipientLenStore : Word := E + 376
/-- After MV s8,a0. -/
abbrev AfterRecipientSave : Word := E + 380

private theorem addr_add_off0 (a : Word) : a + signExtend12 (0 : BitVec 12) = a := by
  simp [signExtend12]

/-- `sub x30, a0, a2` at AfterWalkNext5Bne: contentPtr = next - len. -/
theorem teerRecipientSub (next lenW t5Old : Word) :
    cpsTripleWithin 1 AfterWalkNext5Bne AfterRecipientSub teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x30 ↦ᵣ t5Old))
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x30 ↦ᵣ (next - lenW))) := by
  have hs := sub_spec_gen_within .x30 .x10 .x12 next lenW t5Old AfterWalkNext5Bne (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNext5Bne teerProg 87
        (.SUB .x30 .x10 .x12) (by simp only [AfterWalkNext5Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hs
  have hpc : AfterWalkNext5Bne + 4 = AfterRecipientSub := by
    simp only [AfterWalkNext5Bne, AfterRecipientSub]; bv_omega
  rw [hpc] at he
  exact he

/-- `la x5, teer_recipient_ptr` at E+352. -/
theorem teerLaRecipientPtr (v : Word) :
    cpsTripleWithin 2 AfterRecipientSub (E + 360) teerLinkedEarly
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ RecipientPtrAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterRecipientSub
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_recipient_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 352)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterRecipientSub teerProg 88
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_recipient_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 352)))
        (by simp only [AfterRecipientSub]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AfterRecipientSub + 4)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_recipient_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 352)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (AfterRecipientSub + 4) teerProg 89
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_recipient_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 352)))
        (by simp only [AfterRecipientSub]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterRecipientSub RecipientPtrAddr
    (by decide) (by decide) hau had
  rw [show (AfterRecipientSub : Word) + 8 = E + 360 from by
    simp only [AfterRecipientSub, E]; bv_omega] at h
  exact h

private theorem teerSdCell (rs2 : Reg) (addr data : Word) (pc : Word)
    (hmem : ∀ a i, CodeReq.singleton pc (.SD .x5 rs2 (0 : BitVec 12)) a = some i →
      teerLinkedEarly a = some i) :
    cpsTripleWithin 1 pc (pc + 4) teerLinkedEarly
      ((.x5 ↦ᵣ addr) ** (rs2 ↦ᵣ data) ** memOwn addr)
      ((.x5 ↦ᵣ addr) ** (rs2 ↦ᵣ data) ** memOwn addr) := by
  have heq := addr_add_off0 addr
  have h0 := sd_spec_gen_own_within .x5 rs2 addr data (0 : BitVec 12) pc
  have h1 := cpsTripleWithin_extend_code hmem h0
  have h2 : cpsTripleWithin 1 pc (pc + 4) teerLinkedEarly
      ((.x5 ↦ᵣ addr) ** (rs2 ↦ᵣ data) ** memOwn addr)
      ((.x5 ↦ᵣ addr) ** (rs2 ↦ᵣ data) ** (addr ↦ₘ data)) := by
    convert h1 using 1 <;> simp only [heq]
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2

/-- `sd x30, 0(x5)` into teer_recipient_ptr. -/
theorem teerSdRecipientPtr (v5 contentPtr : Word) (hv : v5 = RecipientPtrAddr) :
    cpsTripleWithin 1 (E + 360) AfterRecipientPtrStore teerLinkedEarly
      ((.x5 ↦ᵣ v5) ** (.x30 ↦ᵣ contentPtr) ** memOwn RecipientPtrAddr)
      ((.x5 ↦ᵣ v5) ** (.x30 ↦ᵣ contentPtr) ** memOwn RecipientPtrAddr) := by
  subst hv
  have h := teerSdCell .x30 RecipientPtrAddr contentPtr (E + 360)
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 360) teerProg 90
        (.SD .x5 .x30 (0 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
  have hpc : (E + 360 : Word) + 4 = AfterRecipientPtrStore := by
    simp only [AfterRecipientPtrStore, E]; bv_omega
  rw [hpc] at h
  exact h

/-- `la x5, teer_recipient_len` at E+364. -/
theorem teerLaRecipientLen (v : Word) :
    cpsTripleWithin 2 AfterRecipientPtrStore (E + 372) teerLinkedEarly
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ RecipientLenAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterRecipientPtrStore
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_recipient_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 364)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterRecipientPtrStore teerProg 91
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_recipient_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 364)))
        (by simp only [AfterRecipientPtrStore]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AfterRecipientPtrStore + 4)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_recipient_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 364)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (AfterRecipientPtrStore + 4) teerProg 92
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_recipient_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 364)))
        (by simp only [AfterRecipientPtrStore]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterRecipientPtrStore RecipientLenAddr
    (by decide) (by decide) hau had
  rw [show (AfterRecipientPtrStore : Word) + 8 = E + 372 from by
    simp only [AfterRecipientPtrStore, E]; bv_omega] at h
  exact h

/-- `sd x12, 0(x5)` into teer_recipient_len. -/
theorem teerSdRecipientLen (v5 lenW : Word) (hv : v5 = RecipientLenAddr) :
    cpsTripleWithin 1 (E + 372) AfterRecipientLenStore teerLinkedEarly
      ((.x5 ↦ᵣ v5) ** (.x12 ↦ᵣ lenW) ** memOwn RecipientLenAddr)
      ((.x5 ↦ᵣ v5) ** (.x12 ↦ᵣ lenW) ** memOwn RecipientLenAddr) := by
  subst hv
  have h := teerSdCell .x12 RecipientLenAddr lenW (E + 372)
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 372) teerProg 93
        (.SD .x5 .x12 (0 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
  have hpc : (E + 372 : Word) + 4 = AfterRecipientLenStore := by
    simp only [AfterRecipientLenStore, E]; bv_omega
  rw [hpc] at h
  exact h

/-- `mv s8, a0` after recipient stores. -/
theorem teerRecipientSaveS8 (next v24 : Word) :
    cpsTripleWithin 1 AfterRecipientLenStore AfterRecipientSave teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ v24))
      ((.x10 ↦ᵣ next) ** (.x24 ↦ᵣ next)) := by
  have hm := mv_spec_gen_within .x24 .x10 next v24 AfterRecipientLenStore (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterRecipientLenStore teerProg 94
        (.MV .x24 .x10) (by simp only [AfterRecipientLenStore]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hm
  have hpc : AfterRecipientLenStore + 4 = AfterRecipientSave := by
    simp only [AfterRecipientLenStore, AfterRecipientSave]; bv_omega
  rw [hpc] at he
  exact he

/-- Full recipient block: SUB + store ptr/len + save s8 (8 steps). -/
theorem teerRecipientStore (next lenW t5Old v5 v24 : Word) :
    cpsTripleWithin 8 AfterWalkNext5Bne AfterRecipientSave teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x30 ↦ᵣ t5Old) ** (.x5 ↦ᵣ v5) **
        (.x24 ↦ᵣ v24) ** memOwn RecipientPtrAddr ** memOwn RecipientLenAddr)
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x30 ↦ᵣ (next - lenW)) **
        (.x5 ↦ᵣ RecipientLenAddr) ** (.x24 ↦ᵣ next) **
        memOwn RecipientPtrAddr ** memOwn RecipientLenAddr) := by
  have hsub := teerRecipientSub next lenW t5Old
  have hsubF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x24 ↦ᵣ v24) **
      memOwn RecipientPtrAddr ** memOwn RecipientLenAddr) (by pcf) hsub
  have hlaP := teerLaRecipientPtr v5
  have hlaPF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x30 ↦ᵣ (next - lenW)) **
      (.x24 ↦ᵣ v24) ** memOwn RecipientPtrAddr ** memOwn RecipientLenAddr)
    (by pcf) hlaP
  have hsdP := teerSdRecipientPtr RecipientPtrAddr (next - lenW) rfl
  have hsdPF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x24 ↦ᵣ v24) **
      memOwn RecipientLenAddr) (by pcf) hsdP
  have hlaL := teerLaRecipientLen RecipientPtrAddr
  have hlaLF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x30 ↦ᵣ (next - lenW)) **
      (.x24 ↦ᵣ v24) ** memOwn RecipientPtrAddr ** memOwn RecipientLenAddr)
    (by pcf) hlaL
  have hsdL := teerSdRecipientLen RecipientLenAddr lenW rfl
  have hsdLF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x30 ↦ᵣ (next - lenW)) ** (.x24 ↦ᵣ v24) **
      memOwn RecipientPtrAddr) (by pcf) hsdL
  have hmv := teerRecipientSaveS8 next v24
  have hmvF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ lenW) ** (.x30 ↦ᵣ (next - lenW)) ** (.x5 ↦ᵣ RecipientLenAddr) **
      memOwn RecipientPtrAddr ** memOwn RecipientLenAddr) (by pcf) hmv
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsubF hlaPF
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 hsdPF
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hlaLF
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 hsdLF
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 hmvF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c4

#print axioms teerRecipientSub
#print axioms teerLaRecipientPtr
#print axioms teerSdRecipientPtr
#print axioms teerLaRecipientLen
#print axioms teerSdRecipientLen
#print axioms teerRecipientSaveS8
#print axioms teerRecipientStore

end EvmAsm.Codegen.TxEip7702TeerSpec
