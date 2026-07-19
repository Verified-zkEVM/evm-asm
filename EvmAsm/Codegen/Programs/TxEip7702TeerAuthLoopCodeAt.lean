/-
  Teer auth-loop code_at_header_state_root setup + Call(Assumed) + BNE ok:
  AfterSvfTxCountBne (E+1296) → AfterCodeAtBne (E+1388) when
  bv_witness_state_ptr ≠ 0 and code_at status 0.

  ABI: a0=pre_rlp_ptr, a1=pre_rlp_len, a2=authority, a3=witness_state_ptr (x13),
       a4=witness_state_len (x14), a5=codes_ptr (x15), a6=codes_len (x16).
  Leaf unproven; TeerCodeAtAssumed.success_flat is the named hyp.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopSvfTxCount
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

abbrev AfterWitnessStateLa : Word := E + 1304
abbrev AfterWitnessStateLd : Word := E + 1308
abbrev AfterWitnessStateBeq : Word := E + 1312
abbrev AfterPreRlpPtrLa : Word := E + 1320
abbrev AfterPreRlpPtrLd : Word := E + 1324
abbrev AfterPreRlpLenLa : Word := E + 1332
abbrev AfterPreRlpLenLd : Word := E + 1336
abbrev AfterAuthorityLa2 : Word := E + 1344
abbrev AfterWitnessLenLa : Word := E + 1352
abbrev AfterWitnessLenLd : Word := E + 1356
abbrev AfterCodesPtrLa : Word := E + 1364
abbrev AfterCodesPtrLd : Word := E + 1368
abbrev AfterCodesLenLa : Word := E + 1376
abbrev AtCodeAt : Word := E + 1380
abbrev LinkCodeAt : Word := E + 1384
abbrev AfterCodeAtBne : Word := E + 1388

def WitnessStatePtrAddr : Word := BitVec.ofNat 64 GuestAddrs.bv_witness_state_ptr
def WitnessStateLenAddr : Word := BitVec.ofNat 64 GuestAddrs.bv_witness_state_len
def PreRlpPtrAddr : Word := BitVec.ofNat 64 GuestAddrs.sv_pre_rlp_ptr
def PreRlpLenAddr : Word := BitVec.ofNat 64 GuestAddrs.sv_pre_rlp_len
def CodesPtrAddr : Word := BitVec.ofNat 64 GuestAddrs.svf_codes_ptr
def CodesLenAddr : Word := BitVec.ofNat 64 GuestAddrs.svf_codes_len

abbrev CodeAtEntry : Word :=
  BitVec.ofNat 64 GuestAddrs.code_at_header_state_root

def codeAtJalOff : BitVec 21 :=
  jalOff GuestAddrs.code_at_header_state_root
    (GuestAddrs.tx_eip7702_existing_authority_refund + 1380)

abbrev teerWitnessBeqOff : BitVec 13 := (540 : BitVec 13)
abbrev teerCodeAtBneOff : BitVec 13 := (464 : BitVec 13)

theorem codeAtJalOff_resolves :
    AtCodeAt + signExtend21 codeAtJalOff = CodeAtEntry := by
  simp only [AtCodeAt, CodeAtEntry, codeAtJalOff, E]; decide

theorem teerWitnessBeqOff_taken :
    AfterWitnessStateLd + signExtend13 teerWitnessBeqOff = AtSvfTxCountSkip := by
  simp only [AfterWitnessStateLd, AtSvfTxCountSkip, teerWitnessBeqOff, E]; decide

theorem teerCodeAtBneOff_taken :
    LinkCodeAt + signExtend13 teerCodeAtBneOff = AtSvfTxCountSkip := by
  simp only [LinkCodeAt, AtSvfTxCountSkip, teerCodeAtBneOff, E]; decide

private theorem se12_zero_ca : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- Named hyp for unproven code_at_header_state_root leaf (status-0 path).
    Posts `x5 ↦ 0` so following `la x5, cahsr_*` has a concrete old value. -/
structure TeerCodeAtAssumed (cr : CodeReq) where
  entry : Word
  nSteps : Nat
  success_flat :
    ∀ (ret prePtr preLenW witPtr witLenW codesPtr codesLenW : Word),
      (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin nSteps entry ret cr
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ preLenW) **
          (.x12 ↦ᵣ AuthorityAddr) ** (.x13 ↦ᵣ witPtr) **
          (.x14 ↦ᵣ witLenW) ** (.x15 ↦ᵣ codesPtr) ** (.x16 ↦ᵣ codesLenW) **
          memOwn AuthorityAddr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
          memOwn AuthorityAddr **
          regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))

def teerCodeAtCalleeP (prePtr preLenW witPtr witLenW codesPtr codesLenW : Word) :
    Assertion :=
  (.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ preLenW) **
  (.x12 ↦ᵣ AuthorityAddr) ** (.x13 ↦ᵣ witPtr) **
  (.x14 ↦ᵣ witLenW) ** (.x15 ↦ᵣ codesPtr) ** (.x16 ↦ᵣ codesLenW) **
  memOwn AuthorityAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

def teerCodeAtCalleeQ : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (0 : Word)) **
  memOwn AuthorityAddr **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem teerCodeAtCalleeP_pcFree
    (prePtr preLenW witPtr witLenW codesPtr codesLenW : Word) :
    (teerCodeAtCalleeP prePtr preLenW witPtr witLenW codesPtr codesLenW).pcFree := by
  unfold teerCodeAtCalleeP; pcf

/-- `la x5, bv_witness_state_ptr`. -/
theorem teerLaWitnessStatePtr (v : Word) :
    cpsTripleWithin 2 AfterSvfTxCountBne AfterWitnessStateLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ WitnessStatePtrAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterSvfTxCountBne
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.bv_witness_state_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1296)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSvfTxCountBne teerProg 324
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.bv_witness_state_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1296)))
        (by simp only [AfterSvfTxCountBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1300)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.bv_witness_state_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1296)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1300) teerProg 325
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.bv_witness_state_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1296)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterSvfTxCountBne WitnessStatePtrAddr
    (by decide) (by decide) hau had
  rw [show (AfterSvfTxCountBne : Word) + 8 = AfterWitnessStateLa from by
    simp only [AfterSvfTxCountBne, AfterWitnessStateLa]; bv_omega] at h
  exact h

/-- `ld x13, 0(x5)` witness_state_ptr. -/
theorem teerLdWitnessStatePtr (witPtr t3Old : Word) :
    cpsTripleWithin 1 AfterWitnessStateLa AfterWitnessStateLd teerLinkedField0
      ((.x5 ↦ᵣ WitnessStatePtrAddr) ** (.x13 ↦ᵣ t3Old) **
        (WitnessStatePtrAddr ↦ₘ witPtr))
      ((.x5 ↦ᵣ WitnessStatePtrAddr) ** (.x13 ↦ᵣ witPtr) **
        (WitnessStatePtrAddr ↦ₘ witPtr)) := by
  have h0 := ld_spec_gen_within .x13 .x5 WitnessStatePtrAddr t3Old witPtr
    (0 : BitVec 12) AfterWitnessStateLa (by decide)
  rw [show WitnessStatePtrAddr + signExtend12 (0 : BitVec 12) = WitnessStatePtrAddr from by
    rw [se12_zero_ca]; exact BitVec.add_zero WitnessStatePtrAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWitnessStateLa teerProg 326
        (.LD .x13 .x5 (0 : BitVec 12))
        (by simp only [AfterWitnessStateLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterWitnessStateLa + 4 = AfterWitnessStateLd := by
    simp only [AfterWitnessStateLa, AfterWitnessStateLd]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `beq x13, x0` not-taken: witness ptr ≠ 0. -/
theorem teerWitnessBeqNtaken (witPtr : Word) (hne : witPtr ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterWitnessStateLd AfterWitnessStateBeq teerLinkedField0
      ((.x13 ↦ᵣ witPtr) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x13 ↦ᵣ witPtr) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x13 .x0 teerWitnessBeqOff witPtr (0 : Word)
    AfterWitnessStateLd
  change cpsBranchWithin _ _ _ _ _ _ AfterWitnessStateBeq _ at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterWitnessStateLd teerProg 327
          (.BEQ .x13 .x0 teerWitnessBeqOff)
          (by simp only [AfterWitnessStateLd]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hBP).2)

/-- `beq x13, x0` taken: witness ptr = 0 → AtSvfTxCountSkip. -/
theorem teerWitnessBeqTaken (witPtr : Word) (heq : witPtr = (0 : Word)) :
    cpsTripleWithin 1 AfterWitnessStateLd AtSvfTxCountSkip teerLinkedField0
      ((.x13 ↦ᵣ witPtr) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x13 ↦ᵣ witPtr) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x13 .x0 teerWitnessBeqOff witPtr (0 : Word)
    AfterWitnessStateLd
  rw [teerWitnessBeqOff_taken] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterWitnessStateLd teerProg 327
          (.BEQ .x13 .x0 teerWitnessBeqOff)
          (by simp only [AfterWitnessStateLd]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 heq)

theorem teerLaPreRlpPtr (v : Word) :
    cpsTripleWithin 2 AfterWitnessStateBeq AfterPreRlpPtrLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ PreRlpPtrAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterWitnessStateBeq
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.sv_pre_rlp_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1312)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWitnessStateBeq teerProg 328
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.sv_pre_rlp_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1312)))
        (by simp only [AfterWitnessStateBeq]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1316)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.sv_pre_rlp_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1312)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1316) teerProg 329
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.sv_pre_rlp_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1312)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterWitnessStateBeq PreRlpPtrAddr
    (by decide) (by decide) hau had
  rw [show (AfterWitnessStateBeq : Word) + 8 = AfterPreRlpPtrLa from by
    simp only [AfterWitnessStateBeq, AfterPreRlpPtrLa]; bv_omega] at h
  exact h

theorem teerLdPreRlpPtr (prePtr a0Old : Word) :
    cpsTripleWithin 1 AfterPreRlpPtrLa AfterPreRlpPtrLd teerLinkedField0
      ((.x5 ↦ᵣ PreRlpPtrAddr) ** (.x10 ↦ᵣ a0Old) ** (PreRlpPtrAddr ↦ₘ prePtr))
      ((.x5 ↦ᵣ PreRlpPtrAddr) ** (.x10 ↦ᵣ prePtr) ** (PreRlpPtrAddr ↦ₘ prePtr)) := by
  have h0 := ld_spec_gen_within .x10 .x5 PreRlpPtrAddr a0Old prePtr
    (0 : BitVec 12) AfterPreRlpPtrLa (by decide)
  rw [show PreRlpPtrAddr + signExtend12 (0 : BitVec 12) = PreRlpPtrAddr from by
    rw [se12_zero_ca]; exact BitVec.add_zero PreRlpPtrAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPreRlpPtrLa teerProg 330
        (.LD .x10 .x5 (0 : BitVec 12))
        (by simp only [AfterPreRlpPtrLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterPreRlpPtrLa + 4 = AfterPreRlpPtrLd := by
    simp only [AfterPreRlpPtrLa, AfterPreRlpPtrLd]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerLaPreRlpLen (v : Word) :
    cpsTripleWithin 2 AfterPreRlpPtrLd AfterPreRlpLenLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ PreRlpLenAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterPreRlpPtrLd
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.sv_pre_rlp_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1324)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPreRlpPtrLd teerProg 331
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.sv_pre_rlp_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1324)))
        (by simp only [AfterPreRlpPtrLd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1328)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.sv_pre_rlp_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1324)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1328) teerProg 332
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.sv_pre_rlp_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1324)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterPreRlpPtrLd PreRlpLenAddr
    (by decide) (by decide) hau had
  rw [show (AfterPreRlpPtrLd : Word) + 8 = AfterPreRlpLenLa from by
    simp only [AfterPreRlpPtrLd, AfterPreRlpLenLa]; bv_omega] at h
  exact h

theorem teerLdPreRlpLen (preLenW a1Old : Word) :
    cpsTripleWithin 1 AfterPreRlpLenLa AfterPreRlpLenLd teerLinkedField0
      ((.x5 ↦ᵣ PreRlpLenAddr) ** (.x11 ↦ᵣ a1Old) ** (PreRlpLenAddr ↦ₘ preLenW))
      ((.x5 ↦ᵣ PreRlpLenAddr) ** (.x11 ↦ᵣ preLenW) ** (PreRlpLenAddr ↦ₘ preLenW)) := by
  have h0 := ld_spec_gen_within .x11 .x5 PreRlpLenAddr a1Old preLenW
    (0 : BitVec 12) AfterPreRlpLenLa (by decide)
  rw [show PreRlpLenAddr + signExtend12 (0 : BitVec 12) = PreRlpLenAddr from by
    rw [se12_zero_ca]; exact BitVec.add_zero PreRlpLenAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPreRlpLenLa teerProg 333
        (.LD .x11 .x5 (0 : BitVec 12))
        (by simp only [AfterPreRlpLenLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterPreRlpLenLa + 4 = AfterPreRlpLenLd := by
    simp only [AfterPreRlpLenLa, AfterPreRlpLenLd]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerLaAuthorityCodeAt (v : Word) :
    cpsTripleWithin 2 AfterPreRlpLenLd AfterAuthorityLa2 teerLinkedField0
      (.x12 ↦ᵣ v) (.x12 ↦ᵣ AuthorityAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterPreRlpLenLd
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_authority
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1336)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterPreRlpLenLd teerProg 334
        (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_authority
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1336)))
        (by simp only [AfterPreRlpLenLd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1340)
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_authority
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1336)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1340) teerProg 335
        (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_authority
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1336)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x12 v AfterPreRlpLenLd AuthorityAddr
    (by decide) (by decide) hau had
  rw [show (AfterPreRlpLenLd : Word) + 8 = AfterAuthorityLa2 from by
    simp only [AfterPreRlpLenLd, AfterAuthorityLa2]; bv_omega] at h
  exact h

theorem teerLaWitnessStateLen (v : Word) :
    cpsTripleWithin 2 AfterAuthorityLa2 AfterWitnessLenLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ WitnessStateLenAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterAuthorityLa2
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.bv_witness_state_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1344)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthorityLa2 teerProg 336
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.bv_witness_state_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1344)))
        (by simp only [AfterAuthorityLa2]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1348)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.bv_witness_state_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1344)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1348) teerProg 337
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.bv_witness_state_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1344)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterAuthorityLa2 WitnessStateLenAddr
    (by decide) (by decide) hau had
  rw [show (AfterAuthorityLa2 : Word) + 8 = AfterWitnessLenLa from by
    simp only [AfterAuthorityLa2, AfterWitnessLenLa]; bv_omega] at h
  exact h

theorem teerLdWitnessStateLen (witLenW a4Old : Word) :
    cpsTripleWithin 1 AfterWitnessLenLa AfterWitnessLenLd teerLinkedField0
      ((.x5 ↦ᵣ WitnessStateLenAddr) ** (.x14 ↦ᵣ a4Old) **
        (WitnessStateLenAddr ↦ₘ witLenW))
      ((.x5 ↦ᵣ WitnessStateLenAddr) ** (.x14 ↦ᵣ witLenW) **
        (WitnessStateLenAddr ↦ₘ witLenW)) := by
  have h0 := ld_spec_gen_within .x14 .x5 WitnessStateLenAddr a4Old witLenW
    (0 : BitVec 12) AfterWitnessLenLa (by decide)
  rw [show WitnessStateLenAddr + signExtend12 (0 : BitVec 12) = WitnessStateLenAddr from by
    rw [se12_zero_ca]; exact BitVec.add_zero WitnessStateLenAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWitnessLenLa teerProg 338
        (.LD .x14 .x5 (0 : BitVec 12))
        (by simp only [AfterWitnessLenLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterWitnessLenLa + 4 = AfterWitnessLenLd := by
    simp only [AfterWitnessLenLa, AfterWitnessLenLd]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerLaCodesPtr (v : Word) :
    cpsTripleWithin 2 AfterWitnessLenLd AfterCodesPtrLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ CodesPtrAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterWitnessLenLd
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.svf_codes_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1356)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWitnessLenLd teerProg 339
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.svf_codes_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1356)))
        (by simp only [AfterWitnessLenLd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1360)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.svf_codes_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1356)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1360) teerProg 340
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.svf_codes_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1356)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterWitnessLenLd CodesPtrAddr
    (by decide) (by decide) hau had
  rw [show (AfterWitnessLenLd : Word) + 8 = AfterCodesPtrLa from by
    simp only [AfterWitnessLenLd, AfterCodesPtrLa]; bv_omega] at h
  exact h

theorem teerLdCodesPtr (codesPtr a5Old : Word) :
    cpsTripleWithin 1 AfterCodesPtrLa AfterCodesPtrLd teerLinkedField0
      ((.x5 ↦ᵣ CodesPtrAddr) ** (.x15 ↦ᵣ a5Old) ** (CodesPtrAddr ↦ₘ codesPtr))
      ((.x5 ↦ᵣ CodesPtrAddr) ** (.x15 ↦ᵣ codesPtr) ** (CodesPtrAddr ↦ₘ codesPtr)) := by
  have h0 := ld_spec_gen_within .x15 .x5 CodesPtrAddr a5Old codesPtr
    (0 : BitVec 12) AfterCodesPtrLa (by decide)
  rw [show CodesPtrAddr + signExtend12 (0 : BitVec 12) = CodesPtrAddr from by
    rw [se12_zero_ca]; exact BitVec.add_zero CodesPtrAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCodesPtrLa teerProg 341
        (.LD .x15 .x5 (0 : BitVec 12))
        (by simp only [AfterCodesPtrLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterCodesPtrLa + 4 = AfterCodesPtrLd := by
    simp only [AfterCodesPtrLa, AfterCodesPtrLd]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerLaCodesLen (v : Word) :
    cpsTripleWithin 2 AfterCodesPtrLd AfterCodesLenLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ CodesLenAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterCodesPtrLd
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.svf_codes_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1368)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCodesPtrLd teerProg 342
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.svf_codes_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1368)))
        (by simp only [AfterCodesPtrLd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1372)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.svf_codes_len
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1368)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1372) teerProg 343
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.svf_codes_len
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1368)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterCodesPtrLd CodesLenAddr
    (by decide) (by decide) hau had
  rw [show (AfterCodesPtrLd : Word) + 8 = AfterCodesLenLa from by
    simp only [AfterCodesPtrLd, AfterCodesLenLa]; bv_omega] at h
  exact h

theorem teerLdCodesLen (codesLenW a6Old : Word) :
    cpsTripleWithin 1 AfterCodesLenLa AtCodeAt teerLinkedField0
      ((.x5 ↦ᵣ CodesLenAddr) ** (.x16 ↦ᵣ a6Old) ** (CodesLenAddr ↦ₘ codesLenW))
      ((.x5 ↦ᵣ CodesLenAddr) ** (.x16 ↦ᵣ codesLenW) ** (CodesLenAddr ↦ₘ codesLenW)) := by
  have h0 := ld_spec_gen_within .x16 .x5 CodesLenAddr a6Old codesLenW
    (0 : BitVec 12) AfterCodesLenLa (by decide)
  rw [show CodesLenAddr + signExtend12 (0 : BitVec 12) = CodesLenAddr from by
    rw [se12_zero_ca]; exact BitVec.add_zero CodesLenAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCodesLenLa teerProg 344
        (.LD .x16 .x5 (0 : BitVec 12))
        (by simp only [AfterCodesLenLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterCodesLenLa + 4 = AtCodeAt := by
    simp only [AfterCodesLenLa, AtCodeAt]; bv_omega
  rw [hpc] at e0
  exact e0

set_option maxRecDepth 8000 in
/-- Setup ABI for code_at: AfterWitnessStateBeq → AtCodeAt. -/
theorem teerCodeAtSetup
    (prePtr preLenW witLenW codesPtr codesLenW
      t0Old a0Old a1Old a2Old a4Old a5Old a6Old : Word) :
    cpsTripleWithin 17 AfterWitnessStateBeq AtCodeAt teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        (.x12 ↦ᵣ a2Old) ** (.x14 ↦ᵣ a4Old) ** (.x15 ↦ᵣ a5Old) **
        (.x16 ↦ᵣ a6Old) **
        (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
        (WitnessStateLenAddr ↦ₘ witLenW) **
        (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW))
      ((.x5 ↦ᵣ CodesLenAddr) ** (.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ preLenW) **
        (.x12 ↦ᵣ AuthorityAddr) ** (.x14 ↦ᵣ witLenW) **
        (.x15 ↦ᵣ codesPtr) ** (.x16 ↦ᵣ codesLenW) **
        (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
        (WitnessStateLenAddr ↦ₘ witLenW) **
        (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW)) := by
  -- Chain la/ld pairs with framing (mechanical dual of bal_finals setup).
  have h0 := teerLaPreRlpPtr t0Old
  have h0F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
      (.x14 ↦ᵣ a4Old) ** (.x15 ↦ᵣ a5Old) ** (.x16 ↦ᵣ a6Old) **
      (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
      (WitnessStateLenAddr ↦ₘ witLenW) **
      (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW)) (by pcf) h0
  have h1 := teerLdPreRlpPtr prePtr a0Old
  have h1F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) ** (.x14 ↦ᵣ a4Old) **
      (.x15 ↦ᵣ a5Old) ** (.x16 ↦ᵣ a6Old) **
      (PreRlpLenAddr ↦ₘ preLenW) ** (WitnessStateLenAddr ↦ₘ witLenW) **
      (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW)) (by pcf) h1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h2 := teerLaPreRlpLen PreRlpPtrAddr
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
      (.x14 ↦ᵣ a4Old) ** (.x15 ↦ᵣ a5Old) ** (.x16 ↦ᵣ a6Old) **
      (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
      (WitnessStateLenAddr ↦ₘ witLenW) **
      (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW)) (by pcf) h2
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h2F
  have h3 := teerLdPreRlpLen preLenW a1Old
  have h3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ prePtr) ** (.x12 ↦ᵣ a2Old) ** (.x14 ↦ᵣ a4Old) **
      (.x15 ↦ᵣ a5Old) ** (.x16 ↦ᵣ a6Old) **
      (PreRlpPtrAddr ↦ₘ prePtr) ** (WitnessStateLenAddr ↦ₘ witLenW) **
      (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW)) (by pcf) h3
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 h3F
  have h4 := teerLaAuthorityCodeAt a2Old
  have h4F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ PreRlpLenAddr) ** (.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ preLenW) **
      (.x14 ↦ᵣ a4Old) ** (.x15 ↦ᵣ a5Old) ** (.x16 ↦ᵣ a6Old) **
      (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
      (WitnessStateLenAddr ↦ₘ witLenW) **
      (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW)) (by pcf) h4
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 h4F
  have h5 := teerLaWitnessStateLen PreRlpLenAddr
  have h5F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ preLenW) ** (.x12 ↦ᵣ AuthorityAddr) **
      (.x14 ↦ᵣ a4Old) ** (.x15 ↦ᵣ a5Old) ** (.x16 ↦ᵣ a6Old) **
      (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
      (WitnessStateLenAddr ↦ₘ witLenW) **
      (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW)) (by pcf) h5
  have c45 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c34 h5F
  have h6 := teerLdWitnessStateLen witLenW a4Old
  have h6F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ preLenW) ** (.x12 ↦ᵣ AuthorityAddr) **
      (.x15 ↦ᵣ a5Old) ** (.x16 ↦ᵣ a6Old) **
      (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
      (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW)) (by pcf) h6
  have c56 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c45 h6F
  have h7 := teerLaCodesPtr WitnessStateLenAddr
  have h7F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ preLenW) ** (.x12 ↦ᵣ AuthorityAddr) **
      (.x14 ↦ᵣ witLenW) ** (.x15 ↦ᵣ a5Old) ** (.x16 ↦ᵣ a6Old) **
      (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
      (WitnessStateLenAddr ↦ₘ witLenW) **
      (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW)) (by pcf) h7
  have c67 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c56 h7F
  have h8 := teerLdCodesPtr codesPtr a5Old
  have h8F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ preLenW) ** (.x12 ↦ᵣ AuthorityAddr) **
      (.x14 ↦ᵣ witLenW) ** (.x16 ↦ᵣ a6Old) **
      (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
      (WitnessStateLenAddr ↦ₘ witLenW) **
      (CodesLenAddr ↦ₘ codesLenW)) (by pcf) h8
  have c78 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c67 h8F
  have h9 := teerLaCodesLen CodesPtrAddr
  have h9F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ preLenW) ** (.x12 ↦ᵣ AuthorityAddr) **
      (.x14 ↦ᵣ witLenW) ** (.x15 ↦ᵣ codesPtr) ** (.x16 ↦ᵣ a6Old) **
      (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
      (WitnessStateLenAddr ↦ₘ witLenW) **
      (CodesPtrAddr ↦ₘ codesPtr) ** (CodesLenAddr ↦ₘ codesLenW)) (by pcf) h9
  have c89 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c78 h9F
  have h10 := teerLdCodesLen codesLenW a6Old
  have h10F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ prePtr) ** (.x11 ↦ᵣ preLenW) ** (.x12 ↦ᵣ AuthorityAddr) **
      (.x14 ↦ᵣ witLenW) ** (.x15 ↦ᵣ codesPtr) **
      (PreRlpPtrAddr ↦ₘ prePtr) ** (PreRlpLenAddr ↦ₘ preLenW) **
      (WitnessStateLenAddr ↦ₘ witLenW) **
      (CodesPtrAddr ↦ₘ codesPtr)) (by pcf) h10
  have c910 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c89 h10F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c910

set_option maxRecDepth 8000 in
/-- JAL code_at under TeerCodeAtAssumed → LinkCodeAt. -/
theorem teerCodeAtCall
    (asm : TeerCodeAtAssumed teerLinkedField0)
    (hentry : asm.entry = CodeAtEntry)
    (prePtr preLenW witPtr witLenW codesPtr codesLenW old1 : Word) :
    cpsTripleWithin (1 + asm.nSteps) AtCodeAt LinkCodeAt teerLinkedField0
      ((.x1 ↦ᵣ old1) **
        teerCodeAtCalleeP prePtr preLenW witPtr witLenW codesPtr codesLenW)
      ((.x1 ↦ᵣ LinkCodeAt) ** teerCodeAtCalleeQ) := by
  have hret : (LinkCodeAt &&& ~~~(1 : Word)) = LinkCodeAt := by
    simp only [LinkCodeAt, E]; decide
  have hcallee0 := asm.success_flat LinkCodeAt prePtr preLenW witPtr witLenW
    codesPtr codesLenW hret
  have hcallee0' : cpsTripleWithin asm.nSteps asm.entry LinkCodeAt teerLinkedField0
      ((.x1 ↦ᵣ LinkCodeAt) **
        teerCodeAtCalleeP prePtr preLenW witPtr witLenW codesPtr codesLenW)
      ((.x1 ↦ᵣ LinkCodeAt) ** teerCodeAtCalleeQ) := by
    unfold teerCodeAtCalleeP teerCodeAtCalleeQ
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcallee : cpsTripleWithin asm.nSteps CodeAtEntry LinkCodeAt teerLinkedField0
      ((.x1 ↦ᵣ LinkCodeAt) **
        teerCodeAtCalleeP prePtr preLenW witPtr witLenW codesPtr codesLenW)
      ((.x1 ↦ᵣ LinkCodeAt) ** teerCodeAtCalleeQ) := by
    rw [← hentry]; exact hcallee0'
  have hcall := callWithin_spec AtCodeAt CodeAtEntry old1 codeAtJalOff
    asm.nSteps codeAtJalOff_resolves
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtCodeAt teerProg 345
        (.JAL .x1 codeAtJalOff) (by simp only [AtCodeAt]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerCodeAtCalleeP_pcFree prePtr preLenW witPtr witLenW codesPtr codesLenW)
    hcallee
  rw [show (AtCodeAt + 4 : Word) = LinkCodeAt from by
    simp only [AtCodeAt, LinkCodeAt]; bv_omega] at hcall
  exact hcall

/-- BNE a0,x0 ok after code_at (status 0) → AfterCodeAtBne. -/
theorem teerCodeAtBneOk :
    cpsTripleWithin 1 LinkCodeAt AfterCodeAtBne teerLinkedField0
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 teerCodeAtBneOff
    (0 : Word) (0 : Word) LinkCodeAt
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkCodeAt teerProg 346
        (.BNE .x10 .x0 teerCodeAtBneOff)
        (by simp only [LinkCodeAt]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkCodeAt + 4 = AfterCodeAtBne := by
    simp only [LinkCodeAt, AfterCodeAtBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

set_option maxRecDepth 8000 in
/-- Load witness ptr + BEQ ntaken (≠0): AfterSvfTxCountBne → AfterWitnessStateBeq. -/
theorem teerWitnessStateNez (witPtr t0Old t3Old : Word) (hne : witPtr ≠ (0 : Word)) :
    cpsTripleWithin 4 AfterSvfTxCountBne AfterWitnessStateBeq teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x13 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (WitnessStatePtrAddr ↦ₘ witPtr))
      ((.x5 ↦ᵣ WitnessStatePtrAddr) ** (.x13 ↦ᵣ witPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        (WitnessStatePtrAddr ↦ₘ witPtr)) := by
  have hla := teerLaWitnessStatePtr t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (WitnessStatePtrAddr ↦ₘ witPtr))
    (by pcf) hla
  have hld := teerLdWitnessStatePtr witPtr t3Old
  have hldF := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hbne := teerWitnessBeqNtaken witPtr hne
  have hbneF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ WitnessStatePtrAddr) ** (WitnessStatePtrAddr ↦ₘ witPtr)) (by pcf) hbne
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hbneF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

#print axioms teerLaWitnessStatePtr
#print axioms teerLdWitnessStatePtr
#print axioms teerWitnessBeqNtaken
#print axioms teerWitnessStateNez
#print axioms teerCodeAtSetup
#print axioms teerCodeAtCall
#print axioms teerCodeAtBneOk

end EvmAsm.Codegen.TxEip7702TeerSpec
