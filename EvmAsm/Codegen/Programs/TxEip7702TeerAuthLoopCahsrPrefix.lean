/-
  Teer auth-loop post-code_at cahsr_code_length load + empty skip / len=23:
  AfterCodeAtBne (E+1388) → AtSvfTxCountSkip (E+1848) when length=0,
  or → AfterCahsrLenEq23 (E+1412) when length=23.

  Path: la/ld cahsr_code_length; beq x6,x0 empty→skip; li x7,23; bne eq→prefix.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopCodeAt
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopChain
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.ControlFlow

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

abbrev AfterCahsrLenLa : Word := E + 1396
abbrev AfterCahsrLenLd : Word := E + 1400
abbrev AfterCahsrLenBeqNtaken : Word := E + 1404
abbrev AfterCahsrLenLi23 : Word := E + 1408
abbrev AfterCahsrLenEq23 : Word := E + 1412

def CahsrCodeLengthAddr : Word := BitVec.ofNat 64 GuestAddrs.cahsr_code_length
def CahsrCodeOffsetAddr : Word := BitVec.ofNat 64 GuestAddrs.cahsr_code_offset

abbrev teerCahsrLenBeqOff : BitVec 13 := (448 : BitVec 13)
abbrev teerCahsrLenBneOff : BitVec 13 := (436 : BitVec 13)

theorem teerCahsrLenBeqOff_taken :
    AfterCahsrLenLd + signExtend13 teerCahsrLenBeqOff = AtSvfTxCountSkip := by
  simp only [AfterCahsrLenLd, AtSvfTxCountSkip, teerCahsrLenBeqOff, E]; decide

theorem teerCahsrLenBneOff_taken :
    AfterCahsrLenLi23 + signExtend13 teerCahsrLenBneOff = AtChainMismatch := by
  simp only [AfterCahsrLenLi23, AtChainMismatch, teerCahsrLenBneOff, E]; decide

private theorem se12_zero_cp : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- `la x5, cahsr_code_length` AfterCodeAtBne → AfterCahsrLenLa. -/
theorem teerLaCahsrCodeLength (v : Word) :
    cpsTripleWithin 2 AfterCodeAtBne AfterCahsrLenLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ CahsrCodeLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterCodeAtBne
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.cahsr_code_length
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1388)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCodeAtBne teerProg 347
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.cahsr_code_length
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1388)))
        (by simp only [AfterCodeAtBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1392)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.cahsr_code_length
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1388)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1392) teerProg 348
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.cahsr_code_length
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1388)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterCodeAtBne CahsrCodeLengthAddr
    (by decide) (by decide) hau had
  rw [show (AfterCodeAtBne : Word) + 8 = AfterCahsrLenLa from by
    simp only [AfterCodeAtBne, AfterCahsrLenLa]; bv_omega] at h
  exact h

/-- `ld x6, 0(x5)` cahsr_code_length. -/
theorem teerLdCahsrCodeLength (lenW t1Old : Word) :
    cpsTripleWithin 1 AfterCahsrLenLa AfterCahsrLenLd teerLinkedField0
      ((.x5 ↦ᵣ CahsrCodeLengthAddr) ** (.x6 ↦ᵣ t1Old) **
        (CahsrCodeLengthAddr ↦ₘ lenW))
      ((.x5 ↦ᵣ CahsrCodeLengthAddr) ** (.x6 ↦ᵣ lenW) **
        (CahsrCodeLengthAddr ↦ₘ lenW)) := by
  have h0 := ld_spec_gen_within .x6 .x5 CahsrCodeLengthAddr t1Old lenW
    (0 : BitVec 12) AfterCahsrLenLa (by decide)
  rw [show CahsrCodeLengthAddr + signExtend12 (0 : BitVec 12) = CahsrCodeLengthAddr from by
    rw [se12_zero_cp]; exact BitVec.add_zero CahsrCodeLengthAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCahsrLenLa teerProg 349
        (.LD .x6 .x5 (0 : BitVec 12))
        (by simp only [AfterCahsrLenLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterCahsrLenLa + 4 = AfterCahsrLenLd := by
    simp only [AfterCahsrLenLa, AfterCahsrLenLd]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `beq x6, x0` taken: length = 0 → AtSvfTxCountSkip. -/
theorem teerCahsrLenBeqTaken (lenW : Word) (heq : lenW = (0 : Word)) :
    cpsTripleWithin 1 AfterCahsrLenLd AtSvfTxCountSkip teerLinkedField0
      ((.x6 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x0 teerCahsrLenBeqOff lenW (0 : Word)
    AfterCahsrLenLd
  rw [teerCahsrLenBeqOff_taken] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterCahsrLenLd teerProg 350
          (.BEQ .x6 .x0 teerCahsrLenBeqOff)
          (by simp only [AfterCahsrLenLd]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 heq)

theorem teerCahsrLenBeqTaken_zero :
    cpsTripleWithin 1 AfterCahsrLenLd AtSvfTxCountSkip teerLinkedField0
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
  teerCahsrLenBeqTaken (0 : Word) rfl

/-- `beq x6, x0` not-taken: length ≠ 0 → AfterCahsrLenBeqNtaken. -/
theorem teerCahsrLenBeqNtaken (lenW : Word) (hne : lenW ≠ (0 : Word)) :
    cpsTripleWithin 1 AfterCahsrLenLd AfterCahsrLenBeqNtaken teerLinkedField0
      ((.x6 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x6 .x0 teerCahsrLenBeqOff lenW (0 : Word)
    AfterCahsrLenLd
  change cpsBranchWithin _ _ _ _ _ _ AfterCahsrLenBeqNtaken _ at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterCahsrLenLd teerProg 350
          (.BEQ .x6 .x0 teerCahsrLenBeqOff)
          (by simp only [AfterCahsrLenLd]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbeq)
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hBP).2)

/-- `li x7, 23` AfterCahsrLenBeqNtaken → AfterCahsrLenLi23. -/
theorem teerLiCahsrLen23 (v7 : Word) :
    cpsTripleWithin 1 AfterCahsrLenBeqNtaken AfterCahsrLenLi23 teerLinkedField0
      (.x7 ↦ᵣ v7) (.x7 ↦ᵣ (23 : Word)) := by
  have h0 := li_spec_gen_within .x7 v7 (23 : Word) AfterCahsrLenBeqNtaken (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCahsrLenBeqNtaken teerProg 351
        (.LI .x7 (23 : Word))
        (by simp only [AfterCahsrLenBeqNtaken]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterCahsrLenBeqNtaken + 4 = AfterCahsrLenLi23 := by
    simp only [AfterCahsrLenBeqNtaken, AfterCahsrLenLi23]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `bne x6, x7` not-taken: length = 23 → AfterCahsrLenEq23. -/
theorem teerCahsrLenBneEq23 (lenW : Word) (heq : lenW = (23 : Word)) :
    cpsTripleWithin 1 AfterCahsrLenLi23 AfterCahsrLenEq23 teerLinkedField0
      ((.x6 ↦ᵣ lenW) ** (.x7 ↦ᵣ (23 : Word)))
      ((.x6 ↦ᵣ lenW) ** (.x7 ↦ᵣ (23 : Word))) := by
  have hbr := bne_spec_gen_within .x6 .x7 teerCahsrLenBneOff lenW (23 : Word)
    AfterCahsrLenLi23
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCahsrLenLi23 teerProg 352
        (.BNE .x6 .x7 teerCahsrLenBneOff)
        (by simp only [AfterCahsrLenLi23]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd heq ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterCahsrLenLi23 + 4 = AfterCahsrLenEq23 := by
    simp only [AfterCahsrLenLi23, AfterCahsrLenEq23]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `bne x6, x7` taken: length ≠ 23 → AtChainMismatch. -/
theorem teerCahsrLenBneNe23 (lenW : Word) (hne : lenW ≠ (23 : Word)) :
    cpsTripleWithin 1 AfterCahsrLenLi23 AtChainMismatch teerLinkedField0
      ((.x6 ↦ᵣ lenW) ** (.x7 ↦ᵣ (23 : Word)))
      ((.x6 ↦ᵣ lenW) ** (.x7 ↦ᵣ (23 : Word))) := by
  have hbr := bne_spec_gen_within .x6 .x7 teerCahsrLenBneOff lenW (23 : Word)
    AfterCahsrLenLi23
  rw [teerCahsrLenBneOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterCahsrLenLi23 teerProg 352
          (.BNE .x6 .x7 teerCahsrLenBneOff)
          (by simp only [AfterCahsrLenLi23]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact hne ((sepConj_pure_right _).1 hBP).2)

/-- Empty cahsr length: load + BEQ taken → AtSvfTxCountSkip (5 steps). -/
theorem teerCahsrLenEmptySkip (t0Old t1Old : Word) :
    cpsTripleWithin 4 AfterCodeAtBne AtSvfTxCountSkip teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (CahsrCodeLengthAddr ↦ₘ (0 : Word)))
      ((.x5 ↦ᵣ CahsrCodeLengthAddr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (CahsrCodeLengthAddr ↦ₘ (0 : Word))) := by
  have hla := teerLaCahsrCodeLength t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (CahsrCodeLengthAddr ↦ₘ (0 : Word)))
    (by pcf) hla
  have hld := teerLdCahsrCodeLength (0 : Word) t1Old
  have hldF := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hb := teerCahsrLenBeqTaken_zero
  have hbF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ CahsrCodeLengthAddr) ** (CahsrCodeLengthAddr ↦ₘ (0 : Word)))
    (by pcf) hb
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hbF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

/-- length = 23 fallthrough: load + BEQ ntaken + li 23 + BNE ntaken → AfterCahsrLenEq23. -/
theorem teerCahsrLenEq23 (t0Old t1Old t2Old : Word) :
    cpsTripleWithin 6 AfterCodeAtBne AfterCahsrLenEq23 teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (CahsrCodeLengthAddr ↦ₘ (23 : Word)))
      ((.x5 ↦ᵣ CahsrCodeLengthAddr) ** (.x6 ↦ᵣ (23 : Word)) ** (.x7 ↦ᵣ (23 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (CahsrCodeLengthAddr ↦ₘ (23 : Word))) := by
  have hla := teerLaCahsrCodeLength t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (CahsrCodeLengthAddr ↦ₘ (23 : Word))) (by pcf) hla
  have hld := teerLdCahsrCodeLength (23 : Word) t1Old
  have hldF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ t2Old) ** (.x0 ↦ᵣ (0 : Word))) (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hbne0 := teerCahsrLenBeqNtaken (23 : Word) (by decide)
  have hbne0F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ CahsrCodeLengthAddr) ** (.x7 ↦ᵣ t2Old) **
      (CahsrCodeLengthAddr ↦ₘ (23 : Word))) (by pcf) hbne0
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hbne0F
  have hli := teerLiCahsrLen23 t2Old
  have hliF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ CahsrCodeLengthAddr) ** (.x6 ↦ᵣ (23 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (CahsrCodeLengthAddr ↦ₘ (23 : Word))) (by pcf) hli
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hliF
  have hbne1 := teerCahsrLenBneEq23 (23 : Word) rfl
  have hbne1F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ CahsrCodeLengthAddr) ** (.x0 ↦ᵣ (0 : Word)) **
      (CahsrCodeLengthAddr ↦ₘ (23 : Word))) (by pcf) hbne1
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 hbne1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c34

abbrev AfterCodesPtrLa2 : Word := E + 1420
abbrev AfterCodesPtrLd2 : Word := E + 1424
abbrev AfterCodeOffLa : Word := E + 1432
abbrev AfterCodeOffLd : Word := E + 1436
abbrev AfterCodePtrAdd : Word := E + 1440
abbrev AfterLbu0 : Word := E + 1444
abbrev AfterLiEf : Word := E + 1448
abbrev AfterBneEf : Word := E + 1452
abbrev AfterLbu1 : Word := E + 1456
abbrev AfterLi01 : Word := E + 1460
abbrev AfterBne01 : Word := E + 1464
abbrev AfterLbu2 : Word := E + 1468
abbrev AfterBne00 : Word := E + 1472
abbrev AtCahsrPrefixJal : Word := E + 1472

def CodesPtrAddr2 : Word := BitVec.ofNat 64 GuestAddrs.svf_codes_ptr

abbrev teerCahsrEfBneOff : BitVec 13 := (396 : BitVec 13)
abbrev teerCahsr01BneOff : BitVec 13 := (384 : BitVec 13)
abbrev teerCahsr00BneOff : BitVec 13 := (376 : BitVec 13)
abbrev teerCahsrPrefixJalOff : BitVec 21 := (376 : BitVec 21)

theorem teerCahsrEfBneOff_taken :
    AfterLiEf + signExtend13 teerCahsrEfBneOff = AtChainMismatch := by
  simp only [AfterLiEf, AtChainMismatch, teerCahsrEfBneOff, E]; decide

theorem teerCahsr01BneOff_taken :
    AfterLi01 + signExtend13 teerCahsr01BneOff = AtChainMismatch := by
  simp only [AfterLi01, AtChainMismatch, teerCahsr01BneOff, E]; decide

theorem teerCahsr00BneOff_taken :
    AfterLbu2 + signExtend13 teerCahsr00BneOff = AtChainMismatch := by
  simp only [AfterLbu2, AtChainMismatch, teerCahsr00BneOff, E]; decide

theorem teerCahsrPrefixJalOff_target :
    AtCahsrPrefixJal + signExtend21 teerCahsrPrefixJalOff = AtSvfTxCountSkip := by
  simp only [AtCahsrPrefixJal, AtSvfTxCountSkip, teerCahsrPrefixJalOff, E]; decide

private theorem se12_one_cp : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_two_cp : signExtend12 (2 : BitVec 12) = (2 : Word) := by decide

/-- `la x5, svf_codes_ptr` AfterCahsrLenEq23 → AfterCodesPtrLa2. -/
theorem teerLaCodesPtr2 (v : Word) :
    cpsTripleWithin 2 AfterCahsrLenEq23 AfterCodesPtrLa2 teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ CodesPtrAddr2) := by
  have hau : ∀ a i, CodeReq.singleton AfterCahsrLenEq23
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.svf_codes_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1412)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCahsrLenEq23 teerProg 353
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.svf_codes_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1412)))
        (by simp only [AfterCahsrLenEq23]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1416)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.svf_codes_ptr
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1412)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1416) teerProg 354
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.svf_codes_ptr
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1412)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterCahsrLenEq23 CodesPtrAddr2
    (by decide) (by decide) hau had
  rw [show (AfterCahsrLenEq23 : Word) + 8 = AfterCodesPtrLa2 from by
    simp only [AfterCahsrLenEq23, AfterCodesPtrLa2]; bv_omega] at h
  exact h

/-- `ld x5, 0(x5)` codes_ptr (rd = rs1). -/
theorem teerLdCodesPtr2 (codesPtr : Word) :
    cpsTripleWithin 1 AfterCodesPtrLa2 AfterCodesPtrLd2 teerLinkedField0
      ((.x5 ↦ᵣ CodesPtrAddr2) ** (CodesPtrAddr2 ↦ₘ codesPtr))
      ((.x5 ↦ᵣ codesPtr) ** (CodesPtrAddr2 ↦ₘ codesPtr)) := by
  have h0 := ld_spec_gen_same_within .x5 CodesPtrAddr2 codesPtr
    (0 : BitVec 12) AfterCodesPtrLa2 (by decide)
  rw [show CodesPtrAddr2 + signExtend12 (0 : BitVec 12) = CodesPtrAddr2 from by
    rw [se12_zero_cp]; exact BitVec.add_zero CodesPtrAddr2] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCodesPtrLa2 teerProg 355
        (.LD .x5 .x5 (0 : BitVec 12))
        (by simp only [AfterCodesPtrLa2]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterCodesPtrLa2 + 4 = AfterCodesPtrLd2 := by
    simp only [AfterCodesPtrLa2, AfterCodesPtrLd2]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `la x6, cahsr_code_offset` AfterCodesPtrLd2 → AfterCodeOffLa. -/
theorem teerLaCahsrCodeOffset (v : Word) :
    cpsTripleWithin 2 AfterCodesPtrLd2 AfterCodeOffLa teerLinkedField0
      (.x6 ↦ᵣ v) (.x6 ↦ᵣ CahsrCodeOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterCodesPtrLd2
      (.AUIPC .x6 (Codegen.laHi GuestAddrs.cahsr_code_offset
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1424)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCodesPtrLd2 teerProg 356
        (.AUIPC .x6 (Codegen.laHi GuestAddrs.cahsr_code_offset
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1424)))
        (by simp only [AfterCodesPtrLd2]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1428)
      (.ADDI .x6 .x6 (Codegen.laLo GuestAddrs.cahsr_code_offset
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1424)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1428) teerProg 357
        (.ADDI .x6 .x6 (Codegen.laLo GuestAddrs.cahsr_code_offset
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1424)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x6 v AfterCodesPtrLd2 CahsrCodeOffsetAddr
    (by decide) (by decide) hau had
  rw [show (AfterCodesPtrLd2 : Word) + 8 = AfterCodeOffLa from by
    simp only [AfterCodesPtrLd2, AfterCodeOffLa]; bv_omega] at h
  exact h

/-- `ld x6, 0(x6)` code offset (rd = rs1). -/
theorem teerLdCahsrCodeOffset (offW : Word) :
    cpsTripleWithin 1 AfterCodeOffLa AfterCodeOffLd teerLinkedField0
      ((.x6 ↦ᵣ CahsrCodeOffsetAddr) ** (CahsrCodeOffsetAddr ↦ₘ offW))
      ((.x6 ↦ᵣ offW) ** (CahsrCodeOffsetAddr ↦ₘ offW)) := by
  have h0 := ld_spec_gen_same_within .x6 CahsrCodeOffsetAddr offW
    (0 : BitVec 12) AfterCodeOffLa (by decide)
  rw [show CahsrCodeOffsetAddr + signExtend12 (0 : BitVec 12) = CahsrCodeOffsetAddr from by
    rw [se12_zero_cp]; exact BitVec.add_zero CahsrCodeOffsetAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCodeOffLa teerProg 358
        (.LD .x6 .x6 (0 : BitVec 12))
        (by simp only [AfterCodeOffLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterCodeOffLa + 4 = AfterCodeOffLd := by
    simp only [AfterCodeOffLa, AfterCodeOffLd]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `add x5, x5, x6` → code byte pointer. -/
theorem teerAddCodePtr (codesPtr offW : Word) :
    cpsTripleWithin 1 AfterCodeOffLd AfterCodePtrAdd teerLinkedField0
      ((.x5 ↦ᵣ codesPtr) ** (.x6 ↦ᵣ offW))
      ((.x5 ↦ᵣ (codesPtr + offW)) ** (.x6 ↦ᵣ offW)) := by
  have h0 := add_spec_gen_rd_eq_rs1_within .x5 .x6 codesPtr offW
    AfterCodeOffLd (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCodeOffLd teerProg 359
        (.ADD .x5 .x5 .x6)
        (by simp only [AfterCodeOffLd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterCodeOffLd + 4 = AfterCodePtrAdd := by
    simp only [AfterCodeOffLd, AfterCodePtrAdd]; bv_omega
  rw [hpc] at e0
  exact e0

/-- Load codes_ptr + offset + ADD → AfterCodePtrAdd (7 steps). -/
theorem teerCodePtrSetup (codesPtr offW t0Old t1Old : Word) :
    cpsTripleWithin 7 AfterCahsrLenEq23 AfterCodePtrAdd teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (CodesPtrAddr2 ↦ₘ codesPtr) ** (CahsrCodeOffsetAddr ↦ₘ offW))
      ((.x5 ↦ᵣ (codesPtr + offW)) ** (.x6 ↦ᵣ offW) **
        (CodesPtrAddr2 ↦ₘ codesPtr) ** (CahsrCodeOffsetAddr ↦ₘ offW)) := by
  have hla1 := teerLaCodesPtr2 t0Old
  have hla1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** (CodesPtrAddr2 ↦ₘ codesPtr) **
      (CahsrCodeOffsetAddr ↦ₘ offW)) (by pcf) hla1
  have hld1 := teerLdCodesPtr2 codesPtr
  have hld1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** (CahsrCodeOffsetAddr ↦ₘ offW)) (by pcf) hld1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla1F hld1F
  have hla2 := teerLaCahsrCodeOffset t1Old
  have hla2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ codesPtr) ** (CodesPtrAddr2 ↦ₘ codesPtr) **
      (CahsrCodeOffsetAddr ↦ₘ offW)) (by pcf) hla2
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hla2F
  have hld2 := teerLdCahsrCodeOffset offW
  have hld2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ codesPtr) ** (CodesPtrAddr2 ↦ₘ codesPtr)) (by pcf) hld2
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hld2F
  have hadd := teerAddCodePtr codesPtr offW
  have haddF := cpsTripleWithin_frameR
    ((CodesPtrAddr2 ↦ₘ codesPtr) ** (CahsrCodeOffsetAddr ↦ₘ offW)) (by pcf) hadd
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 haddF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c34

/-- `lbu x6, 0(x5)` first code byte. -/
theorem teerLbuCode0 (codePtr t1Old dwordAddr wordVal : Word)
    (halign : alignToDword codePtr = dwordAddr)
    (hvalid : isValidByteAccess codePtr = true) :
    cpsTripleWithin 1 AfterCodePtrAdd AfterLbu0 teerLinkedField0
      ((.x5 ↦ᵣ codePtr) ** (.x6 ↦ᵣ t1Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ codePtr) **
        (.x6 ↦ᵣ (extractByte wordVal (byteOffset codePtr)).zeroExtend 64) **
        (dwordAddr ↦ₘ wordVal)) := by
  have hadd : codePtr + signExtend12 (0 : BitVec 12) = codePtr := by
    rw [se12_zero_cp]; exact BitVec.add_zero codePtr
  have h0 := lbu_spec_gen_within .x6 .x5 codePtr t1Old (0 : BitVec 12)
    AfterCodePtrAdd dwordAddr wordVal (by decide)
    (by rw [hadd]; exact halign)
    (by rw [hadd]; exact hvalid)
  rw [hadd] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterCodePtrAdd teerProg 360
        (.LBU .x6 .x5 (0 : BitVec 12))
        (by simp only [AfterCodePtrAdd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterCodePtrAdd + 4 = AfterLbu0 := by
    simp only [AfterCodePtrAdd, AfterLbu0]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `li x7, 239` (0xef). -/
theorem teerLiCodeEf (v7 : Word) :
    cpsTripleWithin 1 AfterLbu0 AfterLiEf teerLinkedField0
      (.x7 ↦ᵣ v7) (.x7 ↦ᵣ (239 : Word)) := by
  have h0 := li_spec_gen_within .x7 v7 (239 : Word) AfterLbu0 (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLbu0 teerProg 361
        (.LI .x7 (239 : Word))
        (by simp only [AfterLbu0]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLbu0 + 4 = AfterLiEf := by
    simp only [AfterLbu0, AfterLiEf]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `bne x6, x7` not-taken: byte0 = 0xef. -/
theorem teerBneCodeEfOk (b0 : Word) (heq : b0 = (239 : Word)) :
    cpsTripleWithin 1 AfterLiEf AfterBneEf teerLinkedField0
      ((.x6 ↦ᵣ b0) ** (.x7 ↦ᵣ (239 : Word)))
      ((.x6 ↦ᵣ b0) ** (.x7 ↦ᵣ (239 : Word))) := by
  have hbr := bne_spec_gen_within .x6 .x7 teerCahsrEfBneOff b0 (239 : Word) AfterLiEf
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLiEf teerProg 362
        (.BNE .x6 .x7 teerCahsrEfBneOff)
        (by simp only [AfterLiEf]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd heq ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterLiEf + 4 = AfterBneEf := by
    simp only [AfterLiEf, AfterBneEf]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `lbu x6, 1(x5)` second code byte. -/
theorem teerLbuCode1 (codePtr t1Old dwordAddr wordVal : Word)
    (halign : alignToDword (codePtr + (1 : Word)) = dwordAddr)
    (hvalid : isValidByteAccess (codePtr + (1 : Word)) = true) :
    cpsTripleWithin 1 AfterBneEf AfterLbu1 teerLinkedField0
      ((.x5 ↦ᵣ codePtr) ** (.x6 ↦ᵣ t1Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ codePtr) **
        (.x6 ↦ᵣ (extractByte wordVal (byteOffset (codePtr + (1 : Word)))).zeroExtend 64) **
        (dwordAddr ↦ₘ wordVal)) := by
  have h0 := lbu_spec_gen_within .x6 .x5 codePtr t1Old (1 : BitVec 12)
    AfterBneEf dwordAddr wordVal (by decide)
    (by rw [se12_one_cp]; exact halign)
    (by rw [se12_one_cp]; exact hvalid)
  rw [show codePtr + signExtend12 (1 : BitVec 12) = codePtr + (1 : Word) from by
    rw [se12_one_cp]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterBneEf teerProg 363
        (.LBU .x6 .x5 (1 : BitVec 12))
        (by simp only [AfterBneEf]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterBneEf + 4 = AfterLbu1 := by
    simp only [AfterBneEf, AfterLbu1]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `li x7, 1`. -/
theorem teerLiCode01 (v7 : Word) :
    cpsTripleWithin 1 AfterLbu1 AfterLi01 teerLinkedField0
      (.x7 ↦ᵣ v7) (.x7 ↦ᵣ (1 : Word)) := by
  have h0 := li_spec_gen_within .x7 v7 (1 : Word) AfterLbu1 (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLbu1 teerProg 364
        (.LI .x7 (1 : Word))
        (by simp only [AfterLbu1]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLbu1 + 4 = AfterLi01 := by
    simp only [AfterLbu1, AfterLi01]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `bne x6, x7` not-taken: byte1 = 0x01. -/
theorem teerBneCode01Ok (b1 : Word) (heq : b1 = (1 : Word)) :
    cpsTripleWithin 1 AfterLi01 AfterBne01 teerLinkedField0
      ((.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ (1 : Word)))
      ((.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ (1 : Word))) := by
  have hbr := bne_spec_gen_within .x6 .x7 teerCahsr01BneOff b1 (1 : Word) AfterLi01
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLi01 teerProg 365
        (.BNE .x6 .x7 teerCahsr01BneOff)
        (by simp only [AfterLi01]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd heq ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterLi01 + 4 = AfterBne01 := by
    simp only [AfterLi01, AfterBne01]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `lbu x6, 2(x5)` third code byte. -/
theorem teerLbuCode2 (codePtr t1Old dwordAddr wordVal : Word)
    (halign : alignToDword (codePtr + (2 : Word)) = dwordAddr)
    (hvalid : isValidByteAccess (codePtr + (2 : Word)) = true) :
    cpsTripleWithin 1 AfterBne01 AfterLbu2 teerLinkedField0
      ((.x5 ↦ᵣ codePtr) ** (.x6 ↦ᵣ t1Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ codePtr) **
        (.x6 ↦ᵣ (extractByte wordVal (byteOffset (codePtr + (2 : Word)))).zeroExtend 64) **
        (dwordAddr ↦ₘ wordVal)) := by
  have h0 := lbu_spec_gen_within .x6 .x5 codePtr t1Old (2 : BitVec 12)
    AfterBne01 dwordAddr wordVal (by decide)
    (by rw [se12_two_cp]; exact halign)
    (by rw [se12_two_cp]; exact hvalid)
  rw [show codePtr + signExtend12 (2 : BitVec 12) = codePtr + (2 : Word) from by
    rw [se12_two_cp]] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterBne01 teerProg 366
        (.LBU .x6 .x5 (2 : BitVec 12))
        (by simp only [AfterBne01]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterBne01 + 4 = AfterLbu2 := by
    simp only [AfterBne01, AfterLbu2]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `bne x6, x0` not-taken: byte2 = 0. -/
theorem teerBneCode00Ok (b2 : Word) (heq : b2 = (0 : Word)) :
    cpsTripleWithin 1 AfterLbu2 AfterBne00 teerLinkedField0
      ((.x6 ↦ᵣ b2) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ b2) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x6 .x0 teerCahsr00BneOff b2 (0 : Word) AfterLbu2
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLbu2 teerProg 367
        (.BNE .x6 .x0 teerCahsr00BneOff)
        (by simp only [AfterLbu2]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd heq ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterLbu2 + 4 = AfterBne00 := by
    simp only [AfterLbu2, AfterBne00]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- Unconditional `jal x0` → AtSvfTxCountSkip (already-delegated 0xef0100). -/
theorem teerCahsrPrefixJalSkip :
    cpsTripleWithin 1 AtCahsrPrefixJal AtSvfTxCountSkip teerLinkedField0
      empAssertion empAssertion := by
  have h0 := jal_x0_spec_gen_within teerCahsrPrefixJalOff AtCahsrPrefixJal
  rw [teerCahsrPrefixJalOff_target] at h0
  exact cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtCahsrPrefixJal teerProg 368
        (.JAL .x0 teerCahsrPrefixJalOff)
        (by simp only [AtCahsrPrefixJal]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) h0

#print axioms teerLaCahsrCodeLength
#print axioms teerLdCahsrCodeLength
#print axioms teerCahsrLenBeqTaken_zero
#print axioms teerCahsrLenEmptySkip
#print axioms teerCahsrLenEq23
#print axioms teerCodePtrSetup
#print axioms teerLbuCode0
#print axioms teerBneCodeEfOk
#print axioms teerCahsrPrefixJalSkip

end EvmAsm.Codegen.TxEip7702TeerSpec
