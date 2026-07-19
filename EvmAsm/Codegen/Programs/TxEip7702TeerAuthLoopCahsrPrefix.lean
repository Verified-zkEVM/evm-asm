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

#print axioms teerLaCahsrCodeLength
#print axioms teerLdCahsrCodeLength
#print axioms teerCahsrLenBeqTaken_zero
#print axioms teerCahsrLenEmptySkip
#print axioms teerCahsrLenEq23

end EvmAsm.Codegen.TxEip7702TeerSpec
