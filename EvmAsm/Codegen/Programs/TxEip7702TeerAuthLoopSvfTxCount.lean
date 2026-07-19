/-
  Teer auth-loop svf_tx_count check:
  AtSvfTxCount (E+1276) → AfterSvfTxCountBne (E+1296) when count = 1
  (fallthrough to code_at setup), or taken skip → AtSvfTxCountSkip (E+1848).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopAcctAbsent
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

abbrev AfterSvfTxCountLa : Word := E + 1284
abbrev AfterSvfTxCountLd : Word := E + 1288
abbrev AfterSvfTxCountLi : Word := E + 1292
abbrev AfterSvfTxCountBne : Word := E + 1296
/-- BNE taken: tx_count ≠ 1 → skip code_at path. -/
abbrev AtSvfTxCountSkip : Word := E + 1848

def SvfTxCountAddr : Word := BitVec.ofNat 64 GuestAddrs.svf_tx_count

abbrev teerSvfTxCountBneOff : BitVec 13 := (556 : BitVec 13)

theorem teerSvfTxCountBneOff_taken :
    AfterSvfTxCountLi + signExtend13 teerSvfTxCountBneOff = AtSvfTxCountSkip := by
  simp only [AfterSvfTxCountLi, AtSvfTxCountSkip, teerSvfTxCountBneOff, E]; decide

private theorem se12_zero_svf : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- `la x5, svf_tx_count` AtSvfTxCount → AfterSvfTxCountLa. -/
theorem teerLaSvfTxCount (v : Word) :
    cpsTripleWithin 2 AtSvfTxCount AfterSvfTxCountLa teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ SvfTxCountAddr) := by
  have hau : ∀ a i, CodeReq.singleton AtSvfTxCount
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.svf_tx_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1276)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtSvfTxCount teerProg 319
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.svf_tx_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1276)))
        (by simp only [AtSvfTxCount]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 1280)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.svf_tx_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 1276)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 1280) teerProg 320
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.svf_tx_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 1276)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AtSvfTxCount SvfTxCountAddr
    (by decide) (by decide) hau had
  rw [show (AtSvfTxCount : Word) + 8 = AfterSvfTxCountLa from by
    simp only [AtSvfTxCount, AfterSvfTxCountLa]; bv_omega] at h
  exact h

/-- `ld x5, 0(x5)` svf_tx_count (rd = rs1). -/
theorem teerLdSvfTxCount (countW : Word) :
    cpsTripleWithin 1 AfterSvfTxCountLa AfterSvfTxCountLd teerLinkedField0
      ((.x5 ↦ᵣ SvfTxCountAddr) ** (SvfTxCountAddr ↦ₘ countW))
      ((.x5 ↦ᵣ countW) ** (SvfTxCountAddr ↦ₘ countW)) := by
  have h0 := ld_spec_gen_same_within .x5 SvfTxCountAddr countW
    (0 : BitVec 12) AfterSvfTxCountLa (by decide)
  rw [show SvfTxCountAddr + signExtend12 (0 : BitVec 12) = SvfTxCountAddr from by
    rw [se12_zero_svf]; exact BitVec.add_zero SvfTxCountAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSvfTxCountLa teerProg 321
        (.LD .x5 .x5 (0 : BitVec 12))
        (by simp only [AfterSvfTxCountLa]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterSvfTxCountLa + 4 = AfterSvfTxCountLd := by
    simp only [AfterSvfTxCountLa, AfterSvfTxCountLd]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `li x6, 1`. -/
theorem teerLiSvfTxCountOne (v6 : Word) :
    cpsTripleWithin 1 AfterSvfTxCountLd AfterSvfTxCountLi teerLinkedField0
      (.x6 ↦ᵣ v6) (.x6 ↦ᵣ (1 : Word)) := by
  have h0 := li_spec_gen_within .x6 v6 (1 : Word) AfterSvfTxCountLd (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSvfTxCountLd teerProg 322
        (.LI .x6 (1 : Word))
        (by simp only [AfterSvfTxCountLd]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterSvfTxCountLd + 4 = AfterSvfTxCountLi := by
    simp only [AfterSvfTxCountLd, AfterSvfTxCountLi]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `bne x5, x6` not-taken: count = 1 → AfterSvfTxCountBne (code_at setup). -/
theorem teerSvfTxCountBneEq1 (countW : Word) (heq : countW = (1 : Word)) :
    cpsTripleWithin 1 AfterSvfTxCountLi AfterSvfTxCountBne teerLinkedField0
      ((.x5 ↦ᵣ countW) ** (.x6 ↦ᵣ (1 : Word)))
      ((.x5 ↦ᵣ countW) ** (.x6 ↦ᵣ (1 : Word))) := by
  have hbr := bne_spec_gen_within .x5 .x6 teerSvfTxCountBneOff countW (1 : Word)
    AfterSvfTxCountLi
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSvfTxCountLi teerProg 323
        (.BNE .x5 .x6 teerSvfTxCountBneOff)
        (by simp only [AfterSvfTxCountLi]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd heq ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterSvfTxCountLi + 4 = AfterSvfTxCountBne := by
    simp only [AfterSvfTxCountLi, AfterSvfTxCountBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

theorem teerSvfTxCountBneEq1_one :
    cpsTripleWithin 1 AfterSvfTxCountLi AfterSvfTxCountBne teerLinkedField0
      ((.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (1 : Word)))
      ((.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (1 : Word))) :=
  teerSvfTxCountBneEq1 (1 : Word) rfl

/-- `bne x5, x6` taken: count ≠ 1 → AtSvfTxCountSkip. -/
theorem teerSvfTxCountBneNe1 (countW : Word) (hne : countW ≠ (1 : Word)) :
    cpsTripleWithin 1 AfterSvfTxCountLi AtSvfTxCountSkip teerLinkedField0
      ((.x5 ↦ᵣ countW) ** (.x6 ↦ᵣ (1 : Word)))
      ((.x5 ↦ᵣ countW) ** (.x6 ↦ᵣ (1 : Word))) := by
  have hbr := bne_spec_gen_within .x5 .x6 teerSvfTxCountBneOff countW (1 : Word)
    AfterSvfTxCountLi
  rw [teerSvfTxCountBneOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterSvfTxCountLi teerProg 323
          (.BNE .x5 .x6 teerSvfTxCountBneOff)
          (by simp only [AfterSvfTxCountLi]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact hne ((sepConj_pure_right _).1 hBP).2)

/-- Load count + li 1 (no BNE): AtSvfTxCount → AfterSvfTxCountLi. -/
theorem teerSvfTxCountLoadLi (countW t0Old t1Old : Word) :
    cpsTripleWithin 4 AtSvfTxCount AfterSvfTxCountLi teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (SvfTxCountAddr ↦ₘ countW))
      ((.x5 ↦ᵣ countW) ** (.x6 ↦ᵣ (1 : Word)) ** (SvfTxCountAddr ↦ₘ countW)) := by
  have hla := teerLaSvfTxCount t0Old
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ t1Old) ** (SvfTxCountAddr ↦ₘ countW)) (by pcf) hla
  have hld := teerLdSvfTxCount countW
  have hldF := cpsTripleWithin_frameR (.x6 ↦ᵣ t1Old) (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hli := teerLiSvfTxCountOne t1Old
  have hliF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ countW) ** (SvfTxCountAddr ↦ₘ countW)) (by pcf) hli
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hliF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

set_option maxRecDepth 8000 in
/-- count = 1: load+li+BNE ntaken → AfterSvfTxCountBne (code_at setup). -/
theorem teerSvfTxCountEq1 (t0Old t1Old : Word) :
    cpsTripleWithin 5 AtSvfTxCount AfterSvfTxCountBne teerLinkedField0
      ((.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (SvfTxCountAddr ↦ₘ (1 : Word)))
      ((.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ (1 : Word)) ** (SvfTxCountAddr ↦ₘ (1 : Word))) := by
  have hload := teerSvfTxCountLoadLi (1 : Word) t0Old t1Old
  have hbne := teerSvfTxCountBneEq1_one
  have hbneF := cpsTripleWithin_frameR (SvfTxCountAddr ↦ₘ (1 : Word)) (by pcf) hbne
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hload hbneF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c

#print axioms teerLaSvfTxCount
#print axioms teerLdSvfTxCount
#print axioms teerLiSvfTxCountOne
#print axioms teerSvfTxCountBneEq1_one
#print axioms teerSvfTxCountBneNe1
#print axioms teerSvfTxCountLoadLi
#print axioms teerSvfTxCountEq1

end EvmAsm.Codegen.TxEip7702TeerSpec
