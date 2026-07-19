/-
  Teer type==4 check + inner_off load + s5/s6 setup (instr 42–53).
  PC AfterTypeBne → AtWalkInit (E+216).
  Requires TypeAddr/InnerOffAddr value-carrying posts from type_dispatch.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerType
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _)

/-- PC after type==4 BNE not-taken (E+188). -/
abbrev AfterType4Bne : Word := E + 188
/-- PC at walk_init JAL (E+216). -/
abbrev AtWalkInit : Word := E + 216

abbrev teerType4BneOff : BitVec 13 := (2672 : BitVec 13)

private theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- `la x5, teer_type` at AfterTypeBne → E+176. -/
theorem teerLaTypeCheck (v : Word) :
    cpsTripleWithin 2 AfterTypeBne (E + 176) teerLinkedEarly
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ TypeAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterTypeBne
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_type
        (GuestAddrs.tx_eip7702_existing_authority_refund + 168)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterTypeBne teerProg 42
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_type
          (GuestAddrs.tx_eip7702_existing_authority_refund + 168)))
        (by simp only [AfterTypeBne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 172)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_type
        (GuestAddrs.tx_eip7702_existing_authority_refund + 168)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 172) teerProg 43
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_type
          (GuestAddrs.tx_eip7702_existing_authority_refund + 168)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterTypeBne TypeAddr
    (by decide) (by decide) hau had
  rw [show (AfterTypeBne : Word) + 8 = E + 176 from by
    simp only [AfterTypeBne]; bv_omega] at h
  exact h

/-- `ld x6, 0(x5)` teer_type (instr 44). -/
theorem teerLdType (typeVal v6 : Word) :
    cpsTripleWithin 1 (E + 176) (E + 180) teerLinkedEarly
      ((.x5 ↦ᵣ TypeAddr) ** (.x6 ↦ᵣ v6) ** (TypeAddr ↦ₘ typeVal))
      ((.x5 ↦ᵣ TypeAddr) ** (.x6 ↦ᵣ typeVal) ** (TypeAddr ↦ₘ typeVal)) := by
  have h0 := ld_spec_gen_within .x6 .x5 TypeAddr v6 typeVal
    (0 : BitVec 12) (E + 176) (by decide)
  rw [show TypeAddr + signExtend12 (0 : BitVec 12) = TypeAddr from by
    rw [se12_zero]; exact BitVec.add_zero TypeAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 176) teerProg 44
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 176 : Word) + 4 = E + 180 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `li x7, 4` (instr 45). -/
theorem teerLiFour (v7 : Word) :
    cpsTripleWithin 1 (E + 180) (E + 184) teerLinkedEarly
      (.x7 ↦ᵣ v7) (.x7 ↦ᵣ (4 : Word)) := by
  have h0 := li_spec_gen_within .x7 v7 (4 : Word) (E + 180) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 180) teerProg 45
        (.LI .x7 (4 : Word)) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 180 : Word) + 4 = E + 184 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `bne x6, x7, fail` not-taken when typeVal = 4 (instr 46). -/
theorem teerType4BneOk :
    cpsTripleWithin 1 (E + 184) AfterType4Bne teerLinkedEarly
      ((.x6 ↦ᵣ (4 : Word)) ** (.x7 ↦ᵣ (4 : Word)))
      ((.x6 ↦ᵣ (4 : Word)) ** (.x7 ↦ᵣ (4 : Word))) := by
  have hbr := bne_spec_gen_within .x6 .x7 teerType4BneOff
    (4 : Word) (4 : Word) (E + 184)
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 184) teerProg 46
        (.BNE .x6 .x7 teerType4BneOff) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : (E + 184 : Word) + 4 = AfterType4Bne := by
    simp only [AfterType4Bne]; bv_omega
  rw [hpc] at hnt
  exact hnt

set_option maxRecDepth 8000 in
/-- Type==4 check AfterTypeBne → AfterType4Bne under TypeAddr ↦ₘ 4. -/
theorem teerType4Check
    (typeVal v5 v6 v7 : Word)
    (htype4 : typeVal = (4 : Word)) :
    cpsTripleWithin 5 AfterTypeBne AfterType4Bne teerLinkedEarly
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (TypeAddr ↦ₘ typeVal))
      ((.x5 ↦ᵣ TypeAddr) ** (.x6 ↦ᵣ (4 : Word)) ** (.x7 ↦ᵣ (4 : Word)) **
        (TypeAddr ↦ₘ (4 : Word))) := by
  subst htype4
  have hla := teerLaTypeCheck v5
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (TypeAddr ↦ₘ (4 : Word))) (by pcf) hla
  have hld := teerLdType (4 : Word) v6
  have hldF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7)) (by pcf) hld
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hli := teerLiFour v7
  have hliF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ TypeAddr) ** (.x6 ↦ᵣ (4 : Word)) ** (TypeAddr ↦ₘ (4 : Word)))
    (by pcf) hli
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hliF
  have hbne := teerType4BneOk
  have hbneF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ TypeAddr) ** (TypeAddr ↦ₘ (4 : Word))) (by pcf) hbne
  have h23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h12 hbneF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h23

/-- `la x5, teer_inner_off` at AfterType4Bne → E+196. -/
theorem teerLaInnerCheck (v : Word) :
    cpsTripleWithin 2 AfterType4Bne (E + 196) teerLinkedEarly
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ InnerOffAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterType4Bne
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_inner_off
        (GuestAddrs.tx_eip7702_existing_authority_refund + 188)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterType4Bne teerProg 47
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_inner_off
          (GuestAddrs.tx_eip7702_existing_authority_refund + 188)))
        (by simp only [AfterType4Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 192)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_inner_off
        (GuestAddrs.tx_eip7702_existing_authority_refund + 188)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 192) teerProg 48
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_inner_off
          (GuestAddrs.tx_eip7702_existing_authority_refund + 188)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterType4Bne InnerOffAddr
    (by decide) (by decide) hau had
  rw [show (AfterType4Bne : Word) + 8 = E + 196 from by
    simp only [AfterType4Bne]; bv_omega] at h
  exact h

/-- `ld x6, 0(x5)` teer_inner_off (instr 49). -/
theorem teerLdInner (innerVal v6 : Word) :
    cpsTripleWithin 1 (E + 196) (E + 200) teerLinkedEarly
      ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ v6) ** (InnerOffAddr ↦ₘ innerVal))
      ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
        (InnerOffAddr ↦ₘ innerVal)) := by
  have h0 := ld_spec_gen_within .x6 .x5 InnerOffAddr v6 innerVal
    (0 : BitVec 12) (E + 196) (by decide)
  rw [show InnerOffAddr + signExtend12 (0 : BitVec 12) = InnerOffAddr from by
    rw [se12_zero]; exact BitVec.add_zero InnerOffAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 196) teerProg 49
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 196 : Word) + 4 = E + 200 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `add s5, s0, t1` (instr 50): x21 = loadPtr + inner. -/
theorem teerAddS5 (loadPtr innerVal v21 : Word) :
    cpsTripleWithin 1 (E + 200) (E + 204) teerLinkedEarly
      ((.x8 ↦ᵣ loadPtr) ** (.x6 ↦ᵣ innerVal) ** (.x21 ↦ᵣ v21))
      ((.x8 ↦ᵣ loadPtr) ** (.x6 ↦ᵣ innerVal) **
        (.x21 ↦ᵣ loadPtr + innerVal)) := by
  have h0 := add_spec_gen_within .x21 .x8 .x6 loadPtr innerVal v21
    (E + 200) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 200) teerProg 50
        (.ADD .x21 .x8 .x6) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 200 : Word) + 4 = E + 204 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `sub s6, s1, t1` (instr 51): x22 = lenW - inner. -/
theorem teerSubS6 (lenW innerVal v22 : Word) :
    cpsTripleWithin 1 (E + 204) (E + 208) teerLinkedEarly
      ((.x9 ↦ᵣ lenW) ** (.x6 ↦ᵣ innerVal) ** (.x22 ↦ᵣ v22))
      ((.x9 ↦ᵣ lenW) ** (.x6 ↦ᵣ innerVal) **
        (.x22 ↦ᵣ lenW - innerVal)) := by
  have h0 := sub_spec_gen_within .x22 .x9 .x6 lenW innerVal v22
    (E + 204) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 204) teerProg 51
        (.SUB .x22 .x9 .x6) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 204 : Word) + 4 = E + 208 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a0, s5` (instr 52). -/
theorem teerMvA0S5 (s5 v10 : Word) :
    cpsTripleWithin 1 (E + 208) (E + 212) teerLinkedEarly
      ((.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ v10))
      ((.x21 ↦ᵣ s5) ** (.x10 ↦ᵣ s5)) := by
  have h0 := mv_spec_gen_within .x10 .x21 s5 v10 (E + 208) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 208) teerProg 52
        (.MV .x10 .x21) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 208 : Word) + 4 = E + 212 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a1, s6` (instr 53). -/
theorem teerMvA1S6 (s6 v11 : Word) :
    cpsTripleWithin 1 (E + 212) AtWalkInit teerLinkedEarly
      ((.x22 ↦ᵣ s6) ** (.x11 ↦ᵣ v11))
      ((.x22 ↦ᵣ s6) ** (.x11 ↦ᵣ s6)) := by
  have h0 := mv_spec_gen_within .x11 .x22 s6 v11 (E + 212) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 212) teerProg 53
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 212 : Word) + 4 = AtWalkInit := by
    simp only [AtWalkInit]; bv_omega
  rw [hpc] at e0
  exact e0

set_option maxRecDepth 8000 in
/-- Inner load + s5/s6 + a0/a1 setup: AfterType4Bne → AtWalkInit. -/
theorem teerInnerSetup
    (loadPtr lenW innerVal v5 v6 v10 v11 v21 v22 : Word) :
    cpsTripleWithin 7 AfterType4Bne AtWalkInit teerLinkedEarly
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        (InnerOffAddr ↦ₘ innerVal))
      ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ loadPtr + innerVal) ** (.x11 ↦ᵣ lenW - innerVal) **
        (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
        (InnerOffAddr ↦ₘ innerVal)) := by
  have hla := teerLaInnerCheck v5
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      (InnerOffAddr ↦ₘ innerVal)) (by pcf) hla
  have hld := teerLdInner innerVal v6
  have hldF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22))
    (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hldF
  have hadd := teerAddS5 loadPtr innerVal v21
  have haddF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ InnerOffAddr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x22 ↦ᵣ v22) **
      (InnerOffAddr ↦ₘ innerVal)) (by pcf) hadd
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 haddF
  have hsub := teerSubS6 lenW innerVal v22
  have hsubF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ InnerOffAddr) ** (.x8 ↦ᵣ loadPtr) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x21 ↦ᵣ loadPtr + innerVal) ** (InnerOffAddr ↦ₘ innerVal)) (by pcf) hsub
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hsubF
  have hm0 := teerMvA0S5 (loadPtr + innerVal) v10
  have hm0F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
      (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x11 ↦ᵣ v11) **
      (.x22 ↦ᵣ lenW - innerVal) ** (InnerOffAddr ↦ₘ innerVal)) (by pcf) hm0
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 hm0F
  have hm1 := teerMvA1S6 (lenW - innerVal) v11
  have hm1F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) **
      (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ loadPtr + innerVal) ** (.x21 ↦ᵣ loadPtr + innerVal) **
      (InnerOffAddr ↦ₘ innerVal)) (by pcf) hm1
  have c45 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c34 hm1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c45

set_option maxRecDepth 8000 in
/-- Compose type4 check + inner setup: AfterTypeBne → AtWalkInit. -/
theorem teerType4ThenInner
    (loadPtr lenW typeVal innerVal v5 v6 v7 v10 v11 v21 v22 : Word)
    (htype4 : typeVal = (4 : Word)) :
    cpsTripleWithin (5 + 7) AfterTypeBne AtWalkInit teerLinkedEarly
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        (TypeAddr ↦ₘ typeVal) ** (InnerOffAddr ↦ₘ innerVal))
      ((.x5 ↦ᵣ InnerOffAddr) ** (.x6 ↦ᵣ innerVal) ** (.x7 ↦ᵣ (4 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ loadPtr + innerVal) ** (.x11 ↦ᵣ lenW - innerVal) **
        (.x21 ↦ᵣ loadPtr + innerVal) ** (.x22 ↦ᵣ lenW - innerVal) **
        (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal)) := by
  have h4 := teerType4Check typeVal v5 v6 v7 htype4
  have h4F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      (InnerOffAddr ↦ₘ innerVal)) (by pcf) h4
  have hin := teerInnerSetup loadPtr lenW innerVal TypeAddr (4 : Word) v10 v11 v21 v22
  have hinF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (4 : Word)) ** (TypeAddr ↦ₘ (4 : Word))) (by pcf) hin
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h4F hinF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

#print axioms teerType4Check
#print axioms teerInnerSetup
#print axioms teerType4ThenInner

end EvmAsm.Codegen.TxEip7702TeerSpec
