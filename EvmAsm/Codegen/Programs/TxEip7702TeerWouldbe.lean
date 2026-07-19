/-
  Teer wouldbe store + rolled BEQ → EpiRestore:
  AtLoopExit (E+2856) → EpiRestore (E+2920) when rolled_back = 0.
  MV a0,s10; la/ld regular_refund; la/sd wouldbe_state/regular;
  la/ld rolled_back; BEQ taken skips LI zeros into frame restore.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerEpilogue
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopOrZero
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopField0
import EvmAsm.Codegen.Programs.TxEip7702TeerScratchZero
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

set_option maxRecDepth 8000

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

abbrev AfterWouldbeMv : Word := E + 2860
abbrev AfterLaRegularWb : Word := E + 2868
abbrev AfterLdRegularWb : Word := E + 2872
abbrev AfterLaWouldbeState : Word := E + 2880
abbrev AfterSdWouldbeState : Word := E + 2884
abbrev AfterLaWouldbeRegular : Word := E + 2892
abbrev AfterSdWouldbeRegular : Word := E + 2896
abbrev AfterLaRolledWb : Word := E + 2904
abbrev AfterLdRolledWb : Word := E + 2908
abbrev AfterWouldbeBeqNtaken : Word := E + 2912

def WouldbeStateAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_wouldbe_state
def WouldbeRegularAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_wouldbe_regular

abbrev teerWouldbeBeqOff : BitVec 13 := (12 : BitVec 13)

private theorem se12_zero_wb : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

theorem teerWouldbeBeqOff_taken :
    AfterLdRolledWb + signExtend13 teerWouldbeBeqOff = EpiRestore := by
  simp only [AfterLdRolledWb, EpiRestore, teerWouldbeBeqOff, E]; decide

/-- `mv a0, s10` at AtLoopExit. -/
theorem teerWouldbeMvA0 (s10Val a0Old : Word) :
    cpsTripleWithin 1 AtLoopExit AfterWouldbeMv teerLinkedField0
      ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ a0Old))
      ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ s10Val)) := by
  have h0 := mv_spec_gen_within .x10 .x26 s10Val a0Old AtLoopExit (by decide)
  have h1 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AtLoopExit teerProg 714
        (.MV .x10 .x26)
        (by simp only [AtLoopExit]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AtLoopExit + 4 = AfterWouldbeMv := by
    simp only [AtLoopExit, AfterWouldbeMv]; bv_omega
  rw [hpc] at h1
  exact h1

/-- `la x5, teer_regular_refund` at E+2860. -/
theorem teerLaRegularWb (v : Word) :
    cpsTripleWithin 2 AfterWouldbeMv AfterLaRegularWb teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ RegularRefundAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterWouldbeMv
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_regular_refund
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2860)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWouldbeMv teerProg 715
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_regular_refund
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2860)))
        (by simp only [AfterWouldbeMv]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2864)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_regular_refund
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2860)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2864) teerProg 716
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_regular_refund
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2860)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterWouldbeMv RegularRefundAddr
    (by decide) (by decide) hau had
  rw [show (AfterWouldbeMv : Word) + 8 = AfterLaRegularWb from by
    simp only [AfterWouldbeMv, AfterLaRegularWb]; bv_omega] at h
  exact h

/-- `ld a1, 0(x5)` regular_refund. -/
theorem teerLdRegularWb (v5 a1Old refund : Word) (hv : v5 = RegularRefundAddr) :
    cpsTripleWithin 1 AfterLaRegularWb AfterLdRegularWb teerLinkedField0
      ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ a1Old) ** (RegularRefundAddr ↦ₘ refund))
      ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ refund) ** (RegularRefundAddr ↦ₘ refund)) := by
  subst hv
  have h0 := ld_spec_gen_within .x11 .x5 RegularRefundAddr a1Old refund
    (0 : BitVec 12) AfterLaRegularWb (by decide)
  rw [show RegularRefundAddr + signExtend12 (0 : BitVec 12) = RegularRefundAddr from by
    rw [se12_zero_wb]; exact BitVec.add_zero RegularRefundAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaRegularWb teerProg 717
        (.LD .x11 .x5 (0 : BitVec 12))
        (by simp only [AfterLaRegularWb]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLaRegularWb + 4 = AfterLdRegularWb := by
    simp only [AfterLaRegularWb, AfterLdRegularWb]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `la x5, teer_wouldbe_state` at E+2872. -/
theorem teerLaWouldbeState (v : Word) :
    cpsTripleWithin 2 AfterLdRegularWb AfterLaWouldbeState teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ WouldbeStateAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterLdRegularWb
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_wouldbe_state
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2872)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLdRegularWb teerProg 718
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_wouldbe_state
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2872)))
        (by simp only [AfterLdRegularWb]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2876)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_wouldbe_state
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2872)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2876) teerProg 719
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_wouldbe_state
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2872)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterLdRegularWb WouldbeStateAddr
    (by decide) (by decide) hau had
  rw [show (AfterLdRegularWb : Word) + 8 = AfterLaWouldbeState from by
    simp only [AfterLdRegularWb, AfterLaWouldbeState]; bv_omega] at h
  exact h

/-- `sd a0, 0(x5)` wouldbe_state := s10. -/
theorem teerSdWouldbeState (stateVal : Word) :
    cpsTripleWithin 1 AfterLaWouldbeState AfterSdWouldbeState teerLinkedField0
      ((.x5 ↦ᵣ WouldbeStateAddr) ** (.x10 ↦ᵣ stateVal) ** memOwn WouldbeStateAddr)
      ((.x5 ↦ᵣ WouldbeStateAddr) ** (.x10 ↦ᵣ stateVal) ** memOwn WouldbeStateAddr) := by
  have h0 := sd_spec_gen_own_within .x5 .x10 WouldbeStateAddr stateVal
    (0 : BitVec 12) AfterLaWouldbeState
  rw [show WouldbeStateAddr + signExtend12 (0 : BitVec 12) = WouldbeStateAddr from by
    rw [se12_zero_wb]; exact BitVec.add_zero WouldbeStateAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaWouldbeState teerProg 720
        (.SD .x5 .x10 (0 : BitVec 12))
        (by simp only [AfterLaWouldbeState]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have e1 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) e0
  have hpc : AfterLaWouldbeState + 4 = AfterSdWouldbeState := by
    simp only [AfterLaWouldbeState, AfterSdWouldbeState]; bv_omega
  rw [hpc] at e1
  exact e1

/-- `la x5, teer_wouldbe_regular` at E+2884. -/
theorem teerLaWouldbeRegular (v : Word) :
    cpsTripleWithin 2 AfterSdWouldbeState AfterLaWouldbeRegular teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ WouldbeRegularAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterSdWouldbeState
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_wouldbe_regular
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2884)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSdWouldbeState teerProg 721
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_wouldbe_regular
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2884)))
        (by simp only [AfterSdWouldbeState]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2888)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_wouldbe_regular
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2884)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2888) teerProg 722
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_wouldbe_regular
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2884)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterSdWouldbeState WouldbeRegularAddr
    (by decide) (by decide) hau had
  rw [show (AfterSdWouldbeState : Word) + 8 = AfterLaWouldbeRegular from by
    simp only [AfterSdWouldbeState, AfterLaWouldbeRegular]; bv_omega] at h
  exact h

/-- `sd a1, 0(x5)` wouldbe_regular := refund. -/
theorem teerSdWouldbeRegular (refund : Word) :
    cpsTripleWithin 1 AfterLaWouldbeRegular AfterSdWouldbeRegular teerLinkedField0
      ((.x5 ↦ᵣ WouldbeRegularAddr) ** (.x11 ↦ᵣ refund) ** memOwn WouldbeRegularAddr)
      ((.x5 ↦ᵣ WouldbeRegularAddr) ** (.x11 ↦ᵣ refund) ** memOwn WouldbeRegularAddr) := by
  have h0 := sd_spec_gen_own_within .x5 .x11 WouldbeRegularAddr refund
    (0 : BitVec 12) AfterLaWouldbeRegular
  rw [show WouldbeRegularAddr + signExtend12 (0 : BitVec 12) = WouldbeRegularAddr from by
    rw [se12_zero_wb]; exact BitVec.add_zero WouldbeRegularAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaWouldbeRegular teerProg 723
        (.SD .x5 .x11 (0 : BitVec 12))
        (by simp only [AfterLaWouldbeRegular]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have e1 := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) e0
  have hpc : AfterLaWouldbeRegular + 4 = AfterSdWouldbeRegular := by
    simp only [AfterLaWouldbeRegular, AfterSdWouldbeRegular]; bv_omega
  rw [hpc] at e1
  exact e1

/-- `la x5, teer_rolled_back` at E+2896. -/
theorem teerLaRolledWb (v : Word) :
    cpsTripleWithin 2 AfterSdWouldbeRegular AfterLaRolledWb teerLinkedField0
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ RolledBackAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterSdWouldbeRegular
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_rolled_back
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2896)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterSdWouldbeRegular teerProg 724
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_rolled_back
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2896)))
        (by simp only [AfterSdWouldbeRegular]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 2900)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_rolled_back
        (GuestAddrs.tx_eip7702_existing_authority_refund + 2896)))
        a = some i → teerLinkedField0 a = some i := fun a i hi =>
    teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 2900) teerProg 725
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_rolled_back
          (GuestAddrs.tx_eip7702_existing_authority_refund + 2896)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterSdWouldbeRegular RolledBackAddr
    (by decide) (by decide) hau had
  rw [show (AfterSdWouldbeRegular : Word) + 8 = AfterLaRolledWb from by
    simp only [AfterSdWouldbeRegular, AfterLaRolledWb]; bv_omega] at h
  exact h

/-- `ld x6, 0(x5)` rolled_back. -/
theorem teerLdRolledWb (v5 t1Old rolled : Word) (hv : v5 = RolledBackAddr) :
    cpsTripleWithin 1 AfterLaRolledWb AfterLdRolledWb teerLinkedField0
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ t1Old) ** (RolledBackAddr ↦ₘ rolled))
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ rolled) ** (RolledBackAddr ↦ₘ rolled)) := by
  subst hv
  have h0 := ld_spec_gen_within .x6 .x5 RolledBackAddr t1Old rolled
    (0 : BitVec 12) AfterLaRolledWb (by decide)
  rw [show RolledBackAddr + signExtend12 (0 : BitVec 12) = RolledBackAddr from by
    rw [se12_zero_wb]; exact BitVec.add_zero RolledBackAddr] at h0
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerField0_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterLaRolledWb teerProg 726
        (.LD .x6 .x5 (0 : BitVec 12))
        (by simp only [AfterLaRolledWb]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : AfterLaRolledWb + 4 = AfterLdRolledWb := by
    simp only [AfterLaRolledWb, AfterLdRolledWb]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `beq x6, x0` taken: rolled = 0 → EpiRestore. -/
theorem teerWouldbeBeqTaken_zero :
    cpsTripleWithin 1 AfterLdRolledWb EpiRestore teerLinkedField0
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x6 .x0 teerWouldbeBeqOff
    (0 : Word) (0 : Word) AfterLdRolledWb
  rw [teerWouldbeBeqOff_taken] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (fun a i hi => teerField0_mono_teer a i
        (CodeReq.ofProg_mem_at E AfterLdRolledWb teerProg 727
          (.BEQ .x6 .x0 teerWouldbeBeqOff)
          (by simp only [AfterLdRolledWb]; bv_omega)
          (by rw [teer_length]; decide) rfl
          (by rw [teer_length]; decide) a i hi)) hbr)
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 rfl)

/-- Wouldbe stores + rolled=0 BEQ → EpiRestore (14 steps). -/
theorem teerWouldbeToEpi_rolled0
    (s10Val a0Old a1Old t0Old t1Old refund : Word) :
    cpsTripleWithin 14 AtLoopExit EpiRestore teerLinkedField0
      ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refund) **
        memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
        (RolledBackAddr ↦ₘ (0 : Word)))
      ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ s10Val) ** (.x11 ↦ᵣ refund) **
        (.x5 ↦ᵣ RolledBackAddr) ** (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (RegularRefundAddr ↦ₘ refund) **
        memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
        (RolledBackAddr ↦ₘ (0 : Word))) := by
  have hmv := teerWouldbeMvA0 s10Val a0Old
  have hmvF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ a1Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
      (RolledBackAddr ↦ₘ (0 : Word))) (by pcf) hmv
  have hla0 := teerLaRegularWb t0Old
  have hla0F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ s10Val) ** (.x11 ↦ᵣ a1Old) **
      (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
      (RolledBackAddr ↦ₘ (0 : Word))) (by pcf) hla0
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF hla0F
  have hld0 := teerLdRegularWb RegularRefundAddr a1Old refund rfl
  have hld0F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ s10Val) **
      (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
      (RolledBackAddr ↦ₘ (0 : Word))) (by pcf) hld0
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hld0F
  have hla1 := teerLaWouldbeState RegularRefundAddr
  have hla1F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ s10Val) ** (.x11 ↦ᵣ refund) **
      (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
      (RolledBackAddr ↦ₘ (0 : Word))) (by pcf) hla1
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hla1F
  have hsd0 := teerSdWouldbeState s10Val
  have hsd0F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ s10Val) ** (.x11 ↦ᵣ refund) **
      (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn WouldbeRegularAddr **
      (RolledBackAddr ↦ₘ (0 : Word))) (by pcf) hsd0
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 hsd0F
  have hla2 := teerLaWouldbeRegular WouldbeStateAddr
  have hla2F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ s10Val) ** (.x11 ↦ᵣ refund) **
      (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
      (RolledBackAddr ↦ₘ (0 : Word))) (by pcf) hla2
  have c45 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c34 hla2F
  have hsd1 := teerSdWouldbeRegular refund
  have hsd1F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ s10Val) **
      (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn WouldbeStateAddr **
      (RolledBackAddr ↦ₘ (0 : Word))) (by pcf) hsd1
  have c56 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c45 hsd1F
  have hla3 := teerLaRolledWb WouldbeRegularAddr
  have hla3F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ s10Val) ** (.x11 ↦ᵣ refund) **
      (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
      (RolledBackAddr ↦ₘ (0 : Word))) (by pcf) hla3
  have c67 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c56 hla3F
  have hld1 := teerLdRolledWb RolledBackAddr t1Old (0 : Word) rfl
  have hld1F := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ s10Val) ** (.x11 ↦ᵣ refund) **
      (.x0 ↦ᵣ (0 : Word)) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr) (by pcf) hld1
  have c78 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c67 hld1F
  have hb := teerWouldbeBeqTaken_zero
  have hbF := cpsTripleWithin_frameR
    ((.x26 ↦ᵣ s10Val) ** (.x10 ↦ᵣ s10Val) ** (.x11 ↦ᵣ refund) **
      (.x5 ↦ᵣ RolledBackAddr) **
      (RegularRefundAddr ↦ₘ refund) **
      memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
      (RolledBackAddr ↦ₘ (0 : Word))) (by pcf) hb
  have c89 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c78 hbF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c89

#print axioms teerWouldbeMvA0
#print axioms teerWouldbeToEpi_rolled0

end EvmAsm.Codegen.TxEip7702TeerSpec
