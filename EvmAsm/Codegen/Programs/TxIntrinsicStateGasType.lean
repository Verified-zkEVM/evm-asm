/-
  Type-dispatch setup + call + success BNE (instr 20-27) for
  `tx_intrinsic_state_gas`, under TypeDispatchAssumed.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasExtract
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

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
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _)

abbrev LinkType : Word := T + 108
abbrev AfterTypeBne : Word := T + 112
abbrev Fail2 : Word := T + 168

abbrev typeJalOff : BitVec 21 :=
  jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_intrinsic_state_gas + 104)

/-- Restore a0/a1 from s0/s1 (instr 20-21). -/
theorem tisTypeAbiRestore (txBase txLenW : Word) (v10 v11 : Word) :
    cpsTripleWithin 2 AfterExtractBne (T + 88) fullCode
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11))
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW)) := by
  have h0 := mv_spec_gen_within .x10 .x8 txBase v10 AfterExtractBne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T AfterExtractBne tisProg 20
        (.MV .x10 .x8) (by simp only [AfterExtractBne]; bv_omega)
        (by rw [tis_length]; decide) rfl (by rw [tis_length]; decide) a i hi)) h0
  have h1 := mv_spec_gen_within .x11 .x9 txLenW v11 (T + 84) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 84) tisProg 21
        (.MV .x11 .x9) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi)) h1
  -- mv a0,s0 already pins x8; frame only x9/x11
  have e0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ txLenW) ** (.x11 ↦ᵣ v11)) (by pcf) e0
  -- mv a1,s1 already pins x9; frame x8/x10
  have e1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x10 ↦ᵣ txBase)) (by pcf) e1
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h01

/-- `la x12, tis_type` at T+88 → T+96. -/
theorem tisLaType (v : Word) :
    cpsTripleWithin 2 (T + 88) (T + 96) fullCode
      (.x12 ↦ᵣ v) (.x12 ↦ᵣ TypeAddr) := by
  have hau : ∀ a i, CodeReq.singleton (T + 88)
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.tis_type
        (GuestAddrs.tx_intrinsic_state_gas + 88)))
        a = some i → fullCode a = some i := fun a i hi => tis_mono a i
    (CodeReq.ofProg_mem_at T (T + 88) tisProg 22
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.tis_type
        (GuestAddrs.tx_intrinsic_state_gas + 88)))
      (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (T + 92)
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.tis_type
        (GuestAddrs.tx_intrinsic_state_gas + 88)))
        a = some i → fullCode a = some i := fun a i hi => tis_mono a i
    (CodeReq.ofProg_mem_at T (T + 92) tisProg 23
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.tis_type
        (GuestAddrs.tx_intrinsic_state_gas + 88)))
      (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide) a i hi)
  have h := la_materialize_within .x12 v (T + 88) TypeAddr
    (by decide) (by decide) hau had
  rw [show (T + 88 : Word) + 8 = T + 96 from by bv_omega] at h
  exact h

/-- `la x13, tis_inner_off` at T+96 → T+104. -/
theorem tisLaInnerOff (v : Word) :
    cpsTripleWithin 2 (T + 96) (T + 104) fullCode
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ InnerOffAddr) := by
  have hau : ∀ a i, CodeReq.singleton (T + 96)
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.tis_inner_off
        (GuestAddrs.tx_intrinsic_state_gas + 96)))
        a = some i → fullCode a = some i := fun a i hi => tis_mono a i
    (CodeReq.ofProg_mem_at T (T + 96) tisProg 24
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.tis_inner_off
        (GuestAddrs.tx_intrinsic_state_gas + 96)))
      (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (T + 100)
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.tis_inner_off
        (GuestAddrs.tx_intrinsic_state_gas + 96)))
        a = some i → fullCode a = some i := fun a i hi => tis_mono a i
    (CodeReq.ofProg_mem_at T (T + 100) tisProg 25
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.tis_inner_off
        (GuestAddrs.tx_intrinsic_state_gas + 96)))
      (by bv_omega) (by rw [tis_length]; decide) rfl
      (by rw [tis_length]; decide) a i hi)
  have h := la_materialize_within .x13 v (T + 96) InnerOffAddr
    (by decide) (by decide) hau had
  rw [show (T + 96 : Word) + 8 = T + 104 from by bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Type setup: MV a0/a1 + two las (instr 20-25) → T+104. -/
theorem tisTypeSetup (txBase txLenW : Word) (v10 v11 v12 v13 : Word) :
    cpsTripleWithin 6 AfterExtractBne (T + 104) fullCode
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13))
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ TypeAddr) ** (.x13 ↦ᵣ InnerOffAddr)) := by
  have hmv := tisTypeAbiRestore txBase txLenW v10 v11
  have hmvF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13)) (by pcf) hmv
  have h0 := tisLaType v12
  have h0F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x13 ↦ᵣ v13)) (by pcf) h0
  have h1 := tisLaInnerOff v13
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ TypeAddr)) (by pcf) h1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF h0F
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

def typeCalleeP (txBase lenW : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
  (.x12 ↦ᵣ TypeAddr) ** (.x13 ↦ᵣ InnerOffAddr) **
  bytesRegion txBase txBytes **
  memOwn TypeAddr ** memOwn InnerOffAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

def typeCalleeQ (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) **
  bytesRegion txBase txBytes **
  memOwn TypeAddr ** memOwn InnerOffAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem typeCalleeP_pcFree (txBase lenW : Word) (txBytes : List (BitVec 8)) :
    (typeCalleeP txBase lenW txBytes).pcFree := by
  unfold typeCalleeP; pcf

set_option maxRecDepth 8000 in
theorem tisTypeCall
    (asm : TypeDispatchAssumed fullCode)
    (hentry : asm.entry = TypeEntry)
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (old1 : Word)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length) :
    cpsTripleWithin (1 + nTypeSteps) (T + 104) LinkType fullCode
      ((.x1 ↦ᵣ old1) ** typeCalleeP txBase lenW txBytes)
      ((.x1 ↦ᵣ LinkType) ** typeCalleeQ txBase txBytes) := by
  have hret : (LinkType &&& ~~~(1 : Word)) = LinkType := by
    simp only [LinkType, T]; decide
  have hcallee0 := asm.success_flat LinkType txBase lenW
    TypeAddr InnerOffAddr txBytes hret hlen
  have hcallee0' : cpsTripleWithin nTypeSteps asm.entry LinkType fullCode
      ((.x1 ↦ᵣ LinkType) ** typeCalleeP txBase lenW txBytes)
      ((.x1 ↦ᵣ LinkType) ** typeCalleeQ txBase txBytes) := by
    unfold typeCalleeP typeCalleeQ
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcallee : cpsTripleWithin nTypeSteps TypeEntry LinkType fullCode
      ((.x1 ↦ᵣ LinkType) ** typeCalleeP txBase lenW txBytes)
      ((.x1 ↦ᵣ LinkType) ** typeCalleeQ txBase txBytes) := by
    rw [← hentry]; exact hcallee0'
  have hcall := callWithin_spec (T + 104) TypeEntry old1 typeJalOff nTypeSteps
    (by show (T + 104) + signExtend21 typeJalOff = TypeEntry; decide)
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T (T + 104) tisProg 26
        (.JAL .x1 typeJalOff) (by bv_omega) (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi))
    (typeCalleeP_pcFree txBase lenW txBytes)
    hcallee
  rw [show (T + 104 + 4 : Word) = LinkType from by
    simp only [LinkType]; bv_omega] at hcall
  exact hcall

set_option maxRecDepth 8000 in
theorem tisTypeBneOk :
    cpsTripleWithin 1 LinkType AfterTypeBne fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 (60 : BitVec 13)
    (0 : Word) (0 : Word) LinkType
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => tis_mono a i
      (CodeReq.ofProg_mem_at T LinkType tisProg 27
        (.BNE .x10 .x0 (60 : BitVec 13))
        (by simp only [LinkType]; bv_omega)
        (by rw [tis_length]; decide) rfl
        (by rw [tis_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkType + 4 = AfterTypeBne := by
    simp only [LinkType, AfterTypeBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

set_option maxRecDepth 8000 in
/-- Type path AfterExtractBne → AfterTypeBne under TypeDispatchAssumed. -/
theorem tisTypeSuccess
    (asm : TypeDispatchAssumed fullCode)
    (hentry : asm.entry = TypeEntry)
    (txBase lenW outPtr : Word) (txBytes : List (BitVec 8))
    (old1 v10 v11 v12 v13 : Word)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length) :
    cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterExtractBne AfterTypeBne fullCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x18 ↦ᵣ outPtr) **
        bytesRegion txBase txBytes **
        memOwn TypeAddr ** memOwn InnerOffAddr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr) **
        bytesRegion txBase txBytes **
        memOwn TypeAddr ** memOwn InnerOffAddr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  have hsetup := tisTypeSetup txBase lenW v10 v11 v12 v13
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** (.x18 ↦ᵣ outPtr) **
      bytesRegion txBase txBytes **
      memOwn TypeAddr ** memOwn InnerOffAddr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hsetup
  have hcall := tisTypeCall asm hentry txBase lenW txBytes old1 hlen
  have hcallF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ outPtr)) (by pcf) hcall
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold typeCalleeP at *
    xperm_hyp hp) hsetupF hcallF
  have hbne := tisTypeBneOk
  have hbneF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkType) ** (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ outPtr) **
      bytesRegion txBase txBytes **
      memOwn TypeAddr ** memOwn InnerOffAddr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by pcf) hbne
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold typeCalleeQ at *
    xperm_hyp hp) h01 hbneF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h12

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
