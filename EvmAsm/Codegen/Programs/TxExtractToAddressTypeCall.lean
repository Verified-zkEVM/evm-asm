/-
  Extract body: type_dispatch setup + call + success BEQ (E+72 → E+112).

  Under extractSuccess (⇒ teer status 0). Uses typeDispatch_assumed_flat_typeCode
  + type_in_extractLinked (not intrinsic fullCode).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchTisDischarge
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch typeDispatch_assumed_flat_typeCode D)
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nTypeSteps nExtractStackDwords extractToBufOwn teaScratchOwn typeCode)

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

abbrev TeaTypeAddr : Word := BitVec.ofNat 64 GuestAddrs.tea_type
abbrev TeaInnerAddr : Word := BitVec.ofNat 64 GuestAddrs.tea_inner_off
abbrev TypeEntry : Word := BitVec.ofNat 64 GuestAddrs.tx_type_dispatch

/-- After pre-zero (instr 18). -/
abbrev AfterPreZero : Word := E + 72
/-- JAL type_dispatch PC (instr 24). -/
abbrev TypeJalPc : Word := E + 96
/-- Link after JAL (instr 25 BEQ). -/
abbrev LinkType : Word := E + 100
/-- BEQ taken (a0=0): E+100+12. -/
abbrev AfterTypeBeqz : Word := E + 112

private def typeJalOff : BitVec 21 :=
  jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_extract_to_address + 96)

/-- `mv a0,s0; mv a1,s1` at E+72. -/
theorem extractTypeAbiRestore (txBase txLenW : Word) (v10 v11 : Word) :
    cpsTripleWithin 2 AfterPreZero (E + 80) extractLinkedCode
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11))
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW)) := by
  have h0 := mv_spec_gen_within .x10 .x8 txBase v10 AfterPreZero (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E AfterPreZero extractProg 18
        (.MV .x10 .x8) (by simp only [AfterPreZero]; bv_omega)
        (by rw [extract_length]; decide) rfl (by rw [extract_length]; decide) a i hi)) h0
  have h1 := mv_spec_gen_within .x11 .x9 txLenW v11 (E + 76) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 76) extractProg 19
        (.MV .x11 .x9) (by bv_omega) (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h1
  have e0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ txLenW) ** (.x11 ↦ᵣ v11)) (by pcf) e0
  have e1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x10 ↦ᵣ txBase)) (by pcf) e1
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h01

/-- `la a2, tea_type` at E+80 → E+88. -/
theorem extractLaTeaType (v : Word) :
    cpsTripleWithin 2 (E + 80) (E + 88) extractLinkedCode
      (.x12 ↦ᵣ v) (.x12 ↦ᵣ TeaTypeAddr) := by
  have hau : ∀ a i, CodeReq.singleton (E + 80)
      (.AUIPC .x12 (laHi GuestAddrs.tea_type
        (GuestAddrs.tx_extract_to_address + 80)))
        a = some i → extractLinkedCode a = some i := fun a i hi => extract_mono a i
    (CodeReq.ofProg_mem_at E (E + 80) extractProg 20
      (.AUIPC .x12 (laHi GuestAddrs.tea_type
        (GuestAddrs.tx_extract_to_address + 80)))
      (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 84)
      (.ADDI .x12 .x12 (laLo GuestAddrs.tea_type
        (GuestAddrs.tx_extract_to_address + 80)))
        a = some i → extractLinkedCode a = some i := fun a i hi => extract_mono a i
    (CodeReq.ofProg_mem_at E (E + 84) extractProg 21
      (.ADDI .x12 .x12 (laLo GuestAddrs.tea_type
        (GuestAddrs.tx_extract_to_address + 80)))
      (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide) a i hi)
  have h := la_materialize_within .x12 v (E + 80) TeaTypeAddr
    (by decide) (by decide) hau had
  rw [show (E + 80 : Word) + 8 = E + 88 from by bv_omega] at h
  exact h

/-- `la a3, tea_inner_off` at E+88 → E+96. -/
theorem extractLaTeaInner (v : Word) :
    cpsTripleWithin 2 (E + 88) TypeJalPc extractLinkedCode
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ TeaInnerAddr) := by
  have hau : ∀ a i, CodeReq.singleton (E + 88)
      (.AUIPC .x13 (laHi GuestAddrs.tea_inner_off
        (GuestAddrs.tx_extract_to_address + 88)))
        a = some i → extractLinkedCode a = some i := fun a i hi => extract_mono a i
    (CodeReq.ofProg_mem_at E (E + 88) extractProg 22
      (.AUIPC .x13 (laHi GuestAddrs.tea_inner_off
        (GuestAddrs.tx_extract_to_address + 88)))
      (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 92)
      (.ADDI .x13 .x13 (laLo GuestAddrs.tea_inner_off
        (GuestAddrs.tx_extract_to_address + 88)))
        a = some i → extractLinkedCode a = some i := fun a i hi => extract_mono a i
    (CodeReq.ofProg_mem_at E (E + 92) extractProg 23
      (.ADDI .x13 .x13 (laLo GuestAddrs.tea_inner_off
        (GuestAddrs.tx_extract_to_address + 88)))
      (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide) a i hi)
  have h := la_materialize_within .x13 v (E + 88) TeaInnerAddr
    (by decide) (by decide) hau had
  rw [show (E + 88 : Word) + 8 = TypeJalPc from by
    simp only [TypeJalPc]; bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Setup: MV a0/a1 + two las → TypeJalPc. -/
theorem extractTypeSetup (txBase txLenW : Word) (v10 v11 v12 v13 : Word) :
    cpsTripleWithin 6 AfterPreZero TypeJalPc extractLinkedCode
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13))
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ TeaTypeAddr) ** (.x13 ↦ᵣ TeaInnerAddr)) := by
  have hmv := extractTypeAbiRestore txBase txLenW v10 v11
  have hmvF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13)) (by pcf) hmv
  have h0 := extractLaTeaType v12
  have h0F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x13 ↦ᵣ v13)) (by pcf) h0
  have h1 := extractLaTeaInner v13
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
      (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ TeaTypeAddr)) (by pcf) h1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF h0F
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

/-- Matches TypeDispatchAssumed.success_flat footprint (tea cells as type/inner). -/
def extractTypeCalleeP (txBase lenW : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
  (.x12 ↦ᵣ TeaTypeAddr) ** (.x13 ↦ᵣ TeaInnerAddr) **
  bytesRegion txBase txBytes **
  memOwn TeaTypeAddr ** memOwn TeaInnerAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

def extractTypeCalleeQ (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) **
  bytesRegion txBase txBytes **
  memOwn TeaTypeAddr ** memOwn TeaInnerAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem extractTypeCalleeP_pcFree (txBase lenW : Word) (txBytes : List (BitVec 8)) :
    (extractTypeCalleeP txBase lenW txBytes).pcFree := by
  unfold extractTypeCalleeP; pcf

theorem teaScratchOwn_eq_typeInner :
    teaScratchOwn = (memOwn TeaTypeAddr ** memOwn TeaInnerAddr) := by
  unfold teaScratchOwn TeaTypeAddr TeaInnerAddr; rfl

set_option maxRecDepth 8000 in
/-- JAL type_dispatch under success domain. -/
theorem extractTypeCall
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (old1 : Word)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin (1 + nTypeSteps) TypeJalPc LinkType extractLinkedCode
      ((.x1 ↦ᵣ old1) ** extractTypeCalleeP txBase lenW txBytes)
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleeQ txBase txBytes) := by
  have hret : (LinkType &&& ~~~(1 : Word)) = LinkType := by
    simp only [LinkType, E]; decide
  have hcallee0 := typeDispatch_assumed_flat_typeCode LinkType txBase lenW
    TeaTypeAddr TeaInnerAddr txBytes hret hlen hsuccess halign hover hvalid0
  -- Assumed footprint = x1 ** extractTypeCalleeP/Q (defeq after unfold).
  have hcalleeD : cpsTripleWithin nTypeSteps D LinkType typeCode
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleeP txBase lenW txBytes)
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleeQ txBase txBytes) := by
    simpa only [extractTypeCalleeP, extractTypeCalleeQ] using hcallee0
  have hentry : D = TypeEntry := by simp only [D, TypeEntry]
  have hcallee0' : cpsTripleWithin nTypeSteps TypeEntry LinkType typeCode
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleeP txBase lenW txBytes)
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleeQ txBase txBytes) := by
    rw [← hentry]; exact hcalleeD

  have hcallee := cpsTripleWithin_extend_code type_in_extractLinked hcallee0'
  have hcall := callWithin_spec TypeJalPc TypeEntry old1 typeJalOff nTypeSteps
    (by show TypeJalPc + signExtend21 typeJalOff = TypeEntry
        simp only [TypeJalPc, TypeEntry, typeJalOff, E]; decide)
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E TypeJalPc extractProg 24
        (.JAL .x1 typeJalOff) (by simp only [TypeJalPc]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi))
    (extractTypeCalleeP_pcFree txBase lenW txBytes)
    hcallee
  rw [show (TypeJalPc + 4 : Word) = LinkType from by
    simp only [TypeJalPc, LinkType]; bv_omega] at hcall
  exact hcall


set_option maxRecDepth 8000 in
/-- BEQ a0==0 taken → AfterTypeBeqz. -/
theorem extractTypeBeqzOk :
    cpsTripleWithin 1 LinkType AfterTypeBeqz extractLinkedCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := beq_spec_gen_within .x10 .x0 (12 : BitVec 13)
    (0 : Word) (0 : Word) LinkType
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E LinkType extractProg 25
        (.BEQ .x10 .x0 (12 : BitVec 13))
        (by simp only [LinkType]; bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) hbr
  have ht := cpsBranchWithin_takenStripPure2 hbrC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkType + signExtend13 (12 : BitVec 13) = AfterTypeBeqz := by
    simp only [LinkType, AfterTypeBeqz, E]; decide
  rw [hpc] at ht
  exact ht

set_option maxRecDepth 8000 in
/-- Setup + call + BEQ success: AfterPreZero → AfterTypeBeqz under extractSuccess. -/
theorem extractTypeSuccess
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (old1 v10 v11 v12 v13 : Word)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterPreZero AfterTypeBeqz
      extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        bytesRegion txBase txBytes **
        teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        bytesRegion txBase txBytes **
        teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  have hsetup := extractTypeSetup txBase lenW v10 v11 v12 v13
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** bytesRegion txBase txBytes **
      memOwn TeaTypeAddr ** memOwn TeaInnerAddr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)))
    (by pcf) hsetup
  have hcall := extractTypeCall txBase lenW txBytes old1 hlen hsuccess
    halign hover hvalid0
  have hcallF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW)) (by pcf) hcall
  have hb := extractTypeBeqzOk
  have hbF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkType) ** (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      bytesRegion txBase txBytes **
      memOwn TeaTypeAddr ** memOwn TeaInnerAddr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by pcf) hb
  have hsetupW : cpsTripleWithin 6 AfterPreZero TypeJalPc extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        bytesRegion txBase txBytes ** teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ old1) ** extractTypeCalleeP txBase lenW txBytes **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW)) := by
    unfold extractTypeCalleeP
    rw [teaScratchOwn_eq_typeInner]
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hsetupF
  have hcallW : cpsTripleWithin (1 + nTypeSteps) TypeJalPc LinkType extractLinkedCode
      ((.x1 ↦ᵣ old1) ** extractTypeCalleeP txBase lenW txBytes **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW))
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleeQ txBase txBytes **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsetupW hcallW
  have hbW : cpsTripleWithin 1 LinkType AfterTypeBeqz extractLinkedCode
      ((.x1 ↦ᵣ LinkType) ** extractTypeCalleeQ txBase txBytes **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW))
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        bytesRegion txBase txBytes ** teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
    unfold extractTypeCalleeQ
    rw [teaScratchOwn_eq_typeInner]
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hbF
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hbW
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12


#print axioms extractTypeSetup
#print axioms extractTypeCall
#print axioms extractTypeBeqzOk
#print axioms extractTypeSuccess

end EvmAsm.Codegen.TxExtractToAddressSpec
