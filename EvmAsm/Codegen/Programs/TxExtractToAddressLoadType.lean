/-
  Extract body: load tea_type/tea_inner_off + form walk_init args (E+112 → E+144).

  Under value-carrying type_dispatch post (tea cells hold teer type/inner).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressTypeCall
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

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

/-- JAL walk_init PC (instr 36). -/
abbrev WalkInitJalPc : Word := E + 144

/-- `la t0, tea_type` at AfterTypeBeqz → E+120. -/
theorem extractLaTeaTypeLoad (v : Word) :
    cpsTripleWithin 2 AfterTypeBeqz (E + 120) extractLinkedCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ TeaTypeAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterTypeBeqz
      (.AUIPC .x5 (laHi GuestAddrs.tea_type
        (GuestAddrs.tx_extract_to_address + 112)))
        a = some i → extractLinkedCode a = some i := fun a i hi => extract_mono a i
    (CodeReq.ofProg_mem_at E AfterTypeBeqz extractProg 28
      (.AUIPC .x5 (laHi GuestAddrs.tea_type
        (GuestAddrs.tx_extract_to_address + 112)))
      (by simp only [AfterTypeBeqz]; bv_omega)
      (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 116)
      (.ADDI .x5 .x5 (laLo GuestAddrs.tea_type
        (GuestAddrs.tx_extract_to_address + 112)))
        a = some i → extractLinkedCode a = some i := fun a i hi => extract_mono a i
    (CodeReq.ofProg_mem_at E (E + 116) extractProg 29
      (.ADDI .x5 .x5 (laLo GuestAddrs.tea_type
        (GuestAddrs.tx_extract_to_address + 112)))
      (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterTypeBeqz TeaTypeAddr
    (by decide) (by decide) hau had
  rw [show (AfterTypeBeqz + 8 : Word) = E + 120 from by
    simp only [AfterTypeBeqz]; bv_omega] at h
  exact h

/-- `ld s4, 0(t0)` at E+120 → E+124. -/
theorem extractLdType (typeW v20 : Word) :
    cpsTripleWithin 1 (E + 120) (E + 124) extractLinkedCode
      ((.x5 ↦ᵣ TeaTypeAddr) ** (.x20 ↦ᵣ v20) ** (TeaTypeAddr ↦ₘ typeW))
      ((.x5 ↦ᵣ TeaTypeAddr) ** (.x20 ↦ᵣ typeW) ** (TeaTypeAddr ↦ₘ typeW)) := by
  have h0 := ld_spec_gen_within .x20 .x5 TeaTypeAddr v20 typeW (0 : BitVec 12)
    (E + 120) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 120) extractProg 30
        (.LD .x20 .x5 (0 : BitVec 12)) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h0
  simpa only [signExtend12] using e0

/-- `la t0, tea_inner_off` at E+124 → E+132. -/
theorem extractLaTeaInnerLoad (v : Word) :
    cpsTripleWithin 2 (E + 124) (E + 132) extractLinkedCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ TeaInnerAddr) := by
  have hau : ∀ a i, CodeReq.singleton (E + 124)
      (.AUIPC .x5 (laHi GuestAddrs.tea_inner_off
        (GuestAddrs.tx_extract_to_address + 124)))
        a = some i → extractLinkedCode a = some i := fun a i hi => extract_mono a i
    (CodeReq.ofProg_mem_at E (E + 124) extractProg 31
      (.AUIPC .x5 (laHi GuestAddrs.tea_inner_off
        (GuestAddrs.tx_extract_to_address + 124)))
      (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 128)
      (.ADDI .x5 .x5 (laLo GuestAddrs.tea_inner_off
        (GuestAddrs.tx_extract_to_address + 124)))
        a = some i → extractLinkedCode a = some i := fun a i hi => extract_mono a i
    (CodeReq.ofProg_mem_at E (E + 128) extractProg 32
      (.ADDI .x5 .x5 (laLo GuestAddrs.tea_inner_off
        (GuestAddrs.tx_extract_to_address + 124)))
      (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (E + 124) TeaInnerAddr
    (by decide) (by decide) hau had
  rw [show ((E + 124 : Word) + 8) = E + 132 from by bv_omega] at h
  exact h

/-- `ld t5, 0(t0)` at E+132 → E+136. -/
theorem extractLdInner (innerW v30 : Word) :
    cpsTripleWithin 1 (E + 132) (E + 136) extractLinkedCode
      ((.x5 ↦ᵣ TeaInnerAddr) ** (.x30 ↦ᵣ v30) ** (TeaInnerAddr ↦ₘ innerW))
      ((.x5 ↦ᵣ TeaInnerAddr) ** (.x30 ↦ᵣ innerW) ** (TeaInnerAddr ↦ₘ innerW)) := by
  have h0 := ld_spec_gen_within .x30 .x5 TeaInnerAddr v30 innerW (0 : BitVec 12)
    (E + 132) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 132) extractProg 33
        (.LD .x30 .x5 (0 : BitVec 12)) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h0
  simpa only [signExtend12] using e0

/-- `add a0, s0, t5` at E+136 → E+140. -/
theorem extractAddInner (txBase innerW v10 : Word) :
    cpsTripleWithin 1 (E + 136) (E + 140) extractLinkedCode
      ((.x8 ↦ᵣ txBase) ** (.x30 ↦ᵣ innerW) ** (.x10 ↦ᵣ v10))
      ((.x8 ↦ᵣ txBase) ** (.x30 ↦ᵣ innerW) ** (.x10 ↦ᵣ (txBase + innerW))) := by
  have h0 := add_spec_gen_within .x10 .x8 .x30 txBase innerW v10 (E + 136) (by decide)
  exact cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 136) extractProg 34
        (.ADD .x10 .x8 .x30) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h0

/-- `sub a1, s1, t5` at E+140 → WalkInitJalPc. -/
theorem extractSubInner (lenW innerW v11 : Word) :
    cpsTripleWithin 1 (E + 140) WalkInitJalPc extractLinkedCode
      ((.x9 ↦ᵣ lenW) ** (.x30 ↦ᵣ innerW) ** (.x11 ↦ᵣ v11))
      ((.x9 ↦ᵣ lenW) ** (.x30 ↦ᵣ innerW) ** (.x11 ↦ᵣ (lenW - innerW))) := by
  have h0 := sub_spec_gen_within .x11 .x9 .x30 lenW innerW v11 (E + 140) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => extract_mono a i
      (CodeReq.ofProg_mem_at E (E + 140) extractProg 35
        (.SUB .x11 .x9 .x30) (by bv_omega)
        (by rw [extract_length]; decide) rfl
        (by rw [extract_length]; decide) a i hi)) h0
  simpa only [WalkInitJalPc] using e0

set_option maxRecDepth 8000 in
/-- Full load+args: AfterTypeBeqz → WalkInitJalPc under value-carrying tea cells. -/
theorem extractLoadTypeInner
    (txBase lenW typeW innerW : Word)
    (v5 v10 v11 v20 v30 : Word) :
    cpsTripleWithin 8 AfterTypeBeqz WalkInitJalPc extractLinkedCode
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x20 ↦ᵣ v20) ** (.x30 ↦ᵣ v30) **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW))
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + innerW)) ** (.x11 ↦ᵣ (lenW - innerW)) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ innerW) **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW)) := by
  -- la1: only x5 in core
  have hla1 := extractLaTeaTypeLoad v5
  have hla1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x20 ↦ᵣ v20) ** (.x30 ↦ᵣ v30) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW)) (by pcf) hla1
  -- ld1: x5, x20, tea_type in core
  have hld1 := extractLdType typeW v20
  have hld1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x30 ↦ᵣ v30) **
      (TeaInnerAddr ↦ₘ innerW)) (by pcf) hld1
  -- la2: only x5 in core (was TeaTypeAddr)
  have hla2 := extractLaTeaInnerLoad TeaTypeAddr
  have hla2F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ v30) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW)) (by pcf) hla2
  -- ld2: x5, x30, tea_inner in core
  have hld2 := extractLdInner innerW v30
  have hld2F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x20 ↦ᵣ typeW) ** (TeaTypeAddr ↦ₘ typeW)) (by pcf) hld2
  -- add: x8, x30, x10 in core
  have hadd := extractAddInner txBase innerW v10
  have haddF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ lenW) ** (.x5 ↦ᵣ TeaInnerAddr) ** (.x11 ↦ᵣ v11) **
      (.x20 ↦ᵣ typeW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW)) (by pcf) hadd
  -- sub: x9, x30, x11 in core
  have hsub := extractSubInner lenW innerW v11
  have hsubF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ txBase) ** (.x5 ↦ᵣ TeaInnerAddr) **
      (.x10 ↦ᵣ (txBase + innerW)) **
      (.x20 ↦ᵣ typeW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW)) (by pcf) hsub
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla1F hld1F
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hla2F
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hld2F
  have c34 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c23 haddF
  have c45 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c34 hsubF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c45

/-- Under teer success: load with teer type/inner. -/
theorem extractLoadTypeInner_teer
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (v5 v10 v11 v20 v30 : Word)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word)) :
    cpsTripleWithin 8 AfterTypeBeqz WalkInitJalPc extractLinkedCode
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x20 ↦ᵣ v20) ** (.x30 ↦ᵣ v30) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2))
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + (teerTxTypeDispatch txBytes).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch txBytes).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2)) := by
  have _ := hsuccess
  exact extractLoadTypeInner txBase lenW
    (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2
    v5 v10 v11 v20 v30

#print axioms extractLaTeaTypeLoad
#print axioms extractLdType
#print axioms extractLoadTypeInner
#print axioms extractLoadTypeInner_teer

end EvmAsm.Codegen.TxExtractToAddressSpec
