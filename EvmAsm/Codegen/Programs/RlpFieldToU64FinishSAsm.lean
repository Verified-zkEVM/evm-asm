/-
  Final status dispatch and whole-routine composition for strict K34.
-/

import EvmAsm.Codegen.Programs.RlpFieldToU64SAsm

namespace EvmAsm.Codegen.RlpFieldToU64SAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

def scalarCore
    (sp0 listBase offset len v12 value status : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ (B + 84)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  ((.x10 ↦ᵣ value) ** (.x11 ↦ᵣ status)) **
  contentCarry sp0 listBase offset len v12 saved

def scalarResult
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 value status,
    ((scalarCore sp0 listBase offset len v12 value status saved bytes **
      ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
        offset len⌝) **
      ⌜ScalarOutcome bytes offset.toNat len.toNat value status⌝) h

def scalarTaken
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 value status,
    (((scalarCore sp0 listBase offset len v12 value status saved bytes **
       ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
         offset len⌝) **
      ⌜ScalarOutcome bytes offset.toNat len.toNat value status⌝) **
     ⌜status ≠ 0⌝) h

def scalarFall
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 value status,
    (((scalarCore sp0 listBase offset len v12 value status saved bytes **
       ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
         offset len⌝) **
      ⌜ScalarOutcome bytes offset.toNat len.toNat value status⌝) **
     ⌜status = 0⌝) h

theorem contentDone_to_scalarResult
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    contentDone sp0 listBase saved bytes listLen index h →
      scalarResult sp0 listBase saved bytes listLen index h := by
  intro h hp
  unfold contentDone at hp
  obtain ⟨offset, len, v12, hp⟩ := hp
  unfold contentRawPost contentCallPost at hp
  extract_pure_deep hp
  obtain ⟨hp, h_ok⟩ := hp
  let R : Assertion :=
    (.x1 ↦ᵣ (B + 84)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
    contentCarry sp0 listBase offset len v12 saved
  have hsplit : (R ** contentOutcome bytes offset.toNat len.toNat) h := by
    unfold R
    xperm_hyp hp
  obtain ⟨hRState, ho, hd, hu, hRProof, hout⟩ := hsplit
  have hs := contentOutcome_semantic bytes offset.toNat len.toNat ho hout
  obtain ⟨value, status, hs⟩ := hs
  extract_pure_deep hs
  obtain ⟨hs, h_scalar⟩ := hs
  unfold scalarResult
  refine ⟨offset, len, v12, value, status, ?_⟩
  apply (sepConj_pure_right h).2
  constructor
  · apply (sepConj_pure_right h).2
    constructor
    · have hjoined : (R **
          ((.x10 ↦ᵣ value) ** (.x11 ↦ᵣ status))) h :=
        ⟨hRState, ho, hd, hu, hRProof, hs⟩
      unfold R at hjoined
      unfold scalarCore
      xperm_hyp hjoined
    · exact h_ok
  · exact h_scalar

#print axioms contentDone_to_scalarResult

def scalarFrame
    (sp0 listBase offset len v12 value : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ (B + 84)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** bytesRegion listBase bytes ** (.x10 ↦ᵣ value) **
  contentCarry sp0 listBase offset len v12 saved

theorem pcFree_scalarFrame sp0 listBase offset len v12 value saved bytes :
    (scalarFrame sp0 listBase offset len v12 value saved bytes).pcFree := by
  unfold scalarFrame
  pcf

private theorem scalarCore_to_result
    (sp0 listBase offset len v12 value status : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h_ok : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
      index offset len)
    (h_out : ScalarOutcome bytes offset.toNat len.toNat value status) : ∀ h,
    scalarCore sp0 listBase offset len v12 value status saved bytes h →
      scalarResult sp0 listBase saved bytes listLen index h := by
  intro h hp
  unfold scalarResult
  refine ⟨offset, len, v12, value, status, ?_⟩
  apply (sepConj_pure_right h).2
  exact ⟨(sepConj_pure_right h).2 ⟨hp, h_ok⟩, h_out⟩

private theorem scalarCore_to_taken
    (sp0 listBase offset len v12 value status : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h_ok : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
      index offset len)
    (h_out : ScalarOutcome bytes offset.toNat len.toNat value status)
    (h_ne : status ≠ 0) : ∀ h,
    scalarCore sp0 listBase offset len v12 value status saved bytes h →
      scalarTaken sp0 listBase saved bytes listLen index h := by
  intro h hp
  unfold scalarTaken
  refine ⟨offset, len, v12, value, status, ?_⟩
  apply (sepConj_pure_right h).2
  exact ⟨(sepConj_pure_right h).2
    ⟨(sepConj_pure_right h).2 ⟨hp, h_ok⟩, h_out⟩, h_ne⟩

private theorem scalarCore_to_fall
    (sp0 listBase offset len v12 value status : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h_ok : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
      index offset len)
    (h_out : ScalarOutcome bytes offset.toNat len.toNat value status)
    (h_eq : status = 0) : ∀ h,
    scalarCore sp0 listBase offset len v12 value status saved bytes h →
      scalarFall sp0 listBase saved bytes listLen index h := by
  intro h hp
  unfold scalarFall
  refine ⟨offset, len, v12, value, status, ?_⟩
  apply (sepConj_pure_right h).2
  exact ⟨(sepConj_pure_right h).2
    ⟨(sepConj_pure_right h).2 ⟨hp, h_ok⟩, h_out⟩, h_eq⟩

private theorem scalarBranchCase
    (sp0 listBase offset len v12 value status : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h_ok : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
      index offset len)
    (h_out : ScalarOutcome bytes offset.toNat len.toNat value status) :
    cpsBranchWithin 1 (B + 84) code
      (scalarCore sp0 listBase offset len v12 value status saved bytes)
      (B + 100) (scalarTaken sp0 listBase saved bytes listLen index)
      (B + 88) (scalarFall sp0 listBase saved bytes listLen index) := by
  have hb0 := bne_spec_gen_within .x11 .x0 (16 : BitVec 13)
    status (0 : Word) (B + 84)
  rw [show B + 84 + signExtend13 (16 : BitVec 13) = B + 100 from by decide,
    show B + 84 + 4 = B + 88 from by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 84) rlpFieldToU64_prog 21
      (.BNE .x11 .x0 (16 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R := scalarFrame sp0 listBase offset len v12 value saved bytes
  have hbF := cpsBranchWithin_frameR R
    (pcFree_scalarFrame _ _ _ _ _ _ _ _) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hbF
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold scalarCore at hp
      unfold R scalarFrame
      xperm_hyp hp) (fun h hp => ?_) (fun h hp => ?_) hbC
  · extract_pure_deep hp
    obtain ⟨h_ne, hp⟩ := hp
    apply scalarCore_to_taken sp0 listBase offset len v12 value status saved
      bytes listLen index h_ok h_out h_ne h
    unfold R scalarFrame at hp
    unfold scalarCore
    xperm_hyp hp
  · extract_pure_deep hp
    obtain ⟨h_eq, hp⟩ := hp
    apply scalarCore_to_fall sp0 listBase offset len v12 value status saved
      bytes listLen index h_ok h_out h_eq h
    unfold R scalarFrame at hp
    unfold scalarCore
    xperm_hyp hp

#print axioms scalarBranchCase

theorem scalarBranch
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 84) code
      (scalarResult sp0 listBase saved bytes listLen index)
      (B + 100) (scalarTaken sp0 listBase saved bytes listLen index)
      (B + 88) (scalarFall sp0 listBase saved bytes listLen index) := by
  unfold scalarResult
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_exists_pre (fun value => ?_)
  refine cpsBranchWithin_exists_pre (fun status => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_out => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_ok => ?_)
  exact scalarBranchCase sp0 listBase offset len v12 value status saved bytes
    listLen index h_ok h_out

#print axioms scalarBranch

/-- Store a successfully decoded scalar, materialize wrapper status zero, and
    jump to the shared restore join (instructions 22--24). -/
theorem successMachineTail
    (outputPtr value oldOut : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (B + 88) (B + 128) code
      (((.x9 ↦ᵣ outputPtr) ** (.x10 ↦ᵣ value) **
        (outputPtr ↦ₘ oldOut)) ** ((.x0 ↦ᵣ (0 : Word)) ** F))
      ((.x9 ↦ᵣ outputPtr) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (outputPtr ↦ₘ value) ** F) := by
  have hs0 := sd_spec_gen_within .x9 .x10 outputPtr value oldOut
    (0 : BitVec 12) (B + 88)
  rw [show outputPtr + signExtend12 (0 : BitVec 12) = outputPtr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega] at hs0
  have hs := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 88) rlpFieldToU64_prog 22
      (.SD .x9 .x10 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hs0
  have hsF := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word)) ** F)
    (pcFree_sepConj pcFree_regIs hF) hs
  have hl0 := li_spec_gen_within .x10 value (0 : Word) (B + 92) (by decide)
  have hl := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 92) rlpFieldToU64_prog 23
      (.LI .x10 (0 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) hl0
  let R : Assertion :=
    (.x9 ↦ᵣ outputPtr) ** (.x0 ↦ᵣ (0 : Word)) **
    (outputPtr ↦ₘ value) ** F
  have hlF := cpsTripleWithin_frameR R (by unfold R; pcf; exact hF) hl
  have hj0 := jal_x0_spec_gen_within (32 : BitVec 21) (B + 96)
  rw [show B + 96 + signExtend21 (32 : BitVec 21) = B + 128 from by decide]
    at hj0
  have hj := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 96) rlpFieldToU64_prog 24
      (.JAL .x0 (32 : BitVec 21)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hj0
  have hjF0 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ outputPtr) ** (.x10 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** (outputPtr ↦ₘ value) ** F)
    (by pcf; exact hF) hj
  have hjF := cpsTripleWithin_weaken
    (fun h hp => (sepConj_emp_left h).2 hp)
    (fun h hp => (sepConj_emp_left h).1 hp) hjF0
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsF hlF
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h01 hjF
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) h012

#print axioms successMachineTail

/-- Scalar status two is preserved as wrapper status two
    (instructions 25, 26, 31). -/
theorem tooLongMachineTail
    (old5 old10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (B + 100) (B + 128) code
      ((.x5 ↦ᵣ old5) ** (.x11 ↦ᵣ (2 : Word)) **
        (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x5 ↦ᵣ (2 : Word)) **
        (.x11 ↦ᵣ (2 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hl0 := li_spec_gen_within .x5 old5 (2 : Word) (B + 100) (by decide)
  have hl := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 100) rlpFieldToU64_prog 25
      (.LI .x5 (2 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) hl0
  let R0 : Assertion :=
    (.x11 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ old10) **
    (.x0 ↦ᵣ (0 : Word)) ** F
  have hlF := cpsTripleWithin_frameR R0 (by unfold R0; pcf; exact hF) hl
  have hb0 := beq_spec_gen_within .x11 .x5 (20 : BitVec 13)
    (2 : Word) (2 : Word) (B + 104)
  rw [show B + 104 + signExtend13 (20 : BitVec 13) = B + 124 from by decide,
    show B + 104 + 4 = B + 108 from by bv_omega] at hb0
  have hb := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 104) rlpFieldToU64_prog 26
      (.BEQ .x11 .x5 (20 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R1 : Assertion :=
    (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) ** F
  have hbF := cpsBranchWithin_frameR R1 (by unfold R1; pcf; exact hF) hb
  have hbTaken := cpsBranchWithin_takenPath hbF (fun h hp => by
    extract_pure_deep hp
    obtain ⟨h_ne, -⟩ := hp
    exact h_ne rfl)
  have hr0 := li_spec_gen_within .x10 old10 (2 : Word) (B + 124) (by decide)
  have hr := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 124) rlpFieldToU64_prog 31
      (.LI .x10 (2 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) hr0
  let R2 : Assertion :=
    (.x5 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ (2 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) ** F
  have hrF := cpsTripleWithin_frameR R2 (by unfold R2; pcf; exact hF) hr
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlF hbTaken
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨-, hp⟩ := hp
    xperm_hyp hp) h01 hrF
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) h012

#print axioms tooLongMachineTail

/-- Scalar status three (leading-zero rejection) maps to wrapper status one
    (instructions 25--28). -/
theorem noncanonicalMachineTail
    (old5 old10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (B + 100) (B + 128) code
      ((.x5 ↦ᵣ old5) ** (.x11 ↦ᵣ (3 : Word)) **
        (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x5 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
        (.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hl0 := li_spec_gen_within .x5 old5 (2 : Word) (B + 100) (by decide)
  have hl := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 100) rlpFieldToU64_prog 25
      (.LI .x5 (2 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) hl0
  let R0 : Assertion :=
    (.x11 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ old10) **
    (.x0 ↦ᵣ (0 : Word)) ** F
  have hlF := cpsTripleWithin_frameR R0 (by unfold R0; pcf; exact hF) hl
  have hb0 := beq_spec_gen_within .x11 .x5 (20 : BitVec 13)
    (3 : Word) (2 : Word) (B + 104)
  rw [show B + 104 + signExtend13 (20 : BitVec 13) = B + 124 from by decide,
    show B + 104 + 4 = B + 108 from by bv_omega] at hb0
  have hb := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 104) rlpFieldToU64_prog 26
      (.BEQ .x11 .x5 (20 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R1 : Assertion :=
    (.x10 ↦ᵣ old10) ** (.x0 ↦ᵣ (0 : Word)) ** F
  have hbF := cpsBranchWithin_frameR R1 (by unfold R1; pcf; exact hF) hb
  have hbFall := cpsBranchWithin_ntakenPath hbF (fun h hp => by
    extract_pure_deep hp
    obtain ⟨h_eq, -⟩ := hp
    have h_ne : (3 : Word) ≠ 2 := by decide
    exact h_ne h_eq)
  have hs0 := li_spec_gen_within .x10 old10 (1 : Word) (B + 108) (by decide)
  have hs := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 108) rlpFieldToU64_prog 27
      (.LI .x10 (1 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) hs0
  let R2 : Assertion :=
    (.x5 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) ** F
  have hsF := cpsTripleWithin_frameR R2 (by unfold R2; pcf; exact hF) hs
  have hj0 := jal_x0_spec_gen_within (16 : BitVec 21) (B + 112)
  rw [show B + 112 + signExtend21 (16 : BitVec 21) = B + 128 from by decide]
    at hj0
  have hj := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 112) rlpFieldToU64_prog 28
      (.JAL .x0 (16 : BitVec 21)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hj0
  let R3 : Assertion :=
    (.x5 ↦ᵣ (2 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
    (.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F
  have hjF0 := cpsTripleWithin_frameR R3 (by unfold R3; pcf; exact hF) hj
  have hjF := cpsTripleWithin_weaken
    (fun h hp => (sepConj_emp_left h).2 hp)
    (fun h hp => (sepConj_emp_left h).1 hp) hjF0
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlF hbFall
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    extract_pure_deep hp
    obtain ⟨-, hp⟩ := hp
    xperm_hyp hp) h01 hsF
  have h0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    h012 hjF
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) h0123

#print axioms noncanonicalMachineTail

theorem scalarOutcome_result
    {bytes : List (BitVec 8)} {listBase offset len value status : Word}
    {listLen index : Nat}
    (h_ok : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
      index offset len)
    (h_out : ScalarOutcome bytes offset.toNat len.toNat value status) :
    ∃ wrapperStatus,
      Result bytes listBase listLen index wrapperStatus value ∧
      ((status = 0 ∧ wrapperStatus = 0) ∨
       (status = 2 ∧ wrapperStatus = 2) ∨
       (status = 3 ∧ wrapperStatus = 1)) := by
  cases h_out with
  | tooLong h_len =>
      exact ⟨2, .tooLong offset len h_ok h_len, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | empty h_len =>
      exact ⟨0, .empty offset len h_ok h_len, Or.inl ⟨rfl, rfl⟩⟩
  | noncanonical h_pos h_fit h_zero =>
      exact ⟨1, .noncanonical offset len h_ok h_pos h_fit h_zero,
        Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  | success h_pos h_fit h_nz =>
      exact ⟨0, .success offset len h_ok h_pos h_fit h_nz, Or.inl ⟨rfl, rfl⟩⟩

#print axioms scalarOutcome_result

end EvmAsm.Codegen.RlpFieldToU64SAsm
