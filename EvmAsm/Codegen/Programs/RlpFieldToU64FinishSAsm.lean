/-
  Final status dispatch and whole-routine composition for the lenient scalar
  decoder (status 0 success or status 2 too-long).
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


theorem scalarOutcome_result
    {bytes : List (BitVec 8)} {listBase offset len value status : Word}
    {listLen index : Nat}
    (h_ok : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
      index offset len)
    (h_out : ScalarOutcome bytes offset.toNat len.toNat value status) :
    ∃ wrapperStatus,
      Result bytes listBase listLen index wrapperStatus value ∧
      ((status = 0 ∧ wrapperStatus = 0) ∨
       (status = 2 ∧ wrapperStatus = 2)) := by
  cases h_out with
  | tooLong h_len =>
      exact ⟨2, .tooLong offset len h_ok h_len, Or.inr ⟨rfl, rfl⟩⟩
  | empty h_len =>
      exact ⟨0, .empty offset len h_ok h_len, Or.inl ⟨rfl, rfl⟩⟩
  | success h_pos h_fit =>
      exact ⟨0, .success offset len h_ok h_pos h_fit, Or.inl ⟨rfl, rfl⟩⟩


def stableRest
    (ra sp0 listBase offset len v12 : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ra) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  bytesRegion listBase bytes ** (.x2 ↦ᵣ sp0) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree sp0 8 **
  (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x8 ↦ᵣ listBase) **
  (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)

theorem pcFree_stableRest ra sp0 listBase offset len v12 saved bytes :
    (stableRest ra sp0 listBase offset len v12 saved bytes).pcFree := by
  unfold stableRest
  pcf

def joinCore
    (ra sp0 listBase offset len v12 x5 scalarStatus wrapperStatus outputValue : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  stableRest ra sp0 listBase offset len v12 saved bytes **
  (.x5 ↦ᵣ x5) ** (.x9 ↦ᵣ saved.s1) ** (.x10 ↦ᵣ wrapperStatus) **
  (.x11 ↦ᵣ scalarStatus) ** (.x0 ↦ᵣ (0 : Word)) **
  (saved.s1 ↦ₘ outputValue)

def joinedResult
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 ra x5 scalarStatus wrapperStatus outputValue,
    (joinCore ra sp0 listBase offset len v12 x5 scalarStatus wrapperStatus
      outputValue saved bytes **
     ⌜Result bytes listBase listLen index wrapperStatus outputValue⌝) h

def scalarCoreAt5
    (sp0 listBase offset len v12 x5 value status : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ (B + 84)) ** (.x5 ↦ᵣ x5) ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  ((.x10 ↦ᵣ value) ** (.x11 ↦ᵣ status)) **
  contentCarry sp0 listBase offset len v12 saved

private theorem successSemanticTail
    (sp0 listBase offset len v12 x5 value : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h_result : Result bytes listBase listLen index 0 value) :
    cpsTripleWithin 3 (B + 88) (B + 128) code
      (scalarCoreAt5 sp0 listBase offset len v12 x5 value 0 saved bytes **
       (saved.s1 ↦ₘ (0 : Word)))
      (joinedResult sp0 listBase saved bytes listLen index) := by
  let F : Assertion :=
    (.x5 ↦ᵣ x5) ** (.x11 ↦ᵣ (0 : Word)) **
    stableRest (B + 84) sp0 listBase offset len v12 saved bytes
  have ht := successMachineTail saved.s1 value 0 F (by
    unfold F
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs
        (pcFree_stableRest _ _ _ _ _ _ _ _)))
  refine cpsTripleWithin_weaken (fun h hp => by
      unfold scalarCoreAt5 contentCarry listOtherSaved at hp
      unfold F stableRest
      xperm_hyp hp) (fun h hp => ?_) ht
  unfold joinedResult
  refine ⟨offset, len, v12, B + 84, x5, 0, 0, value, ?_⟩
  apply (sepConj_pure_right h).2
  constructor
  · unfold F stableRest at hp
    unfold joinCore stableRest
    xperm_hyp hp
  · exact h_result


private theorem tooLongSemanticTail
    (sp0 listBase offset len v12 x5 : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h_result : Result bytes listBase listLen index 2 0) :
    cpsTripleWithin 3 (B + 100) (B + 128) code
      (scalarCoreAt5 sp0 listBase offset len v12 x5 0 2 saved bytes **
       (saved.s1 ↦ₘ (0 : Word)))
      (joinedResult sp0 listBase saved bytes listLen index) := by
  let F : Assertion :=
    (.x9 ↦ᵣ saved.s1) ** (saved.s1 ↦ₘ (0 : Word)) **
    stableRest (B + 84) sp0 listBase offset len v12 saved bytes
  have ht := tooLongMachineTail x5 0 F (by
    unfold F
    exact pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_memIs
        (pcFree_stableRest _ _ _ _ _ _ _ _)))
  refine cpsTripleWithin_weaken (fun h hp => by
      unfold scalarCoreAt5 contentCarry listOtherSaved at hp
      unfold F stableRest
      xperm_hyp hp) (fun h hp => ?_) ht
  unfold joinedResult
  refine ⟨offset, len, v12, B + 84, 2, 2, 2, 0, ?_⟩
  apply (sepConj_pure_right h).2
  constructor
  · unfold F stableRest at hp
    unfold joinCore stableRest
    xperm_hyp hp
  · exact h_result



def scalarNo5
    (sp0 listBase offset len v12 value status : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ (B + 84)) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  ((.x10 ↦ᵣ value) ** (.x11 ↦ᵣ status)) **
  contentCarry sp0 listBase offset len v12 saved ** (saved.s1 ↦ₘ (0 : Word))

private theorem successSemanticOwned
    (sp0 listBase offset len v12 value : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h_result : Result bytes listBase listLen index 0 value) :
    cpsTripleWithin 3 (B + 88) (B + 128) code
      (scalarCore sp0 listBase offset len v12 value 0 saved bytes **
       (saved.s1 ↦ₘ (0 : Word)))
      (joinedResult sp0 listBase saved bytes listLen index) := by
  let P := scalarNo5 sp0 listBase offset len v12 value 0 saved bytes
  have hfixed : ∀ x5,
      cpsTripleWithin 3 (B + 88) (B + 128) code
        (P ** (.x5 ↦ᵣ x5))
        (joinedResult sp0 listBase saved bytes listLen index) := by
    intro x5
    have ht := successSemanticTail sp0 listBase offset len v12 x5 value saved
      bytes listLen index h_result
    exact cpsTripleWithin_weaken (fun h hp => by
      unfold P scalarNo5 at hp
      unfold scalarCoreAt5
      xperm_hyp hp) (fun _ hp => hp) ht
  have howned := cpsTripleWithin_of_forall_regIs_to_regOwn hfixed
  exact cpsTripleWithin_weaken (fun h hp => by
      unfold scalarCore at hp
      unfold P scalarNo5
      xperm_hyp hp) (fun _ hp => hp) howned

private theorem tooLongSemanticOwned
    (sp0 listBase offset len v12 : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h_result : Result bytes listBase listLen index 2 0) :
    cpsTripleWithin 3 (B + 100) (B + 128) code
      (scalarCore sp0 listBase offset len v12 0 2 saved bytes **
       (saved.s1 ↦ₘ (0 : Word)))
      (joinedResult sp0 listBase saved bytes listLen index) := by
  let P := scalarNo5 sp0 listBase offset len v12 0 2 saved bytes
  have hfixed : ∀ x5,
      cpsTripleWithin 3 (B + 100) (B + 128) code
        (P ** (.x5 ↦ᵣ x5))
        (joinedResult sp0 listBase saved bytes listLen index) := by
    intro x5
    have ht := tooLongSemanticTail sp0 listBase offset len v12 x5 saved bytes
      listLen index h_result
    exact cpsTripleWithin_weaken (fun h hp => by
      unfold P scalarNo5 at hp
      unfold scalarCoreAt5
      xperm_hyp hp) (fun _ hp => hp) ht
  have howned := cpsTripleWithin_of_forall_regIs_to_regOwn hfixed
  exact cpsTripleWithin_weaken (fun h hp => by
      unfold scalarCore at hp
      unfold P scalarNo5
      xperm_hyp hp) (fun _ hp => hp) howned


def fallReady
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 value status,
    (⌜status = 0⌝ **
      ⌜ScalarOutcome bytes offset.toNat len.toNat value status⌝ **
      ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
        offset len⌝ **
      (scalarCore sp0 listBase offset len v12 value status saved bytes **
       (saved.s1 ↦ₘ (0 : Word)))) h

def takenReady
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 value status,
    (⌜status ≠ 0⌝ **
      ⌜ScalarOutcome bytes offset.toNat len.toNat value status⌝ **
      ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
        offset len⌝ **
      (scalarCore sp0 listBase offset len v12 value status saved bytes **
       (saved.s1 ↦ₘ (0 : Word)))) h

theorem fallSemanticTail
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 3 (B + 88) (B + 128) code
      (fallReady sp0 listBase saved bytes listLen index)
      (joinedResult sp0 listBase saved bytes listLen index) := by
  unfold fallReady
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun value => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun status => ?_)
  refine cpsTripleWithin_pure_pre (P := status = 0) (fun h_eq => ?_)
  refine cpsTripleWithin_pure_pre
    (P := ScalarOutcome bytes offset.toNat len.toNat value status)
    (fun h_out => ?_)
  refine cpsTripleWithin_pure_pre
    (P := EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
      offset len) (fun h_ok => ?_)
  cases h_out with
  | tooLong h_len => simp at h_eq
  | empty h_len =>
      exact successSemanticOwned sp0 listBase offset len v12 0 saved bytes
        listLen index (.empty offset len h_ok h_len)
  | success h_pos h_fit =>
      exact successSemanticOwned sp0 listBase offset len v12 _ saved bytes
        listLen index (.success offset len h_ok h_pos h_fit)


theorem takenSemanticTail
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 4 (B + 100) (B + 128) code
      (takenReady sp0 listBase saved bytes listLen index)
      (joinedResult sp0 listBase saved bytes listLen index) := by
  unfold takenReady
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun value => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun status => ?_)
  refine cpsTripleWithin_pure_pre (P := status ≠ 0) (fun h_ne => ?_)
  refine cpsTripleWithin_pure_pre
    (P := ScalarOutcome bytes offset.toNat len.toNat value status)
    (fun h_out => ?_)
  refine cpsTripleWithin_pure_pre
    (P := EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
      offset len) (fun h_ok => ?_)
  cases h_out with
  | empty h_len => simp at h_ne
  | success h_pos h_fit => simp at h_ne
  | tooLong h_len =>
      have ht := tooLongSemanticOwned sp0 listBase offset len v12 saved bytes
        listLen index (.tooLong offset len h_ok h_len)
      exact cpsTripleWithin_mono_nSteps (by omega) ht


theorem scalarTaken_framed_to_ready
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    (scalarTaken sp0 listBase saved bytes listLen index **
      (saved.s1 ↦ₘ (0 : Word))) h →
    takenReady sp0 listBase saved bytes listLen index h := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, hp, hm⟩ := hp
  unfold scalarTaken at hp
  obtain ⟨offset, len, v12, value, status, hp⟩ := hp
  unfold takenReady
  refine ⟨offset, len, v12, value, status, ?_⟩
  obtain ⟨hp, h_ne⟩ := (sepConj_pure_right h1).1 hp
  obtain ⟨hp, h_out⟩ := (sepConj_pure_right h1).1 hp
  obtain ⟨hcore, h_ok⟩ := (sepConj_pure_right h1).1 hp
  have hstate : (scalarCore sp0 listBase offset len v12 value status saved bytes **
      (saved.s1 ↦ₘ (0 : Word))) h := ⟨h1, h2, hd, hu, hcore, hm⟩
  apply (sepConj_pure_left h).2
  refine ⟨h_ne, (sepConj_pure_left h).2 ⟨h_out,
    (sepConj_pure_left h).2 ⟨h_ok, ?_⟩⟩⟩
  exact hstate

theorem scalarFall_framed_to_ready
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    (scalarFall sp0 listBase saved bytes listLen index **
      (saved.s1 ↦ₘ (0 : Word))) h →
    fallReady sp0 listBase saved bytes listLen index h := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, hp, hm⟩ := hp
  unfold scalarFall at hp
  obtain ⟨offset, len, v12, value, status, hp⟩ := hp
  unfold fallReady
  refine ⟨offset, len, v12, value, status, ?_⟩
  obtain ⟨hp, h_eq⟩ := (sepConj_pure_right h1).1 hp
  obtain ⟨hp, h_out⟩ := (sepConj_pure_right h1).1 hp
  obtain ⟨hcore, h_ok⟩ := (sepConj_pure_right h1).1 hp
  have hstate : (scalarCore sp0 listBase offset len v12 value status saved bytes **
      (saved.s1 ↦ₘ (0 : Word))) h := ⟨h1, h2, hd, hu, hcore, hm⟩
  apply (sepConj_pure_left h).2
  refine ⟨h_eq, (sepConj_pure_left h).2 ⟨h_out,
    (sepConj_pure_left h).2 ⟨h_ok, ?_⟩⟩⟩
  exact hstate

theorem scalarBranchWithOutput
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 84) code
      (scalarResult sp0 listBase saved bytes listLen index **
       (saved.s1 ↦ₘ (0 : Word)))
      (B + 100) (takenReady sp0 listBase saved bytes listLen index)
      (B + 88) (fallReady sp0 listBase saved bytes listLen index) := by
  have hb := scalarBranch sp0 listBase saved bytes listLen index
  have hbF := cpsBranchWithin_frameR (saved.s1 ↦ₘ (0 : Word)) (by pcf) hb
  exact cpsBranchWithin_weaken (fun _ hp => hp)
    (scalarTaken_framed_to_ready sp0 listBase saved bytes listLen index)
    (scalarFall_framed_to_ready sp0 listBase saved bytes listLen index) hbF


theorem scalarDispatch
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 5 (B + 84) (B + 128) code
      (scalarResult sp0 listBase saved bytes listLen index **
       (saved.s1 ↦ₘ (0 : Word)))
      (joinedResult sp0 listBase saved bytes listLen index) := by
  have hb := scalarBranchWithOutput sp0 listBase saved bytes listLen index
  have ht := takenSemanticTail sp0 listBase saved bytes listLen index
  have hf0 := fallSemanticTail sp0 listBase saved bytes listLen index
  have hf : cpsTripleWithin 4 (B + 88) (B + 128) code
      (fallReady sp0 listBase saved bytes listLen index)
      (joinedResult sp0 listBase saved bytes listLen index) :=
    cpsTripleWithin_mono_nSteps (by omega) hf0
  exact cpsBranchWithin_merge_same_cr hb ht hf

theorem contentDone_framed_to_scalarResult
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    (contentDone sp0 listBase saved bytes listLen index **
      (saved.s1 ↦ₘ (0 : Word))) h →
    (scalarResult sp0 listBase saved bytes listLen index **
      (saved.s1 ↦ₘ (0 : Word))) h :=
  sepConj_mono_left
    (contentDone_to_scalarResult sp0 listBase saved bytes listLen index)


theorem callContentWithOutput
    (sp0 listBase vOld : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + (7 * bytes.length + 11))
      (B + 80) (B + 84) code
      (((.x1 ↦ᵣ vOld) ** contentReady sp0 listBase saved bytes listLen index) **
       (saved.s1 ↦ₘ (0 : Word)))
      (scalarResult sp0 listBase saved bytes listLen index **
       (saved.s1 ↦ₘ (0 : Word))) := by
  have hc := callContent sp0 listBase vOld saved bytes listLen index hsalign
    hslack hover hvalid
  have hcF := cpsTripleWithin_frameR (saved.s1 ↦ₘ (0 : Word)) (by pcf) hc
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (contentDone_framed_to_scalarResult sp0 listBase saved bytes listLen index)
    hcF

theorem selectedToJoin
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      ((7 + (1 + (7 * bytes.length + 11))) + 5)
      (B + 52) (B + 128) code
      (((.x1 ↦ᵣ (B + 48)) **
        listSelected sp0 listBase offsetCell lengthCell saved bytes listLen index) **
       (saved.s1 ↦ₘ (0 : Word)))
      (joinedResult sp0 listBase saved bytes listLen index) := by
  have hs0' := selectedSetup sp0 listBase saved bytes listLen index hs0
  have hs := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (B + 48)) ** (saved.s1 ↦ₘ (0 : Word))) (by pcf) hs0'
  have hc := callContentWithOutput sp0 listBase (B + 48) saved bytes listLen
    index hsalign hslack hover hvalid
  have hsc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hs hc
  have hsc' := cpsTripleWithin_weaken (P' :=
      (((.x1 ↦ᵣ (B + 48)) **
        listSelected sp0 listBase offsetCell lengthCell saved bytes listLen index) **
       (saved.s1 ↦ₘ (0 : Word))))
    (fun _ hp => by xperm_hyp hp) (fun _ hp => hp) hsc
  have hd := scalarDispatch sp0 listBase saved bytes listLen index
  exact cpsTripleWithin_seq_same_cr hsc' hd


def failureResultAtJoin
    (sp0 listBase oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h =>
    ((((.x1 ↦ᵣ (B + 48)) **
       listFailed sp0 listBase offsetCell lengthCell oldOffset oldLen saved bytes
         listLen index) ** (saved.s1 ↦ₘ (0 : Word))) **
     ⌜Result bytes listBase listLen index 1 0⌝) h

def allJoinedResult
    (sp0 listBase oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => joinedResult sp0 listBase saved bytes listLen index h ∨
    failureResultAtJoin sp0 listBase oldOffset oldLen saved bytes listLen index h

theorem selectedToAllJoin
    (sp0 listBase oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      ((7 + (1 + (7 * bytes.length + 11))) + 5)
      (B + 52) (B + 128) code
      (((.x1 ↦ᵣ (B + 48)) **
        listSelected sp0 listBase offsetCell lengthCell saved bytes listLen index) **
       (saved.s1 ↦ₘ (0 : Word)))
      (allJoinedResult sp0 listBase oldOffset oldLen saved bytes listLen index) := by
  have hs := selectedToJoin sp0 listBase saved bytes listLen index hs0 hsalign
    hslack hover hvalid
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => Or.inl hp) hs

theorem failureToAllJoin
    (sp0 listBase oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 2 (B + 116) (B + 128) code
      (((.x1 ↦ᵣ (B + 48)) **
        listFailed sp0 listBase offsetCell lengthCell oldOffset oldLen saved bytes
          listLen index) ** (saved.s1 ↦ₘ (0 : Word)))
      (allJoinedResult sp0 listBase oldOffset oldLen saved bytes listLen index) := by
  have hf0 := failureJoin sp0 listBase offsetCell lengthCell oldOffset oldLen
    saved bytes listLen index
  have hf := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (B + 48)) ** (saved.s1 ↦ₘ (0 : Word))) (by pcf) hf0
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) hf
  have h_fail : EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase
      listLen index := by
    obtain ⟨h1, h2, hd, hu, hlist, hframe⟩ := hp
    unfold listFailed at hlist
    obtain ⟨v11, v12, hlist⟩ := hlist
    exact ((sepConj_pure_right h1).1 hlist).2
  right
  unfold failureResultAtJoin
  apply (sepConj_pure_right h).2
  constructor
  · xperm_hyp hp
  · exact .listFailure h_fail


theorem listDispatchToJoin
    (sp0 listBase oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let tailSteps := (7 + (1 + (7 * bytes.length + 11))) + 5
    cpsTripleWithin (1 + tailSteps) (B + 48) (B + 128) code
      (((.x1 ↦ᵣ (B + 48)) **
        listCallResult sp0 listBase offsetCell lengthCell oldOffset oldLen saved
          bytes listLen index) ** (saved.s1 ↦ₘ (0 : Word)))
      (allJoinedResult sp0 listBase oldOffset oldLen saved bytes listLen index) := by
  dsimp
  have hb0 := listResultBranch sp0 listBase offsetCell lengthCell oldOffset
    oldLen saved bytes listLen index
  have hb := cpsBranchWithin_frameR
    ((.x1 ↦ᵣ (B + 48)) ** (saved.s1 ↦ₘ (0 : Word))) (by pcf) hb0
  have hs0' := selectedToAllJoin sp0 listBase oldOffset oldLen saved bytes
    listLen index hs0 hsalign hslack hover hvalid
  have hs : cpsTripleWithin
      ((7 + (1 + (7 * bytes.length + 11))) + 5)
      (B + 52) (B + 128) code
      (listSelected sp0 listBase offsetCell lengthCell saved bytes listLen index **
       ((.x1 ↦ᵣ (B + 48)) ** (saved.s1 ↦ₘ (0 : Word))))
      (allJoinedResult sp0 listBase oldOffset oldLen saved bytes listLen index) :=
    cpsTripleWithin_weaken (fun h hp => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
      (fun _ hp => hp) hs0'
  have hf0 := failureToAllJoin sp0 listBase oldOffset oldLen saved bytes
    listLen index
  have hf : cpsTripleWithin
      ((7 + (1 + (7 * bytes.length + 11))) + 5)
      (B + 116) (B + 128) code
      (listFailed sp0 listBase offsetCell lengthCell oldOffset oldLen saved bytes
        listLen index **
       ((.x1 ↦ᵣ (B + 48)) ** (saved.s1 ↦ₘ (0 : Word))))
      (allJoinedResult sp0 listBase oldOffset oldLen saved bytes listLen index) := by
    have hf1 : cpsTripleWithin 2 (B + 116) (B + 128) code
        (listFailed sp0 listBase offsetCell lengthCell oldOffset oldLen saved bytes
          listLen index **
         ((.x1 ↦ᵣ (B + 48)) ** (saved.s1 ↦ₘ (0 : Word))))
        (allJoinedResult sp0 listBase oldOffset oldLen saved bytes listLen index) :=
      cpsTripleWithin_weaken (fun h hp => by
        simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
        (fun _ hp => hp) hf0
    exact cpsTripleWithin_mono_nSteps (by omega) hf1
  have hm := cpsBranchWithin_merge_same_cr hb hf hs
  exact cpsTripleWithin_weaken (fun h hp => by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hp)
    (fun _ hp => hp) hm


def successPayload
    (sp0 listBase offset len v12 x5 scalarStatus wrapperStatus outputValue : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  ((regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion listBase bytes **
    (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
    (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree sp0 8 **
    (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (offsetCell ↦ₘ offset) **
    (lengthCell ↦ₘ len) ** (.x5 ↦ᵣ x5) **
    (.x10 ↦ᵣ wrapperStatus) ** (.x11 ↦ᵣ scalarStatus) **
    (.x0 ↦ᵣ (0 : Word)) ** (saved.s1 ↦ₘ outputValue)) **
   ⌜Result bytes listBase listLen index wrapperStatus outputValue⌝)

def successRestoreReady
    (sp0 newSp listBase : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 x5 scalarStatus wrapperStatus outputValue,
    (((.x2 ↦ᵣ sp0) ** regsOwnAt frame ** savedFrame newSp outer) **
      successPayload sp0 listBase offset len v12 x5 scalarStatus wrapperStatus
        outputValue saved bytes listLen index) h

theorem joinedResult_to_restoreReady
    (sp0 newSp listBase : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    (joinedResult sp0 listBase saved bytes listLen index **
      savedFrame newSp outer) h →
    successRestoreReady sp0 newSp listBase outer saved bytes listLen index h := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, hj, hsf⟩ := hp
  unfold joinedResult at hj
  obtain ⟨offset, len, v12, ra, x5, scalarStatus, wrapperStatus, outputValue,
    hj⟩ := hj
  obtain ⟨hcore, h_result⟩ := (sepConj_pure_right h1).1 hj
  let P : Assertion :=
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** bytesRegion listBase bytes **
    (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
    (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree sp0 8 **
    (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (offsetCell ↦ₘ offset) **
    (lengthCell ↦ₘ len) ** (.x5 ↦ᵣ x5) **
    (.x10 ↦ᵣ wrapperStatus) ** (.x11 ↦ᵣ scalarStatus) **
    (.x0 ↦ᵣ (0 : Word)) ** (saved.s1 ↦ₘ outputValue)
  have hsplit : (((.x2 ↦ᵣ sp0) **
      ((.x1 ↦ᵣ ra) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ saved.s1))) ** P) h1 := by
    unfold joinCore stableRest at hcore
    unfold P
    xperm_hyp hcore
  obtain ⟨hf, hP, hdfp, hufp, hframe, hpayload⟩ := hsplit
  have hframe' : ((.x2 ↦ᵣ sp0) ** regsOwnAt frame) hf := by
    exact sepConj_mono_right (fun h' hregs =>
      frameRegs_implies_owned listBase saved.s1 h'
        (sepConj_mono_left (regIs_implies_regOwn .x1) h' hregs)) hf hframe
  unfold successRestoreReady
  refine ⟨offset, len, v12, x5, scalarStatus, wrapperStatus, outputValue, ?_⟩
  have hbase : (((.x2 ↦ᵣ sp0) ** regsOwnAt frame) ** P) h1 :=
    ⟨hf, hP, hdfp, hufp, hframe', hpayload⟩
  have hcombined : ((((.x2 ↦ᵣ sp0) ** regsOwnAt frame) ** P) **
      savedFrame newSp outer) h := ⟨h1, h2, hd, hu, hbase, hsf⟩
  have himpl : ∀ h', P h' →
      successPayload sp0 listBase offset len v12 x5 scalarStatus wrapperStatus
        outputValue saved bytes listLen index h' := by
    intro h' hp'
    unfold P at hp'
    unfold successPayload
    exact (sepConj_pure_right h').2 ⟨hp', h_result⟩
  have hcombined' := sepConj_mono_left (sepConj_mono_right himpl) h hcombined
  xperm_hyp hcombined'


def failurePayload
    (sp0 listBase oldOffset oldLen v11 v12 : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ v11) **
    (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
    (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree sp0 8 **
    bytesRegion listBase bytes ** (offsetCell ↦ₘ oldOffset) **
    (lengthCell ↦ₘ oldLen) ** (.x10 ↦ᵣ (1 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) ** (saved.s1 ↦ₘ (0 : Word))) **
   ⌜Result bytes listBase listLen index 1 0⌝)

def failureRestoreReady
    (sp0 newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ v11 v12,
    (((.x2 ↦ᵣ sp0) ** regsOwnAt frame ** savedFrame newSp outer) **
      failurePayload sp0 listBase oldOffset oldLen v11 v12 saved bytes listLen
        index) h

theorem failureResult_to_restoreReady
    (sp0 newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    (failureResultAtJoin sp0 listBase oldOffset oldLen saved bytes listLen index **
      savedFrame newSp outer) h →
    failureRestoreReady sp0 newSp listBase oldOffset oldLen outer saved bytes
      listLen index h := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, hj, hsf⟩ := hp
  obtain ⟨hj, h_result⟩ := (sepConj_pure_right h1).1 hj
  obtain ⟨ha, hb, hdab, huab, hmain, hmem⟩ := hj
  obtain ⟨hraState, hlist, hdraw, hurow, hra, hfailed⟩ := hmain
  unfold listFailed at hfailed
  obtain ⟨v11, v12, hfailed⟩ := hfailed
  obtain ⟨hcore, h_fail⟩ := (sepConj_pure_right hlist).1 hfailed
  let P : Assertion :=
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ v11) **
    (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
    (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree sp0 8 **
    bytesRegion listBase bytes ** (offsetCell ↦ₘ oldOffset) **
    (lengthCell ↦ₘ oldLen) ** (.x10 ↦ᵣ (1 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) ** (saved.s1 ↦ₘ (0 : Word))
  have hflat : (((.x2 ↦ᵣ sp0) **
      ((.x1 ↦ᵣ (B + 48)) ** (.x8 ↦ᵣ saved.s0) **
       (.x9 ↦ᵣ saved.s1))) ** P) h1 := by
    have hinner : ((.x1 ↦ᵣ (B + 48)) **
        listCallCore sp0 listBase offsetCell lengthCell saved bytes 1 oldOffset
          oldLen v11 v12) ha := ⟨hraState, hlist, hdraw, hurow, hra, hcore⟩
    have hall : (((.x1 ↦ᵣ (B + 48)) **
        listCallCore sp0 listBase offsetCell lengthCell saved bytes 1 oldOffset
          oldLen v11 v12) ** (saved.s1 ↦ₘ (0 : Word))) h1 :=
      ⟨ha, hb, hdab, huab, hinner, hmem⟩
    unfold listCallCore listCallRest listSavedRegs listOtherSaved at hall
    unfold P
    xperm_hyp hall
  obtain ⟨hf, hP, hdfp, hufp, hframe, hpayload⟩ := hflat
  have hframe' : ((.x2 ↦ᵣ sp0) ** regsOwnAt frame) hf := by
    exact sepConj_mono_right (fun h' hregs =>
      frameRegs_implies_owned saved.s0 saved.s1 h'
        (sepConj_mono_left (regIs_implies_regOwn .x1) h' hregs)) hf hframe
  unfold failureRestoreReady
  refine ⟨v11, v12, ?_⟩
  have hbase : (((.x2 ↦ᵣ sp0) ** regsOwnAt frame) ** P) h1 :=
    ⟨hf, hP, hdfp, hufp, hframe', hpayload⟩
  have hcombined : ((((.x2 ↦ᵣ sp0) ** regsOwnAt frame) ** P) **
      savedFrame newSp outer) h := ⟨h1, h2, hd, hu, hbase, hsf⟩
  have himpl : ∀ h', P h' →
      failurePayload sp0 listBase oldOffset oldLen v11 v12 saved bytes listLen
        index h' := by
    intro h' hp'
    unfold P at hp'
    unfold failurePayload
    exact (sepConj_pure_right h').2 ⟨hp', h_result⟩
  have hcombined' := sepConj_mono_left (sepConj_mono_right himpl) h hcombined
  xperm_hyp hcombined'


def successReturned
    (spOuter newSp listBase : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 x5 scalarStatus wrapperStatus outputValue,
    (((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
      savedFrame newSp outer) **
      successPayload newSp listBase offset len v12 x5 scalarStatus wrapperStatus
        outputValue saved bytes listLen index) h

def failureReturned
    (spOuter newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ v11 v12,
    (((.x2 ↦ᵣ spOuter) ** regsAt frame (savedVals outer) **
      savedFrame newSp outer) **
      failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes listLen
        index) h

def allRestoreReady
    (newSp innerSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h =>
    successRestoreReady newSp innerSp listBase outer saved bytes listLen index h ∨
    failureRestoreReady newSp innerSp listBase oldOffset oldLen outer saved bytes
      listLen index h

def allReturned
    (spOuter newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h =>
    successReturned spOuter newSp listBase outer saved bytes listLen index h ∨
    failureReturned spOuter newSp listBase oldOffset oldLen outer saved bytes
      listLen index h

theorem restoreSuccess
    (spOuter newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    cpsTripleWithin 5 (B + 128) outer.ra code
      (successRestoreReady newSp newSp listBase outer saved bytes listLen index)
      (allReturned spOuter newSp listBase oldOffset oldLen outer saved bytes
        listLen index) := by
  unfold successRestoreReady
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun x5 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun scalarStatus => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun wrapperStatus => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun outputValue => ?_)
  apply cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_)
    (restoreTail spOuter newSp outer
      (successPayload newSp listBase offset len v12 x5 scalarStatus wrapperStatus
        outputValue saved bytes listLen index)
      (by unfold successPayload; pcf) hnewSp hret)
  left
  unfold successReturned
  exact ⟨offset, len, v12, x5, scalarStatus, wrapperStatus, outputValue, hp⟩


theorem restoreFailure
    (spOuter newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    cpsTripleWithin 5 (B + 128) outer.ra code
      (failureRestoreReady newSp newSp listBase oldOffset oldLen outer saved bytes
        listLen index)
      (allReturned spOuter newSp listBase oldOffset oldLen outer saved bytes
        listLen index) := by
  unfold failureRestoreReady
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  apply cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_)
    (restoreTail spOuter newSp outer
      (failurePayload newSp listBase oldOffset oldLen v11 v12 saved bytes listLen
        index)
      (by unfold failurePayload; pcf) hnewSp hret)
  right
  unfold failureReturned
  exact ⟨v11, v12, hp⟩

theorem restoreAll
    (spOuter newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    cpsTripleWithin 5 (B + 128) outer.ra code
      (allRestoreReady newSp newSp listBase oldOffset oldLen outer saved bytes
        listLen index)
      (allReturned spOuter newSp listBase oldOffset oldLen outer saved bytes
        listLen index) := by
  unfold allRestoreReady
  exact cpsTripleWithin_pre_or
    (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => hp)
      (restoreSuccess spOuter newSp listBase oldOffset oldLen outer saved bytes
        listLen index hnewSp hret))
    (restoreFailure spOuter newSp listBase oldOffset oldLen outer saved bytes
      listLen index hnewSp hret)


end EvmAsm.Codegen.RlpFieldToU64SAsm
