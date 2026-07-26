import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.LaResolve

/-! Verified SAsm contract for K68 `header_validate_extra_data_length`.

The routine performs one strict K20 field lookup (field 12), compares the
returned length with 32, and restores its one saved register.  The semantic
post keeps the K20 parse result and the three protocol statuses explicit.
-/

namespace EvmAsm.Codegen.HeaderValidateExtraDataLengthSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt
open EvmAsm.Codegen.RlpListNthItemSAsm

abbrev B : Word := (GuestAddrs.header_validate_extra_data_length : Word)
abbrev K20B : Word := (GuestAddrs.rlp_list_nth_item : Word)
abbrev offsetCell : Word := (GuestAddrs.hved_off : Word)
abbrev lengthCell : Word := (GuestAddrs.hved_len : Word)

theorem program_length : headerValidateExtraDataLength_prog.length = 22 := by decide

def wrapperCode : CodeReq :=
  CodeReq.ofProg B headerValidateExtraDataLength_prog

def code : CodeReq :=
  wrapperCode.union EvmAsm.Codegen.RlpListNthItemSAsm.code

theorem wrapper_list_disjoint :
    wrapperCode.Disjoint EvmAsm.Codegen.RlpListNthItemSAsm.code := by
  unfold wrapperCode EvmAsm.Codegen.RlpListNthItemSAsm.code B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]
    decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]
    decide
  · rw [program_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]
    decide

private theorem wrapperCode_mono : ∀ a i, wrapperCode a = some i → code a = some i := by
  intro a i hi
  unfold code
  exact CodeReq.union_mono_left a i hi

inductive Result (bytes : List (BitVec 8)) (base : Word)
    (listLen : Nat) (oldOffset oldLen : Word) :
    Word → Word → Word → Prop
  | ok (offset len : Word)
      (hsel : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen 12 offset len)
      (hlen : len.toNat ≤ 32) :
      Result bytes base listLen oldOffset oldLen 0 offset len
  | tooLong (offset len : Word)
      (hsel : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen 12 offset len)
      (hlen : 32 < len.toNat) :
      Result bytes base listLen oldOffset oldLen 1 offset len
  | parseFailure
      (hfail : EvmAsm.Codegen.RlpListNthItemSAsm.Failure
        bytes base listLen 12) :
      Result bytes base listLen oldOffset oldLen 2 oldOffset oldLen

theorem Result.status_cases {bytes : List (BitVec 8)} {base : Word}
    {listLen : Nat} {oldOffset oldLen status offset len : Word}
    (h : Result bytes base listLen oldOffset oldLen status offset len) :
    status = 0 ∨ status = 1 ∨ status = 2 := by
  cases h <;> simp

theorem k20Call
    (sp0 listBase listLenW offsetPtr lenPtr oldOffset oldLen oldRa : Word)
    (s0 s1 s2 s3 s4 s5 : Word) (bytes : List (BitVec 8))
    (listLen : Nat)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (12 + 2)) + 6)) + 9))
      (B + 28) (B + 32) code
      (((.x1 ↦ᵣ oldRa) **
        callEntryRest sp0 listBase listLenW (12 : Word) offsetPtr lenPtr
          oldOffset oldLen
          { ra := B + 32, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
            s4 := s4, s5 := s5 } bytes))
      (((.x1 ↦ᵣ (B + 32)) **
        callReturnResult sp0 listBase (12 : Word) offsetPtr lenPtr oldOffset oldLen
          { ra := B + 32, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
            s4 := s4, s5 := s5 } bytes listLen 12)) := by
  let saved : RlpListNthItemSAsm.Saved :=
    { ra := B + 32, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
      s4 := s4, s5 := s5 }
  have hret : saved.ra &&& ~~~(1 : Word) = saved.ra := by
    dsimp [saved, B]
    decide
  have htarget : (B + 28) + signExtend21
      (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.header_validate_extra_data_length + 28)) = K20B := by
    unfold B K20B
    decide
  have hmem : ∀ a i, CodeReq.singleton (B + 28)
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.header_validate_extra_data_length + 28))) a = some i →
      code a = some i := by
    intro a i hi
    unfold code
    apply CodeReq.union_mono_left
    exact CodeReq.ofProg_mem_at B (B + 28) headerValidateExtraDataLength_prog 7
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.header_validate_extra_data_length + 28))) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide) a i hi
  have hcalleeMem : ∀ a i,
      EvmAsm.Codegen.RlpListNthItemSAsm.code a = some i → code a = some i := by
    intro a i hi
    unfold code
    exact CodeReq.mono_union_right wrapper_list_disjoint (fun _ _ h => h) a i hi
  have hcall := rlpListNthItem_call_spec_within
    (cr := code) (B + 28) K20B oldRa sp0 listBase listLenW (12 : Word)
      offsetPtr lenPtr oldOffset oldLen
      (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.header_validate_extra_data_length + 28))
      (empAssertion) (by pcf) saved bytes listLen 12
      hlistLenW (by decide) (by decide) hsalign hslack hover hvalid
      (by decide) htarget rfl hmem hcalleeMem
  rw [show B + 28 + 4 = B + 32 by bv_omega] at hcall
  simpa [saved, sepConj_emp_right'] using hcall

def frame : FrameDesc := [(.x1, 0)]

def savedVals (ra : Word) : Reg → Word
  | .x1 => ra
  | _ => 0

def savedFrame (sp : Word) (ra : Word) : Assertion := sp ↦ₘ ra

theorem frameSlotsSaved_eq (sp ra : Word) :
    EvmAsm.Rv64.SAsm.frameSlotsSaved frame sp (savedVals ra) = savedFrame sp ra := by
  simp only [frame, EvmAsm.Rv64.SAsm.frameSlotsSaved, List.foldr, savedVals,
    savedFrame, sepConj_emp_right']
  have hs : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  rw [hs]
  congr 1
  simp

theorem setupPrologue
    (sp0 newSp ra : Word) (F : Assertion)
    (hnewSp : newSp = sp0 + signExtend12 (-16 : BitVec 12))
    (hF : F.pcFree) :
    cpsTripleWithin 2 B (B + 8) code
      ((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals ra) **
        frameSlotsOwn frame newSp ** F)
      ((.x2 ↦ᵣ newSp) ** regsAt frame (savedVals ra) ** savedFrame newSp ra ** F) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-16 : BitVec 12) B (by decide)
  rw [← hnewSp] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B B headerValidateExtraDataLength_prog 0
      (.ADDI .x2 .x2 (-16 : BitVec 12)) rfl
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt frame (savedVals ra) ** frameSlotsOwn frame newSp ** F)
    (pcFree_sepConj (pcFree_regsAt _ _)
      (pcFree_sepConj (pcFree_frameSlotsOwn _ _) hF)) ha
  have hs0 := storeSeq_spec frame newSp (savedVals ra) (B + 4) (by decide)
  have hsMono : ∀ a i,
      CodeReq.ofProg (B + 4) (storeProg frame) a = some i → wrapperCode a = some i := by
    intro a i hi
    exact CodeReq.ofProg_mono_sub B (B + 4) headerValidateExtraDataLength_prog
      (storeProg frame) 1 (by bv_omega) (by rfl)
      (by rw [program_length]; simp [frame])
      (by rw [program_length]; decide) a i hi
  have hs := cpsTripleWithin_extend_code hsMono hs0
  rw [frameSlotsSaved_eq] at hs
  have hflen : 4 * frame.length = 4 := by simp [frame]
  rw [hflen] at hs
  rw [show B + 4 + BitVec.ofNat 64 4 = B + 8 by decide] at hs
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF
    (cpsTripleWithin_frameR F hF hs)
  have hseq' : cpsTripleWithin 2 B (B + 8) wrapperCode
      ((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals ra) **
        frameSlotsOwn frame newSp ** F)
      ((.x2 ↦ᵣ newSp) ** regsAt frame (savedVals ra) **
        savedFrame newSp ra ** F) := by
    simpa [frame, sepConj_assoc'] using hseq
  exact cpsTripleWithin_extend_code wrapperCode_mono hseq'

theorem setupArgs
    (old12 old13 old14 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 5 (B + 8) (B + 28) code
      (((.x12 ↦ᵣ old12) ** (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14)) ** F)
      (((.x12 ↦ᵣ (12 : Word)) ** (.x13 ↦ᵣ offsetCell) **
        (.x14 ↦ᵣ lengthCell)) ** F) := by
  have h0 := li_spec_gen_within .x12 old12 (12 : Word) (B + 8) (by decide)
  have h0' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 8) headerValidateExtraDataLength_prog 2
      (.LI .x12 (12 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h0
  have hau0 := CodeReq.ofProg_mem_at B (B + 12) headerValidateExtraDataLength_prog 3
    (.AUIPC .x13 (laHi GuestAddrs.hved_off
      (GuestAddrs.header_validate_extra_data_length + 12))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had0 := CodeReq.ofProg_mem_at B (B + 16) headerValidateExtraDataLength_prog 4
    (.ADDI .x13 .x13 (laLo GuestAddrs.hved_off
      (GuestAddrs.header_validate_extra_data_length + 12))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have ho := la_materialize_within .x13 old13 (B + 12) offsetCell
    (by decide) (by unfold B offsetCell; decide) hau0 had0
  have hau1 := CodeReq.ofProg_mem_at B (B + 20) headerValidateExtraDataLength_prog 5
    (.AUIPC .x14 (laHi GuestAddrs.hved_len
      (GuestAddrs.header_validate_extra_data_length + 20))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had1 := CodeReq.ofProg_mem_at B (B + 24) headerValidateExtraDataLength_prog 6
    (.ADDI .x14 .x14 (laLo GuestAddrs.hved_len
      (GuestAddrs.header_validate_extra_data_length + 20))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have hl := la_materialize_within .x14 old14 (B + 20) lengthCell
    (by decide) (by unfold B lengthCell; decide) hau1 had1
  have h0F := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** F)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hF)) h0'
  have hoF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ (12 : Word)) ** (.x14 ↦ᵣ old14) ** F)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hF)) ho
  have hlF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ (12 : Word)) ** (.x13 ↦ᵣ offsetCell) ** F)
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs hF)) hl
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F hoF
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hlF
  rw [show B + 20 + 8 = B + 28 by decide] at h012
  have h012' : cpsTripleWithin 5 (B + 8) (B + 28) wrapperCode
      (((.x12 ↦ᵣ old12) ** (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14)) ** F)
      (((.x12 ↦ᵣ (12 : Word)) ** (.x13 ↦ᵣ offsetCell) **
        (.x14 ↦ᵣ lengthCell)) ** F) := by
    simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using h012
  exact cpsTripleWithin_extend_code wrapperCode_mono h012'

def callRest (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (offset len v11 v12 : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** RlpListNthItemSAsm.savedRegTail saved ** stackFree sp0 8 **
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ v11) **
   (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
   regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion listBase bytes **
   (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))

def callCore (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (status offset len v11 v12 : Word) : Assertion :=
  (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
  callRest sp0 listBase offsetPtr lenPtr saved bytes offset len v11 v12

def selectedPath (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen : Nat) (_oldOffset _oldLen : Word) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (callCore sp0 listBase offsetPtr lenPtr saved bytes 0 offset len v11 v12 **
      ⌜RlpListNthItemSAsm.Success bytes listBase listLen 12 offset len⌝) h

def failedPath (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen : Nat) (_oldOffset _oldLen : Word) : Assertion :=
  fun h => ∃ v11 v12,
    (callCore sp0 listBase offsetPtr lenPtr saved bytes 1 _oldOffset _oldLen v11 v12 **
      ⌜RlpListNthItemSAsm.Failure bytes listBase listLen 12⌝) h

def callResult (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen : Nat) (oldOffset oldLen : Word) : Assertion :=
  RlpListNthItemSAsm.callReturnResult sp0 listBase (12 : Word) offsetPtr lenPtr
    oldOffset oldLen saved bytes listLen 12

theorem callResult_cases
    (sp0 listBase offsetPtr lenPtr : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen : Nat) (oldOffset oldLen : Word) : ∀ h,
    callResult sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen h →
      selectedPath sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen h ∨
      failedPath sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen h := by
  intro h hq
  unfold callResult RlpListNthItemSAsm.callReturnResult at hq
  obtain ⟨status, offset, len, v11, v12, hq⟩ := hq
  extract_pure_deep hq
  obtain ⟨hcore, hresult⟩ := hq
  cases hresult with
  | ok offset len h_ok =>
    left
    have hcore' : callCore sp0 listBase offsetPtr lenPtr saved bytes
        0 offset len v11 v12 h := by
      unfold callCore callRest
      xperm_hyp hcore
    exact ⟨offset, len, v11, v12, (sepConj_pure_right h).2 ⟨hcore', h_ok⟩⟩
  | fail h_fail =>
    right
    have hcore' : callCore sp0 listBase offsetPtr lenPtr saved bytes
        1 oldOffset oldLen v11 v12 h := by
      unfold callCore callRest
      xperm_hyp hcore
    exact ⟨v11, v12, (sepConj_pure_right h).2 ⟨hcore', h_fail⟩⟩

theorem branchSelected
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen : Nat) :
    cpsBranchWithin 1 (B + 32) code
      (selectedPath sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen)
      (B + 72) (failedPath sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen)
      (B + 36) (selectedPath sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen) := by
  unfold selectedPath
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_ok => ?_)
  have hb0 := bne_spec_gen_within .x10 .x0 (40 : BitVec 13)
    (0 : Word) (0 : Word) (B + 32)
  rw [show B + 32 + signExtend13 (40 : BitVec 13) = B + 72 by decide,
    show B + 32 + 4 = B + 36 by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 32) headerValidateExtraDataLength_prog 8
      (.BNE .x10 .x0 (40 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R : Assertion :=
    callRest sp0 listBase offsetPtr lenPtr saved bytes offset len v11 v12 **
    ⌜RlpListNthItemSAsm.Success bytes listBase listLen 12 offset len⌝
  have hbF := cpsBranchWithin_frameR R
    (pcFree_sepConj (by unfold callRest; pcf) (by pcf)) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code) wrapperCode_mono hbF
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold callCore at hp
      unfold R
      xperm_pure hp) (fun h hp => ?_) (fun h hp => ?_) hbC
  · extract_pure_deep hp
    obtain ⟨h_ne, -⟩ := hp
    exact False.elim (h_ne rfl)
  · extract_pure_deep hp
    obtain ⟨-, hstate⟩ := hp
    refine ⟨offset, len, v11, v12, ?_⟩
    unfold R at hstate
    unfold callCore
    xperm_pure hstate

theorem branchFailed
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen : Nat) :
    cpsBranchWithin 1 (B + 32) code
      (failedPath sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen)
      (B + 72) (failedPath sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen)
      (B + 36) (selectedPath sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen) := by
  unfold failedPath
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_fail => ?_)
  have hb0 := bne_spec_gen_within .x10 .x0 (40 : BitVec 13)
    (1 : Word) (0 : Word) (B + 32)
  rw [show B + 32 + signExtend13 (40 : BitVec 13) = B + 72 by decide,
    show B + 32 + 4 = B + 36 by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 32) headerValidateExtraDataLength_prog 8
      (.BNE .x10 .x0 (40 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R : Assertion :=
    callRest sp0 listBase offsetPtr lenPtr saved bytes oldOffset oldLen v11 v12 **
    ⌜RlpListNthItemSAsm.Failure bytes listBase listLen 12⌝
  have hbF := cpsBranchWithin_frameR R
    (pcFree_sepConj (by unfold callRest; pcf) (by pcf)) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code) wrapperCode_mono hbF
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold callCore at hp
      unfold R
      xperm_pure hp) (fun h hp => ?_) (fun h hp => ?_) hbC
  · extract_pure_deep hp
    obtain ⟨h_ne, hstate⟩ := hp
    refine ⟨v11, v12, ?_⟩
    unfold R at hstate
    unfold callCore
    xperm_pure hstate
  · extract_pure_deep hp
    obtain ⟨h_eq, -⟩ := hp
    have h_ne : (1 : Word) ≠ 0 := by decide
    exact False.elim (h_ne h_eq)

theorem callBranch
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen : Nat) :
    cpsBranchWithin 1 (B + 32) code
      (callResult sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen)
      (B + 72) (failedPath sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen)
      (B + 36) (selectedPath sp0 listBase offsetPtr lenPtr saved bytes listLen oldOffset oldLen) := by
  exact cpsBranchWithin_weaken
    (fun h hp => callResult_cases sp0 listBase offsetPtr lenPtr saved bytes listLen
      oldOffset oldLen h hp) (fun _ hp => hp) (fun _ hp => hp)
    (cpsBranchWithin_pre_or
      (branchSelected sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes listLen)
      (branchFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes listLen))

/-
/-! ## Selected-length comparison and ABI tail

The K20 success arm carries the selected field length in the global cell.  The
wrapper reloads that cell, compares it with 32, and joins both status paths at
the common restore tail. -/

def selectedCarry (sp0 listBase : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (v11 v12 : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** RlpListNthItemSAsm.savedRegTail saved ** stackFree sp0 8 **
  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes

theorem pcFree_selectedCarry (sp0 listBase : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (v11 v12 : Word) :
    (selectedCarry sp0 listBase saved bytes v11 v12).pcFree := by
  unfold selectedCarry RlpListNthItemSAsm.savedRegTail
  pcf

def lengthReady (sp0 listBase : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
      (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
      selectedCarry sp0 listBase saved bytes v11 v12) **
      ⌜RlpListNthItemSAsm.Success bytes listBase listLen 12 offset len⌝) h

def selectedLengthExact (len old5 old6 old7 : Word) (F : Assertion) :
    cpsTripleWithin 4 (B + 36) (B + 52) code
      (((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (lengthCell ↦ₘ len)) ** F)
      (((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
        (lengthCell ↦ₘ len)) ** F) := by
  have hau := CodeReq.ofProg_mem_at B (B + 36) headerValidateExtraDataLength_prog 9
    (.AUIPC .x5 (laHi GuestAddrs.hved_len
      (GuestAddrs.header_validate_extra_data_length + 36))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had := CodeReq.ofProg_mem_at B (B + 40) headerValidateExtraDataLength_prog 10
    (.ADDI .x5 .x5 (laLo GuestAddrs.hved_len
      (GuestAddrs.header_validate_extra_data_length + 36))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have h0 := la_materialize_within .x5 old5 (B + 36) lengthCell
    (by decide) (by unfold B lengthCell; decide) hau had
  have h1 := ld_spec_gen_within .x6 .x5 lengthCell old6 len
    (0 : BitVec 12) (B + 44) (by decide)
  rw [show lengthCell + signExtend12 (0 : BitVec 12) = lengthCell from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h1
  have h1' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 44) headerValidateExtraDataLength_prog 11
      (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h1
  have h2 := li_spec_gen_within .x7 old7 (32 : Word) (B + 48) (by decide)
  have h2' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 48) headerValidateExtraDataLength_prog 12
      (.LI .x7 (32 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h2
  have h0F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) ** (lengthCell ↦ₘ len) ** F)
    (by pcf) h0
  have h1F := cpsTripleWithin_frameR ((.x7 ↦ᵣ old7) ** F) (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) ** (lengthCell ↦ₘ len) ** F)
    (by pcf) h2'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have hs := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  exact hs

def selectedLength (sp0 listBase : Word)
    (saved : RlpListNthItemSAsm.Saved) (bytes : List (BitVec 8))
    (listLen : Nat) :
    cpsTripleWithin 4 (B + 36) (B + 52) code
      (selectedPath sp0 listBase offsetCell lengthCell saved bytes listLen 0 0)
      (lengthReady sp0 listBase saved bytes listLen) := by
  unfold selectedPath
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun offset => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun len => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v11 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v12 => ?_)
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_pure hp)
    (fun _ hp => hp) (cpsTripleWithin_pure_pre
      (P := RlpListNthItemSAsm.Success bytes listBase listLen 12 offset len)
      (H := callCore sp0 listBase offsetCell lengthCell saved bytes 0 offset len v11 v12)
      (fun h_ok => ?_))
  let F : Assertion :=
    (offsetCell ↦ₘ offset) ** selectedCarry sp0 listBase saved bytes v11 v12 **
      ⌜RlpListNthItemSAsm.Success bytes listBase listLen 12 offset len⌝
  have h7 (old5 old6 : Word) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := ((lengthCell ↦ₘ len) ** F ** (.x5 ↦ᵣ old5)) ** (.x6 ↦ᵣ old6))
      (Q := lengthReady sp0 listBase saved bytes listLen)
      (fun old7 => by
        have hs := selectedLengthExact len old5 old6 old7 F
        refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => ?_) hs
        unfold lengthReady
        exact ⟨offset, len, v11, v12, by
          unfold F at hq
          xperm_hyp hq⟩)
  have h6 (old5 : Word) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := ((lengthCell ↦ₘ len) ** F) ** (.x5 ↦ᵣ old5))
      (Q := lengthReady sp0 listBase saved bytes listLen)
      (fun old6 => cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => hp) (h7 old5 old6))
  have h5 := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
    (P := (lengthCell ↦ₘ len) ** F) (Q := lengthReady sp0 listBase saved bytes listLen)
    (fun old5 => cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => hp) (h6 old5))
  refine cpsTripleWithin_weaken
    (P' := callCore sp0 listBase offsetCell lengthCell saved bytes 0 offset len v11 v12)
    (Q' := lengthReady sp0 listBase saved bytes listLen)
    (fun _ hp => by
      unfold callCore callRest RlpListNthItemSAsm.savedRegTail at hp
      unfold F selectedCarry
      xperm_pure hp) (fun _ hp => hp) h5

theorem lengthBranch
    (sp0 listBase : Word) (saved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) :
    cpsBranchWithin 1 (B + 52) code
      (lengthReady sp0 listBase saved bytes listLen)
      (B + 64) (lengthReady sp0 listBase saved bytes listLen)
      (B + 56) (lengthReady sp0 listBase saved bytes listLen) := by
  unfold lengthReady
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_ok => ?_)
  have hb := bltu_spec_gen_within .x7 .x6 (12 : BitVec 13)
    (32 : Word) len (B + 52)
  rw [show B + 52 + signExtend13 (12 : BitVec 13) = B + 64 by decide,
    show B + 52 + 4 = B + 56 by bv_omega] at hb
  have hb' := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 52) headerValidateExtraDataLength_prog 13
      (.BLTU .x7 .x6 (12 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb
  have F := selectedCarry sp0 listBase saved bytes v11 v12
  have hF := pcFree_sepConj (pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (by unfold F; pcf) (by pcf))))) (by pcf)
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
    (cpsBranchWithin_frameR F hF hb')

 -/
end EvmAsm.Codegen.HeaderValidateExtraDataLengthSAsm
