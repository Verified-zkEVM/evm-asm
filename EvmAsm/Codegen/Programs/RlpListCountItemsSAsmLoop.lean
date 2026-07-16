import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmInit

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## Initialization dispatch and loop assertions -/

/-- Resources preserved after the two working saved registers have been
    initialized.  The output word remains unchanged until a terminal arm. -/
def stableRest (newSp listBase outPtr oldCount : Word) (saved : Saved) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outPtr) **
  savedFrame newSp saved ** (outPtr ↦ₘ oldCount)

/-- Resources stable across every strict `rlp_walk_next` call. -/
def loopFrame (newSp listBase outPtr endPtr oldCount raW : Word) (saved : Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x18 ↦ᵣ endPtr) ** stableRest newSp listBase outPtr oldCount saved **
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
   regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ raW) ** (.x0 ↦ᵣ (0 : Word)) **
   bytesRegion listBase bytes)

/-- Wrapper loop header at `B+48`. -/
def loopInv (newSp listBase outPtr endPtr oldCount : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen cursorOff : Nat) (j : Nat) : Assertion :=
  fun h => ∃ count off : Nat, ∃ v11 v12 raW : Word,
    ((loopFrame newSp listBase outPtr endPtr oldCount raW saved bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** (.x19 ↦ᵣ BitVec.ofNat 64 count))) **
     ⌜j = remaining listLen off ∧
       LoopInvariant bytes listBase listLen cursorOff endPtr count off
         (listBase + BitVec.ofNat 64 off)⌝) h

def initLoopPost (newSp listBase outPtr oldCount : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ cursorOff endPtr,
    loopInv newSp listBase outPtr endPtr oldCount saved bytes listLen cursorOff
      (remaining listLen cursorOff) h

/-- Common reject station at `B+84`; both malformed outer lists and failed
    strict child decodes arrive here. -/
def rejected (newSp listBase outPtr oldCount : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ status v10 v11 v12 workEnd countW raW : Word,
    (((stableRest newSp listBase outPtr oldCount saved **
       ((.x18 ↦ᵣ workEnd) ** (.x19 ↦ᵣ countW))) **
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ raW) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)) **
     ⌜status ≠ 0 ∧ Failure bytes listBase listLen⌝) h

theorem initRejectBranch (newSp listBase outPtr oldCount status cursor endPtr : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (h_status : status ≠ 0) (h_failure : Failure bytes listBase listLen) :
    cpsTripleWithin 1 (B + 36) (B + 84) code
      (((.x12 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
       ((initStable newSp listBase outPtr oldCount saved **
         initCommon listBase bytes) **
        ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr))))
      (rejected newSp listBase outPtr oldCount saved bytes listLen) := by
  have hb0 := bne_spec_gen_within .x12 .x0 (48 : BitVec 13) status 0 (B + 36)
  rw [show B + 36 + signExtend13 (48 : BitVec 13) = B + 84 from by decide] at hb0
  have hb := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 36) rlpListCountItems_prog 9
      (.BNE .x12 .x0 (48 : BitVec 13)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) hb0
  have ht := cpsBranchWithin_takenPath hb (fun hp h_false => by
    obtain ⟨_, _, _, _, _, hpure⟩ := h_false
    exact h_status ((sepConj_pure_right _).1 hpure).2)
  have htF := cpsTripleWithin_frameR
    ((initStable newSp listBase outPtr oldCount saved **
      initCommon listBase bytes) **
     ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr))) (by pcf) ht
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hp => by
    unfold rejected
    refine ⟨status, cursor, endPtr, status, saved.s2, saved.s3, B + 36, ?_⟩
    refine (sepConj_pure_right h).2 ⟨?_, h_status, h_failure⟩
    drop_pure hp
    unfold initStable initCommon at hp
    unfold stableRest
    xperm_hyp hp) htF

theorem initSuccessBranch (newSp listBase outPtr oldCount endPtr : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen cursorOff : Nat)
    (h_list : StrictListPayload bytes listBase listLen cursorOff endPtr) :
    cpsTripleWithin 3 (B + 36) (B + 48) code
      (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
       ((initStable newSp listBase outPtr oldCount saved **
         initCommon listBase bytes) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
         (.x11 ↦ᵣ endPtr))))
      (initLoopPost newSp listBase outPtr oldCount saved bytes listLen) := by
  have hb0 := bne_spec_gen_within .x12 .x0 (48 : BitVec 13) 0 0 (B + 36)
  have hb := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 36) rlpListCountItems_prog 9
      (.BNE .x12 .x0 (48 : BitVec 13)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) hb0
  have hn := cpsBranchWithin_ntakenPath hb (fun hp h_false => by
    obtain ⟨_, _, _, _, _, hpure⟩ := h_false
    exact ((sepConj_pure_right _).1 hpure).2 rfl)
  rw [show B + 36 + 4 = B + 40 from by decide] at hn
  have hnF := cpsTripleWithin_frameR
    ((initStable newSp listBase outPtr oldCount saved **
      initCommon listBase bytes) **
     ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ endPtr)))
    (by pcf) hn
  have hnClean : cpsTripleWithin 1 (B + 36) (B + 40) code
      (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
       ((initStable newSp listBase outPtr oldCount saved **
         initCommon listBase bytes) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
         (.x11 ↦ᵣ endPtr))))
      (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
       ((initStable newSp listBase outPtr oldCount saved **
         initCommon listBase bytes) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
         (.x11 ↦ᵣ endPtr)))) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      xperm_pure hp) hnF
  have hm0 := mv_spec_gen_within .x18 .x11 endPtr saved.s2 (B + 40) (by decide)
  have hm := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 40) rlpListCountItems_prog 10 (.MV .x18 .x11)
      (by bv_omega) (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) hm0
  have hmF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ saved.s3) **
     ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outPtr) **
      savedFrame newSp saved ** (outPtr ↦ₘ oldCount) **
      initCommon listBase bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
       (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))))) (by pcf) hm
  have hl0 := li_spec_gen_within .x19 saved.s3 (0 : Word) (B + 44) (by decide)
  have hl := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 44) rlpListCountItems_prog 11
      (.LI .x19 (0 : Word)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) hl0
  have hlF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ endPtr) **
     ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outPtr) **
      savedFrame newSp saved ** (outPtr ↦ₘ oldCount) **
      initCommon listBase bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
       (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
       (.x0 ↦ᵣ (0 : Word))))) (by pcf) hl
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold initStable initCommon at hp
    unfold initCommon
    xperm_hyp hp) hnClean hmF
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold initCommon at hp ⊢
    xperm_hyp hp) h01 hlF
  exact cpsTripleWithin_weaken (fun _ hp => by
    unfold initStable initCommon at hp ⊢
    xperm_hyp hp) (fun h hp => by
    unfold initLoopPost loopInv
    refine ⟨cursorOff, endPtr, 0, cursorOff, endPtr, 0, B + 36, ?_⟩
    refine (sepConj_pure_right h).2 ⟨?_, rfl, ?_⟩
    · unfold initCommon at hp
      unfold loopFrame stableRest
      xperm_hyp hp
    · exact ⟨h_list, StrictPrefix.zero, rfl, h_list.cursor_le, by omega⟩) h012

theorem initNormalizedDispatch (newSp listBase outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat) :
    cpsNBranchWithin 3 (B + 36) code
      ((((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
          initNormalized listBase bytes listLen) **
        initStable newSp listBase outPtr oldCount saved))
      [(B + 48, initLoopPost newSp listBase outPtr oldCount saved bytes listLen),
       (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen)] := by
  let successPre : Assertion := fun h => ∃ cursorOff endPtr,
    (((((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
         (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)))) **
       initStable newSp listBase outPtr oldCount saved) **
      ⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝) h)
  let failPre : Assertion := fun h => ∃ status cursor endPtr,
    (((((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status))) **
       initStable newSp listBase outPtr oldCount saved) **
      ⌜status ≠ 0 ∧ Failure bytes listBase listLen⌝) h)
  have hs : cpsNBranchWithin 3 (B + 36) code successPre
      [(B + 48, initLoopPost newSp listBase outPtr oldCount saved bytes listLen),
       (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen)] := by
    unfold successPre
    refine cpsNBranchWithin_exists_pre (fun cursorOff => ?_)
    refine cpsNBranchWithin_exists_pre (fun endPtr => ?_)
    refine cpsNBranchWithin_pure_pre (fun h_list => ?_)
    exact cpsNBranchWithin_of_triple (by simp)
      (cpsTripleWithin_weaken (fun h hp => by
        unfold initCommon at hp ⊢
        xperm_hyp hp) (fun _ hp => hp)
        (initSuccessBranch newSp listBase outPtr oldCount endPtr saved bytes
          listLen cursorOff h_list))
  have hf : cpsNBranchWithin 3 (B + 36) code failPre
      [(B + 48, initLoopPost newSp listBase outPtr oldCount saved bytes listLen),
       (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen)] := by
    unfold failPre
    refine cpsNBranchWithin_exists_pre (fun status => ?_)
    refine cpsNBranchWithin_exists_pre (fun cursor => ?_)
    refine cpsNBranchWithin_exists_pre (fun endPtr => ?_)
    refine cpsNBranchWithin_pure_pre (fun hpure => ?_)
    have ht : cpsTripleWithin 3 (B + 36) (B + 84) code
        (((.x12 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
         ((initStable newSp listBase outPtr oldCount saved **
           initCommon listBase bytes) **
          ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr))))
        (rejected newSp listBase outPtr oldCount saved bytes listLen) :=
      cpsTripleWithin_mono_nSteps (by omega)
        (initRejectBranch newSp listBase outPtr oldCount status cursor endPtr saved
          bytes listLen hpure.1 hpure.2)
    have hn : cpsNBranchWithin 3 (B + 36) code _
        [(B + 48, initLoopPost newSp listBase outPtr oldCount saved bytes listLen),
         (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen)] :=
      cpsNBranchWithin_of_triple (by simp) ht
    exact cpsNBranchWithin_weaken_pre (fun h hp => by
      unfold initCommon at hp ⊢
      xperm_hyp hp) hn
  have harms := RlpListNthItemSAsm.cpsNBranchWithin_pre_or_init hs hf
  exact cpsNBranchWithin_weaken_pre (fun h hp => by
    unfold initNormalized at hp
    unfold successPre failPre
    obtain ⟨h1, h2, hd, hu, hleft, hstable⟩ := hp
    obtain ⟨h3, h4, hd2, hu2, hcommon, hout⟩ := hleft
    rcases hout with hout | hout
    · refine Or.inl ?_
      obtain ⟨cursorOff, endPtr, hs0⟩ := hout
      refine ⟨cursorOff, endPtr, ?_⟩
      have hall : ((((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
           (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
           ⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝)) **
          initStable newSp listBase outPtr oldCount saved) h) :=
        ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, hs0⟩, hstable⟩
      have hall' : (⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝ **
          ((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
           ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
            (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word))) **
           initStable newSp listBase outPtr oldCount saved)) h := by
        xperm_hyp hall
      xperm_hyp hall'
    · refine Or.inr ?_
      obtain ⟨status, cursor, endPtr, hf0⟩ := hout
      refine ⟨status, cursor, endPtr, ?_⟩
      have hall : ((((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
           ⌜status ≠ 0 ∧ Failure bytes listBase listLen⌝)) **
          initStable newSp listBase outPtr oldCount saved) h) :=
        ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, hf0⟩, hstable⟩
      have hall' : (⌜status ≠ 0 ∧ Failure bytes listBase listLen⌝ **
          ((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
           ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status)) **
           initStable newSp listBase outPtr oldCount saved)) h := by
        xperm_hyp hall
      xperm_hyp hall') harms

theorem initCallDispatchExact
    (newSp listBase listLenW outPtr oldCount : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (h_listLenW : listLenW = BitVec.ofNat 64 listLen)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsNBranchWithin 85 (B + 32) code
      (((.x1 ↦ᵣ saved.ra) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
         (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes)) **
       initStable newSp listBase outPtr oldCount saved)
      [(B + 48, initLoopPost newSp listBase outPtr oldCount saved bytes listLen),
       (B + 84, rejected newSp listBase outPtr oldCount saved bytes listLen)] := by
  subst listLenW
  have hcall := initCallExact listBase bytes listLen outPtr v5 v6 v7 v28 v29 v30
    v31 saved.ra h_align h_slack h_over h_valid
  have hcallF := cpsTripleWithin_frameR
    (initStable newSp listBase outPtr oldCount saved) (by pcf) hcall
  have hcallN : cpsTripleWithin 82 (B + 32) (B + 36) code _
      (((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
        initNormalized listBase bytes listLen) **
       initStable newSp listBase outPtr oldCount saved) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => by
      have hn := initOutcome_to_normalized listBase bytes listLen (by omega)
        h_slack h_over
      have hp' := sepConj_mono_left (sepConj_mono_right hn) h hp
      xperm_hyp hp') hcallF
  exact cpsNBranchWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_cpsNBranchWithin_perm_same_cr (fun h hp => by
      xperm_hyp hp) hcallN
      (initNormalizedDispatch newSp listBase outPtr oldCount saved bytes listLen))


end EvmAsm.Codegen.RlpListCountItemsSAsm
