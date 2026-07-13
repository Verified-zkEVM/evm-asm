import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmRound

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

def joined (newSp listBase outPtr : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ status result v1 v8 v9 v18 v19 v11 v12 : Word,
    (((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ v1) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** savedFrame newSp saved **
      (outPtr ↦ₘ result) ** (.x10 ↦ᵣ status) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes) **
     ⌜Result bytes listBase listLen status result⌝) h

def scratchExact (v5 v6 v7 v28 v29 v30 v31 : Word) : Assertion :=
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x28 ↦ᵣ v28) **
  (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)

def scratchOwned : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31

theorem scratchExact_implies_owned (v5 v6 v7 v28 v29 v30 v31 : Word) :
    ∀ h, scratchExact v5 v6 v7 v28 v29 v30 v31 h →
      scratchOwned h := by
  intro h hp
  unfold scratchExact at hp
  unfold scratchOwned
  exact sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x28)
          (sepConj_mono (regIs_implies_regOwn .x29)
            (sepConj_mono (regIs_implies_regOwn .x30)
              (regIs_implies_regOwn .x31)))))) h hp

theorem successTail (newSp listBase outPtr oldCount endPtr : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen count : Nat)
    (v5 v6 v7 v11 v12 v28 v29 v30 v31 raW : Word)
    (h_success : Success bytes listBase listLen count)
    (h_count : count < 2 ^ 64) :
    cpsTripleWithin 3 (B + 72) (B + 92) code
      ((.x18 ↦ᵣ endPtr) ** stableRest newSp listBase outPtr oldCount saved **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ raW) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (.x10 ↦ᵣ endPtr) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** (.x19 ↦ᵣ BitVec.ofNat 64 count))
      (joined newSp listBase outPtr saved bytes listLen) := by
  have hsd0 := sd_spec_gen_within .x9 .x19 outPtr (BitVec.ofNat 64 count)
    oldCount (0 : BitVec 12) (B + 72)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show outPtr + (0 : Word) = outPtr from by bv_omega,
      show B + 72 + 4 = B + 76 from by decide] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 72) rlpListCountItems_prog 18
      (.SD .x9 .x19 (0 : BitVec 12)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) hsd0
  have hli0 := li_spec_gen_within .x10 endPtr (0 : Word) (B + 76) (by decide)
  have hli := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 76) rlpListCountItems_prog 19
      (.LI .x10 (0 : Word)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) hli0
  have hj0 := jal_x0_spec_gen_within (12 : BitVec 21) (B + 80)
  rw [show B + 80 + signExtend21 (12 : BitVec 21) = B + 92 from by decide] at hj0
  have hj := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 80) rlpListCountItems_prog 20
      (.JAL .x0 (12 : BitVec 21)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) hj0
  let F0 : Assertion :=
    (.x18 ↦ᵣ endPtr) **
    ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x1 ↦ᵣ raW) **
     savedFrame newSp saved ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
     (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** (.x10 ↦ᵣ endPtr) ** (.x11 ↦ᵣ v11) **
     (.x12 ↦ᵣ v12))
  have hsF := cpsTripleWithin_frameR F0 (by dsimp [F0]; pcf) hsd
  let F1 : Assertion :=
    (.x18 ↦ᵣ endPtr) **
    ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outPtr) **
     (.x19 ↦ᵣ BitVec.ofNat 64 count) ** savedFrame newSp saved **
     (outPtr ↦ₘ BitVec.ofNat 64 count) ** (.x1 ↦ᵣ raW) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
     (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
  have hlF := cpsTripleWithin_frameR F1 (by dsimp [F1]; pcf) hli
  let F2 : Assertion :=
    (.x18 ↦ᵣ endPtr) **
    ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outPtr) **
     (.x19 ↦ᵣ BitVec.ofNat 64 count) ** savedFrame newSp saved **
     (outPtr ↦ₘ BitVec.ofNat 64 count) ** (.x1 ↦ᵣ raW) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
     (.x31 ↦ᵣ v31) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)
  have hjF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (0 : Word)) ** F2)
    (by dsimp [F2]; pcf) hj
  rw [sepConj_emp_left'] at hjF
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold F0 at hp
    unfold F1
    xperm_hyp hp) hsF hlF
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold F1 at hp
    unfold F2
    xperm_hyp hp) h01 hjF
  exact cpsTripleWithin_weaken (fun _ hp => by
    unfold stableRest at hp
    unfold F0
    xperm_hyp hp) (fun h hp => by
    unfold joined
    refine ⟨0, BitVec.ofNat 64 count, raW, listBase, outPtr, endPtr,
      BitVec.ofNat 64 count, v11, v12, ?_⟩
    refine (sepConj_pure_right h).2 ⟨?_, .ok count h_count h_success⟩
    unfold F2 at hp
    have hpGrouped : ((scratchExact v5 v6 v7 v28 v29 v30 v31 **
        ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raW) ** (.x8 ↦ᵣ listBase) **
         (.x9 ↦ᵣ outPtr) ** (.x18 ↦ᵣ endPtr) **
         (.x19 ↦ᵣ BitVec.ofNat 64 count) ** savedFrame newSp saved **
         (outPtr ↦ₘ BitVec.ofNat 64 count) ** (.x10 ↦ᵣ (0 : Word)) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)) h) := by
      unfold scratchExact
      xperm_hyp hp
    have hpOwn := sepConj_mono
      (scratchExact_implies_owned v5 v6 v7 v28 v29 v30 v31)
      (fun _ x => x) h hpGrouped
    unfold scratchOwned at hpOwn
    xperm_hyp hpOwn) h012

theorem failureTailConcrete
    (newSp listBase outPtr oldCount v10 v11 v12 workEnd countW raW : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (h_failure : Failure bytes listBase listLen) :
    cpsTripleWithin 2 (B + 84) (B + 92) code
      ((stableRest newSp listBase outPtr oldCount saved **
        ((.x18 ↦ᵣ workEnd) ** (.x19 ↦ᵣ countW))) **
       ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ raW) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes))
      (joined newSp listBase outPtr saved bytes listLen) := by
  have hsd0 := sd_spec_gen_within .x9 .x0 outPtr (0 : Word) oldCount
    (0 : BitVec 12) (B + 84)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show outPtr + (0 : Word) = outPtr from by bv_omega,
      show B + 84 + 4 = B + 88 from by decide] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 84) rlpListCountItems_prog 21
      (.SD .x9 .x0 (0 : BitVec 12)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) hsd0
  have hli0 := li_spec_gen_within .x10 v10 (1 : Word) (B + 88) (by decide)
  have hli := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 88) rlpListCountItems_prog 22
      (.LI .x10 (1 : Word)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) hli0
  let F0 : Assertion :=
    (.x18 ↦ᵣ workEnd) ** (.x19 ↦ᵣ countW) **
    ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x1 ↦ᵣ raW) **
     savedFrame newSp saved ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
     (.x12 ↦ᵣ v12) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     bytesRegion listBase bytes)
  have hsF := cpsTripleWithin_frameR F0 (by dsimp [F0]; pcf) hsd
  let F1 : Assertion :=
    (.x18 ↦ᵣ workEnd) ** (.x19 ↦ᵣ countW) **
    ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outPtr) **
     (.x1 ↦ᵣ raW) ** savedFrame newSp saved ** (outPtr ↦ₘ (0 : Word)) **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x5 ** regOwn .x6 **
     regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
     regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)
  have hlF := cpsTripleWithin_frameR F1 (by dsimp [F1]; pcf) hli
  have hc := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold F0 at hp
    unfold F1
    xperm_hyp hp) hsF hlF
  exact cpsTripleWithin_weaken (fun _ hp => by
    unfold stableRest at hp
    unfold F0
    xperm_hyp hp) (fun h hp => by
    unfold joined
    refine ⟨1, 0, raW, listBase, outPtr, workEnd, countW, v11, v12, ?_⟩
    refine (sepConj_pure_right h).2 ⟨?_, .fail h_failure⟩
    unfold F1 at hp
    xperm_hyp hp) hc

theorem failureTail (newSp listBase outPtr oldCount : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) :
    cpsTripleWithin 2 (B + 84) (B + 92) code
      (rejected newSp listBase outPtr oldCount saved bytes listLen)
      (joined newSp listBase outPtr saved bytes listLen) := by
  unfold rejected
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun status => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v10 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v11 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v12 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun workEnd => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun countW => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun raW => ?_)
  let Rest : Assertion :=
    ((stableRest newSp listBase outPtr oldCount saved **
      ((.x18 ↦ᵣ workEnd) ** (.x19 ↦ᵣ countW))) **
     ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ raW) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes))
  have ht : cpsTripleWithin 2 (B + 84) (B + 92) code
      (⌜status ≠ 0 ∧ Failure bytes listBase listLen⌝ ** Rest)
      (joined newSp listBase outPtr saved bytes listLen) :=
    cpsTripleWithin_pure_pre (fun hpure =>
      cpsTripleWithin_weaken (fun h hp => by
        unfold Rest at hp
        xperm_hyp hp) (fun _ hp => hp)
        (failureTailConcrete newSp listBase outPtr oldCount v10 v11 v12 workEnd
          countW raW saved bytes listLen hpure.2))
  exact cpsTripleWithin_weaken (fun h hp => by
    unfold Rest
    xperm_hyp hp) (fun _ hp => hp) ht

theorem selectedTail (newSp listBase outPtr oldCount : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) :
    cpsTripleWithin 3 (B + 72) (B + 92) code
      (selected newSp listBase outPtr oldCount saved bytes listLen)
      (joined newSp listBase outPtr saved bytes listLen) := by
  unfold selected
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun endPtr => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun count => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v5 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v6 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v7 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v11 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v12 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v28 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v29 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v30 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v31 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun raW => ?_)
  let Rest : Assertion :=
    ((.x18 ↦ᵣ endPtr) ** stableRest newSp listBase outPtr oldCount saved **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
     (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ raW) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** (.x10 ↦ᵣ endPtr) ** (.x11 ↦ᵣ v11) **
     (.x12 ↦ᵣ v12) ** (.x19 ↦ᵣ BitVec.ofNat 64 count))
  have ht : cpsTripleWithin 3 (B + 72) (B + 92) code
      (⌜Success bytes listBase listLen count ∧ count < 2 ^ 64⌝ ** Rest)
      (joined newSp listBase outPtr saved bytes listLen) :=
    cpsTripleWithin_pure_pre (fun hpure =>
      cpsTripleWithin_weaken (fun h hp => by
        unfold Rest at hp
        xperm_hyp hp) (fun _ hp => hp)
        (successTail newSp listBase outPtr oldCount endPtr saved bytes listLen
          count v5 v6 v7 v11 v12 v28 v29 v30 v31 raW hpure.1 hpure.2))
  exact cpsTripleWithin_weaken (fun h hp => by
    unfold Rest
    xperm_hyp hp) (fun _ hp => hp) ht

theorem scanAndTails (newSp listBase outPtr oldCount : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (93 * (listLen + 1) + 3) (B + 48) (B + 92) code
      (initLoopPost newSp listBase outPtr oldCount saved bytes listLen)
      (joined newSp listBase outPtr saved bytes listLen) := by
  have hscan := scanFromInit newSp listBase outPtr oldCount saved bytes listLen
    h_align h_slack h_over h_valid
  exact cpsNBranchWithin_merge hscan (fun ex hmem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hsel | hfail
    · subst ex
      exact selectedTail newSp listBase outPtr oldCount saved bytes listLen
    · subst ex
      exact cpsTripleWithin_mono_nSteps (by omega)
        (failureTail newSp listBase outPtr oldCount saved bytes listLen))

theorem epilogueOwned (sp0 newSp : Word) (saved : Saved)
    (F : Assertion) (h_F : F.pcFree)
    (h_newSp : newSp = sp0 + signExtend12 (-48 : BitVec 12))
    (h_ret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin 7 (B + 92) saved.ra code
      (((.x2 ↦ᵣ newSp) ** regsOwnAt countFrame ** savedFrame newSp saved) ** F)
      (((.x2 ↦ᵣ sp0) ** regsAt countFrame (savedVals saved) **
        savedFrame newSp saved) ** F) := by
  have hl0 := loadSeq_spec_own countFrame newSp (savedVals saved)
    (B + 92) (by decide) (by decide)
  have hlMono : ∀ a i,
      CodeReq.ofProg (B + 92) (loadProg countFrame) a = some i → code a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub B (B + 92) rlpListCountItems_prog
      (loadProg countFrame) 23 (by bv_omega) rfl
      (by rw [total_length]; simp [countFrame])
      (by rw [total_length]; norm_num) a i h_mem
  have hl := cpsTripleWithin_extend_code hlMono hl0
  rw [show B + 92 + BitVec.ofNat 64 (4 * countFrame.length) = B + 112 from by
    simp [countFrame]; bv_omega] at hl
  rw [frameSlotsSaved_countFrame] at hl
  have hlF := cpsTripleWithin_frameR F h_F hl
  have ha0 := addi_spec_gen_same_within .x2 newSp (48 : BitVec 12) (B + 112)
    (by decide)
  rw [show newSp + signExtend12 (48 : BitVec 12) = sp0 from by
    rw [h_newSp]
    exact sext_frameRestore sp0 (-48 : BitVec 12) (48 : BitVec 12) (by decide)] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 112) rlpListCountItems_prog 28
      (.ADDI .x2 .x2 (48 : BitVec 12)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt countFrame (savedVals saved) ** savedFrame newSp saved ** F)
    (by unfold savedFrame; pcf; exact h_F) ha
  have hr0 := EvmAsm.Evm64.ret_spec_within' (B + 116) saved.ra
  rw [h_ret] at hr0
  have hr := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 116) rlpListCountItems_prog 29
      (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) hr0
  have hrF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
      (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
      savedFrame newSp saved) ** F) (by
        unfold savedFrame
        pcf
        exact h_F) hr
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlF haF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_countFrame] at hp
    xperm_hyp hp) h12 hrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hp => by
    rw [regsAt_countFrame]
    xperm_hyp hp) h123

def finalResult (sp0 newSp listBase outPtr : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ status result v11 v12 : Word,
    ((((.x2 ↦ᵣ sp0) ** regsAt countFrame (savedVals saved) **
       savedFrame newSp saved) **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
       regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (outPtr ↦ₘ result))) **
     ⌜Result bytes listBase listLen status result⌝) h

theorem joinToFinal (sp0 newSp listBase outPtr : Word) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (h_newSp : newSp = sp0 + signExtend12 (-48 : BitVec 12))
    (h_ret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin 7 (B + 92) saved.ra code
      (joined newSp listBase outPtr saved bytes listLen)
      (finalResult sp0 newSp listBase outPtr saved bytes listLen) := by
  unfold joined
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun status => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun result => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v1 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v8 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v9 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v18 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v19 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v11 => ?_)
  refine RlpListNthItemSAsm.cpsTripleWithin_exists_assertion (fun v12 => ?_)
  let F : Assertion :=
    ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** (outPtr ↦ₘ result) **
     ⌜Result bytes listBase listLen status result⌝)
  have he := epilogueOwned sp0 newSp saved F (by dsimp [F]; pcf)
    h_newSp h_ret
  exact cpsTripleWithin_weaken (fun h hp => by
    let Rest : Assertion :=
      (.x2 ↦ᵣ newSp) ** savedFrame newSp saved ** F
    have hpGrouped : ((((.x1 ↦ᵣ v1) **
        ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
         (.x19 ↦ᵣ v19))) ** Rest) h) := by
      unfold Rest F
      xperm_hyp hp
    have hpX1 : (((.x1 ↦ᵣ v1) **
        (((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
          (.x19 ↦ᵣ v19)) ** Rest)) h) := by
      xperm_hyp hpGrouped
    have hpX1Own := sepConj_mono_left (regIs_implies_regOwn .x1) h hpX1
    have hpReady : (((regOwn .x1 ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19)) ** Rest) h) := by
      xperm_hyp hpX1Own
    have hpRegs := sepConj_mono_left
      (countFrameRegs_implies_owned v8 v9 v18 v19) h hpReady
    unfold Rest at hpRegs
    xperm_hyp hpRegs) (fun h hp => by
    unfold finalResult
    refine ⟨status, result, v11, v12, ?_⟩
    unfold F at hp
    xperm_hyp hp) he

#print axioms scratchExact_implies_owned
#print axioms successTail
#print axioms failureTailConcrete
#print axioms failureTail
#print axioms selectedTail
#print axioms scanAndTails
#print axioms epilogueOwned
#print axioms joinToFinal

end EvmAsm.Codegen.RlpListCountItemsSAsm
