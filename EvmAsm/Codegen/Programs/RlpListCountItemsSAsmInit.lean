
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmCode

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

structure Saved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word

def countFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32)]

def savedVals (saved : Saved) : Reg → Word
  | .x1 => saved.ra
  | .x8 => saved.s0
  | .x9 => saved.s1
  | .x18 => saved.s2
  | .x19 => saved.s3
  | _ => 0

theorem countFrame_length : countFrame.length = 5 := by decide

theorem regsAt_countFrame (saved : Saved) :
    regsAt countFrame (savedVals saved) =
      ((.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
       (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3)) := by
  simp [countFrame, regsAt, savedVals]
  rw [sepConj_emp_right']

def savedFrame (newSp : Word) (saved : Saved) : Assertion :=
  (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) **
  ((newSp + 16) ↦ₘ saved.s1) ** ((newSp + 24) ↦ₘ saved.s2) **
  ((newSp + 32) ↦ₘ saved.s3)

theorem frameSlotsSaved_countFrame (newSp : Word) (saved : Saved) :
    frameSlotsSaved countFrame newSp (savedVals saved) = savedFrame newSp saved := by
  simp [countFrame, frameSlotsSaved, savedFrame, savedVals,
    sepConj_emp_right', signExtend12]

theorem countFrameRegs_implies_owned (s0 s1 s2 s3 : Word) : ∀ h,
    (regOwn .x1 ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
      (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) h → regsOwnAt countFrame h := by
  intro h h_regs
  unfold regsOwnAt countFrame
  simp only [List.foldr_cons, List.foldr_nil, sepConj_emp_right']
  exact sepConj_mono (fun _ h_ra => h_ra)
    (sepConj_mono (regIs_implies_regOwn .x8)
      (sepConj_mono (regIs_implies_regOwn .x9)
        (sepConj_mono (regIs_implies_regOwn .x18)
          (regIs_implies_regOwn .x19)))) h h_regs

theorem setupMoves (listBase outPtr v8 v9 : Word) :
    cpsTripleWithin 2 (B + 24) (B + 32) code
      ((.x8 ↦ᵣ v8) ** (.x10 ↦ᵣ listBase) **
       (.x9 ↦ᵣ v9) ** (.x12 ↦ᵣ outPtr))
      ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) **
       (.x9 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr)) := by
  have h0 := mv_spec_gen_within .x8 .x10 listBase v8 (B + 24) (by decide)
  have h1 := mv_spec_gen_within .x9 .x12 outPtr v9 (B + 28) (by decide)
  have l0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 24) rlpListCountItems_prog 6 (.MV .x8 .x10)
      (by bv_omega) (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) h0
  have l1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 28) rlpListCountItems_prog 7 (.MV .x9 .x12)
      (by bv_omega) (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) h1
  have s0 := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v9) ** (.x12 ↦ᵣ outPtr)) (by pcf) l0
  have s1 := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase)) (by pcf) l1
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s0 s1
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) h01

def entryRest (listBase listLenW outPtr oldCount : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ outPtr) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion listBase bytes ** (outPtr ↦ₘ oldCount)

def setupPost (newSp listBase listLenW outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ saved.ra) **
  (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outPtr) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  savedFrame newSp saved ** entryRest listBase listLenW outPtr oldCount bytes

theorem wrapperPrologue (sp0 newSp listBase listLenW outPtr oldCount : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (h_newSp : newSp = sp0 + signExtend12 (-48 : BitVec 12)) :
    cpsTripleWithin 8 B (B + 32) code
      ((.x2 ↦ᵣ sp0) ** regsAt countFrame (savedVals saved) **
       frameSlotsOwn countFrame newSp **
       entryRest listBase listLenW outPtr oldCount bytes)
      (setupPost newSp listBase listLenW outPtr oldCount saved bytes) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-48 : BitVec 12) B (by decide)
  rw [← h_newSp] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B B rlpListCountItems_prog 0
      (.ADDI .x2 .x2 (-48 : BitVec 12)) rfl
      (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt countFrame (savedVals saved) ** frameSlotsOwn countFrame newSp **
      entryRest listBase listLenW outPtr oldCount bytes) (by pcf) ha
  have hs0 := storeSeq_spec countFrame newSp (savedVals saved) (B + 4) (by decide)
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (B + 4) (storeProg countFrame) a = some i → code a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub B (B + 4) rlpListCountItems_prog
      (storeProg countFrame) 1 (by bv_omega) rfl
      (by rw [total_length]; simp [countFrame])
      (by rw [total_length]; norm_num) a i h_mem
  have hs := cpsTripleWithin_extend_code h_storeMono hs0
  rw [show B + 4 + BitVec.ofNat 64 (4 * countFrame.length) = B + 24 from by
    simp [countFrame]; bv_omega] at hs
  have hsF := cpsTripleWithin_frameR
    (entryRest listBase listLenW outPtr oldCount bytes) (by pcf) hs
  have hm0 := setupMoves listBase outPtr saved.s0 saved.s1
  have hmF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ saved.ra) **
     (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) ** savedFrame newSp saved **
     ((.x11 ↦ᵣ listLenW) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
      (outPtr ↦ₘ oldCount))) (by pcf) hm0
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hsF
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_countFrame, frameSlotsSaved_countFrame] at hp
    unfold entryRest at hp
    xperm_hyp hp) h01 hmF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by unfold setupPost entryRest; xperm_hyp hp) h012

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

theorem nthFailure_to_countFailure {bytes : List (BitVec 8)} {base : Word}
    {listLen index : Nat}
    (h_failure : RlpListNthItemSAsm.Failure bytes base listLen index) :
    Failure bytes base listLen := by
  cases h_failure with
  | init h_invalid => exact .init h_invalid
  | walk cursorOff count off endPtr h_list _ h_prefix h_fail =>
      exact .walk cursorOff count off endPtr h_list h_prefix h_fail

def initStable (newSp listBase outPtr oldCount : Word) (saved : Saved) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outPtr) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) ** savedFrame newSp saved **
  (outPtr ↦ₘ oldCount)

def initCommon (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (B + 36)) ** bytesRegion listBase bytes

def initNormalized (listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) : Assertion := fun h =>
  (∃ cursorOff endPtr,
    (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
      (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      ⌜RlpListNthItemSAsm.StrictListPayload bytes listBase listLen
        cursorOff endPtr⌝) h)) ∨
  (∃ status cursor endPtr,
    (((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
      ⌜status ≠ 0 ∧ Failure bytes listBase listLen⌝) h))

theorem initOutcome_to_normalized (listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (hoff : 0 < bytes.length)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64) : ∀ h,
    RlpListNthItemSAsm.initOutcome listBase bytes listLen hoff h →
      initNormalized listBase bytes listLen h := by
  intro h h_outcome
  have h_norm := RlpListNthItemSAsm.initOutcome_to_normalized
    listBase bytes listLen 0 hoff (by omega) (by omega) h_over h h_outcome
  unfold RlpListNthItemSAsm.initNormalized at h_norm
  unfold initNormalized
  rcases h_norm with h_success | h_failure
  · exact Or.inl h_success
  · rcases h_failure with ⟨status, cursor, endPtr, h_body⟩
    refine Or.inr ⟨status, cursor, endPtr, ?_⟩
    exact RlpListNthItemSAsm.threeRegs_pure_mono
      (fun hp => ⟨hp.1, nthFailure_to_countFailure hp.2⟩) h h_body

theorem initCallExact (listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (outPtr : Word)
    (v5 v6 v7 v28 v29 v30 v31 oldRa : Word)
    (h_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ bytes.length)
    (h_over : listBase.toNat + bytes.length < 2 ^ 64)
    (h_valid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 82 (B + 32) (B + 36) code
      ((.x1 ↦ᵣ oldRa) **
       ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) **
        (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
        (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase bytes))
      ((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
        RlpListNthItemSAsm.initOutcome listBase bytes listLen (by omega)) := by
  have hoff : 0 < bytes.length := by omega
  have hwi := rlp_walk_init_spec_within WI listBase (B + 36)
    (BitVec.ofNat 64 listLen) outPtr v5 v6 v7 v28 v29 v30 v31 bytes 0
    h_align hoff (by omega) (h_valid 0 hoff)
    (fun h_f8 _ => by
      have h_lo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun h_f8 _ => by
      have h_lo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      omega)
    (fun h_f8 _ => by
      intro k hk
      have h_lo : ((bytes[0]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.not_ult_le h_f8
        have h3 := (bytes[0]'hoff).isLt
        bv_omega
      exact h_valid _ (by omega))
  rw [show listBase + BitVec.ofNat 64 0 = listBase from by bv_omega] at hwi
  let Prest : Assertion :=
    (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLen) **
    (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
    (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
    (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion listBase bytes
  let Q : Assertion :=
    (initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
      RlpListNthItemSAsm.initOutcome listBase bytes listLen hoff
  have hwi' : cpsTripleWithin 81 WI ((B + 36) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 36)) ** Prest) Q :=
    cpsTripleWithin_weaken
      (fun h hp => by unfold Prest at hp; xperm_hyp hp)
      (fun h hp => by
        unfold Q initCommon RlpListNthItemSAsm.initOutcome
        simp only [Nat.zero_add] at hp ⊢
        xperm_hyp hp) hwi
  have hc := callWalkInit oldRa (by unfold Prest; pcf) hwi'
  simpa [Prest, Q] using hc

end EvmAsm.Codegen.RlpListCountItemsSAsm
