import EvmAsm.Codegen.Programs.RlpListNthItemSAsmScan

namespace EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

def preTailRejected (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h =>
    scanRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved bytes
      listLen index h ∨
    initRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved bytes
      listLen index h

/-- Exact-register entry through initialization and the complete strict scan. -/
theorem initAndScanExact
    (newSp listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsNBranchWithin (85 + 93 * (index + 2)) (B + 48) code
      (((.x1 ↦ᵣ saved.ra) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
         (.x12 ↦ᵣ indexW) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes)) **
       (initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
        (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)))
      [(B + 88, scanSelected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index),
       (B + 112, preTailRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index)] := by
  have hi := initCallDispatchExact newSp listBase listLenW indexW offsetPtr lenPtr
    oldOffset oldLen saved bytes listLen index v5 v6 v7 v28 v29 v30 v31
    hlistLenW hsalign hslack hover hvalid
  have hs := scanFromInit newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
    saved bytes listLen index hindexW hindex hsalign hslack hover hvalid
  have hc := cpsNBranchWithin_extend_head_nbranch hi hs
  exact cpsNBranchWithin_weaken_posts hc (by
    intro ex hex
    simp only [List.mem_append, List.mem_cons] at hex
    rcases hex with (rfl | rfl | hf) | (rfl | hf)
    · exact ⟨(B + 88, scanSelected newSp listBase indexW offsetPtr lenPtr oldOffset
          oldLen saved bytes listLen index), by simp, rfl, fun _ hp => hp⟩
    · refine ⟨(B + 112, preTailRejected newSp listBase indexW offsetPtr lenPtr
          oldOffset oldLen saved bytes listLen index), by simp, rfl, ?_⟩
      intro h hp
      unfold preTailRejected
      exact Or.inl hp
    · exact absurd hf List.not_mem_nil
    · refine ⟨(B + 112, preTailRejected newSp listBase indexW offsetPtr lenPtr
          oldOffset oldLen saved bytes listLen index), by simp, rfl, ?_⟩
      intro h hp
      unfold preTailRejected
      exact Or.inr hp
    · exact absurd hf List.not_mem_nil)

#print axioms initAndScanExact

/-- Concrete success tail (wrapper slots 22--27): compute the content offset,
    update both ABI output cells, set status zero, and jump to the restore join. -/
theorem selectedTailCore (listBase next len offsetPtr lenPtr oldOffset oldLen v5 : Word) :
    cpsTripleWithin 6 (B + 88) (B + 116) code
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x5 ↦ᵣ v5) **
       (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
       (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
       (.x5 ↦ᵣ (next - len - listBase)) ** (.x8 ↦ᵣ listBase) **
       (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
       (offsetPtr ↦ₘ (next - len - listBase)) ** (lenPtr ↦ₘ len)) := by
  have h0 := sub_spec_gen_within .x5 .x10 .x12 next len v5 (B + 88) (by decide)
  have h0' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 88) rlpListNthItem_prog 22
      (.SUB .x5 .x10 .x12) (by bv_omega) (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) h0
  have h1 := sub_spec_gen_rd_eq_rs1_within .x5 .x8 (next - len) listBase
    (B + 92) (by decide)
  have h1' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 92) rlpListNthItem_prog 23
      (.SUB .x5 .x5 .x8) (by bv_omega) (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) h1
  have h2 := sd_spec_gen_within .x18 .x5 offsetPtr (next - len - listBase)
    oldOffset (0 : BitVec 12) (B + 96)
  have h2' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 96) rlpListNthItem_prog 24
      (.SD .x18 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) h2
  have h3 := sd_spec_gen_within .x19 .x12 lenPtr len oldLen
    (0 : BitVec 12) (B + 100)
  have h3' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 100) rlpListNthItem_prog 25
      (.SD .x19 .x12 (0 : BitVec 12)) (by bv_omega) (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) h3
  have h4 := li_spec_gen_within .x10 next (0 : Word) (B + 104) (by decide)
  have h4' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 104) rlpListNthItem_prog 26
      (.LI .x10 (0 : Word)) (by bv_omega) (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) h4
  have h5 := jal_x0_spec_gen_within (8 : BitVec 21) (B + 108)
  rw [show B + 108 + signExtend21 (8 : BitVec 21) = B + 116 by decide] at h5
  have h5' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 108) rlpListNthItem_prog 27
      (.JAL .x0 (8 : BitVec 21)) (by bv_omega) (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) h5
  runBlock h0' h1' h2' h3' h4' h5'

#print axioms selectedTailCore

/-- Concrete failure tail (wrapper slot 28): set the ABI status to one. -/
theorem rejectedTailCore (oldA0 : Word) :
    cpsTripleWithin 1 (B + 112) (B + 116) code
      (.x10 ↦ᵣ oldA0) (.x10 ↦ᵣ (1 : Word)) := by
  have h0 := li_spec_gen_within .x10 oldA0 (1 : Word) (B + 112) (by decide)
  exact cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 112) rlpListNthItem_prog 28
      (.LI .x10 (1 : Word)) (by bv_omega) (by rw [total_length]; norm_num) rfl
      (by rw [total_length]; norm_num)) h0

#print axioms rejectedTailCore

/-- Shared ABI epilogue (slots 29--37), parameterized by arbitrary current
    values of the seven restored registers and an arbitrary framed result. -/
theorem epilogueOwned (sp0 newSp : Word) (saved : Saved)
    (F : Assertion) (hF : F.pcFree)
    (hnewSp : newSp = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin 9 (B + 116) saved.ra code
      (((.x2 ↦ᵣ newSp) ** regsOwnAt listNthFrame **
        savedFrame newSp saved) ** F)
      (((.x2 ↦ᵣ sp0) ** regsAt listNthFrame (savedVals saved) **
        savedFrame newSp saved) ** F) := by
  have hl0 := loadSeq_spec_own listNthFrame newSp (savedVals saved)
    (B + 116) (by decide) (by decide)
  have hlMono : ∀ a i,
      CodeReq.ofProg (B + 116) (loadProg listNthFrame) a = some i → code a = some i := by
    intro a i hmem
    exact CodeReq.ofProg_mono_sub B (B + 116) rlpListNthItem_prog
      (loadProg listNthFrame) 29 (by bv_omega) (by rfl)
      (by rw [total_length]; simp [listNthFrame])
      (by rw [total_length]; norm_num) a i hmem
  have hl := cpsTripleWithin_extend_code hlMono hl0
  rw [show B + 116 + BitVec.ofNat 64 (4 * listNthFrame.length) = B + 144 from by
    simp [listNthFrame]; bv_omega] at hl
  rw [frameSlotsSaved_listNthFrame] at hl
  have hlF := cpsTripleWithin_frameR F hF hl
  have hd0 := addi_spec_gen_same_within .x2 newSp (64 : BitVec 12) (B + 144)
    (by decide)
  rw [show newSp + signExtend12 (64 : BitVec 12) = sp0 from by
    rw [hnewSp]
    exact sext_frameRestore sp0 (-64 : BitVec 12) (64 : BitVec 12) (by decide)] at hd0
  have hd := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 144) rlpListNthItem_prog 36
      (.ADDI .x2 .x2 (64 : BitVec 12)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl (by rw [total_length]; norm_num)) hd0
  have hdF := cpsTripleWithin_frameR
    (regsAt listNthFrame (savedVals saved) ** savedFrame newSp saved ** F)
    (by unfold savedFrame; pcf; assumption) hd
  have hr0 := EvmAsm.Evm64.ret_spec_within' (B + 148) saved.ra
  rw [hret] at hr0
  have hr := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 148) rlpListNthItem_prog 37
      (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega)
      (by rw [total_length]; norm_num) rfl (by rw [total_length]; norm_num)) hr0
  have hrF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
      (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
      (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
      savedFrame newSp saved) ** F) (by
        unfold savedFrame
        pcf
        assumption) hr
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlF hdF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_listNthFrame] at hp
    xperm_hyp hp) h12 hrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hp => by
    rw [regsAt_listNthFrame]
    xperm_hyp hp) h123

#print axioms epilogueOwned

def joinResult (newSp listBase _indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ status offset len v11 v12,
    ((((.x2 ↦ᵣ newSp) ** regsOwnAt listNthFrame ** savedFrame newSp saved) **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
       (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))) **
      ⌜Result bytes listBase listLen index oldOffset oldLen status offset len⌝) h

def selectedExpanded (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (index cursorOff : Nat) : Assertion :=
  fun h => ∃ next len : Word,
    ((loopFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved bytes **
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
       (.x21 ↦ᵣ BitVec.ofNat 64 index)) ** (regOwn .x13 ** regOwn .x14)) **
     ⌜StrictNthItem bytes listBase endPtr index cursorOff next len⌝) h

/-- Adapt the selected scan station through its concrete stores to the genuine
    semantic success result at the shared restore join. -/
theorem selectedToJoin
    (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 6 (B + 88) (B + 116) code
      (scanSelected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index)
      (joinResult newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index) := by
  unfold scanSelected
  refine cpsTripleWithin_exists_assertion (fun (cursorOff : Nat) => ?_)
  refine cpsTripleWithin_exists_assertion (fun (endPtr : Word) => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝ **
      (loopSelected newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes index cursorOff ** (regOwn .x13 ** regOwn .x14)))
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hlist => ?_)
  refine cpsTripleWithin_weaken
    (P := selectedExpanded newSp listBase indexW offsetPtr lenPtr endPtr oldOffset
      oldLen saved bytes index cursorOff)
    (P' := loopSelected newSp listBase indexW offsetPtr lenPtr endPtr oldOffset
      oldLen saved bytes index cursorOff ** (regOwn .x13 ** regOwn .x14))
    (fun h (hp : (loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes index cursorOff **
        (regOwn .x13 ** regOwn .x14)) h) => by
      show selectedExpanded newSp listBase indexW offsetPtr lenPtr endPtr oldOffset
        oldLen saved bytes index cursorOff h
      unfold selectedExpanded
      unfold loopSelected at hp
      obtain ⟨h1, h2, hd, hu, hloop, hregs⟩ := hp
      obtain ⟨next, len, hbody⟩ := hloop
      refine ⟨next, len, ?_⟩
      let Hcombined : Assertion :=
        ((loopFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
            saved bytes **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
           (.x21 ↦ᵣ BitVec.ofNat 64 index))) **
         ⌜StrictNthItem bytes listBase endPtr index cursorOff next len⌝) **
        (regOwn .x13 ** regOwn .x14)
      have hcombined : Hcombined h := by
        exact ⟨h1, h2, hd, hu, hbody, hregs⟩
      unfold Hcombined at hcombined
      xperm_hyp hcombined) (fun _ hq => hq) ?_
  unfold selectedExpanded
  refine cpsTripleWithin_exists_assertion (fun (next : Word) => ?_)
  refine cpsTripleWithin_exists_assertion (fun (len : Word) => ?_)
  let Pitem : Assertion :=
    ⌜StrictNthItem bytes listBase endPtr index cursorOff next len⌝ **
    (loopFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved
      bytes **
     ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
      (.x21 ↦ᵣ BitVec.ofNat 64 index)) ** (regOwn .x13 ** regOwn .x14))
  refine cpsTripleWithin_weaken
    (P := Pitem)
    (fun h hp => by unfold Pitem; xperm_hyp hp) (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hnth => ?_)
  let F : Assertion :=
    (.x20 ↦ᵣ endPtr) ** (.x9 ↦ᵣ indexW) ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
    (.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
    (.x11 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ BitVec.ofNat 64 index) **
    (regOwn .x13 ** regOwn .x14)
  let Pcore : Assertion :=
    (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
    (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
    (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen)
  let Qcore : Assertion :=
    (.x10 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
    (.x5 ↦ᵣ (next - len - listBase)) ** (.x8 ↦ᵣ listBase) **
    (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
    (offsetPtr ↦ₘ (next - len - listBase)) ** (lenPtr ↦ₘ len)
  have hfamily : ∀ v5, cpsTripleWithin 6 (B + 88) (B + 116) code
      (Pcore ** (.x5 ↦ᵣ v5)) Qcore := by
    intro v5
    exact cpsTripleWithin_weaken (fun h hp => by unfold Pcore at hp; xperm_hyp hp)
      (fun h hq => by unfold Qcore; exact hq)
      (selectedTailCore listBase next len offsetPtr lenPtr oldOffset oldLen v5)
  have hcOwn0 := cpsTripleWithin_of_forall_regIs_to_regOwn hfamily
  have hcOwn := cpsTripleWithin_weaken
    (P := Pcore ** regOwn .x5)
    (P' := (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** regOwn .x5 **
      (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
      (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))
    (fun h hp => by
      unfold Pcore
      xperm_hyp hp) (fun _ hq => hq) hcOwn0
  have hcF := cpsTripleWithin_frameR F (by unfold F savedFrame; pcf) hcOwn
  exact cpsTripleWithin_weaken
    (P := ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** regOwn .x5 **
      (.x8 ↦ᵣ listBase) ** (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
      (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen)) ** F)
    (P' := loopFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
      saved bytes **
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
       (.x21 ↦ᵣ BitVec.ofNat 64 index)) ** (regOwn .x13 ** regOwn .x14))
    (fun h hp => by
      unfold F
      unfold loopFrame stableFrame stableRest at hp
      xperm_hyp hp)
    (fun h hp => by
      unfold F Qcore at hp
      have hexplicit :
          ((regOwn .x1 ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) **
             (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
             (.x20 ↦ᵣ endPtr) **
             (.x21 ↦ᵣ BitVec.ofNat 64 index)) **
           ((.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
            (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (next - len - listBase)) **
            regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ (0 : Word)) **
            (.x12 ↦ᵣ len) ** regOwn .x13 ** regOwn .x14 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
            (offsetPtr ↦ₘ (next - len - listBase)) ** (lenPtr ↦ₘ len))) h := by
        xperm_hyp hp
      have howned := sepConj_mono_left
        (listNthFrameRegs_implies_owned listBase indexW offsetPtr lenPtr endPtr
          (BitVec.ofNat 64 index)) h hexplicit
      let Rwithout : Assertion :=
        (.x2 ↦ᵣ newSp) ** savedFrame newSp saved ** (.x10 ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase bytes ** (offsetPtr ↦ₘ (next - len - listBase)) **
        (lenPtr ↦ₘ len)
      obtain ⟨ha, hb, hdab, huab, hframe, hrest⟩ := howned
      have hrest' : ((.x5 ↦ᵣ (next - len - listBase)) ** Rwithout) hb := by
        unfold Rwithout
        xperm_hyp hrest
      have hrestOwn := sepConj_mono_left (regIs_implies_regOwn .x5) hb hrest'
      have hallOwned : (regsOwnAt listNthFrame ** (regOwn .x5 ** Rwithout)) h :=
        ⟨ha, hb, hdab, huab, hframe, hrestOwn⟩
      unfold joinResult
      refine ⟨0, next - len - listBase, len, 0, len,
        (sepConj_pure_right h).2 ⟨?_, ?_⟩⟩
      · unfold Rwithout at hallOwned
        xperm_hyp hallOwned
      · exact Result.ok _ _ ⟨cursorOff, endPtr, next, hlist, hnth, rfl⟩) hcF

#print axioms selectedToJoin

theorem scanRejected_implies_failure
    (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) :
    ∀ h, scanRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
      saved bytes listLen index h → Failure bytes listBase listLen index := by
  intro h hp
  unfold scanRejected at hp
  obtain ⟨cursorOff, endPtr, hp⟩ := hp
  obtain ⟨hleft, _hlist⟩ := (sepConj_pure_right h).1 hp
  obtain ⟨ha, hb, hd, hu, hreject, _hregs⟩ := hleft
  unfold loopRejected at hreject
  obtain ⟨count, off, status, hstate⟩ := hreject
  obtain ⟨_, hpure⟩ := (sepConj_pure_right ha).1 hstate
  exact .walk cursorOff count off endPtr hpure.2.2.1 hpure.2.1
    hpure.2.2.2.1 hpure.2.2.2.2

#print axioms scanRejected_implies_failure

theorem initRejected_implies_failure
    (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) :
    ∀ h, initRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
      saved bytes listLen index h → Failure bytes listBase listLen index := by
  intro h hp
  unfold initRejected at hp
  obtain ⟨status, cursor, endPtr, hp⟩ := hp
  extract_pure_deep hp
  exact hp.1.2

theorem preTailRejected_implies_failure
    (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) :
    ∀ h, preTailRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
      saved bytes listLen index h → Failure bytes listBase listLen index := by
  intro h hp
  unfold preTailRejected at hp
  rcases hp with hp | hp
  · exact scanRejected_implies_failure newSp listBase indexW offsetPtr lenPtr
      oldOffset oldLen saved bytes listLen index h hp
  · exact initRejected_implies_failure newSp listBase indexW offsetPtr lenPtr
      oldOffset oldLen saved bytes listLen index h hp

#print axioms initRejected_implies_failure
#print axioms preTailRejected_implies_failure

theorem preTailRejected_implies_result
    (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) :
    ∀ h, preTailRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
      saved bytes listLen index h →
      Result bytes listBase listLen index oldOffset oldLen 1 oldOffset oldLen := by
  intro h hp
  exact .fail (preTailRejected_implies_failure newSp listBase indexW offsetPtr
    lenPtr oldOffset oldLen saved bytes listLen index h hp)

#print axioms preTailRejected_implies_result

def rejectedExpanded (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ oldA0 v11 v12 s4 s5,
    (((regOwn .x1 ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) **
       (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
       (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5)) **
      ((.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
       (.x10 ↦ᵣ oldA0) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
       (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))) **
     ⌜Failure bytes listBase listLen index⌝) h

/-- Both initialization and scan failures expose the same owned ABI station. -/
theorem preTailRejected_to_expanded
    (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    preTailRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
      bytes listLen index h →
    rejectedExpanded newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
      bytes listLen index h := by
  intro h hp
  have hfailure := preTailRejected_implies_failure newSp listBase indexW offsetPtr
    lenPtr oldOffset oldLen saved bytes listLen index h hp
  unfold preTailRejected at hp
  unfold rejectedExpanded
  rcases hp with hscan | hinit
  · unfold scanRejected at hscan
    obtain ⟨cursorOff, endPtr, hscan⟩ := hscan
    have hscanOrig := hscan
    obtain ⟨hleft, _hlist⟩ := (sepConj_pure_right h).1 hscan
    obtain ⟨ha, hb, hd, hu, hloop, hregs⟩ := hleft
    unfold loopRejected at hloop
    obtain ⟨count, off, status, hstate⟩ := hloop
    refine ⟨listBase + BitVec.ofNat 64 off, status, 0,
      endPtr, BitVec.ofNat 64 count, (sepConj_pure_right h).2 ⟨?_, hfailure⟩⟩
    drop_pure hstate
    unfold loopFrame stableFrame stableRest at hstate
    let R : Assertion :=
      (regOwn .x1 ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) **
       (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
       (.x20 ↦ᵣ endPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 count)) **
      ((.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
       (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** regOwn .x5 **
       regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ status) **
       (.x12 ↦ᵣ (0 : Word)) ** regOwn .x28 ** regOwn .x29 **
       regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (offsetPtr ↦ₘ oldOffset) **
       (lenPtr ↦ₘ oldLen))
    have hlocal : R ha := by
      unfold R
      xperm_hyp hstate
    have hjoined : (R ** (regOwn .x13 ** regOwn .x14)) h :=
      ⟨ha, hb, hd, hu, hlocal, hregs⟩
    unfold R at hjoined
    xperm_hyp hjoined
  · unfold initRejected at hinit
    obtain ⟨status, cursor, endPtr, hinit⟩ := hinit
    have hinitOrig := hinit
    refine ⟨cursor, endPtr, status, saved.s4, saved.s5,
      (sepConj_pure_right h).2 ⟨?_, hfailure⟩⟩
    unfold initStable initCommon at hinitOrig
    drop_pure hinitOrig
    let R : Assertion :=
      ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) ** (.x18 ↦ᵣ offsetPtr) **
       (.x19 ↦ᵣ lenPtr) ** (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)) **
      ((.x2 ↦ᵣ newSp) ** savedFrame newSp saved ** (.x10 ↦ᵣ cursor) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ status) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
       regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
       (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))
    have hgroup :
        ((((.x1 ↦ᵣ (B + 52)) ** (.x13 ↦ᵣ offsetPtr) **
          (.x14 ↦ᵣ lenPtr)) ** R) h) := by
      unfold R
      xperm_hyp hinitOrig
    have howned := sepConj_mono_left
      (sepConj_mono (regIs_implies_regOwn .x1)
        (sepConj_mono (regIs_implies_regOwn .x13)
          (regIs_implies_regOwn .x14))) h hgroup
    unfold R at howned
    xperm_hyp howned

#print axioms preTailRejected_to_expanded

/-- Run the one-instruction failure tail and fold its status into `Result.fail`. -/
theorem rejectedExpandedToJoin
    (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 1 (B + 112) (B + 116) code
      (rejectedExpanded newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index)
      (joinResult newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index) := by
  unfold rejectedExpanded
  refine cpsTripleWithin_exists_assertion (fun oldA0 => ?_)
  refine cpsTripleWithin_exists_assertion (fun v11 => ?_)
  refine cpsTripleWithin_exists_assertion (fun v12 => ?_)
  refine cpsTripleWithin_exists_assertion (fun s4 => ?_)
  refine cpsTripleWithin_exists_assertion (fun s5 => ?_)
  let Pbody : Assertion :=
    (regOwn .x1 ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) **
     (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) ** (.x20 ↦ᵣ s4) **
     (.x21 ↦ᵣ s5)) **
    ((.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
     (.x10 ↦ᵣ oldA0) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))
  refine cpsTripleWithin_weaken
    (P := ⌜Failure bytes listBase listLen index⌝ ** Pbody)
    (fun h hp => by unfold Pbody; xperm_hyp hp) (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hfailure => ?_)
  let F : Assertion :=
    (regOwn .x1 ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) **
     (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) ** (.x20 ↦ᵣ s4) **
     (.x21 ↦ᵣ s5)) **
    ((.x2 ↦ᵣ newSp) ** savedFrame newSp saved ** regOwn .x5 ** regOwn .x6 **
     regOwn .x7 ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 **
     regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
     regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))
  have ht := cpsTripleWithin_frameR F (by unfold F savedFrame; pcf)
    (rejectedTailCore oldA0)
  exact cpsTripleWithin_weaken
    (fun h hp => by unfold F; xperm_hyp hp)
    (fun h hp => by
      unfold F at hp
      have hexplicit :
          ((regOwn .x1 ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ indexW) **
             (.x18 ↦ᵣ offsetPtr) ** (.x19 ↦ᵣ lenPtr) **
             (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5)) **
           ((.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
            (.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
            (offsetPtr ↦ₘ oldOffset) ** (lenPtr ↦ₘ oldLen))) h := by
        xperm_hyp hp
      have howned := sepConj_mono_left
        (listNthFrameRegs_implies_owned listBase indexW offsetPtr lenPtr s4 s5)
        h hexplicit
      unfold joinResult
      refine ⟨1, oldOffset, oldLen, v11, v12,
        (sepConj_pure_right h).2 ⟨?_, .fail hfailure⟩⟩
      xperm_hyp howned) ht

#print axioms rejectedExpandedToJoin

theorem rejectedToJoin
    (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 1 (B + 112) (B + 116) code
      (preTailRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index)
      (joinResult newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index) := by
  exact cpsTripleWithin_weaken
    (preTailRejected_to_expanded newSp listBase indexW offsetPtr lenPtr oldOffset
      oldLen saved bytes listLen index)
    (fun _ hq => hq)
    (rejectedExpandedToJoin newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
      saved bytes listLen index)

#print axioms rejectedToJoin

/-- Initialization, strict child scan, and both semantic tails reconverge at
    the single ABI restore join. -/
theorem initScanToJoinExact
    (newSp listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin ((85 + 93 * (index + 2)) + 6) (B + 48) (B + 116) code
      (((.x1 ↦ᵣ saved.ra) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
         (.x12 ↦ᵣ indexW) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes)) **
       (initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
        (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)))
      (joinResult newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index) := by
  have hscan := initAndScanExact newSp listBase listLenW indexW offsetPtr lenPtr
    oldOffset oldLen saved bytes listLen index v5 v6 v7 v28 v29 v30 v31
    hlistLenW hindexW hindex hsalign hslack hover hvalid
  have hbranch := cpsBranchWithin_of_nBranch2 hscan
  have hrejected : cpsTripleWithin 6 (B + 112) (B + 116) code
      (preTailRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index)
      (joinResult newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index) := cpsTripleWithin_mono_nSteps (by omega)
      (rejectedToJoin newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index)
  exact cpsBranchWithin_merge_same_cr hbranch
    (selectedToJoin newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
      bytes listLen index) hrejected

#print axioms initScanToJoinExact

def returnResult (sp0 newSp listBase _indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ status offset len v11 v12,
    ((((.x2 ↦ᵣ sp0) ** regsAt listNthFrame (savedVals saved) **
       savedFrame newSp saved) **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
       (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))) **
     ⌜Result bytes listBase listLen index oldOffset oldLen status offset len⌝) h

/-- The common join restores the seven callee-saved registers and returns while
    preserving the semantic result and all caller-visible memory. -/
theorem joinToReturn
    (sp0 newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hnewSp : newSp = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin 9 (B + 116) saved.ra code
      (joinResult newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index)
      (returnResult sp0 newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index) := by
  unfold joinResult
  refine cpsTripleWithin_exists_assertion (fun status => ?_)
  refine cpsTripleWithin_exists_assertion (fun offset => ?_)
  refine cpsTripleWithin_exists_assertion (fun len => ?_)
  refine cpsTripleWithin_exists_assertion (fun v11 => ?_)
  refine cpsTripleWithin_exists_assertion (fun v12 => ?_)
  let F : Assertion :=
    (.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
    (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len)
  refine cpsTripleWithin_weaken
    (P := ⌜Result bytes listBase listLen index oldOffset oldLen status offset len⌝ **
      (((.x2 ↦ᵣ newSp) ** regsOwnAt listNthFrame ** savedFrame newSp saved) ** F))
    (fun h hp => by unfold F; xperm_hyp hp) (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hresult => ?_)
  have he := epilogueOwned sp0 newSp saved F (by unfold F; pcf) hnewSp hret
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => by
    unfold F at hp
    unfold returnResult
    refine ⟨status, offset, len, v11, v12,
      (sepConj_pure_right h).2 ⟨?_, hresult⟩⟩
    xperm_hyp hp) he

#print axioms joinToReturn

theorem cpsTripleWithin_of_forall_regIs_to_regOwn7
    {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {r1 r2 r3 r4 r5 r6 r7 : Reg} {P Q : Assertion}
    (hspec : ∀ v1 v2 v3 v4 v5 v6 v7, cpsTripleWithin n entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7)) Q) :
    cpsTripleWithin n entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 **
       regOwn r5 ** regOwn r6 ** regOwn r7) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPOwn, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP, hO1⟩ := hPOwn
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact hspec v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP, g2, g3, d2, u2, hv1,
       g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
       g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
       g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc

/-- Expose arbitrary setup scratch values, then run the complete strict core. -/
theorem setupToJoin
    (newSp listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin ((85 + 93 * (index + 2)) + 6) (B + 48) (B + 116) code
      (setupPost newSp listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes)
      (joinResult newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index) := by
  let P : Assertion :=
    (.x1 ↦ᵣ saved.ra) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
    (.x12 ↦ᵣ indexW) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
    initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
    (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)
  have hvalues : ∀ v5 v6 v7 v28 v29 v30 v31,
      cpsTripleWithin ((85 + 93 * (index + 2)) + 6) (B + 48) (B + 116) code
        (P ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
          (.x31 ↦ᵣ v31))
        (joinResult newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
          bytes listLen index) := by
    intro v5 v6 v7 v28 v29 v30 v31
    exact cpsTripleWithin_weaken (fun h hp => by unfold P at hp; xperm_hyp hp)
      (fun _ hq => hq)
      (initScanToJoinExact newSp listBase listLenW indexW offsetPtr lenPtr oldOffset
        oldLen saved bytes listLen index v5 v6 v7 v28 v29 v30 v31 hlistLenW
        hindexW hindex hsalign hslack hover hvalid)
  have howned := cpsTripleWithin_of_forall_regIs_to_regOwn7 hvalues
  exact cpsTripleWithin_weaken (fun h hp => by
    unfold setupPost entryRest at hp
    unfold P initStable
    xperm_hyp hp) (fun _ hq => hq) howned

#print axioms setupToJoin

/-- Unified whole-routine contract for the strict, spec-aligned K20 replacement.
    Preconditions are entirely static; success, parse rejection, and OOB are
    classified by the single genuine `Result` relation in the postcondition. -/
theorem rlpListNthItem_spec_within
    (sp0 newSp listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hnewSp : newSp = sp0 + signExtend12 (-64 : BitVec 12))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin
      ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
      B saved.ra code
      ((.x2 ↦ᵣ sp0) ** regsAt listNthFrame (savedVals saved) **
       frameSlotsOwn listNthFrame newSp **
       entryRest listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen bytes)
      (returnResult sp0 newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index) := by
  have hp := wrapperPrologue sp0 newSp listBase listLenW indexW offsetPtr lenPtr
    oldOffset oldLen saved bytes hnewSp
  have hc := setupToJoin newSp listBase listLenW indexW offsetPtr lenPtr oldOffset
    oldLen saved bytes listLen index hlistLenW hindexW hindex hsalign hslack hover
    hvalid
  have he := joinToReturn sp0 newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
    saved bytes listLen index hnewSp hret
  exact cpsTripleWithin_seq_same_cr (cpsTripleWithin_seq_same_cr hp hc) he

#print axioms rlpListNthItem_spec_within

end EvmAsm.Codegen.RlpListNthItemSAsm
