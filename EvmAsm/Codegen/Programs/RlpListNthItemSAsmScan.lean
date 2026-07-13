import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase

namespace EvmAsm.Codegen.RlpListNthItemSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

theorem initNormalizedDispatch (newSp listBase indexW offsetPtr lenPtr oldOffset
    oldLen : Word) (saved : Saved) (bytes : List (BitVec 8))
    (listLen index : Nat) :
    cpsNBranchWithin 3 (B + 52) code
      ((((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
          initNormalized listBase bytes listLen index) **
        initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved) **
       ((.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)))
      [(B + 64, initLoopPost newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index),
       (B + 112, initRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index)] := by
  let successPre : Assertion := fun h => ∃ cursorOff endPtr,
    ((((((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
         (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)))) **
       initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved) **
      ((.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5))) **
      ⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝) h)
  let failPre : Assertion := fun h => ∃ status cursor endPtr,
    ((((((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status))) **
       initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved) **
      ((.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5))) **
      ⌜status ≠ 0 ∧ Failure bytes listBase listLen index⌝) h)
  have hs : cpsNBranchWithin 3 (B + 52) code successPre
      [(B + 64, initLoopPost newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index),
       (B + 112, initRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index)] := by
    unfold successPre
    refine cpsNBranchWithin_exists_pre (fun cursorOff => ?_)
    refine cpsNBranchWithin_exists_pre (fun endPtr => ?_)
    refine cpsNBranchWithin_pure_pre (fun hlist => ?_)
    exact cpsNBranchWithin_of_triple (by simp)
      (cpsTripleWithin_weaken (fun h hp => by
        unfold initCommon at hp ⊢
        xperm_hyp hp) (fun _ x => x)
        (initSuccessBranch newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
          endPtr saved bytes listLen index cursorOff hlist))
  have hf : cpsNBranchWithin 3 (B + 52) code failPre
      [(B + 64, initLoopPost newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index),
       (B + 112, initRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index)] := by
    unfold failPre
    refine cpsNBranchWithin_exists_pre (fun status => ?_)
    refine cpsNBranchWithin_exists_pre (fun cursor => ?_)
    refine cpsNBranchWithin_exists_pre (fun endPtr => ?_)
    refine cpsNBranchWithin_pure_pre (fun hpure => ?_)
    have ht : cpsTripleWithin 3 (B + 52) (B + 112) code
        (((.x12 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
         ((initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
           initCommon listBase bytes) **
          ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
           (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5))))
        (initRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
          bytes listLen index) :=
      cpsTripleWithin_mono_nSteps (by omega)
        (initRejectBranch newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
          status cursor endPtr saved bytes listLen index hpure.1 hpure.2)
    have hn : cpsNBranchWithin 3 (B + 52) code _
        [(B + 64, initLoopPost newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
          saved bytes listLen index),
         (B + 112, initRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
          saved bytes listLen index)] := cpsNBranchWithin_of_triple (by simp) ht
    exact cpsNBranchWithin_weaken_pre (fun h hp => by
      unfold initCommon at hp ⊢
      xperm_hyp hp) hn
  have harms := cpsNBranchWithin_pre_or_init hs hf
  exact cpsNBranchWithin_weaken_pre (fun h hp => by
    unfold initNormalized at hp
    unfold successPre failPre
    obtain ⟨h1, h2, hd, hu, hleft, htail⟩ := hp
    obtain ⟨h3, h4, hd2, hu2, hcn, hstable⟩ := hleft
    obtain ⟨h5, h6, hd3, hu3, hcommon, hout⟩ := hcn
    rcases hout with hout | hout
    · refine Or.inl ?_
      obtain ⟨cursorOff, endPtr, hs⟩ := hout
      refine ⟨cursorOff, endPtr, ?_⟩
      have hall : ((((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
           (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
           ⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝)) **
          initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved) **
        ((.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5))) h := ⟨h1, h2, hd, hu,
        ⟨h3, h4, hd2, hu2, ⟨h5, h6, hd3, hu3, hcommon, hs⟩, hstable⟩,
        htail⟩
      have hall' : (⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝ **
          ((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
           ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
            (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word))) **
           initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
           ((.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)))) h := by
        xperm_hyp hall
      xperm_hyp hall'
    · refine Or.inr ?_
      obtain ⟨status, cursor, endPtr, hf⟩ := hout
      refine ⟨status, cursor, endPtr, ?_⟩
      have hall : ((((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
          ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
           (.x12 ↦ᵣ status) **
           ⌜status ≠ 0 ∧ Failure bytes listBase listLen index⌝)) **
          initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved) **
        ((.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5))) h := ⟨h1, h2, hd, hu,
        ⟨h3, h4, hd2, hu2, ⟨h5, h6, hd3, hu3, hcommon, hf⟩, hstable⟩,
        htail⟩
      have hall' : (⌜status ≠ 0 ∧ Failure bytes listBase listLen index⌝ **
          ((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
           ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status)) **
           initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
           ((.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)))) h := by
        xperm_hyp hall
      xperm_hyp hall'
    ) harms

#print axioms initNormalizedDispatch

/-- The embedded strict initializer followed by its local status dispatch. -/
theorem initCallDispatchExact
    (newSp listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsNBranchWithin 85 (B + 48) code
      (((.x1 ↦ᵣ saved.ra) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
         (.x12 ↦ᵣ indexW) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
         (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes)) **
       (initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
        (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)))
      [(B + 64, initLoopPost newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index),
       (B + 112, initRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index)] := by
  subst listLenW
  have hcall := initCallExact listBase bytes listLen indexW v5 v6 v7 v28 v29 v30
    v31 saved.ra hsalign hslack hover hvalid
  have hcallF := cpsTripleWithin_frameR
    (initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
      (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)) (by pcf) hcall
  have hcallN : cpsTripleWithin 82 (B + 48) (B + 52) code _
      (((initCommon listBase bytes ** (.x0 ↦ᵣ (0 : Word))) **
        initNormalized listBase bytes listLen index) **
       initStable newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
       (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => by
      have hn := initOutcome_to_normalized listBase bytes listLen index (by omega)
        hslack hover
      have hp' := sepConj_mono_left (sepConj_mono_right hn) h hp
      xperm_hyp hp') hcallF
  have hdispatch := initNormalizedDispatch newSp listBase indexW offsetPtr lenPtr
    oldOffset oldLen saved bytes listLen index
  exact cpsNBranchWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_cpsNBranchWithin_perm_same_cr (fun h hp => by
      xperm_hyp hp) hcallN hdispatch)

#print axioms initCallDispatchExact

/-- Loop success station (`B+88`), before the two output stores. -/
def loopSelected (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (index cursorOff : Nat) : Assertion :=
  fun h => ∃ next len : Word,
    ((loopFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved bytes **
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
       (.x21 ↦ᵣ BitVec.ofNat 64 index))) **
     ⌜StrictNthItem bytes listBase endPtr index cursorOff next len⌝) h

/-- Loop reject station (`B+112`), before `li a0,1`. -/
def loopRejected (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index cursorOff : Nat) : Assertion :=
  fun h => ∃ count off : Nat, ∃ status : Word,
    ((loopFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
       (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ BitVec.ofNat 64 count))) **
     ⌜status ≠ 0 ∧ count ≤ index ∧
       StrictListPayload bytes listBase listLen cursorOff endPtr ∧
       StrictPrefix bytes listBase endPtr cursorOff count off ∧
       WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h

/-! ## One verified call block -/

def nextCommon (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  (.x1 ↦ᵣ (B + 72)) ** bytesRegion listBase bytes

def nextScratch (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (B + 72)) ** bytesRegion listBase bytes

def nextScratchOwned (listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** regOwn .x1 ** bytesRegion listBase bytes

theorem nextScratch_implies_owned (listBase : Word) (bytes : List (BitVec 8)) :
    ∀ h, nextScratch listBase bytes h → nextScratchOwned listBase bytes h := by
  intro h hp
  unfold nextScratch at hp
  unfold nextScratchOwned
  exact sepConj_mono (fun _ x => x)
    (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x)
              (sepConj_mono (fun _ x => x)
                (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x)))))))) h hp

def nextOutcome (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) : Assertion := fun h =>
  rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off h ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (2 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 off) endPtr = true⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (3 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (4 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (5 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
  (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (6 : Word)) **
    (.x12 ↦ᵣ (0 : Word)) **
    ⌜¬ ∃ next len, rlpItemDecode bytes off
      (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h)

/-- Slot 16's `mv a1,s4` followed by the local verified WalkNext call. -/
theorem nextCallBlock (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off listLen : Nat) (v5 v6 v7 v11 v12 v28 v29 v30 v31 oldRa : Word)
    (F : Assertion) (hF : F.pcFree)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hoff : off ≤ listLen) :
    cpsTripleWithin 89 (B + 64) (B + 72) code
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** (.x20 ↦ᵣ endPtr) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** F)
      ((nextCommon listBase bytes **
        (fun h =>
          rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off h ∨
          (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (2 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 off) endPtr = true⌝) h) ∨
          (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (3 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode bytes off
              (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
          (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (4 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode bytes off
              (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
          (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (5 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode bytes off
              (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h) ∨
          (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ (6 : Word)) **
            (.x12 ↦ᵣ (0 : Word)) **
            ⌜¬ ∃ next len, rlpItemDecode bytes off
              (listBase + BitVec.ofNat 64 off) endPtr next len⌝) h))) **
       ((.x20 ↦ᵣ endPtr) ** F)) := by
  have hoffb : off < bytes.length := by omega
  have hmv0 := mv_spec_gen_within .x11 .x20 endPtr v11 (B + 64) (by decide)
  rw [show (B + 64) + 4 = B + 68 from by bv_omega] at hmv0
  have hmv := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub B (B + 64) rlpListNthItem_prog
      [.MV .x11 .x20] 16 (by bv_omega) (by rfl)
      (by rw [total_length]; norm_num) (by rw [total_length]; norm_num)) hmv0
  have hwn := rlp_walk_next_spec_within WN listBase endPtr (B + 72) v12
    v5 v6 v7 v28 v29 v30 v31 bytes off hsalign hoffb (by omega)
    (hvalid off hoffb)
    (fun _ _ => ⟨by omega, by omega, hvalid _ (by omega)⟩)
    (fun hb8 hc0 => by
      have hlo : ((bytes[off]'hoffb).zeroExtend 64 - (0xb7 : Word)).toNat ≤ 8 := by
        simp only [BitVec.ult, decide_eq_true_eq] at hb8 hc0
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
    (fun hf8 => by
      have hlo : ((bytes[off]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        simp only [BitVec.ult, decide_eq_true_eq] at hf8
        have h3 := (bytes[off]'hoffb).isLt
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
  have hwn' := cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwn
    (P' := (.x1 ↦ᵣ (B + 72)) **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ endPtr) **
       (.x12 ↦ᵣ v12) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
       (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes))
  have hcall := callWalkNext (n := 87) oldRa (by pcf) hwn'
  have hmvF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x12 ↦ᵣ v12) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
     (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ oldRa) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** F) (by pcf; exact hF) hmv
  have hcallF := cpsTripleWithin_frameR ((.x20 ↦ᵣ endPtr) ** F)
    (by pcf; exact hF) hcall
  have hc := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hmvF hcallF
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => by unfold nextCommon; exact hq) hc

#print axioms nextCallBlock

/-! ## Wrapper dispatch instructions -/

private theorem liftBne72 (lhs rhs : Word) :
    cpsBranchWithin 1 (B + 72) code
      ((.x11 ↦ᵣ lhs) ** (.x0 ↦ᵣ rhs))
      (B + 112) ((.x11 ↦ᵣ lhs) ** (.x0 ↦ᵣ rhs) ** ⌜lhs ≠ rhs⌝)
      (B + 76) ((.x11 ↦ᵣ lhs) ** (.x0 ↦ᵣ rhs) ** ⌜lhs = rhs⌝) := by
  have h := bne_spec_gen_within .x11 .x0 (40 : BitVec 13) lhs rhs (B + 72)
  rw [show (B + 72) + signExtend13 (40 : BitVec 13) = B + 112 from by
        rw [show signExtend13 (40 : BitVec 13) = (40 : Word) from by decide]; bv_omega,
      show (B + 72) + 4 = B + 76 from by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (by
      unfold code
      exact CodeReq.ofProg_mem_at B (B + 72)
        rlpListNthItem_prog 18 (.BNE .x11 .x0 (40 : BitVec 13))
        (by bv_omega) (by rw [total_length]; norm_num)
        (by rfl) (by rw [total_length]; norm_num)) h

theorem statusReject (status : Word) (F : Assertion) (hF : F.pcFree)
    (hstatus : status ≠ 0) :
    cpsTripleWithin 1 (B + 72) (B + 112) code
      (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) ** F)
      (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) ** F) := by
  have ht := cpsBranchWithin_takenPath (liftBne72 status 0) (fun _ hfall => by
    obtain ⟨_, _, _, _, _, hpure⟩ := hfall
    exact hstatus (((sepConj_pure_right _).1 hpure).2))
  have ht' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h' hq => by
    refine sepConj_mono_right (fun h'' hp => ((sepConj_pure_right h'').1 hp).1) h' hq) ht
  exact cpsTripleWithin_frameR F hF ht'

theorem statusOk (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (B + 72) (B + 76) code
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** F)
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** F) := by
  have hf := cpsBranchWithin_ntakenPath (liftBne72 0 0) (fun _ htaken => by
    obtain ⟨_, _, _, _, _, hpure⟩ := htaken
    exact (((sepConj_pure_right _).1 hpure).2) rfl)
  have hf' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h' hq => by
    refine sepConj_mono_right (fun h'' hp => ((sepConj_pure_right h'').1 hp).1) h' hq) hf
  exact cpsTripleWithin_frameR F hF hf'

private theorem liftBeq76 (lhs rhs : Word) :
    cpsBranchWithin 1 (B + 76) code
      ((.x21 ↦ᵣ lhs) ** (.x9 ↦ᵣ rhs))
      (B + 88) ((.x21 ↦ᵣ lhs) ** (.x9 ↦ᵣ rhs) ** ⌜lhs = rhs⌝)
      (B + 80) ((.x21 ↦ᵣ lhs) ** (.x9 ↦ᵣ rhs) ** ⌜lhs ≠ rhs⌝) := by
  have h := beq_spec_gen_within .x21 .x9 (12 : BitVec 13) lhs rhs (B + 76)
  rw [show (B + 76) + signExtend13 (12 : BitVec 13) = B + 88 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (B + 76) + 4 = B + 80 from by bv_omega] at h
  exact cpsBranchWithin_extend_code
    (by
      unfold code
      exact CodeReq.ofProg_mem_at B (B + 76)
        rlpListNthItem_prog 19 (.BEQ .x21 .x9 (12 : BitVec 13))
        (by bv_omega) (by rw [total_length]; norm_num)
        (by rfl) (by rw [total_length]; norm_num)) h

theorem indexSelected (value : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (B + 76) (B + 88) code
      (((.x21 ↦ᵣ value) ** (.x9 ↦ᵣ value)) ** F)
      (((.x21 ↦ᵣ value) ** (.x9 ↦ᵣ value)) ** F) := by
  have ht := cpsBranchWithin_takenPath (liftBeq76 value value) (fun _ hf => by
    obtain ⟨_, _, _, _, _, hpure⟩ := hf
    exact (((sepConj_pure_right _).1 hpure).2) rfl)
  have ht' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h' hq => by
    refine sepConj_mono_right (fun h'' hp => ((sepConj_pure_right h'').1 hp).1) h' hq) ht
  exact cpsTripleWithin_frameR F hF ht'

theorem indexContinue (countW indexW : Word) (F : Assertion) (hF : F.pcFree)
    (hne : countW ≠ indexW) :
    cpsTripleWithin 1 (B + 76) (B + 80) code
      (((.x21 ↦ᵣ countW) ** (.x9 ↦ᵣ indexW)) ** F)
      (((.x21 ↦ᵣ countW) ** (.x9 ↦ᵣ indexW)) ** F) := by
  have hf := cpsBranchWithin_ntakenPath (liftBeq76 countW indexW) (fun _ ht => by
    obtain ⟨_, _, _, _, _, hpure⟩ := ht
    exact hne (((sepConj_pure_right _).1 hpure).2))
  have hf' := cpsTripleWithin_weaken (fun _ hp => hp) (fun h' hq => by
    refine sepConj_mono_right (fun h'' hp => ((sepConj_pure_right h'').1 hp).1) h' hq) hf
  exact cpsTripleWithin_frameR F hF hf'

theorem incrementBack (count : Nat) (F : Assertion) (hF : F.pcFree)
    :
    cpsTripleWithin 2 (B + 80) (B + 64) code
      ((.x21 ↦ᵣ BitVec.ofNat 64 count) ** F)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (count + 1)) ** F) := by
  have ha0 := addi_spec_gen_same_within .x21 (BitVec.ofNat 64 count)
    (1 : BitVec 12) (B + 80) (by decide)
  rw [show (B + 80) + 4 = B + 84 from by bv_omega] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub B (B + 80) rlpListNthItem_prog
      [.ADDI .x21 .x21 (1 : BitVec 12)] 20 (by bv_omega) (by rfl)
      (by rw [total_length]; norm_num) (by rw [total_length]; norm_num)) ha0
  have hj0 := jal_x0_spec_gen_within (-20 : BitVec 21) (B + 84)
  rw [show (B + 84) + signExtend21 (-20 : BitVec 21) = B + 64 from by
    rw [show signExtend21 (-20 : BitVec 21) = (-20 : Word) from by decide]; bv_omega] at hj0
  have hj := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub B (B + 84) rlpListNthItem_prog
      [.JAL .x0 (-20 : BitVec 21)] 21 (by bv_omega) (by rfl)
      (by rw [total_length]; norm_num) (by rw [total_length]; norm_num)) hj0
  have haF := cpsTripleWithin_frameR F hF ha
  have hnext : BitVec.ofNat 64 count + signExtend12 (1 : BitVec 12) =
      BitVec.ofNat 64 (count + 1) := by
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    bv_omega
  rw [hnext] at haF
  have hjF := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ BitVec.ofNat 64 (count + 1)) ** F) (by pcf; exact hF) hj
  rw [sepConj_emp_left'] at hjF
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) haF hjF

#print axioms statusReject
#print axioms statusOk
#print axioms indexSelected
#print axioms indexContinue
#print axioms incrementBack

/-! ## Semantic dispatch adapters -/

theorem dispatchFailure
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen index cursorOff count off : Nat) (status : Word)
    (hstatus : status ≠ 0)
    (hlist : StrictListPayload bytes listBase listLen cursorOff endPtr)
    (hcount : count ≤ index)
    (hprefix : StrictPrefix bytes listBase endPtr cursorOff count off)
    (hwalk : WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr) :
    cpsTripleWithin 1 (B + 72) (B + 112) code
      (nextScratch listBase bytes **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
         (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x21 ↦ᵣ BitVec.ofNat 64 count) **
         (.x9 ↦ᵣ indexW) **
         stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved))
      (loopRejected newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff) := by
  have ht := statusReject status
    (nextScratch listBase bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x12 ↦ᵣ (0 : Word)) **
       (.x21 ↦ᵣ BitVec.ofNat 64 count) **
       (.x9 ↦ᵣ indexW) **
       stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved))
    (by pcf) hstatus
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) ht
  · xperm_hyp hp
  · unfold loopRejected loopFrame
    refine ⟨count, off, status, ?_⟩
    have hq' := sepConj_mono
      (fun _ x => x)
      (sepConj_mono (nextScratch_implies_owned listBase bytes) (fun _ x => x)) h hq
    refine (sepConj_pure_right h).2
      ⟨?_, hstatus, hcount, hlist, hprefix, hwalk⟩
    unfold nextScratchOwned at hq'
    xperm_hyp hq'

#print axioms dispatchFailure

theorem dispatchSuccess
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen index cursorOff count off j : Nat) (next len : Word)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hlist : StrictListPayload bytes listBase listLen cursorOff endPtr)
    (hcount : count ≤ index) (hj : j = index + 1 - count)
    (hoff : off ≤ listLen)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hslack : listLen + 9 ≤ bytes.length)
    (hprefix : StrictPrefix bytes listBase endPtr cursorOff count off)
    (hitem : rlpItemDecode bytes off (listBase + BitVec.ofNat 64 off)
      endPtr next len) :
    cpsBranchWithin 4 (B + 72) code
      (nextScratch listBase bytes **
       ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ BitVec.ofNat 64 count) **
        (.x9 ↦ᵣ indexW) **
        stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved))
      (B + 88)
        (loopSelected newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes index cursorOff)
      (B + 64) (fun h => ∃ j', j' < j ∧
        loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes listLen index cursorOff j' h) := by
  subst indexW
  have hs := statusOk
    (nextScratch listBase bytes **
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
       (.x21 ↦ᵣ BitVec.ofNat 64 count) **
       (.x9 ↦ᵣ BitVec.ofNat 64 index) **
       stableFrame newSp listBase (BitVec.ofNat 64 index) offsetPtr lenPtr endPtr oldOffset oldLen saved))
    (by pcf)
  by_cases heq : count = index
  · subst count
    have hi := indexSelected (BitVec.ofNat 64 index)
      (nextScratch listBase bytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) **
         stableFrame newSp listBase (BitVec.ofNat 64 index) offsetPtr lenPtr endPtr oldOffset oldLen saved))
      (by pcf)
    have hc := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hs hi
    refine cpsTripleWithin_as_cpsBranchWithin_left _ _
      (cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hc))
    unfold loopSelected loopFrame
    refine ⟨next, len, ?_⟩
    have hq' := sepConj_mono
      (fun _ x => x)
      (sepConj_mono (nextScratch_implies_owned listBase bytes) (fun _ x => x)) h hq
    refine (sepConj_pure_right h).2 ⟨?_, StrictPrefix.select hprefix hitem⟩
    unfold nextScratchOwned at hq'
    xperm_hyp hq'
  · have hlt : count < index := by omega
    have hword : BitVec.ofNat 64 count ≠ BitVec.ofNat 64 index := by
      intro he
      have he' := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hlt hindex),
        Nat.mod_eq_of_lt hindex] at he'
      omega
    have hi := indexContinue (BitVec.ofNat 64 count) (BitVec.ofNat 64 index)
      (nextScratch listBase bytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) **
         stableFrame newSp listBase (BitVec.ofNat 64 index) offsetPtr lenPtr endPtr oldOffset oldLen saved))
      (by pcf) hword
    have hb := incrementBack count
      (nextScratch listBase bytes **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ BitVec.ofNat 64 index) **
         stableFrame newSp listBase (BitVec.ofNat 64 index) offsetPtr lenPtr endPtr oldOffset oldLen saved))
      (by pcf)
    have hc1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hs hi
    have hc := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hc1 hb
    refine cpsTripleWithin_as_cpsBranchWithin_right _ _
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hc)
    have hend := hlist.end_eq
    subst endPtr
    have hstep := StrictPrefix.step_bounds hprefix hitem hoff (by omega)
    refine ⟨index + 1 - (count + 1), by omega, ?_⟩
    unfold loopInv loopFrame
    refine ⟨count + 1, (next - listBase).toNat, ?_⟩
    have hq' := sepConj_mono
      (fun _ x => x)
        (sepConj_mono (nextScratch_implies_owned listBase bytes)
          (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn .x11)
            (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x))))) h hq
    refine (sepConj_pure_right h).2
      ⟨?_, rfl, by omega, hstep.2.2.1, hstep.2.2.2⟩
    rw [hstep.1] at hq'
    unfold nextScratchOwned at hq'
    xperm_hyp hq'

#print axioms dispatchSuccess

theorem cpsNBranchWithin_pre_or {n : Nat} {entry : Word} {cr : CodeReq}
    {P1 P2 : Assertion} {exits : List (Word × Assertion)}
    (h1 : cpsNBranchWithin n entry cr P1 exits)
    (h2 : cpsNBranchWithin n entry cr P2 exits) :
    cpsNBranchWithin n entry cr (fun h => P1 h ∨ P2 h) exits := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, ha, hb, hd, hu, hor, hRb⟩ := hPR
  rcases hor with hP | hP
  · exact h1 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  · exact h2 R hR s hcr ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc

#print axioms cpsNBranchWithin_pre_or

/-! ## One complete loop round and the measure fold -/

def roundStable (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (count : Nat) : Assertion :=
  (.x20 ↦ᵣ endPtr) **
  stableRest newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
  (.x9 ↦ᵣ indexW) ** (.x21 ↦ᵣ BitVec.ofNat 64 count)

theorem callOk_shape
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (count off : Nat) :
    ∀ h, ((nextCommon listBase bytes **
      rlpWalkNextOk (listBase + BitVec.ofNat 64 off) endPtr bytes off) **
      roundStable newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved count) h →
      ∃ next len,
        ((nextScratch listBase bytes **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
           (.x0 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ BitVec.ofNat 64 count) **
           (.x9 ↦ᵣ indexW) **
           stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved)) **
         ⌜rlpItemDecode bytes off (listBase + BitVec.ofNat 64 off)
           endPtr next len⌝) h := by
  intro h hp
  obtain ⟨p1, p2, pd, pu, hleft, hstable⟩ := hp
  obtain ⟨q1, q2, qd, qu, hcommon, ⟨next, len, hbody⟩⟩ := hleft
  obtain ⟨r1, r2, rd, ru, h10, hrest⟩ := hbody
  obtain ⟨s1, s2, sd, su, h11, hrest2⟩ := hrest
  obtain ⟨h12, hitem⟩ := (sepConj_pure_right s2).1 hrest2
  refine ⟨next, len, (sepConj_pure_right h).2 ⟨?_, hitem⟩⟩
  have hregs : ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ len)) q2 :=
    ⟨r1, r2, rd, ru, h10, s1, s2, sd, su, h11, h12⟩
  have hp' : ((nextCommon listBase bytes **
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len))) **
      roundStable newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved count) h :=
    ⟨p1, p2, pd, pu, ⟨q1, q2, qd, qu, hcommon, hregs⟩, hstable⟩
  unfold nextCommon roundStable at hp'
  unfold nextScratch stableFrame
  xperm_hyp hp'

theorem callFail_shape
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen status : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (count off : Nat) :
    ∀ h, ((nextCommon listBase bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
       (.x12 ↦ᵣ (0 : Word)) **
       ⌜WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝)) **
      roundStable newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved count) h →
      ((nextScratch listBase bytes **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
         (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x21 ↦ᵣ BitVec.ofNat 64 count) ** (.x9 ↦ᵣ indexW) **
         stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved)) **
       ⌜WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h := by
  intro h hp
  obtain ⟨p1, p2, pd, pu, hleft, hstable⟩ := hp
  obtain ⟨q1, q2, qd, qu, hcommon, hbody⟩ := hleft
  obtain ⟨r1, r2, rd, ru, h10, hrest⟩ := hbody
  obtain ⟨s1, s2, sd, su, h11, hrest2⟩ := hrest
  obtain ⟨h12, hwalk⟩ := (sepConj_pure_right s2).1 hrest2
  refine (sepConj_pure_right h).2 ⟨?_, hwalk⟩
  have hregs : ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
      (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ (0 : Word))) q2 :=
    ⟨r1, r2, rd, ru, h10, s1, s2, sd, su, h11, h12⟩
  have hp' : ((nextCommon listBase bytes **
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       (.x11 ↦ᵣ status) ** (.x12 ↦ᵣ (0 : Word)))) **
      roundStable newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved count) h := ⟨p1, p2, pd, pu, ⟨q1, q2, qd, qu, hcommon, hregs⟩, hstable⟩
  unfold nextCommon roundStable at hp'
  unfold nextScratch stableFrame
  xperm_hyp hp'

#print axioms callOk_shape
#print axioms callFail_shape

theorem failureRegs_mono (listBase endPtr : Word) (bytes : List (BitVec 8))
    (off : Nat) (status : Word) (P : Prop)
    (himp : P → WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr) :
    ∀ h,
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
        (.x12 ↦ᵣ (0 : Word)) ** ⌜P⌝) h) →
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
        (.x12 ↦ᵣ (0 : Word)) **
        ⌜WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h) := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, h10, hp⟩ := hp
  obtain ⟨h3, h4, hd2, hu2, h11, hp⟩ := hp
  obtain ⟨h5, h6, hd3, hu3, h12, hP⟩ := hp
  have hP' : P := hP.2
  have hwalk : ⌜WalkFailure bytes off
      (listBase + BitVec.ofNat 64 off) endPtr⌝ h6 := by
    exact ⟨hP.1, himp hP'⟩
  exact ⟨h1, h2, hd, hu, h10,
    ⟨h3, h4, hd2, hu2, h11,
      ⟨h5, h6, hd3, hu3, h12, hwalk⟩⟩⟩

theorem loopRound
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen index cursorOff : Nat)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hlist : StrictListPayload bytes listBase listLen cursorOff endPtr)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (j : Nat) :
    cpsNBranchWithin 93 (B + 64) code
      (loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff j)
      [(B + 88, loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes index cursorOff),
       (B + 112, loopRejected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes listLen index cursorOff),
       (B + 64, fun h => ∃ j', j' < j ∧
        loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes listLen index cursorOff j' h)] := by
  unfold loopInv
  refine cpsNBranchWithin_exists_pre (fun count => ?_)
  refine cpsNBranchWithin_exists_pre (fun off => ?_)
  refine cpsNBranchWithin_pure_pre (fun hfacts => ?_)
  obtain ⟨hj, hcount, hoff, hprefix⟩ := hfacts
  -- Expose the call-clobbered owned registers; x11 differs on the first
  -- entry and later reentries but slot 16 overwrites it before the call.
  refine cpsNBranchWithin3_weaken
    (P := ((stableRest newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
      ((.x20 ↦ᵣ endPtr) ** (.x9 ↦ᵣ indexW) **
       (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       regOwn .x11 ** (.x21 ↦ᵣ BitVec.ofNat 64 count) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1))
    (fun h hp => by unfold loopFrame stableFrame at hp; xperm_hyp hp)
    (fun _ x => x) (fun _ x => x) (fun _ x => x) ?_
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn9
    (fun v5 v6 v7 v12 v28 v29 v30 v31 vRa => ?_)
  let P11 : Assertion :=
    ((stableRest newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
      ((.x20 ↦ᵣ endPtr) ** (.x9 ↦ᵣ indexW) **
       (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       (.x21 ↦ᵣ BitVec.ofNat 64 count) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x12 ↦ᵣ v12) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
      (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x1 ↦ᵣ vRa))
  refine cpsNBranchWithin_weaken_pre (P := P11 ** regOwn .x11)
    (fun h hp => by unfold P11; xperm_hyp hp) ?_
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn (P := P11) (fun v11 => ?_)
  have tcall := nextCallBlock listBase endPtr bytes off listLen
    v5 v6 v7 v11 v12 v28 v29 v30 v31 vRa
    (stableRest newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved **
      (.x9 ↦ᵣ indexW) ** (.x21 ↦ᵣ BitVec.ofNat 64 count))
    (by pcf) hsalign hslack hover hvalid hoff
  -- Success continuation, embedded in the common three-exit round.
  have hok : cpsNBranchWithin 4 (B + 72) code
      (fun h => ∃ next len,
        ((nextScratch listBase bytes **
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
           (.x0 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ BitVec.ofNat 64 count) **
           (.x9 ↦ᵣ indexW) **
           stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved)) **
         ⌜rlpItemDecode bytes off (listBase + BitVec.ofNat 64 off)
           endPtr next len⌝) h)
      [(B + 88, loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes index cursorOff),
       (B + 112, loopRejected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes listLen index cursorOff),
       (B + 64, fun h => ∃ j', j' < j ∧
        loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes listLen index cursorOff j' h)] := by
    refine cpsNBranchWithin_exists_pre (fun next => ?_)
    refine cpsNBranchWithin_exists_pre (fun len => ?_)
    refine cpsNBranchWithin_pure_pre (fun hitem => ?_)
    exact cpsNBranchWithin_of_branch_mem (by simp) (by simp)
      (dispatchSuccess newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff count off j next len hindexW hindex hlist
        hcount hj hoff hover hslack hprefix hitem)
  -- One generic failure arm, embedded at the reject member.
  have hfail : ∀ status : Word, status ≠ 0 →
      cpsNBranchWithin 4 (B + 72) code
        (fun h =>
          ((nextScratch listBase bytes **
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off)) ** (.x11 ↦ᵣ status) **
             (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
             (.x21 ↦ᵣ BitVec.ofNat 64 count) ** (.x9 ↦ᵣ indexW) **
             stableFrame newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen saved)) **
           ⌜WalkFailure bytes off (listBase + BitVec.ofNat 64 off) endPtr⌝) h)
        [(B + 88, loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
          oldOffset oldLen saved bytes index cursorOff),
         (B + 112, loopRejected newSp listBase indexW offsetPtr lenPtr endPtr
          oldOffset oldLen saved bytes listLen index cursorOff),
         (B + 64, fun h => ∃ j', j' < j ∧
          loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
            saved bytes listLen index cursorOff j' h)] := by
    intro status hstatus
    refine cpsNBranchWithin_pure_pre (fun hwalk => ?_)
    exact cpsNBranchWithin_mono_nSteps (by omega)
      (cpsNBranchWithin_of_triple (by simp)
        (dispatchFailure newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes listLen index cursorOff count off status hstatus hlist hcount
          hprefix hwalk))
  have harms := cpsNBranchWithin_pre_or hok
    (cpsNBranchWithin_pre_or (hfail 2 (by decide))
      (cpsNBranchWithin_pre_or (hfail 3 (by decide))
        (cpsNBranchWithin_pre_or (hfail 4 (by decide))
          (cpsNBranchWithin_pre_or (hfail 5 (by decide)) (hfail 6 (by decide))))))
  let callPost : Assertion :=
    (nextCommon listBase bytes ** nextOutcome listBase endPtr bytes off) **
      roundStable newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved count
  have hcont : cpsNBranchWithin 4 (B + 72) code callPost
      [(B + 88, loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes index cursorOff),
       (B + 112, loopRejected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes listLen index cursorOff),
       (B + 64, fun h => ∃ j', j' < j ∧
        loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
          saved bytes listLen index cursorOff j' h)] := by
    refine cpsNBranchWithin_weaken_pre ?_ harms
    intro h hp
    unfold callPost nextOutcome at hp
    -- Distribute the callee's common frame over its six outcomes.
    obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, hout⟩, hstable⟩ := hp
    rcases hout with hs | hb2 | hb3 | hb4 | hb5 | hb6
    · refine Or.inl (callOk_shape newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes count off h ?_)
      exact ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, hs⟩, hstable⟩
    · refine Or.inr (Or.inl (callFail_shape newSp listBase indexW offsetPtr lenPtr
        endPtr oldOffset oldLen 2 saved bytes count off h ?_))
      refine ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, ?_⟩, hstable⟩
      exact failureRegs_mono listBase endPtr bytes off 2 _ Or.inl h4 hb2
    · refine Or.inr (Or.inr (Or.inl (callFail_shape newSp listBase indexW offsetPtr
        lenPtr endPtr oldOffset oldLen 3 saved bytes count off h ?_)))
      refine ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, ?_⟩, hstable⟩
      exact failureRegs_mono listBase endPtr bytes off 3 _ Or.inr h4 hb3
    · refine Or.inr (Or.inr (Or.inr (Or.inl (callFail_shape newSp listBase indexW
        offsetPtr lenPtr endPtr oldOffset oldLen 4 saved bytes count off h ?_))))
      refine ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, ?_⟩, hstable⟩
      exact failureRegs_mono listBase endPtr bytes off 4 _ Or.inr h4 hb4
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (callFail_shape newSp listBase
        indexW offsetPtr lenPtr endPtr oldOffset oldLen 5 saved bytes count off h ?_)))))
      refine ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, ?_⟩, hstable⟩
      exact failureRegs_mono listBase endPtr bytes off 5 _ Or.inr h4 hb5
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      refine callFail_shape newSp listBase indexW offsetPtr lenPtr endPtr oldOffset
        oldLen 6 saved bytes count off h ?_
      refine ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hcommon, ?_⟩, hstable⟩
      exact failureRegs_mono listBase endPtr bytes off 6 _ Or.inr h4 hb6
  have tcall' : cpsTripleWithin 89 (B + 64) (B + 72) code _ callPost :=
    cpsTripleWithin_weaken (fun _ x => x) (fun h hp => by
    dsimp [callPost]
    unfold nextOutcome roundStable
    exact hp) tcall
  have hseq := cpsTripleWithin_seq_cpsNBranchWithin_same_cr tcall' hcont
  exact cpsNBranchWithin_mono_nSteps (by omega)
    (cpsNBranchWithin_weaken_pre (fun h hp => by
      unfold P11 at hp
      unfold stableRest savedFrame at hp ⊢
      xperm_hyp hp) hseq)

#print axioms loopRound

/-- The strict list scan folded over the remaining-index measure. -/
theorem listNthLoop
    (newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8))
    (listLen index cursorOff : Nat)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hlist : StrictListPayload bytes listBase listLen cursorOff endPtr)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (j : Nat) :
    cpsBranchWithin (93 * (j + 1)) (B + 64) code
      (loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff j)
      (B + 88) (loopSelected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes index cursorOff)
      (B + 112) (loopRejected newSp listBase indexW offsetPtr lenPtr endPtr
        oldOffset oldLen saved bytes listLen index cursorOff) :=
  cpsBranchWithin_of_nBranch2
    (measureTwoExitLoop_spec 93
      (loopInv newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff)
      (fun j' => loopRound newSp listBase indexW offsetPtr lenPtr endPtr oldOffset
        oldLen saved bytes listLen index cursorOff hindexW hindex hlist hsalign
        hslack hover hvalid j') j)

#print axioms listNthLoop

def scanSelected (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ cursorOff endPtr,
    ((loopSelected newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes index cursorOff ** (regOwn .x13 ** regOwn .x14)) **
      ⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝) h

def scanRejected (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ cursorOff endPtr,
    ((loopRejected newSp listBase indexW offsetPtr lenPtr endPtr oldOffset oldLen
        saved bytes listLen index cursorOff ** (regOwn .x13 ** regOwn .x14)) **
      ⌜StrictListPayload bytes listBase listLen cursorOff endPtr⌝) h

/-- Consume an initialized strict-list cursor through the verified scan loop. -/
theorem scanFromInit
    (newSp listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsNBranchWithin (93 * (index + 2)) (B + 64) code
      (initLoopPost newSp listBase indexW offsetPtr lenPtr oldOffset oldLen saved
        bytes listLen index)
      [(B + 88, scanSelected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index),
       (B + 112, scanRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index)] := by
  unfold initLoopPost
  refine cpsNBranchWithin_exists_pre (fun cursorOff => ?_)
  refine cpsNBranchWithin_exists_pre (fun endPtr => ?_)
  refine cpsNBranchWithin_pure_pre (fun hlist => ?_)
  let F : Assertion := regOwn .x13 ** regOwn .x14
  have hloop := listNthLoop newSp listBase indexW offsetPtr lenPtr endPtr oldOffset
    oldLen saved bytes listLen index cursorOff hindexW hindex hlist hsalign hslack
    hover hvalid
  have hloopF := cpsBranchWithin_frameR F (by dsimp [F]; pcf)
    (hloop (index + 1))
  have hn := cpsBranchWithin_as_cpsNBranchWithin hloopF
  have hn' : cpsNBranchWithin (93 * (index + 2)) (B + 64) code _
      [(B + 88, scanSelected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index),
       (B + 112, scanRejected newSp listBase indexW offsetPtr lenPtr oldOffset oldLen
        saved bytes listLen index)] := cpsNBranchWithin_weaken_posts hn (by
    intro ex hex
    cases hex with
    | head =>
      refine ⟨(B + 88, scanSelected newSp listBase indexW offsetPtr lenPtr oldOffset
          oldLen saved bytes listLen index), by simp, rfl, ?_⟩
      intro h hp
      unfold F at hp
      unfold scanSelected
      refine ⟨cursorOff, endPtr, (sepConj_pure_right h).2 ⟨?_, hlist⟩⟩
      xperm_hyp hp
    | tail _ ht =>
      cases ht with
      | head =>
       refine ⟨(B + 112, scanRejected newSp listBase indexW offsetPtr lenPtr oldOffset
          oldLen saved bytes listLen index), by simp, rfl, ?_⟩
       intro h hp
       unfold F at hp
       unfold scanRejected
       refine ⟨cursorOff, endPtr, (sepConj_pure_right h).2 ⟨?_, hlist⟩⟩
       xperm_hyp hp
      | tail _ hf => exact absurd hf List.not_mem_nil)
  exact cpsNBranchWithin_weaken_pre (fun h hp => by
    unfold F
    xperm_hyp hp) hn'

#print axioms scanFromInit

end EvmAsm.Codegen.RlpListNthItemSAsm
