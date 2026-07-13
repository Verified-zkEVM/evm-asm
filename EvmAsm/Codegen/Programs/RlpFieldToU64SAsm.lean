/-
  Strict K34 `rlp_field_to_u64` caller proof.

  The wrapper composes the verified strict list selector with the verified
  canonical scalar decoder. Its unified post keeps every runtime outcome in
  one genuine semantic relation.
-/

import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.Tactics.DropPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Codegen.RlpFieldToU64SAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

/-! ## Genuine strict semantics -/

/-- Caller-visible K34 result. A malformed list, OOB index, or non-canonical
    scalar reports status one; an otherwise canonical payload wider than eight
    bytes reports status two; canonical scalars report their BE value. -/
inductive Result (bytes : List (BitVec 8)) (base : Word)
    (listLen index : Nat) : Word → Word → Prop
  | listFailure (hfail : EvmAsm.Codegen.RlpListNthItemSAsm.Failure
      bytes base listLen index) :
      Result bytes base listLen index 1 0
  | tooLong (offset len : Word)
      (hok : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen index offset len)
      (hlen : 8 < len.toNat) :
      Result bytes base listLen index 2 0
  | noncanonical (offset len : Word)
      (hok : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen index offset len)
      (hpos : 0 < len.toNat) (hfit : len.toNat ≤ 8)
      (hzero : getByteAt bytes offset.toNat = 0) :
      Result bytes base listLen index 1 0
  | empty (offset len : Word)
      (hok : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen index offset len)
      (hempty : len.toNat = 0) :
      Result bytes base listLen index 0 0
  | success (offset len : Word)
      (hok : EvmAsm.Codegen.RlpListNthItemSAsm.Success
        bytes base listLen index offset len)
      (hpos : 0 < len.toNat) (hfit : len.toNat ≤ 8)
      (hnz : getByteAt bytes offset.toNat ≠ 0) :
      Result bytes base listLen index 0
        (BitVec.ofNat 64
          (Nat.fromBytesBE ((bytes.drop offset.toNat).take len.toNat)))

theorem Result.status_cases {bytes : List (BitVec 8)} {base : Word}
    {listLen index : Nat} {status value : Word}
    (h : Result bytes base listLen index status value) :
    status = 0 ∨ status = 1 ∨ status = 2 := by
  cases h <;> simp

theorem Result.failure_value_zero {bytes : List (BitVec 8)} {base : Word}
    {listLen index : Nat} {status value : Word}
    (h : Result bytes base listLen index status value) (hne : status ≠ 0) :
    value = 0 := by
  cases h <;> simp_all

/-! ## Re-emitted code and linked closure -/

theorem wrapper_length : rlpFieldToU64Wrapper_prog.length = 37 := by decide
theorem program_length : rlpFieldToU64_prog.length = 37 := by
  simp [rlpFieldToU64_prog, wrapper_length]

theorem reemit_byte_tie :
    rlpFieldToU64_prog = rlpFieldToU64Wrapper_prog := by
  change (show List Instr from rlpFieldToU64Wrapper_prog) = _
  rfl

#guard rlpFieldToU64Wrapper_prog.length = 37
#guard rlpFieldToU64_prog.length = 37

abbrev B : Word := (GuestAddrs.rlp_field_to_u64 : Word)
abbrev K20B : Word := (GuestAddrs.rlp_list_nth_item : Word)
abbrev C64B : Word := (GuestAddrs.rlp_content_to_u64 : Word)
abbrev offsetCell : Word := (GuestAddrs.rfu_offset : Word)
abbrev lengthCell : Word := (GuestAddrs.rfu_length : Word)

def wrapperCode : CodeReq := CodeReq.ofProg B rlpFieldToU64_prog
def contentCode : CodeReq := rlp_content_to_u64_code C64B
def code : CodeReq := wrapperCode.union
  (EvmAsm.Codegen.RlpListNthItemSAsm.code.union contentCode)

theorem wrapper_list_disjoint :
    wrapperCode.Disjoint EvmAsm.Codegen.RlpListNthItemSAsm.code := by
  unfold wrapperCode EvmAsm.Codegen.RlpListNthItemSAsm.code B
    EvmAsm.Codegen.RlpListNthItemSAsm.B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]
    decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]
    decide
  · rw [program_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]
    decide

/-! ## Strict list-callee call shape -/

def listSavedRegs (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved) : Assertion :=
  (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)

def listCallResult
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ status offset len v11 v12,
    (((.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
      ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
       (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))) **
     ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen index
       oldOffset oldLen status offset len⌝) h

/-- Peel K20's restored `ra` out of its flat post, yielding the exact
    `(ra ** P) -> (ra ** Q)` contract expected by `callWithin_spec`. -/
theorem listCalleeCallContract
    (sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
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
      K20B saved.ra code
      ((.x1 ↦ᵣ saved.ra) **
       ((.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
        EvmAsm.Codegen.RlpListNthItemSAsm.entryRest listBase listLenW indexW
          offsetPtr lenPtr oldOffset oldLen bytes))
      ((.x1 ↦ᵣ saved.ra) **
       listCallResult sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
         listLen index) := by
  have hflat := EvmAsm.Codegen.RlpListNthItemSAsm.rlpListNthItem_flat_spec_within
    sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen saved bytes
    listLen index hlistLenW hindexW hindex hsalign hslack hover hvalid hret
  have hcode := cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.mono_union_right wrapper_list_disjoint
      CodeReq.union_mono_left a i hi) hflat
  refine cpsTripleWithin_weaken (fun h hp => by
    unfold listSavedRegs at hp
    rw [EvmAsm.Codegen.RlpListNthItemSAsm.regsAt_listNthFrame]
    xperm_hyp hp) (fun h hq => ?_) hcode
  unfold EvmAsm.Codegen.RlpListNthItemSAsm.flatReturnResult at hq
  obtain ⟨status, offset, len, v11, v12, hq⟩ := hq
  have hfixed : ((.x1 ↦ᵣ saved.ra) **
      (((.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
        ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
         (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))) **
       ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen index
         oldOffset oldLen status offset len⌝)) h := by
    unfold listSavedRegs
    rw [EvmAsm.Codegen.RlpListNthItemSAsm.regsAt_listNthFrame] at hq
    xperm_hyp hq
  obtain ⟨hRa, hRest, hd, hu, hra, hrest⟩ := hfixed
  refine ⟨hRa, hRest, hd, hu, hra, ?_⟩
  unfold listCallResult
  exact ⟨status, offset, len, v11, v12, hrest⟩

#print axioms listCalleeCallContract

/-- The real `jal` at wrapper instruction 11 composed with strict K20. -/
theorem callListNth
    (sp0 listBase listLenW indexW offsetPtr lenPtr oldOffset oldLen vOld : Word)
    (s0 s1 s2 s3 s4 s5 : Word) (bytes : List (BitVec 8))
    (listLen index : Nat)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
      { ra := B + 48, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
        s4 := s4, s5 := s5 }
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9))
      (B + 44) (B + 48) code
      ((.x1 ↦ᵣ vOld) **
       ((.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
        EvmAsm.Codegen.RlpListNthItemSAsm.entryRest listBase listLenW indexW
          offsetPtr lenPtr oldOffset oldLen bytes))
      ((.x1 ↦ᵣ (B + 48)) **
       listCallResult sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
         listLen index) := by
  dsimp
  let saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved :=
    { ra := B + 48, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
      s4 := s4, s5 := s5 }
  have hret : saved.ra &&& ~~~(1 : Word) = saved.ra := by
    dsimp [saved, B]
    decide
  have hcallee := listCalleeCallContract sp0 listBase listLenW indexW offsetPtr
    lenPtr oldOffset oldLen saved bytes listLen index hlistLenW hindexW hindex
    hsalign hslack hover hvalid hret
  have htarget : (B + 44) + signExtend21
      (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.rlp_field_to_u64 + 44)) = K20B := by
    unfold B K20B
    decide
  have hmem : ∀ a i, CodeReq.singleton (B + 44)
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.rlp_field_to_u64 + 44))) a = some i → code a = some i := by
    intro a i hi
    unfold code
    apply CodeReq.union_mono_left
    exact CodeReq.ofProg_mem_at B (B + 44) rlpFieldToU64_prog 11
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.rlp_field_to_u64 + 44))) (by bv_omega) (by decide) rfl
      (by decide) a i hi
  have hcall := callWithin_spec (B + 44) K20B vOld
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.rlp_field_to_u64 + 44))
    ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    htarget hmem (by pcf) hcallee
  dsimp [saved] at hcall
  exact hcall

#print axioms callListNth

/-! ## Three-register ABI frame -/

structure Saved where
  ra : Word
  s0 : Word
  s1 : Word

def frame : FrameDesc := [(.x1, 0), (.x8, 8), (.x9, 16)]

def savedVals (saved : Saved) : Reg → Word
  | .x1 => saved.ra
  | .x8 => saved.s0
  | .x9 => saved.s1
  | _ => 0

def savedFrame (newSp : Word) (saved : Saved) : Assertion :=
  (newSp ↦ₘ saved.ra) ** ((newSp + 8) ↦ₘ saved.s0) **
  ((newSp + 16) ↦ₘ saved.s1)

theorem regsAt_frame (saved : Saved) :
    regsAt frame (savedVals saved) =
      ((.x1 ↦ᵣ saved.ra) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1)) := by
  simp [frame, regsAt, savedVals, sepConj_emp_right']

theorem frameSlotsSaved_frame (newSp : Word) (saved : Saved) :
    frameSlotsSaved frame newSp (savedVals saved) = savedFrame newSp saved := by
  simp [frame, frameSlotsSaved, savedFrame, savedVals, sepConj_emp_right',
    signExtend12]

@[irreducible] def setupRest
    (listBase listLenW indexW outputPtr oldOut oldOffset oldLen : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
  regOwn .x13 ** regOwn .x14 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** regOwn .x21 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  (outputPtr ↦ₘ oldOut) ** (offsetCell ↦ₘ oldOffset) **
  (lengthCell ↦ₘ oldLen)

theorem pcFree_setupRest listBase listLenW indexW outputPtr oldOut oldOffset oldLen
    bytes : (setupRest listBase listLenW indexW outputPtr oldOut oldOffset oldLen
      bytes).pcFree := by
  unfold setupRest
  pcf

private theorem reassoc4_to_frame {A C D F : Assertion} : ∀ h,
    (A ** C ** D ** F) h → (((A ** C ** D) ** F) h) := by
  intro h hp
  have h1 := (sepConj_assoc h).mpr hp
  have h2 := (sepConj_assoc h).mpr h1
  exact sepConj_mono_left (fun h' hh => (sepConj_assoc h').mp hh) h h2

private theorem frame_to_reassoc4 {A C D F : Assertion} : ∀ h,
    (((A ** C ** D) ** F) h) → (A ** C ** D ** F) h := by
  intro h hp
  have h1 := sepConj_mono_left (fun h' hh => (sepConj_assoc h').mpr hh) h hp
  have h2 := (sepConj_assoc h).mp h1
  exact (sepConj_assoc h).mp h2

/-- Allocate K34's 32-byte frame and save `ra/s0/s1` (instructions 0--3). -/
theorem setupPrologue
    (sp0 newSp : Word) (saved : Saved) (F : Assertion)
    (hnewSp : newSp = sp0 + signExtend12 (-32 : BitVec 12)) (hF : F.pcFree) :
    cpsTripleWithin 4 B (B + 16) code
      ((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals saved) **
       frameSlotsOwn frame newSp ** F)
      ((.x2 ↦ᵣ newSp) ** regsAt frame (savedVals saved) **
       savedFrame newSp saved ** F) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12) B (by decide)
  rw [← hnewSp] at ha0
  have ha := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B B rlpFieldToU64_prog 0
      (.ADDI .x2 .x2 (-32 : BitVec 12)) rfl (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt frame (savedVals saved) ** frameSlotsOwn frame newSp ** F)
    (pcFree_sepConj (pcFree_regsAt _ _)
      (pcFree_sepConj (pcFree_frameSlotsOwn _ _) hF)) ha
  have hs0 := storeSeq_spec frame newSp (savedVals saved) (B + 4) (by decide)
  have hstoreMono : ∀ a i,
      CodeReq.ofProg (B + 4) (storeProg frame) a = some i →
        wrapperCode a = some i := by
    intro a i hi
    exact CodeReq.ofProg_mono_sub B (B + 4) rlpFieldToU64_prog
      (storeProg frame) 1 (by bv_omega) (by rfl)
      (by rw [program_length]; simp [frame])
      (by rw [program_length]; decide) a i hi
  have hs := cpsTripleWithin_extend_code hstoreMono hs0
  rw [show B + 4 + BitVec.ofNat 64 (4 * frame.length) = B + 16 from by
    simp [frame]; bv_omega] at hs
  have hsF := cpsTripleWithin_frameR
    F hF hs
  have hsF' := cpsTripleWithin_weaken (P' :=
      (.x2 ↦ᵣ newSp) ** regsAt frame (savedVals saved) **
        frameSlotsOwn frame newSp ** F)
    (Q' := (.x2 ↦ᵣ newSp) ** regsAt frame (savedVals saved) **
      savedFrame newSp saved ** F)
    (fun h hp => reassoc4_to_frame h hp)
    (fun h hq => by
      rw [frameSlotsSaved_frame] at hq
      exact frame_to_reassoc4 h hq) hsF
  have hlocal := cpsTripleWithin_seq_same_cr haF hsF'
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hlocal

#print axioms setupPrologue

/-- Save the input/output pointers and zero the caller-visible output cell
    (instructions 4--6), before either strict callee can fail. -/
theorem setupMovesZero
    (listBase outputPtr oldOut old8 old9 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (B + 16) (B + 28) code
      (((.x8 ↦ᵣ old8) ** (.x9 ↦ᵣ old9) ** (.x10 ↦ᵣ listBase) **
       (.x13 ↦ᵣ outputPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (outputPtr ↦ₘ oldOut)) ** F)
      (((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) ** (.x10 ↦ᵣ listBase) **
       (.x13 ↦ᵣ outputPtr) ** (.x0 ↦ᵣ (0 : Word)) **
       (outputPtr ↦ₘ (0 : Word))) ** F) := by
  have h0 := mv_spec_gen_within .x8 .x10 listBase old8 (B + 16) (by decide)
  have h0' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 16) rlpFieldToU64_prog 4 (.MV .x8 .x10)
      (by bv_omega) (by rw [program_length]; decide) rfl
      (by rw [program_length]; decide)) h0
  have h1 := mv_spec_gen_within .x9 .x13 outputPtr old9 (B + 20) (by decide)
  have h1' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 20) rlpFieldToU64_prog 5 (.MV .x9 .x13)
      (by bv_omega) (by rw [program_length]; decide) rfl
      (by rw [program_length]; decide)) h1
  have h2 := sd_spec_gen_within .x9 .x0 outputPtr (0 : Word) oldOut
    (0 : BitVec 12) (B + 24)
  rw [show outputPtr + signExtend12 (0 : BitVec 12) = outputPtr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h2
  have h2' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 24) rlpFieldToU64_prog 6
      (.SD .x9 .x0 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h2
  have h0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ old9) ** (.x13 ↦ᵣ outputPtr) ** (.x0 ↦ᵣ (0 : Word)) **
      (outputPtr ↦ₘ oldOut)) (by pcf) h0'
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) **
      (.x0 ↦ᵣ (0 : Word)) ** (outputPtr ↦ₘ oldOut)) (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) **
      (.x13 ↦ᵣ outputPtr)) (by pcf) h2'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  have hlocal := cpsTripleWithin_weaken
    (P' := (.x8 ↦ᵣ old8) ** (.x9 ↦ᵣ old9) ** (.x10 ↦ᵣ listBase) **
      (.x13 ↦ᵣ outputPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (outputPtr ↦ₘ oldOut))
    (Q' := (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) **
      (.x10 ↦ᵣ listBase) ** (.x13 ↦ᵣ outputPtr) **
      (.x0 ↦ᵣ (0 : Word)) ** (outputPtr ↦ₘ (0 : Word)))
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h012
  have hframed := cpsTripleWithin_frameR F hF hlocal
  have hall := cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hframed
  exact hall

#print axioms setupMovesZero

/-- Materialize `rfu_offset` and `rfu_length` in `a3/a4`
    (instructions 7--10), with both addresses proved by `la_resolve`. -/
theorem setupGlobals (old13 old14 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (B + 28) (B + 44) code
      (((.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14)) ** F)
      (((.x13 ↦ᵣ offsetCell) ** (.x14 ↦ᵣ lengthCell)) ** F) := by
  have hau0 := CodeReq.ofProg_mem_at B (B + 28) rlpFieldToU64_prog 7
    (.AUIPC .x13 (laHi GuestAddrs.rfu_offset
      (GuestAddrs.rlp_field_to_u64 + 28))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had0 := CodeReq.ofProg_mem_at B (B + 32) rlpFieldToU64_prog 8
    (.ADDI .x13 .x13 (laLo GuestAddrs.rfu_offset
      (GuestAddrs.rlp_field_to_u64 + 28))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have h0 := la_materialize_within .x13 old13 (B + 28) offsetCell
    (by decide) (by unfold B offsetCell; decide) hau0 had0
  have hau1 := CodeReq.ofProg_mem_at B (B + 36) rlpFieldToU64_prog 9
    (.AUIPC .x14 (laHi GuestAddrs.rfu_length
      (GuestAddrs.rlp_field_to_u64 + 36))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had1 := CodeReq.ofProg_mem_at B (B + 40) rlpFieldToU64_prog 10
    (.ADDI .x14 .x14 (laLo GuestAddrs.rfu_length
      (GuestAddrs.rlp_field_to_u64 + 36))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have h1 := la_materialize_within .x14 old14 (B + 36) lengthCell
    (by decide) (by unfold B lengthCell; decide) hau1 had1
  have h0F := cpsTripleWithin_frameR ((.x14 ↦ᵣ old14)) (by pcf) h0
  have h1F := cpsTripleWithin_frameR ((.x13 ↦ᵣ offsetCell)) (by pcf) h1
  have hlocal := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have hlocal' := cpsTripleWithin_weaken
    (P' := (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14))
    (Q' := (.x13 ↦ᵣ offsetCell) ** (.x14 ↦ᵣ lengthCell))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hlocal
  have hframed := cpsTripleWithin_frameR F hF hlocal'
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hframed

#print axioms setupGlobals

theorem frameRegs_implies_owned (s0 s1 : Word) : ∀ h,
    (regOwn .x1 ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1)) h →
      regsOwnAt frame h := by
  intro h hp
  unfold regsOwnAt frame
  simp only [List.foldr_cons, List.foldr_nil, sepConj_emp_right']
  exact sepConj_mono (fun _ hx => hx)
    (sepConj_mono (regIs_implies_regOwn .x8)
      (regIs_implies_regOwn .x9)) h hp

#print axioms Result.status_cases
#print axioms frameRegs_implies_owned

end EvmAsm.Codegen.RlpFieldToU64SAsm
