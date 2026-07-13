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

theorem wrapper_content_disjoint : wrapperCode.Disjoint contentCode := by
  unfold wrapperCode contentCode rlp_content_to_u64_code B C64B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [program_length]; decide
  · rw [rlp_content_to_u64_prog_length]; decide
  · rw [program_length, rlp_content_to_u64_prog_length]; decide

theorem list_content_disjoint :
    EvmAsm.Codegen.RlpListNthItemSAsm.code.Disjoint contentCode := by
  unfold EvmAsm.Codegen.RlpListNthItemSAsm.code contentCode
    EvmAsm.Codegen.RlpListNthItemSAsm.B rlp_content_to_u64_code C64B
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [rlp_content_to_u64_prog_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length,
      rlp_content_to_u64_prog_length]
    decide

theorem contentCode_mono : ∀ a i, contentCode a = some i → code a = some i := by
  intro a i hi
  unfold code
  exact CodeReq.mono_union_right wrapper_content_disjoint
    (CodeReq.mono_union_right list_content_disjoint (fun _ _ h => h)) a i hi

/-! ## Strict list-callee call shape -/

def listOtherSaved (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved) : Assertion :=
  (.x9 ↦ᵣ saved.s1) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5)

def listSavedRegs (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved) : Assertion :=
  (.x8 ↦ᵣ saved.s0) ** listOtherSaved saved

def listCallRest
    (sp0 listBase offsetPtr lenPtr : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (offset len v11 v12 : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** listSavedRegs saved ** stackFree sp0 8 **
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
   (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
   regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
   bytesRegion listBase bytes **
   (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len))

def listCallCore
    (sp0 listBase offsetPtr lenPtr : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (status offset len v11 v12 : Word) : Assertion :=
  (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) **
  listCallRest sp0 listBase offsetPtr lenPtr saved bytes offset len v11 v12

def listCallResult
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ status offset len v11 v12,
    ((listCallCore sp0 listBase offsetPtr lenPtr saved bytes
        status offset len v11 v12) **
     ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen index
       oldOffset oldLen status offset len⌝) h

theorem listResult_cases
    {bytes : List (BitVec 8)} {listBase : Word} {listLen index : Nat}
    {oldOffset oldLen status offset len : Word}
    (h : EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen index
      oldOffset oldLen status offset len) :
    (status = 0 ∧
      EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
        offset len) ∨
    (status = 1 ∧ offset = oldOffset ∧ len = oldLen ∧
      EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen index) := by
  cases h with
  | ok offset len h_ok => exact Or.inl ⟨rfl, h_ok⟩
  | fail h_fail => exact Or.inr ⟨rfl, rfl, rfl, h_fail⟩

#print axioms listResult_cases

def listSelected
    (sp0 listBase offsetPtr lenPtr : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (listCallCore sp0 listBase offsetPtr lenPtr saved bytes 0 offset len v11 v12 **
     ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
       offset len⌝) h

def listFailed
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ v11 v12,
    (listCallCore sp0 listBase offsetPtr lenPtr saved bytes 1 oldOffset oldLen
      v11 v12 **
     ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen index⌝) h

theorem listCallResult_cases
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    listCallResult sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
      listLen index h →
    listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index h ∨
    listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
      listLen index h := by
  intro h hq
  unfold listCallResult at hq
  obtain ⟨status, offset, len, v11, v12, hq⟩ := hq
  extract_pure_deep hq
  obtain ⟨hcore, hresult⟩ := hq
  rcases listResult_cases hresult with ⟨rfl, h_ok⟩ | ⟨rfl, rfl, rfl, h_fail⟩
  · left
    unfold listSelected
    exact ⟨offset, len, v11, v12,
      (sepConj_pure_right h).2 ⟨hcore, h_ok⟩⟩
  · right
    unfold listFailed
    exact ⟨v11, v12, (sepConj_pure_right h).2 ⟨hcore, h_fail⟩⟩

#print axioms listCallResult_cases

theorem pcFree_listCallRest sp0 listBase offsetPtr lenPtr saved bytes offset len
    v11 v12 : (listCallRest sp0 listBase offsetPtr lenPtr saved bytes offset len
      v11 v12).pcFree := by
  unfold listCallRest listSavedRegs listOtherSaved
  pcf

/-- On a strict K20 success, instruction 12's `bne a0, zero` is necessarily
    not taken and preserves the selected offset/length witness. -/
theorem branchSelected
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 48) code
      (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index)
      (B + 116)
        (listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
          listLen index)
      (B + 52)
        (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index) := by
  unfold listSelected
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_ok => ?_)
  have hb0 := bne_spec_gen_within .x10 .x0 (68 : BitVec 13)
    (0 : Word) (0 : Word) (B + 48)
  rw [show B + 48 + signExtend13 (68 : BitVec 13) = B + 116 from by decide,
    show B + 48 + 4 = B + 52 from by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 48) rlpFieldToU64_prog 12
      (.BNE .x10 .x0 (68 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R : Assertion :=
    listCallRest sp0 listBase offsetPtr lenPtr saved bytes offset len v11 v12 **
    ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
      offset len⌝
  have hbF := cpsBranchWithin_frameR R
    (pcFree_sepConj (pcFree_listCallRest _ _ _ _ _ _ _ _ _ _)
      (by pcf)) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hbF
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold listCallCore at hp
      unfold R
      xperm_pure hp) (fun h hp => by
      extract_pure_deep hp
      obtain ⟨h_ne, -⟩ := hp
      exact False.elim (h_ne rfl)) (fun h hp => ?_) hbC
  extract_pure_deep hp
  obtain ⟨-, hstate⟩ := hp
  refine ⟨offset, len, v11, v12, ?_⟩
  unfold R at hstate
  unfold listCallCore
  xperm_pure hstate

#print axioms branchSelected

/-- On a strict K20 failure, instruction 12's `bne a0, zero` is necessarily
    taken and preserves the exact unchanged offset/length cells. -/
theorem branchFailed
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 48) code
      (listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
        listLen index)
      (B + 116)
        (listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
          listLen index)
      (B + 52)
        (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index) := by
  unfold listFailed
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_fail => ?_)
  have hb0 := bne_spec_gen_within .x10 .x0 (68 : BitVec 13)
    (1 : Word) (0 : Word) (B + 48)
  rw [show B + 48 + signExtend13 (68 : BitVec 13) = B + 116 from by decide,
    show B + 48 + 4 = B + 52 from by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 48) rlpFieldToU64_prog 12
      (.BNE .x10 .x0 (68 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R : Assertion :=
    listCallRest sp0 listBase offsetPtr lenPtr saved bytes oldOffset oldLen
      v11 v12 **
    ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen index⌝
  have hbF := cpsBranchWithin_frameR R
    (pcFree_sepConj (pcFree_listCallRest _ _ _ _ _ _ _ _ _ _)
      (by pcf)) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hbF
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold listCallCore at hp
      unfold R
      xperm_pure hp) (fun h hp => ?_) (fun h hp => by
      extract_pure_deep hp
      obtain ⟨h_eq, -⟩ := hp
      have h_ne : (1 : Word) ≠ 0 := by decide
      exact False.elim (h_ne h_eq)) hbC
  extract_pure_deep hp
  obtain ⟨-, hstate⟩ := hp
  refine ⟨v11, v12, ?_⟩
  unfold R at hstate
  unfold listCallCore
  xperm_pure hstate

#print axioms branchFailed

/-- Unified semantic dispatch for instruction 12, directly over K20's
    existential result post. -/
theorem listResultBranch
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 48) code
      (listCallResult sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
        listLen index)
      (B + 116)
        (listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
          listLen index)
      (B + 52)
        (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index) := by
  have hs := branchSelected sp0 listBase offsetPtr lenPtr oldOffset oldLen saved
    bytes listLen index
  have hf := branchFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved
    bytes listLen index
  have hor := cpsBranchWithin_pre_or hs hf
  exact cpsBranchWithin_weaken
    (fun h hp => listCallResult_cases sp0 listBase offsetPtr lenPtr oldOffset
      oldLen saved bytes listLen index h hp)
    (fun _ hq => hq) (fun _ hq => hq) hor

#print axioms listResultBranch

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
    unfold listSavedRegs listOtherSaved at hp
    rw [EvmAsm.Codegen.RlpListNthItemSAsm.regsAt_listNthFrame]
    xperm_hyp hp) (fun h hq => ?_) hcode
  unfold EvmAsm.Codegen.RlpListNthItemSAsm.flatReturnResult at hq
  obtain ⟨status, offset, len, v11, v12, hq⟩ := hq
  have hfixed : ((.x1 ↦ᵣ saved.ra) **
      ((listCallCore sp0 listBase offsetPtr lenPtr saved bytes status offset len
        v11 v12) **
       ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen index
         oldOffset oldLen status offset len⌝)) h := by
    unfold listCallCore listCallRest listSavedRegs listOtherSaved
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

/-- Shared three-register ABI restore/deallocate/return tail (instructions
    32--36), generic over the semantic result footprint. -/
theorem restoreTail (sp0 newSp : Word) (saved : Saved)
    (F : Assertion) (hF : F.pcFree)
    (hnewSp : newSp = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin 5 (B + 128) saved.ra code
      (((.x2 ↦ᵣ newSp) ** regsOwnAt frame ** savedFrame newSp saved) ** F)
      (((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals saved) **
        savedFrame newSp saved) ** F) := by
  have hl0 := loadSeq_spec_own frame newSp (savedVals saved)
    (B + 128) (by decide) (by decide)
  have hlMono : ∀ a i,
      CodeReq.ofProg (B + 128) (loadProg frame) a = some i →
        wrapperCode a = some i := by
    intro a i hi
    exact CodeReq.ofProg_mono_sub B (B + 128) rlpFieldToU64_prog
      (loadProg frame) 32 (by bv_omega) (by rfl)
      (by rw [program_length]; simp [frame])
      (by rw [program_length]; decide) a i hi
  have hl := cpsTripleWithin_extend_code hlMono hl0
  rw [show B + 128 + BitVec.ofNat 64 (4 * frame.length) = B + 140 from by
    simp [frame]; bv_omega] at hl
  rw [frameSlotsSaved_frame] at hl
  have hlF := cpsTripleWithin_frameR F hF hl
  have hd0 := addi_spec_gen_same_within .x2 newSp (32 : BitVec 12) (B + 140)
    (by decide)
  rw [show newSp + signExtend12 (32 : BitVec 12) = sp0 from by
    rw [hnewSp]
    exact sext_frameRestore sp0 (-32 : BitVec 12) (32 : BitVec 12) (by decide)] at hd0
  have hd := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 140) rlpFieldToU64_prog 35
      (.ADDI .x2 .x2 (32 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hd0
  have hdF := cpsTripleWithin_frameR
    (regsAt frame (savedVals saved) ** savedFrame newSp saved ** F)
    (by
      apply pcFree_sepConj
      · exact pcFree_regsAt _ _
      · apply pcFree_sepConj
        · unfold savedFrame; pcf
        · exact hF) hd
  have hr0 := EvmAsm.Evm64.ret_spec_within' (B + 144) saved.ra
  rw [hret] at hr0
  have hr := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 144) rlpFieldToU64_prog 36
      (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hr0
  have hrF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
      savedFrame newSp saved) ** F) (by
        apply pcFree_sepConj
        · exact pcFree_sepConj pcFree_regIs
            (pcFree_sepConj pcFree_regIs
              (pcFree_sepConj pcFree_regIs (by unfold savedFrame; pcf)))
        · exact hF) hr
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlF hdF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_frame] at hp
    xperm_hyp hp) h12 hrF
  have hlocal := cpsTripleWithin_weaken
    (P' := (((.x2 ↦ᵣ newSp) ** regsOwnAt frame ** savedFrame newSp saved) ** F))
    (Q' := (((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals saved) **
      savedFrame newSp saved) ** F))
    (fun _ hp => by xperm_hyp hp)
    (fun h hp => by rw [regsAt_frame]; xperm_hyp hp) h123
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hlocal

#print axioms restoreTail

/-- Failure-status materialization and jump to the shared restore tail
    (instructions 29--30). -/
theorem failureJoin
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsTripleWithin 2 (B + 116) (B + 128) code
      (listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
        listLen index)
      (listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
        listLen index) := by
  unfold listFailed
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_pure hp)
    (fun _ hq => hq) (cpsTripleWithin_pure_pre
      (P := EvmAsm.Codegen.RlpListNthItemSAsm.Failure bytes listBase listLen index)
      (H := listCallCore sp0 listBase offsetPtr lenPtr saved bytes 1 oldOffset
        oldLen v11 v12) (fun h_fail => ?_))
  have hli0 := li_spec_gen_within .x10 (1 : Word) (1 : Word) (B + 116)
    (by decide)
  have hli := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 116) rlpFieldToU64_prog 29
      (.LI .x10 (1 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) hli0
  let R : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) **
    listCallRest sp0 listBase offsetPtr lenPtr saved bytes oldOffset oldLen
      v11 v12
  have hliF := cpsTripleWithin_frameR R (by
    unfold R
    exact pcFree_sepConj pcFree_regIs
      (pcFree_listCallRest _ _ _ _ _ _ _ _ _ _)) hli
  have hj0 := jal_x0_spec_gen_within (8 : BitVec 21) (B + 120)
  rw [show B + 120 + signExtend21 (8 : BitVec 21) = B + 128 from by decide] at hj0
  have hj := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 120) rlpFieldToU64_prog 30
      (.JAL .x0 (8 : BitVec 21)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) hj0
  have hjF0 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (1 : Word)) ** R) (by
      apply pcFree_sepConj
      · exact pcFree_regIs
      · unfold R
        exact pcFree_sepConj pcFree_regIs
          (pcFree_listCallRest _ _ _ _ _ _ _ _ _ _)) hj
  have hjF := cpsTripleWithin_weaken
    (fun h hp => (sepConj_emp_left h).2 hp)
    (fun h hq => (sepConj_emp_left h).1 hq) hjF0
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hliF hjF
  have hcode := cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hseq
  refine cpsTripleWithin_weaken (fun h hp => by
      unfold listCallCore at hp
      unfold R
      xperm_hyp hp) (fun h hq => ?_) hcode
  refine ⟨v11, v12, ?_⟩
  unfold R at hq
  unfold listCallCore
  xperm_pure hq

#print axioms failureJoin

/-- Selected-item address setup (instructions 13--19): reload K20's exact
    offset/length cells and form the content pointer for the scalar callee. -/
theorem selectedSetupExact
    (listBase offset len old5 v11 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (B + 52) (B + 80) code
      (((.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
        (.x8 ↦ᵣ listBase) ** (offsetCell ↦ₘ offset) **
        (lengthCell ↦ₘ len)) ** F)
      (((.x5 ↦ᵣ lengthCell) ** (.x10 ↦ᵣ (listBase + offset)) **
        (.x11 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
        (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)) ** F) := by
  have hau0 := CodeReq.ofProg_mem_at B (B + 52) rlpFieldToU64_prog 13
      (.AUIPC .x5 (laHi GuestAddrs.rfu_offset
        (GuestAddrs.rlp_field_to_u64 + 52))) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had0 := CodeReq.ofProg_mem_at B (B + 56) rlpFieldToU64_prog 14
      (.ADDI .x5 .x5 (laLo GuestAddrs.rfu_offset
        (GuestAddrs.rlp_field_to_u64 + 52))) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have h0 := la_materialize_within .x5 old5 (B + 52) offsetCell
    (by decide) (by unfold B offsetCell; decide) hau0 had0
  have h1 := ld_spec_gen_within .x10 .x5 offsetCell (0 : Word) offset
    (0 : BitVec 12) (B + 60) (by decide)
  rw [show offsetCell + signExtend12 (0 : BitVec 12) = offsetCell from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h1
  have h1' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 60) rlpFieldToU64_prog 15
      (.LD .x10 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h1
  have h2 := add_spec_gen_rd_eq_rs2_within .x10 .x8 listBase offset
    (B + 64) (by decide)
  have h2' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 64) rlpFieldToU64_prog 16
      (.ADD .x10 .x8 .x10) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h2
  have hau1 := CodeReq.ofProg_mem_at B (B + 68) rlpFieldToU64_prog 17
      (.AUIPC .x5 (laHi GuestAddrs.rfu_length
        (GuestAddrs.rlp_field_to_u64 + 68))) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had1 := CodeReq.ofProg_mem_at B (B + 72) rlpFieldToU64_prog 18
      (.ADDI .x5 .x5 (laLo GuestAddrs.rfu_length
        (GuestAddrs.rlp_field_to_u64 + 68))) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have h3 := la_materialize_within .x5 offsetCell (B + 68) lengthCell
    (by decide) (by unfold B lengthCell; decide) hau1 had1
  have h4 := ld_spec_gen_within .x11 .x5 lengthCell v11 len
    (0 : BitVec 12) (B + 76) (by decide)
  rw [show lengthCell + signExtend12 (0 : BitVec 12) = lengthCell from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h4
  have h4' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 76) rlpFieldToU64_prog 19
      (.LD .x11 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h4
  have h0F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x8 ↦ᵣ listBase) **
      (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)) (by pcf) h0
  have h1F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x8 ↦ᵣ listBase) ** (lengthCell ↦ₘ len))
    (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ offsetCell) ** (.x11 ↦ᵣ v11) **
      (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)) (by pcf) h2'
  have h3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (listBase + offset)) ** (.x11 ↦ᵣ v11) **
      (.x8 ↦ᵣ listBase) ** (offsetCell ↦ₘ offset) **
      (lengthCell ↦ₘ len)) (by pcf) h3
  have h4F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (listBase + offset)) ** (.x8 ↦ᵣ listBase) **
      (offsetCell ↦ₘ offset)) (by pcf) h4'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  have h0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 h3F
  have h01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0123 h4F
  have hlocal : cpsTripleWithin 7 (B + 52) (B + 80) wrapperCode
      ((.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
        (.x8 ↦ᵣ listBase) ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len))
      ((.x5 ↦ᵣ lengthCell) ** (.x10 ↦ᵣ (listBase + offset)) **
        (.x11 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
        (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h01234
  have hframed := cpsTripleWithin_frameR F hF hlocal
  exact cpsTripleWithin_extend_code (cr' := code) (fun a i hi => by
    unfold code
    exact CodeReq.union_mono_left a i hi) hframed

#print axioms selectedSetupExact

def selectedCarry
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (v12 : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** listOtherSaved saved ** stackFree sp0 8 **
  regOwn .x6 ** regOwn .x7 ** (.x12 ↦ᵣ v12) **
  regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion listBase bytes

theorem pcFree_selectedCarry sp0 listBase saved bytes v12 :
    (selectedCarry sp0 listBase saved bytes v12).pcFree := by
  unfold selectedCarry listOtherSaved
  pcf

def contentReady
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12,
    ((((.x5 ↦ᵣ lengthCell) ** (.x10 ↦ᵣ (listBase + offset)) **
       (.x11 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
       (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)) **
      selectedCarry sp0 listBase saved bytes v12) **
     ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
       offset len⌝) h

/-- Lift `selectedSetupExact` over K20's owned `x5` scratch register and its
    existential selected item. -/
theorem selectedSetup
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase) :
    cpsTripleWithin 7 (B + 52) (B + 80) code
      (listSelected sp0 listBase offsetCell lengthCell saved bytes listLen index)
      (contentReady sp0 listBase saved bytes listLen index) := by
  unfold listSelected
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_pure hp)
    (fun _ hq => hq) (cpsTripleWithin_pure_pre
      (P := EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
        index offset len)
      (H := listCallCore sp0 listBase offsetCell lengthCell saved bytes 0 offset
        len v11 v12) (fun h_ok => ?_))
  let P : Assertion :=
    (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x8 ↦ᵣ listBase) **
    (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
    selectedCarry sp0 listBase saved bytes v12 **
    ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
      offset len⌝
  have howned := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) (P := P)
    (Q := contentReady sp0 listBase saved bytes listLen index)
    (fun old5 => by
      have hs := selectedSetupExact listBase offset len old5 v11
        (selectedCarry sp0 listBase saved bytes v12 **
          ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
            offset len⌝)
        (pcFree_sepConj (pcFree_selectedCarry _ _ _ _ _) (by pcf))
      refine cpsTripleWithin_weaken
        (Q' := contentReady sp0 listBase saved bytes listLen index)
        (fun h hp => by
          unfold P at hp
          xperm_pure hp) (fun h hq => ?_) hs
      unfold contentReady
      refine ⟨offset, len, v12, ?_⟩
      xperm_pure hq)
  refine cpsTripleWithin_weaken (fun h hp => by
      unfold listCallCore listCallRest listSavedRegs at hp
      unfold P selectedCarry
      rw [hs0] at hp
      xperm_pure hp) (fun _ hq => hq) howned

#print axioms selectedSetup

theorem strictNthItem_last_decode
    {bytes : List (BitVec 8)} {base : Word} {endOff index off : Nat}
    {next len : Word}
    (h : EvmAsm.Codegen.RlpListNthItemSAsm.StrictNthItem bytes base
      (base + BitVec.ofNat 64 endOff) index off next len)
    (hoff : off ≤ endOff) (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    ∃ lastOff, lastOff ≤ endOff ∧
      rlpItemDecode bytes lastOff (base + BitVec.ofNat 64 lastOff)
        (base + BitVec.ofNat 64 endOff) next len := by
  induction h with
  | zero off next len hitem => exact ⟨off, hoff, hitem⟩
  | succ index off next0 len0 finalNext finalLen hitem hrest ih =>
      have ha := BalAccountNonstorageFinalsSpec.rlpItemDecode_advance hitem hoff hover
      exact ih ha.2.2

/-- A strict selected item exposes exactly the bounds required by the scalar
    callee at `(base + offset, len)`. -/
theorem success_content_bounds
    {bytes : List (BitVec 8)} {base offset len : Word} {listLen index : Nat}
    (h : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes base listLen index
      offset len)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    offset.toNat + len.toNat ≤ bytes.length ∧
    base.toNat + (offset.toNat + len.toNat) ≤ 2 ^ 64 := by
  obtain ⟨cursorOff, endPtr, next, hlist, hnth, hoffset⟩ := h
  have hend := EvmAsm.Codegen.RlpListNthItemSAsm.StrictListPayload.end_eq hlist
  subst endPtr
  have hcursor := EvmAsm.Codegen.RlpListNthItemSAsm.StrictListPayload.cursor_le hlist
  have hover' : base.toNat + listLen + 9 < 2 ^ 64 := by omega
  obtain ⟨lastOff, hlast, hitem⟩ :=
    strictNthItem_last_decode hnth hcursor hover'
  have hs := BalAccountNonstorageFinalsSpec.rlpItemDecode_spanStart
    hitem hlast hover'
  subst offset
  constructor
  · omega
  · omega

#print axioms strictNthItem_last_decode
#print axioms success_content_bounds

def contentOutcome (srcBytes : List (BitVec 8)) (srcOff len : Nat) : Assertion :=
  fun h =>
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
    (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
      ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
    (((.x10 ↦ᵣ BitVec.ofNat 64
        (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
      (.x11 ↦ᵣ (0 : Word)) **
      ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0⌝) h)

inductive ScalarOutcome (bytes : List (BitVec 8)) (offset len : Nat) :
    Word → Word → Prop
  | tooLong (h : 8 < len) : ScalarOutcome bytes offset len 0 2
  | empty (h : len = 0) : ScalarOutcome bytes offset len 0 0
  | noncanonical (hpos : 0 < len) (hzero : getByteAt bytes offset = 0) :
      ScalarOutcome bytes offset len 0 3
  | success (hpos : 0 < len) (hnz : getByteAt bytes offset ≠ 0) :
      ScalarOutcome bytes offset len
        (BitVec.ofNat 64
          (Nat.fromBytesBE ((bytes.drop offset).take len))) 0

theorem contentOutcome_semantic (bytes : List (BitVec 8)) (offset len : Nat) : ∀ h,
    contentOutcome bytes offset len h →
    ∃ value status,
      (((.x10 ↦ᵣ value) ** (.x11 ↦ᵣ status)) **
       ⌜ScalarOutcome bytes offset len value status⌝) h := by
  intro h hp
  unfold contentOutcome at hp
  rcases hp with hp | hp | hp | hp
  · extract_pure_deep hp
    obtain ⟨h_len, hstate⟩ := hp
    exact ⟨0, 2, (sepConj_pure_right h).2
      ⟨(by xperm_hyp hstate), .tooLong h_len⟩⟩
  · extract_pure_deep hp
    obtain ⟨h_len, hstate⟩ := hp
    exact ⟨0, 0, (sepConj_pure_right h).2
      ⟨(by xperm_hyp hstate), .empty h_len⟩⟩
  · extract_pure_deep hp
    obtain ⟨h_sem, hstate⟩ := hp
    exact ⟨0, 3, (sepConj_pure_right h).2
      ⟨(by xperm_hyp hstate), .noncanonical h_sem.1 h_sem.2⟩⟩
  · extract_pure_deep hp
    obtain ⟨h_sem, hstate⟩ := hp
    exact ⟨_, 0, (sepConj_pure_right h).2
      ⟨(by xperm_hyp hstate), .success h_sem.1 h_sem.2⟩⟩

#print axioms contentOutcome_semantic

def contentCallPost (srcBase : Word) (srcBytes : List (BitVec 8))
    (srcOff len : Nat) : Assertion :=
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) **
  contentOutcome srcBytes srcOff len

def contentRawPost (srcBase : Word) (srcBytes : List (BitVec 8))
    (srcOff len : Nat) : Assertion :=
  (.x1 ↦ᵣ (B + 84)) ** contentCallPost srcBase srcBytes srcOff len

/-- Actual instruction-20 call, specialized to the selected Word offset/len
    and the verified scalar callee's unified four-way post. -/
theorem callContentExact
    (srcBase offset len vOld x6Old x7Old x28Old : Word)
    (srcBytes : List (BitVec 8))
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : offset.toNat + len.toNat ≤ srcBytes.length)
    (hsover : srcBase.toNat + (offset.toNat + len.toNat) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len.toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (offset.toNat + k)) = true) :
    cpsTripleWithin (1 + (7 * len.toNat + 11)) (B + 80) (B + 84) code
      ((.x1 ↦ᵣ vOld) **
       ((.x10 ↦ᵣ (srcBase + offset)) ** (.x11 ↦ᵣ len) **
        (.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
        (.x28 ↦ᵣ x28Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes))
      (contentRawPost srcBase srcBytes offset.toNat len.toNat) := by
  have hcallee0 := rlp_content_to_u64_spec_within C64B srcBase (B + 84)
    lengthCell x6Old x7Old x28Old srcBytes offset.toNat len.toNat
    len.isLt hsalign hslen hsover hsvalid
  rw [show (B + 84) &&& ~~~(1 : Word) = B + 84 from by unfold B; decide,
    show srcBase + BitVec.ofNat 64 offset.toNat = srcBase + offset from by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
    show (BitVec.ofNat 64 len.toNat : Word) = len from by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]] at hcallee0
  have hcallee1 := cpsTripleWithin_extend_code contentCode_mono hcallee0
  have hcallee : cpsTripleWithin (7 * len.toNat + 11) C64B (B + 84) code
      ((.x1 ↦ᵣ (B + 84)) **
       ((.x10 ↦ᵣ (srcBase + offset)) ** (.x11 ↦ᵣ len) **
        (.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
        (.x28 ↦ᵣ x28Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (B + 84)) **
       contentCallPost srcBase srcBytes offset.toNat len.toNat) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ?_) hcallee1
    unfold contentCallPost contentOutcome
    xperm_pure hq
  have hmem : ∀ a i, CodeReq.singleton (B + 80)
      (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64
        (GuestAddrs.rlp_field_to_u64 + 80))) a = some i → code a = some i := by
    intro a i hi
    unfold code
    apply CodeReq.union_mono_left
    exact CodeReq.ofProg_mem_at B (B + 80) rlpFieldToU64_prog 20
      (.JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64
        (GuestAddrs.rlp_field_to_u64 + 80))) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
      a i hi
  have hcall := callWithin_spec (B + 80) C64B vOld
    (jalOff GuestAddrs.rlp_content_to_u64 (GuestAddrs.rlp_field_to_u64 + 80))
    (7 * len.toNat + 11) (by unfold B C64B; decide) hmem
    (by pcf) hcallee
  unfold contentRawPost
  exact hcall

#print axioms callContentExact

def contentCarry
    (sp0 listBase offset len v12 : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved) : Assertion :=
  (.x2 ↦ᵣ sp0) ** listOtherSaved saved ** stackFree sp0 8 **
  (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x8 ↦ᵣ listBase) ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)

theorem pcFree_contentCarry sp0 listBase offset len v12 saved :
    (contentCarry sp0 listBase offset len v12 saved).pcFree := by
  unfold contentCarry listOtherSaved
  pcf

/-- Exact-scratch scalar call framed by every K34/K20 resource the scalar
    callee does not touch. -/
theorem callContentFramedExact
    (sp0 listBase offset len vOld x6Old x7Old x28Old v12 : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h_ok : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
      index offset len)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + (7 * len.toNat + 11)) (B + 80) (B + 84) code
      ((((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (listBase + offset)) ** (.x11 ↦ᵣ len) **
         (.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
         (.x28 ↦ᵣ x28Old) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes)) **
        contentCarry sp0 listBase offset len v12 saved) **
       ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
         offset len⌝)
      (((contentRawPost listBase bytes offset.toNat len.toNat) **
        contentCarry sp0 listBase offset len v12 saved) **
       ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
         offset len⌝) := by
  have hb := success_content_bounds h_ok hslack hover
  have hsvalid : ∀ k, k < len.toNat →
      isValidByteAccess (listBase + BitVec.ofNat 64 (offset.toNat + k)) = true := by
    intro k hk
    exact hvalid (offset.toNat + k) (by omega)
  have hc := callContentExact listBase offset len vOld x6Old x7Old x28Old
    bytes hsalign hb.1 hb.2 hsvalid
  have hF : (contentCarry sp0 listBase offset len v12 saved **
      ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
        offset len⌝).pcFree :=
    pcFree_sepConj (pcFree_contentCarry _ _ _ _ _ _) (by pcf)
  have hcf := cpsTripleWithin_frameR
    (contentCarry sp0 listBase offset len v12 saved **
      ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
        offset len⌝) hF hc
  exact cpsTripleWithin_weaken (fun h hp => by xperm_pure hp)
    (fun h hq => by xperm_pure hq) hcf

#print axioms callContentFramedExact

def contentDone
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12,
    (((contentRawPost listBase bytes offset.toNat len.toNat) **
      contentCarry sp0 listBase offset len v12 saved) **
     ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
       offset len⌝) h

def contentReadyRa
    (sp0 listBase vOld : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12,
    ((.x1 ↦ᵣ vOld) **
      ((((.x5 ↦ᵣ lengthCell) ** (.x10 ↦ᵣ (listBase + offset)) **
         (.x11 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
         (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)) **
        selectedCarry sp0 listBase saved bytes v12) **
       ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
         offset len⌝)) h

/-- Lift the scalar call over the three scratch registers owned by K20. -/
theorem callContentOwned
    (sp0 listBase vOld : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + (7 * (2 ^ 64 - 1) + 11))
      (B + 80) (B + 84) code
      (contentReadyRa sp0 listBase vOld saved bytes listLen index)
      (contentDone sp0 listBase saved bytes listLen index) := by
  -- The displayed bound is normalized per selected `len` below; monotonicity
  -- to a caller-wide bound is supplied by the whole-routine theorem.
  unfold contentReadyRa
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_pure hp)
    (fun _ hq => hq) (cpsTripleWithin_pure_pre
      (P := EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
        index offset len)
      (H := ((.x1 ↦ᵣ vOld) **
        (((.x5 ↦ᵣ lengthCell) ** (.x10 ↦ᵣ (listBase + offset)) **
          (.x11 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
          (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)) **
         selectedCarry sp0 listBase saved bytes v12)))
      (fun h_ok => ?_))
  let P6 : Assertion :=
    ((.x1 ↦ᵣ vOld) **
      ((.x10 ↦ᵣ (listBase + offset)) ** (.x11 ↦ᵣ len) **
       (.x5 ↦ᵣ lengthCell) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes)) **
    contentCarry sp0 listBase offset len v12 saved ** regOwn .x7 **
    regOwn .x28 **
    ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
      offset len⌝
  have h6 := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6) (P := P6)
    (Q := contentDone sp0 listBase saved bytes listLen index) (fun x6Old => by
    let P7 : Assertion :=
      ((.x1 ↦ᵣ vOld) **
        ((.x10 ↦ᵣ (listBase + offset)) ** (.x11 ↦ᵣ len) **
         (.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ x6Old) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)) **
      contentCarry sp0 listBase offset len v12 saved ** regOwn .x28 **
      ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
        offset len⌝
    have h7 := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7) (P := P7)
      (Q := contentDone sp0 listBase saved bytes listLen index) (fun x7Old => by
      let P28 : Assertion :=
        ((.x1 ↦ᵣ vOld) **
          ((.x10 ↦ᵣ (listBase + offset)) ** (.x11 ↦ᵣ len) **
           (.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)) **
        contentCarry sp0 listBase offset len v12 saved **
        ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
          offset len⌝
      have h28 := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28)
        (P := P28) (Q := contentDone sp0 listBase saved bytes listLen index)
        (fun x28Old => by
          have hc0 := callContentFramedExact sp0 listBase offset len vOld x6Old
            x7Old x28Old v12 saved bytes listLen index h_ok hsalign hslack hover
            hvalid
          have hc : cpsTripleWithin (1 + (7 * (2 ^ 64 - 1) + 11))
              (B + 80) (B + 84) code
              ((((.x1 ↦ᵣ vOld) **
                ((.x10 ↦ᵣ (listBase + offset)) ** (.x11 ↦ᵣ len) **
                 (.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ x6Old) **
                 (.x7 ↦ᵣ x7Old) ** (.x28 ↦ᵣ x28Old) **
                 (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes)) **
                contentCarry sp0 listBase offset len v12 saved) **
               ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
                 index offset len⌝)
              (((contentRawPost listBase bytes offset.toNat len.toNat) **
                contentCarry sp0 listBase offset len v12 saved) **
               ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen
                 index offset len⌝) := cpsTripleWithin_mono_nSteps (by
            have := len.isLt
            omega) hc0
          refine cpsTripleWithin_weaken (fun h hp => by
              unfold P28 at hp
              xperm_pure hp) (fun h hq => ?_) hc
          unfold contentDone
          exact ⟨offset, len, v12, hq⟩)
      refine cpsTripleWithin_weaken (fun h hp => by
          unfold P7 at hp
          unfold P28
          xperm_pure hp) (fun _ hq => hq) h28)
    refine cpsTripleWithin_weaken (fun h hp => by
        unfold P6 at hp
        unfold P7
        xperm_pure hp) (fun _ hq => hq) h7)
  refine cpsTripleWithin_weaken (fun h hp => by
      unfold selectedCarry listOtherSaved at hp
      unfold P6 contentCarry listOtherSaved
      xperm_pure hp) (fun _ hq => hq) h6

#print axioms callContentOwned

theorem callContent
    (sp0 listBase vOld : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + (7 * (2 ^ 64 - 1) + 11))
      (B + 80) (B + 84) code
      ((.x1 ↦ᵣ vOld) ** contentReady sp0 listBase saved bytes listLen index)
      (contentDone sp0 listBase saved bytes listLen index) := by
  have hc := callContentOwned sp0 listBase vOld saved bytes listLen index
    hsalign hslack hover hvalid
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) hc
  unfold contentReady at hp
  unfold contentReadyRa
  obtain ⟨hRa, hReady, hd, hu, hra,
    ⟨offset, len, v12, hready⟩⟩ := hp
  exact ⟨offset, len, v12, hRa, hReady, hd, hu, hra, hready⟩

#print axioms callContent

#print axioms Result.status_cases
#print axioms frameRegs_implies_owned

end EvmAsm.Codegen.RlpFieldToU64SAsm
