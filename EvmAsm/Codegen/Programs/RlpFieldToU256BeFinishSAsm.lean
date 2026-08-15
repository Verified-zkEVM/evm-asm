import EvmAsm.Codegen.Programs.RlpFieldToU256BeLoopSAsm

namespace EvmAsm.Codegen.RlpFieldToU256BeSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

abbrev listCallRest := EvmAsm.Codegen.RlpFieldToU64SAsm.listCallRest
abbrev listCallCore := EvmAsm.Codegen.RlpFieldToU64SAsm.listCallCore

theorem pcFree_listCallRest sp0 listBase offsetPtr lenPtr saved bytes offset len
    v11 v12 : (listCallRest sp0 listBase offsetPtr lenPtr saved bytes offset len
      v11 v12).pcFree :=
  EvmAsm.Codegen.RlpFieldToU64SAsm.pcFree_listCallRest _ _ _ _ _ _ _ _ _ _

private theorem branchSelected
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 60) code
      (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index)
      (B + 152)
        (listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
          listLen index)
      (B + 64)
        (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index) := by
  unfold listSelected EvmAsm.Codegen.RlpFieldToU64SAsm.listSelected
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_ok => ?_)
  have hb0 := bne_spec_gen_within .x10 .x0 (92 : BitVec 13)
    (0 : Word) (0 : Word) (B + 60)
  rw [show B + 60 + signExtend13 (92 : BitVec 13) = B + 152 from by decide,
    show B + 60 + 4 = B + 64 from by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 60) rlpFieldToU256Be_prog 15
      (.BNE .x10 .x0 (92 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R : Assertion :=
    listCallRest sp0 listBase offsetPtr lenPtr saved bytes offset len v11 v12 **
    ⌜ListSuccess bytes listBase listLen index offset len⌝
  have hbF := cpsBranchWithin_frameR R
    (pcFree_sepConj (pcFree_listCallRest _ _ _ _ _ _ _ _ _ _) (by pcf)) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code)
    (fun a i hi => wrapperCode_mono a i hi) hbF
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold EvmAsm.Codegen.RlpFieldToU64SAsm.listCallCore at hp
      unfold R
      xperm_pure hp) (fun h hp => by
      extract_pure_deep hp
      exact False.elim (hp.1 rfl)) (fun h hp => ?_) hbC
  extract_pure_deep hp
  obtain ⟨-, hstate⟩ := hp
  refine ⟨offset, len, v11, v12, ?_⟩
  unfold R at hstate
  unfold EvmAsm.Codegen.RlpFieldToU64SAsm.listCallCore
  xperm_pure hstate

private theorem branchFailed
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 60) code
      (listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
        listLen index)
      (B + 152)
        (listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
          listLen index)
      (B + 64)
        (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index) := by
  unfold listFailed EvmAsm.Codegen.RlpFieldToU64SAsm.listFailed
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun h_fail => ?_)
  have hb0 := bne_spec_gen_within .x10 .x0 (92 : BitVec 13)
    (1 : Word) (0 : Word) (B + 60)
  rw [show B + 60 + signExtend13 (92 : BitVec 13) = B + 152 from by decide,
    show B + 60 + 4 = B + 64 from by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 60) rlpFieldToU256Be_prog 15
      (.BNE .x10 .x0 (92 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R : Assertion :=
    listCallRest sp0 listBase offsetPtr lenPtr saved bytes oldOffset oldLen
      v11 v12 ** ⌜ListFailure bytes listBase listLen index⌝
  have hbF := cpsBranchWithin_frameR R
    (pcFree_sepConj (pcFree_listCallRest _ _ _ _ _ _ _ _ _ _) (by pcf)) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code)
    (fun a i hi => wrapperCode_mono a i hi) hbF
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold EvmAsm.Codegen.RlpFieldToU64SAsm.listCallCore at hp
      unfold R
      xperm_pure hp) (fun h hp => ?_) (fun h hp => by
      extract_pure_deep hp
      have hne : (1 : Word) ≠ 0 := by decide
      exact False.elim (hne hp.1)) hbC
  extract_pure_deep hp
  obtain ⟨-, hstate⟩ := hp
  refine ⟨v11, v12, ?_⟩
  unfold R at hstate
  unfold EvmAsm.Codegen.RlpFieldToU64SAsm.listCallCore
  xperm_pure hstate

/-- K35 instruction 15 splits the strict K20 result into its genuine two
    semantic cases. -/
theorem listResultBranch
    (sp0 listBase offsetPtr lenPtr oldOffset oldLen : Word)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 60) code
      (listCallResult sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
        listLen index)
      (B + 152)
        (listFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved bytes
          listLen index)
      (B + 64)
        (listSelected sp0 listBase offsetPtr lenPtr saved bytes listLen index) := by
  have hs := branchSelected sp0 listBase offsetPtr lenPtr oldOffset oldLen saved
    bytes listLen index
  have hf := branchFailed sp0 listBase offsetPtr lenPtr oldOffset oldLen saved
    bytes listLen index
  have hor := cpsBranchWithin_pre_or hs hf
  exact cpsBranchWithin_weaken
    (fun h hp => EvmAsm.Codegen.RlpFieldToU64SAsm.listCallResult_cases sp0
      listBase offsetPtr lenPtr oldOffset oldLen saved bytes listLen index h hp)
    (fun _ hp => hp) (fun _ hp => hp) hor


/-- Reload the selected length and comparison bound (instructions 16--19). -/
theorem selectedLengthExact
    (len old5 old6 old7 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (B + 64) (B + 80) code
      (((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (lengthCell ↦ₘ len)) ** F)
      (((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
        (lengthCell ↦ₘ len)) ** F) := by
  have hau := CodeReq.ofProg_mem_at B (B + 64) rlpFieldToU256Be_prog 16
    (.AUIPC .x5 (laHi GuestAddrs.rfu_length
      (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 64))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had := CodeReq.ofProg_mem_at B (B + 68) rlpFieldToU256Be_prog 17
    (.ADDI .x5 .x5 (laLo GuestAddrs.rfu_length
      (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 64))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have h0 := la_materialize_within .x5 old5 (B + 64) lengthCell
    (by decide) (by unfold B lengthCell; decide) hau had
  have h1 := ld_spec_gen_within .x6 .x5 lengthCell old6 len
    (0 : BitVec 12) (B + 72) (by decide)
  rw [show lengthCell + signExtend12 (0 : BitVec 12) = lengthCell from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h1
  have h1' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 72) rlpFieldToU256Be_prog 18
      (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h1
  have h2 := li_spec_gen_within .x7 old7 (32 : Word) (B + 76) (by decide)
  have h2' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 76) rlpFieldToU256Be_prog 19
      (.LI .x7 (32 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h2
  have h0F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) ** (lengthCell ↦ₘ len)) (by pcf) h0
  have h1F := cpsTripleWithin_frameR ((.x7 ↦ᵣ old7)) (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) ** (lengthCell ↦ₘ len))
    (by pcf) h2'
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have hs := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 h2F
  have hs' := cpsTripleWithin_weaken
    (P' := (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
      (lengthCell ↦ₘ len))
    (Q' := (.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) **
      (.x7 ↦ᵣ (32 : Word)) ** (lengthCell ↦ₘ len))
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) hs
  exact cpsTripleWithin_frameR F hF
    (cpsTripleWithin_extend_code (fun a i hi => wrapperCode_mono a i hi) hs')


def selectedPathCarry (sp0 listBase : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (v11 v12 : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** (.x9 ↦ᵣ saved.s1) **
  (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree sp0 8 **
  (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
  regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes

theorem pcFree_selectedPathCarry sp0 listBase saved bytes v11 v12 :
    (selectedPathCarry sp0 listBase saved bytes v11 v12).pcFree := by
  unfold selectedPathCarry
  pcf

def lengthReady (sp0 listBase : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) **
       (.x7 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ listBase) ** regOwn .x28 **
       regOwn .x29 ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len)) **
      selectedPathCarry sp0 listBase saved bytes v11 v12) **
     ⌜ListSuccess bytes listBase listLen index offset len⌝)) h

/-- Lift `selectedLengthExact` through K20's existential success package. -/
theorem selectedLength
    (sp0 listBase : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase) :
    cpsTripleWithin 4 (B + 64) (B + 80) code
      (listSelected sp0 listBase offsetCell lengthCell saved bytes listLen index)
      (lengthReady sp0 listBase saved bytes listLen index) := by
  unfold listSelected EvmAsm.Codegen.RlpFieldToU64SAsm.listSelected
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  refine cpsTripleWithin_weaken (fun h hp => by xperm_pure hp)
    (fun _ hp => hp) (cpsTripleWithin_pure_pre
      (P := ListSuccess bytes listBase listLen index offset len)
      (H := listCallCore sp0 listBase offsetCell lengthCell saved bytes 0
        offset len v11 v12) (fun h_ok => ?_))
  let R0 : Assertion :=
    ((.x8 ↦ᵣ listBase) ** regOwn .x28 ** regOwn .x29 **
      (offsetCell ↦ₘ offset)) **
    selectedPathCarry sp0 listBase saved bytes v11 v12 **
    ⌜ListSuccess bytes listBase listLen index offset len⌝
  let R : Assertion := (lengthCell ↦ₘ len) ** R0
  have h7 (old5 old6 : Word) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := (R ** (.x5 ↦ᵣ old5)) ** (.x6 ↦ᵣ old6))
      (Q := lengthReady sp0 listBase saved bytes listLen index)
      (fun old7 => by
        have hs := selectedLengthExact len old5 old6 old7 R0 (by
          unfold R0 selectedPathCarry
          pcf)
        refine cpsTripleWithin_weaken (fun h hp => by
            unfold R R0 at hp
            xperm_hyp hp) (fun h hq => ?_) hs
        unfold lengthReady
        refine ⟨offset, len, v11, v12, ?_⟩
        unfold R0 at hq
        xperm_hyp hq)
  have h6 (old5 : Word) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (R ** regOwn .x7) ** (.x5 ↦ᵣ old5))
      (Q := lengthReady sp0 listBase saved bytes listLen index)
      (fun old6 => cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ hp => hp) (h7 old5 old6))
  have howned := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
    (P := (R ** regOwn .x6) ** regOwn .x7)
    (Q := lengthReady sp0 listBase saved bytes listLen index)
    (fun old5 => cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hp => hp) (h6 old5))
  refine cpsTripleWithin_weaken (fun h hp => by
      unfold listCallCore EvmAsm.Codegen.RlpFieldToU64SAsm.listCallCore
        EvmAsm.Codegen.RlpFieldToU64SAsm.listCallRest
        EvmAsm.Codegen.RlpFieldToU64SAsm.listSavedRegs
        EvmAsm.Codegen.RlpFieldToU64SAsm.listOtherSaved at hp
      unfold R R0 selectedPathCarry
      rw [hs0] at hp
      xperm_pure hp) (fun _ hp => hp) howned


def lengthRest (sp0 listBase offset len : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) (v11 v12 : Word) :
    Assertion :=
  (.x5 ↦ᵣ lengthCell) ** (.x8 ↦ᵣ listBase) ** regOwn .x28 **
  regOwn .x29 ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
  selectedPathCarry sp0 listBase saved bytes v11 v12 **
  ⌜ListSuccess bytes listBase listLen index offset len⌝

theorem pcFree_lengthRest sp0 listBase offset len saved bytes listLen index v11
    v12 : (lengthRest sp0 listBase offset len saved bytes listLen index v11
      v12).pcFree := by
  unfold lengthRest
  pcf

def lengthTooLong (sp0 listBase : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
      lengthRest sp0 listBase offset len saved bytes listLen index v11 v12) **
      ⌜32 < len.toNat⌝) h

def lengthFits (sp0 listBase : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
      lengthRest sp0 listBase offset len saved bytes listLen index v11 v12) **
      ⌜len.toNat ≤ 32⌝) h

private theorem lengthBranchCase
    (sp0 listBase offset len v11 v12 : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 80) code
      ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
        lengthRest sp0 listBase offset len saved bytes listLen index v11 v12)
      (B + 144) (lengthTooLong sp0 listBase saved bytes listLen index)
      (B + 84) (lengthFits sp0 listBase saved bytes listLen index) := by
  have hb0 := bltu_spec_gen_within .x7 .x6 (64 : BitVec 13)
    (32 : Word) len (B + 80)
  rw [show B + 80 + signExtend13 (64 : BitVec 13) = B + 144 from by decide,
    show B + 80 + 4 = B + 84 from by bv_omega] at hb0
  have hb1 := cpsBranchWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 80) rlpFieldToU256Be_prog 20
      (.BLTU .x7 .x6 (64 : BitVec 13)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) hb0
  let R := lengthRest sp0 listBase offset len saved bytes listLen index v11 v12
  have hbF := cpsBranchWithin_frameR R
    (pcFree_lengthRest _ _ _ _ _ _ _ _ _ _) hb1
  have hbC := cpsBranchWithin_extend_code (cr' := code)
    (fun a i hi => wrapperCode_mono a i hi) hbF
  refine cpsBranchWithin_weaken (fun _ hp => by
      unfold R
      xperm_hyp hp) (fun h hp => ?_) (fun h hp => ?_) hbC
  · extract_pure_deep hp
    obtain ⟨h_lt, hp⟩ := hp
    unfold lengthTooLong
    refine ⟨offset, len, v11, v12, ?_⟩
    apply (sepConj_pure_right h).2
    exact ⟨(by unfold R at hp; xperm_hyp hp), (by
      simpa [BitVec.ult] using h_lt)⟩
  · extract_pure_deep hp
    obtain ⟨h_nlt, hp⟩ := hp
    unfold lengthFits
    refine ⟨offset, len, v11, v12, ?_⟩
    apply (sepConj_pure_right h).2
    refine ⟨(by unfold R at hp; xperm_hyp hp), ?_⟩
    simp [BitVec.ult] at h_nlt
    omega

/-- K35 instruction 20 exposes the genuine `len > 32` versus `len ≤ 32`
    semantic split. -/
theorem lengthBranch
    (sp0 listBase : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) :
    cpsBranchWithin 1 (B + 80) code
      (lengthReady sp0 listBase saved bytes listLen index)
      (B + 144) (lengthTooLong sp0 listBase saved bytes listLen index)
      (B + 84) (lengthFits sp0 listBase saved bytes listLen index) := by
  unfold lengthReady
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  exact cpsBranchWithin_weaken (fun _ hp => by
      unfold lengthRest
      xperm_hyp hp) (fun _ hp => hp) (fun _ hp => hp)
    (lengthBranchCase sp0 listBase offset len v11 v12 saved bytes listLen index)


/-- Materialize the selected source cursor and right-aligned destination cursor
    (instructions 21--26). -/
theorem cursorSetupExact
    (listBase outputPtr offset len old5 old28 old29 : Word)
    (hfit : len.toNat ≤ 32) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 6 (B + 84) (B + 108) code
      (((.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) **
        (.x28 ↦ᵣ old28) ** (.x29 ↦ᵣ old29) **
        (offsetCell ↦ₘ offset)) ** F)
      (((.x5 ↦ᵣ offsetCell) ** (.x6 ↦ᵣ len) **
        (.x7 ↦ᵣ BitVec.ofNat 64 (32 - len.toNat)) **
        (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) **
        (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 offset.toNat)) **
        (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len.toNat))) **
        (offsetCell ↦ₘ offset)) ** F) := by
  have hau := CodeReq.ofProg_mem_at B (B + 84) rlpFieldToU256Be_prog 21
    (.AUIPC .x5 (laHi GuestAddrs.rfu_offset
      (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 84))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had := CodeReq.ofProg_mem_at B (B + 88) rlpFieldToU256Be_prog 22
    (.ADDI .x5 .x5 (laLo GuestAddrs.rfu_offset
      (RlpFieldToU256BeOfflineAddrs.rlp_field_to_u256_be + 84))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have h0 := la_materialize_within .x5 old5 (B + 84) offsetCell
    (by decide) (by unfold B offsetCell; decide) hau had
  have h1 := ld_spec_gen_within .x28 .x5 offsetCell old28 offset
    (0 : BitVec 12) (B + 92) (by decide)
  rw [show offsetCell + signExtend12 (0 : BitVec 12) = offsetCell from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h1
  have h1' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 92) rlpFieldToU256Be_prog 23
      (.LD .x28 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [program_length]; decide) rfl (by rw [program_length]; decide)) h1
  have h2 := add_spec_gen_rd_eq_rs2_within .x28 .x8 listBase offset
    (B + 96) (by decide)
  have h2' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 96) rlpFieldToU256Be_prog 24
      (.ADD .x28 .x8 .x28) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h2
  have h3 := sub_spec_gen_rd_eq_rs1_within .x7 .x6 (32 : Word) len
    (B + 100) (by decide)
  have h3' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 100) rlpFieldToU256Be_prog 25
      (.SUB .x7 .x7 .x6) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h3
  have h4 := add_spec_gen_within .x29 .x9 .x7 outputPtr
    ((32 : Word) - len) old29 (B + 104) (by decide)
  have h4' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 104) rlpFieldToU256Be_prog 26
      (.ADD .x29 .x9 .x7) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h4
  have h0F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ listBase) **
      (.x9 ↦ᵣ outputPtr) ** (.x28 ↦ᵣ old28) ** (.x29 ↦ᵣ old29) **
      (offsetCell ↦ₘ offset)) (by pcf) h0
  have h1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ listBase) **
      (.x9 ↦ᵣ outputPtr) ** (.x29 ↦ᵣ old29)) (by pcf) h1'
  have h2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ offsetCell) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
      (.x9 ↦ᵣ outputPtr) ** (.x29 ↦ᵣ old29) ** (offsetCell ↦ₘ offset))
    (by pcf) h2'
  have h3F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ offsetCell) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) **
      (.x28 ↦ᵣ (listBase + offset)) ** (.x29 ↦ᵣ old29) **
      (offsetCell ↦ₘ offset)) (by pcf) h3'
  have h4F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ offsetCell) ** (.x6 ↦ᵣ len) ** (.x8 ↦ᵣ listBase) **
      (.x28 ↦ᵣ (listBase + offset)) ** (offsetCell ↦ₘ offset)) (by pcf) h4'
  have s01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  have s012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s01 h2F
  have s0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s012 h3F
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s0123 h4F
  have hs := cpsTripleWithin_weaken
    (P' := (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
      (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) ** (.x28 ↦ᵣ old28) **
      (.x29 ↦ᵣ old29) ** (offsetCell ↦ₘ offset))
    (Q' := (.x5 ↦ᵣ offsetCell) ** (.x6 ↦ᵣ len) **
      (.x7 ↦ᵣ BitVec.ofNat 64 (32 - len.toNat)) ** (.x8 ↦ᵣ listBase) **
      (.x9 ↦ᵣ outputPtr) **
      (.x28 ↦ᵣ (listBase + BitVec.ofNat 64 offset.toNat)) **
      (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 (32 - len.toNat))) **
      (offsetCell ↦ₘ offset))
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by
      have hoff : BitVec.ofNat 64 offset.toNat = offset := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have hsub : (32 : Word) - len = BitVec.ofNat 64 (32 - len.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
        simp only [show (32 : Word).toNat = 32 from rfl]
        omega
      rw [hoff, ← hsub]
      xperm_hyp hp) s
  exact cpsTripleWithin_frameR F hF
    (cpsTripleWithin_extend_code (fun a i hi => wrapperCode_mono a i hi) hs)


/-- Success status and jump to the common restore join (34--35). -/
theorem successStatusTail (old10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (B + 136) (B + 156) code
      ((.x10 ↦ᵣ old10) ** F) ((.x10 ↦ᵣ (0 : Word)) ** F) := by
  have h0 := li_spec_gen_within .x10 old10 (0 : Word) (B + 136) (by decide)
  have h0' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 136) rlpFieldToU256Be_prog 34
      (.LI .x10 (0 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h0
  have hj := jal_x0_spec_gen_within (16 : BitVec 21) (B + 140)
  rw [show B + 140 + signExtend21 (16 : BitVec 21) = B + 156 by decide] at hj
  have hj' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 140) rlpFieldToU256Be_prog 35
      (.JAL .x0 (16 : BitVec 21)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) hj
  have h0F := cpsTripleWithin_frameR F hF h0'
  have hjF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (0 : Word)) ** F)
    (pcFree_sepConj pcFree_regIs hF) hj'
  have hjS : cpsTripleWithin 1 (B + 140) (B + 156) wrapperCode
      ((.x10 ↦ᵣ (0 : Word)) ** F) ((.x10 ↦ᵣ (0 : Word)) ** F) :=
    cpsTripleWithin_weaken
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hp => by simpa only [sepConj_emp_left'] using hp) hjF
  exact cpsTripleWithin_extend_code (fun a i hi => wrapperCode_mono a i hi)
    (cpsTripleWithin_seq_same_cr h0F hjS)

/-- Too-long status and jump to the common restore join (36--37). -/
theorem tooLongStatusTail (old10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (B + 144) (B + 156) code
      ((.x10 ↦ᵣ old10) ** F) ((.x10 ↦ᵣ (2 : Word)) ** F) := by
  have h0 := li_spec_gen_within .x10 old10 (2 : Word) (B + 144) (by decide)
  have h0' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 144) rlpFieldToU256Be_prog 36
      (.LI .x10 (2 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h0
  have hj := jal_x0_spec_gen_within (8 : BitVec 21) (B + 148)
  rw [show B + 148 + signExtend21 (8 : BitVec 21) = B + 156 by decide] at hj
  have hj' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 148) rlpFieldToU256Be_prog 37
      (.JAL .x0 (8 : BitVec 21)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) hj
  have h0F := cpsTripleWithin_frameR F hF h0'
  have hjF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (2 : Word)) ** F)
    (pcFree_sepConj pcFree_regIs hF) hj'
  have hjS : cpsTripleWithin 1 (B + 148) (B + 156) wrapperCode
      ((.x10 ↦ᵣ (2 : Word)) ** F) ((.x10 ↦ᵣ (2 : Word)) ** F) :=
    cpsTripleWithin_weaken
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hp => by simpa only [sepConj_emp_left'] using hp) hjF
  exact cpsTripleWithin_extend_code (fun a i hi => wrapperCode_mono a i hi)
    (cpsTripleWithin_seq_same_cr h0F hjS)

/-- List-selection failure status at the common restore join (38). -/
theorem failureStatusTail (old10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (B + 152) (B + 156) code
      ((.x10 ↦ᵣ old10) ** F) ((.x10 ↦ᵣ (1 : Word)) ** F) := by
  have h0 := li_spec_gen_within .x10 old10 (1 : Word) (B + 152) (by decide)
  have h0' := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 152) rlpFieldToU256Be_prog 38
      (.LI .x10 (1 : Word)) (by bv_omega) (by rw [program_length]; decide)
      rfl (by rw [program_length]; decide)) h0
  exact cpsTripleWithin_frameR F hF
    (cpsTripleWithin_extend_code (fun a i hi => wrapperCode_mono a i hi) h0')


/-- Restore K35's saved `ra/s0/s1`, deallocate its 32-byte frame, and return
    (instructions 39--43). -/
theorem restoreTail
    (sp0 newSp : Word) (saved : Saved) (F : Assertion) (hF : F.pcFree)
    (hnewSp : newSp = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin 5 (B + 156) saved.ra code
      (((.x2 ↦ᵣ newSp) ** regsOwnAt frame ** savedFrame newSp saved) ** F)
      (((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals saved) **
        savedFrame newSp saved) ** F) := by
  have hl0 := loadSeq_spec_own frame newSp (savedVals saved)
    (B + 156) (by decide) (by decide)
  have hlMono : ∀ a i,
      CodeReq.ofProg (B + 156) (loadProg frame) a = some i →
        wrapperCode a = some i := by
    intro a i hi
    exact CodeReq.ofProg_mono_sub B (B + 156) rlpFieldToU256Be_prog
      (loadProg frame) 39 (by bv_omega) (by rfl)
      (by rw [program_length]; change 39 + 3 ≤ 44; decide)
      (by rw [program_length]; decide) a i hi
  have hl := cpsTripleWithin_extend_code hlMono hl0
  rw [show B + 156 + BitVec.ofNat 64 (4 * frame.length) = B + 168 from by
    rw [show frame.length = 3 by decide]; bv_omega] at hl
  rw [frameSlotsSaved_frame] at hl
  have hlF := cpsTripleWithin_frameR F hF hl
  have hd0 := addi_spec_gen_same_within .x2 newSp (32 : BitVec 12) (B + 168)
    (by decide)
  rw [show newSp + signExtend12 (32 : BitVec 12) = sp0 from by
    rw [hnewSp]
    exact sext_frameRestore sp0 (-32 : BitVec 12) (32 : BitVec 12)
      (by decide)] at hd0
  have hd := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 168) rlpFieldToU256Be_prog 42
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
  have hr0 := EvmAsm.Evm64.ret_spec_within' (B + 172) saved.ra
  rw [hret] at hr0
  have hr := cpsTripleWithin_extend_code (cr' := wrapperCode)
    (CodeReq.ofProg_mem_at B (B + 172) rlpFieldToU256Be_prog 43
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
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlF hdF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_frame] at hp
    xperm_hyp hp) h12 hrF
  have hlocal := cpsTripleWithin_weaken
    (P' := (((.x2 ↦ᵣ newSp) ** regsOwnAt frame **
      savedFrame newSp saved) ** F))
    (Q' := (((.x2 ↦ᵣ sp0) ** regsAt frame (savedVals saved) **
      savedFrame newSp saved) ** F))
    (fun _ hp => by xperm_hyp hp)
    (fun h hp => by rw [regsAt_frame]; xperm_hyp hp) h123
  exact cpsTripleWithin_extend_code (fun a i hi => wrapperCode_mono a i hi) hlocal


end EvmAsm.Codegen.RlpFieldToU256BeSAsm
