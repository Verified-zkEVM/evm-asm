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

#print axioms listResultBranch

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
      (GuestAddrs.rlp_field_to_u256_be + 64))) (by bv_omega)
    (by rw [program_length]; decide) rfl (by rw [program_length]; decide)
  have had := CodeReq.ofProg_mem_at B (B + 68) rlpFieldToU256Be_prog 17
    (.ADDI .x5 .x5 (laLo GuestAddrs.rfu_length
      (GuestAddrs.rlp_field_to_u256_be + 64))) (by bv_omega)
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

#print axioms selectedLengthExact

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

#print axioms selectedLength

end EvmAsm.Codegen.RlpFieldToU256BeSAsm
