import EvmAsm.Codegen.Programs.RlpFieldToU256BeFinishSAsm

namespace EvmAsm.Codegen.RlpFieldToU256BeSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

def copyCarry (sp0 : Word) (saved : ListSaved) (v11 v12 : Word) : Assertion :=
  (.x2 ↦ᵣ sp0) ** (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
  (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) ** stackFree sp0 8 **
  (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
  regOwn .x13 ** regOwn .x14 ** regOwn .x31

theorem pcFree_copyCarry sp0 saved v11 v12 :
    (copyCarry sp0 saved v11 v12).pcFree := by
  unfold copyCarry
  pcf

def successDone (sp0 listBase outputPtr : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (((.x5 ↦ᵣ offsetCell) ** (.x6 ↦ᵣ (0 : Word)) ** regOwn .x7 **
      (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** (.x0 ↦ᵣ (0 : Word)) **
      (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
      copyCarry sp0 saved v11 v12 ** bytesRegion listBase bytes **
      bytesRegion outputPtr (rightAligned32 bytes offset len)) **
      ⌜ListSuccess bytes listBase listLen index offset len ∧ len.toNat ≤ 32⌝) h

private theorem fitCase
    (sp0 listBase outputPtr offset len old28 old29 old30 v11 v12 : Word)
    (saved : ListSaved) (bytes : List (BitVec 8)) (listLen index : Nat)
    (h_ok : ListSuccess bytes listBase listLen index offset len)
    (hfit : len.toNat ≤ 32)
    (hsalign : listBase.toNat % 8 = 0)
    (hoalign : outputPtr.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hoover : outputPtr.toNat + 32 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 32 →
      isValidByteAccess (outputPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 + (7 * 32 + 1)) (B + 84) (B + 136) code
      ((((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) **
        (.x7 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ listBase) **
        (.x9 ↦ᵣ outputPtr) ** (.x28 ↦ᵣ old28) ** (.x29 ↦ᵣ old29) **
        (offsetCell ↦ₘ offset)) **
        (.x30 ↦ᵣ old30) ** (.x0 ↦ᵣ (0 : Word)) **
        (lengthCell ↦ₘ len) **
        copyCarry sp0 saved v11 v12 ** bytesRegion listBase bytes **
        bytesRegion outputPtr (List.replicate 32 0)))
      (successDone sp0 listBase outputPtr saved bytes listLen index) := by
  let F : Assertion :=
    (.x30 ↦ᵣ old30) ** (.x0 ↦ᵣ (0 : Word)) **
    (lengthCell ↦ₘ len) ** copyCarry sp0 saved v11 v12 **
    bytesRegion listBase bytes ** bytesRegion outputPtr (List.replicate 32 0)
  have hc := cursorSetupExact listBase outputPtr offset len lengthCell old28 old29
    hfit F (by unfold F copyCarry; pcf)
  have hb := EvmAsm.Codegen.RlpFieldToU64SAsm.success_content_bounds h_ok
    hslack hover
  have hoff64 : offset.toNat < 2 ^ 64 := by omega
  have hlen64 : len.toNat < 2 ^ 64 := by omega
  have hl := copyLoop_spec_within listBase outputPtr old30 bytes offset.toNat
    len.toNat hsalign hoalign hfit hb.1 hover hoover hvalid houtvalid
  let G : Assertion :=
    (.x5 ↦ᵣ offsetCell) **
    (.x7 ↦ᵣ BitVec.ofNat 64 (32 - len.toNat)) **
    (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) **
    (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
    copyCarry sp0 saved v11 v12
  have hlF := cpsTripleWithin_frameR G (by unfold G copyCarry; pcf) hl
  unfold F at hc
  unfold G at hlF
  have hs := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      xperm_pure hp) hc hlF
  have hs' := cpsTripleWithin_mono_nSteps
    (show 6 + (7 * len.toNat + 1) ≤ 6 + (7 * 32 + 1) by omega) hs
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) hs'
  unfold successDone
  refine ⟨offset, len, v11, v12, ?_⟩
  unfold copyCarry at hp
  have hoff : BitVec.ofNat 64 offset.toNat = offset := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hlen : BitVec.ofNat 64 len.toNat = len := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hoff, hlen] at hp
  let Rest : Assertion :=
    (.x6 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ offsetCell) **
    (.x7 ↦ᵣ BitVec.ofNat 64 (32 - len.toNat)) **
    (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) ** regOwn .x30 **
    (.x0 ↦ᵣ (0 : Word)) ** (offsetCell ↦ₘ offset) **
    (lengthCell ↦ₘ len) ** copyCarry sp0 saved v11 v12 **
    bytesRegion listBase bytes **
    bytesRegion outputPtr (rightAligned32 bytes offset len)
  have hp0 : (((.x28 ↦ᵣ
      (listBase + BitVec.ofNat 64 (offset.toNat + len.toNat))) **
      (.x29 ↦ᵣ (outputPtr + BitVec.ofNat 64 32)) ** Rest) h) := by
    unfold Rest
    unfold copyCarry
    xperm_hyp hp
  have hp1 := sepConj_mono (regIs_implies_regOwn .x28)
    (sepConj_mono (regIs_implies_regOwn .x29) (fun _ hh => hh)) h hp0
  unfold Rest at hp1
  let Rest7 : Assertion :=
    (.x6 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ offsetCell) **
    (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ outputPtr) ** regOwn .x30 **
    (.x0 ↦ᵣ (0 : Word)) ** (offsetCell ↦ₘ offset) **
    (lengthCell ↦ₘ len) ** copyCarry sp0 saved v11 v12 **
    bytesRegion listBase bytes **
    bytesRegion outputPtr (rightAligned32 bytes offset len)
  have hp7 : (((.x7 ↦ᵣ BitVec.ofNat 64 (32 - len.toNat)) **
      regOwn .x28 ** regOwn .x29 ** Rest7) h) := by
    unfold Rest7
    xperm_hyp hp1
  have hp2 := sepConj_mono (regIs_implies_regOwn .x7)
    (fun _ hh => hh) h hp7
  unfold Rest7 at hp2
  apply (sepConj_pure_right h).2
  exact ⟨(by xperm_hyp hp2), ⟨h_ok, hfit⟩⟩

def lengthFitsWithOutput (sp0 listBase outputPtr : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    (⌜len.toNat ≤ 32⌝ **
      ⌜ListSuccess bytes listBase listLen index offset len⌝ **
      ((.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
       (.x5 ↦ᵣ lengthCell) ** (.x8 ↦ᵣ listBase) ** regOwn .x28 **
       regOwn .x29 ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
       selectedPathCarry sp0 listBase saved bytes v11 v12 **
       bytesRegion outputPtr (List.replicate 32 0))) h

private theorem fitWithOutputToSuccessDone
    (sp0 listBase outputPtr : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs1 : saved.s1 = outputPtr)
    (hsalign : listBase.toNat % 8 = 0)
    (hoalign : outputPtr.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hoover : outputPtr.toNat + 32 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 32 →
      isValidByteAccess (outputPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 + (7 * 32 + 1)) (B + 84) (B + 136) code
      (lengthFitsWithOutput sp0 listBase outputPtr saved bytes listLen index)
      (successDone sp0 listBase outputPtr saved bytes listLen index) := by
  unfold lengthFitsWithOutput
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun offset => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun len => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v11 => ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_exists_assertion
    (fun v12 => ?_)
  refine cpsTripleWithin_pure_pre (fun hfit => ?_)
  refine cpsTripleWithin_pure_pre (fun h_ok => ?_)
  have h30 (old28 old29 : Word) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x30)
      (P := ((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) **
        (.x7 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ listBase) **
        (.x9 ↦ᵣ outputPtr) ** (.x28 ↦ᵣ old28) ** (.x29 ↦ᵣ old29) **
        (.x0 ↦ᵣ (0 : Word)) ** (offsetCell ↦ₘ offset) **
        (lengthCell ↦ₘ len) ** copyCarry sp0 saved v11 v12 **
        bytesRegion listBase bytes **
        bytesRegion outputPtr (List.replicate 32 0))
      )
      (Q := successDone sp0 listBase outputPtr saved bytes listLen index)
      (fun old30 => cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ hp => hp)
        (fitCase sp0 listBase outputPtr offset len old28 old29 old30
          v11 v12 saved bytes listLen index h_ok hfit hsalign hoalign hslack
          hover hoover hvalid houtvalid))
  let P29 (old28 : Word) : Assertion :=
    ((.x5 ↦ᵣ lengthCell) ** (.x6 ↦ᵣ len) **
      (.x7 ↦ᵣ (32 : Word)) ** (.x8 ↦ᵣ listBase) **
      (.x9 ↦ᵣ outputPtr) ** (.x28 ↦ᵣ old28) **
      (.x0 ↦ᵣ (0 : Word)) ** (offsetCell ↦ₘ offset) **
      (lengthCell ↦ₘ len) ** copyCarry sp0 saved v11 v12 **
      bytesRegion listBase bytes ** bytesRegion outputPtr (List.replicate 32 0)) **
      regOwn .x30
  have h29 (old28 : Word) :=
    cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29)
      (P := P29 old28)
      (Q := successDone sp0 listBase outputPtr saved bytes listLen index)
      (fun old29 => cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun _ hp => hp) (h30 old28 old29))
  let P28 : Assertion :=
    (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
      (.x5 ↦ᵣ lengthCell) ** (.x8 ↦ᵣ listBase) ** regOwn .x29 **
      (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
      selectedPathCarry sp0 listBase saved bytes v11 v12 **
      bytesRegion outputPtr (List.replicate 32 0)
  have h28 := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28)
    (P := P28)
    (Q := successDone sp0 listBase outputPtr saved bytes listLen index)
    (fun old28 => cpsTripleWithin_weaken (fun h hp => by
        dsimp only [P28] at hp
        unfold selectedPathCarry at hp
        dsimp only [P29, copyCarry] at ⊢
        rw [hs1] at hp
        xperm_hyp hp) (fun _ hp => hp) (h29 old28))
  exact cpsTripleWithin_weaken (fun h hp => by
      dsimp only [P28] at hp ⊢
      xperm_hyp hp) (fun _ hp => hp) h28

/-- Lift the cursor setup and verified copy loop through the fit branch's
    existential K20 result. -/
theorem fitToSuccessDone
    (sp0 listBase outputPtr : Word) (saved : ListSaved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs1 : saved.s1 = outputPtr)
    (hsalign : listBase.toNat % 8 = 0)
    (hoalign : outputPtr.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hoover : outputPtr.toNat + 32 < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (houtvalid : ∀ k, k < 32 →
      isValidByteAccess (outputPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (6 + (7 * 32 + 1)) (B + 84) (B + 136) code
      ((lengthFits sp0 listBase saved bytes listLen index) **
        bytesRegion outputPtr (List.replicate 32 0))
      (successDone sp0 listBase outputPtr saved bytes listLen index) := by
  have hs := fitWithOutputToSuccessDone sp0 listBase outputPtr saved bytes
    listLen index hs1 hsalign hoalign hslack hover hoover hvalid houtvalid
  exact cpsTripleWithin_weaken (fun h hp => by
      obtain ⟨g1, g2, gd, gu, hleft, hout⟩ := hp
      unfold lengthFits at hleft
      obtain ⟨offset, len, v11, v12, hstate⟩ := hleft
      obtain ⟨hcore, hfit⟩ := (sepConj_pure_right g1).1 hstate
      unfold lengthRest at hcore
      extract_pure_deep hcore
      obtain ⟨h_ok, hcore⟩ := hcore
      unfold lengthFitsWithOutput
      refine ⟨offset, len, v11, v12, ?_⟩
      let Core : Assertion :=
        (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) **
          (.x5 ↦ᵣ lengthCell) ** (.x8 ↦ᵣ listBase) ** regOwn .x28 **
          regOwn .x29 ** (offsetCell ↦ₘ offset) ** (lengthCell ↦ₘ len) **
          selectedPathCarry sp0 listBase saved bytes v11 v12
      have hcombined : ((Core **
          bytesRegion outputPtr (List.replicate 32 0)) h) := by
        refine ⟨g1, g2, gd, gu, ?_, hout⟩
        unfold Core
        xperm_hyp hcore
      apply (sepConj_pure_left h).2
      refine ⟨hfit, ?_⟩
      apply (sepConj_pure_left h).2
      refine ⟨h_ok, ?_⟩
      unfold Core at hcombined
      xperm_hyp hcombined)
    (fun _ hp => hp) hs


end EvmAsm.Codegen.RlpFieldToU256BeSAsm
