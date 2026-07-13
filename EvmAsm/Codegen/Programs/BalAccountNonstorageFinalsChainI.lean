/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainI

  Code-station assembly for bal_account_nonstorage_finals.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainH

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- Slot 144, status-zero arm (`B + 576 → B + 580`): preserve a successful
    code-window `rlp_walk_init` result as the unified field-init post. -/
theorem bansf_codeFieldInitSuccess144_spec (aB : Word)
    (fOff fSpanN cOff : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hok : FieldInitOk acctBytes fOff fSpanN cOff) :
    cpsTripleWithin 1 (B + 576) (B + 580) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
       bytesRegion aB acctBytes ** F)
      (fieldInitPost aB fOff fSpanN acctBytes (B + 572 + 4) F) := by
  have hbne := bne_spec_gen_within .x12 .x0 (156 : BitVec 13)
    (0 : Word) (0 : Word) (B + 576)
  rw [show (B + 576) + 4 = B + 580 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    bansf_codeFieldStatus144_code hbne
  have hfall := cpsBranchWithin_ntakenPath hbneL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  have hfallF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
     ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hfall
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
    hfallF
  unfold fieldInitPost
  refine ⟨cOff, (sepConj_pure_right h).2 ⟨?_, hok⟩⟩
  have hq' := sepConj_mono_left (sepConj_mono_right
    (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
  xperm_hyp hq'

#print axioms bansf_codeFieldInitSuccess144_spec

/-- Slot 144, nonzero-status arm (`B + 576 → B + 736`): branch through the
    shared reject stub and release the code field-init registers. -/
theorem bansf_codeFieldInitFailure144_spec (aB cur endW k : Word)
    (acctBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (hk : k ≠ (0 : Word)) :
    cpsTripleWithin 2 (B + 576) (B + 736) bansfCR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
       ((.x12 : Reg) ↦ᵣ k) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
       bytesRegion aB acctBytes ** F)
      (fieldRej aB acctBytes F) := by
  have hbne := bne_spec_gen_within .x12 .x0 (156 : BitVec 13)
    k (0 : Word) (B + 576)
  rw [show (B + 576) + signExtend13 (156 : BitVec 13) = B + 732 from by
        rw [show signExtend13 (156 : BitVec 13) = (156 : Word) from by decide]
        bv_omega,
      show (B + 576) + 4 = B + 580 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    bansf_codeFieldStatus144_code hbne
  have hbneF := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hbneL
  have htaken := cpsBranchWithin_takenPath hbneF
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact hk (((sepConj_pure_right _).1 h_pure).2))
  have hrej := liftCode (cr' := bansfCR)
    (bansf_rejectTail_spec B cur bansf_item4_code.2.2.2.2)
    (fun a i h => CodeReq.union_mono_left a i h)
  have hrejF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x11 : Reg) ↦ᵣ endW) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hrej
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp') htaken hrejF
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
    hchain
  unfold fieldRej
  have hq' :
      (((.x11 : Reg) ↦ᵣ endW) ** ((.x12 : Reg) ↦ᵣ k) **
       ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
       (((.x10 : Reg) ↦ᵣ (1 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F)) h := by
    xperm_hyp hq
  have hqOwn := sepConj_mono (regIs_implies_regOwn .x11)
    (sepConj_mono (regIs_implies_regOwn .x12)
      (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x))) h hq'
  xperm_hyp hqOwn

#print axioms bansf_codeFieldInitFailure144_spec
theorem bansf_codeFieldInit143_spec (aB : Word) (aLen fOff : Nat) (fSpanW : Word)
    (acctBytes : List (BitVec 8))
    (v5 v6 v7 v12 v28 v29 v30 v31 vRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hfB : fOff + fSpanW.toNat ≤ aLen) :
    cpsBranchWithin 84 (B + 572) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
       ((.x11 : Reg) ↦ᵣ fSpanW) **
       ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** F)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 580) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 572 + 4) F) := by
  have hoffb : fOff < acctBytes.length := by omega
  have hovOff : aB.toNat + fOff < 2 ^ 64 := by omega
  -- the callee triple at its entry with ra = B + 572 + 4
  have hwi := rlp_walk_init_spec_within WI aB (B + 572 + 4) fSpanW
    v12 v5 v6 v7 v28 v29 v30 v31 acctBytes fOff hsalign hoffb hovOff
    (hvalid fOff hoffb)
    (fun hf8 => by
      have hlo : ((acctBytes[fOff]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[fOff]'hoffb).isLt
        bv_omega
      omega)
    (fun hf8 => by
      have hlo : ((acctBytes[fOff]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[fOff]'hoffb).isLt
        bv_omega
      omega)
    (fun hf8 => by
      intro k hk
      have hlo : ((acctBytes[fOff]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[fOff]'hoffb).isLt
        bv_omega
      exact hvalid _ (by omega))
  have hwi' := cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwi
    (P' := ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) ** ((.x11 : Reg) ↦ᵣ fSpanW) **
       ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  have hcall := bansf_callSite143_walk_init (n := 81) vRa (by pcf) hwi'
  rw [show (B + 572) + 4 = B + 576 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR F hF hcall
  set bb : BitVec 8 := acctBytes[fOff]'hoffb with hbb
  -- the window-end bridge: ptr + span = aB + ofNat (fOff + span.toNat)
  have hendB : (aB + BitVec.ofNat 64 fOff) + fSpanW
      = aB + BitVec.ofNat 64 (fOff + fSpanW.toNat) := by
    bv_omega
  -- ===== the success continuation (status pinned 0) =====
  have hsucc : cpsBranchWithin 2 (B + 576) bansfCR
      (fun h => ∃ cOff : Nat,
        ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜FieldInitOk acctBytes fOff fSpanW.toNat cOff⌝) h)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 580) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 572 + 4) F) := by
    refine cpsBranchWithin_exists_pre (fun cOff => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
    have hs := bansf_codeFieldInitSuccess144_spec aB fOff fSpanW.toNat cOff
      acctBytes F hF hok
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right (B + 736)
        (fieldRej aB acctBytes F) hs)
  have hfailc : cpsBranchWithin 2 (B + 576) bansfCR
      (fun h => ∃ cur endW k : Word,
        ((((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
          ((.x12 : Reg) ↦ᵣ k) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜k ≠ (0 : Word)⌝) h)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 580) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 572 + 4) F) := by
    refine cpsBranchWithin_exists_pre (fun cur => ?_)
    refine cpsBranchWithin_exists_pre (fun endW => ?_)
    refine cpsBranchWithin_exists_pre (fun k => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hk => ?_)
    have hf := bansf_codeFieldInitFailure144_spec aB cur endW k acctBytes F hF hk
    exact cpsTripleWithin_as_cpsBranchWithin_left (B + 580)
      (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 572 + 4) F) hf
  -- ===== chain: call ; (success ∨ failure) =====
  refine cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ x => x) (fun _ x => x)
    (cpsTripleWithin_seq_branch_same_cr hcallF
      (cpsBranchWithin_weaken (fun h hp => ?_) (fun _ x => x) (fun _ x => x)
        (cpsBranchWithin_pre_or hsucc hfailc)))
  -- pointwise: collapse the nine callee arms into success ∨ failure
  obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, hor⟩, hEx⟩ := hp
  have rebuild : ∀ (arm : Assertion), arm h4 →
      ((((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) ** bytesRegion aB acctBytes) ** arm) ** F)) h :=
    fun arm ha => ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, ha⟩, hEx⟩
  rcases hor with a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9
  · -- fail arm: status 2 (empty span)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (0 : Word), (2 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a1
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ (2 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ (2 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 1 (not a list)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (1 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a2
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (1 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (1 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- short-list success (status 0)
    refine Or.inl ⟨fOff + 1, ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a3
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, hfacts⟩ := (sepConj_pure_right g4).1 grest2
    obtain ⟨hne0, hge0c, hf8, hcons⟩ := hfacts
    have hx10' : ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + 1))) g1 := by
      rwa [show (aB + BitVec.ofNat 64 fOff) + signExtend12 (1 : BitVec 12)
          = aB + BitVec.ofNat 64 (fOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
        bv_omega] at hx10
    have hx11' : ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) g3 := by
      rwa [hendB] at hx11
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + 1))) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10', g3, g4, gd2, gu2, hx11', hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + 1))) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    refine (sepConj_pure_right h).2 ⟨hflat,
      ⟨bb, List.getElem?_eq_getElem hoffb, ?_, by omega, ?_⟩⟩
    · -- listHeaderSize bb = 1: short-form prefix
      have hlt := ult_lt hf8
      have hzb : (bb.zeroExtend 64).toNat = bb.toNat := by bv_omega
      unfold listHeaderSize
      rw [if_pos (by
        rw [show ((0xf8 : Word)).toNat = 0xf8 from rfl] at hlt
        omega)]
    · -- 1 ≤ span: the consistency equation forces a non-trivial span
      have hlen1 : ((bb.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
          = fSpanW := by
        have := hcons
        bv_omega
      have h1 : 1 ≤ fSpanW.toNat := by
        have hgec := not_ult_le hge0c
        rw [← hlen1, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
        bv_omega
      omega
  · -- fail arm: status 3 (short mismatch)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (3 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a4
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (3 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (3 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 4 (long truncated)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (4 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a5
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (4 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (4 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 5 (long leading zero)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (5 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a6
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (5 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (5 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 6 (long non-minimal)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (6 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a7
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (6 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (6 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 7 (long mismatch)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (7 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a8
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (7 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (7 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- long-list success (status 0)
    refine Or.inl ⟨fOff + ((bb.zeroExtend 64 - (0xf7 : Word)) +
      signExtend12 (1 : BitVec 12)).toNat, ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a9
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, hfacts⟩ := (sepConj_pure_right g4).1 grest2
    obtain ⟨hne0, hnc0, hnf8, hfit, hmin5, hsum6⟩ := hfacts
    clear hmin5 hsum6 hnc0
    have hgef8 := not_ult_le hnf8
    rw [show ((0xf8 : Word)).toNat = 0xf8 from rfl] at hgef8
    have hzb : (bb.zeroExtend 64).toNat = bb.toNat := by bv_omega
    have hhdrN : ((bb.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)).toNat
        = 1 + (bb.toNat - 0xf7) := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      have hb := bb.isLt
      bv_omega
    have hx10' : ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64
        (fOff + ((bb.zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)).toNat))) g1 := by
      rwa [show (aB + BitVec.ofNat 64 fOff) +
          ((bb.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))
          = aB + BitVec.ofNat 64
            (fOff + ((bb.zeroExtend 64 - (0xf7 : Word)) +
              signExtend12 (1 : BitVec 12)).toNat) from by
        bv_omega] at hx10
    have hx11' : ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) g3 := by
      rwa [hendB] at hx11
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64
        (fOff + ((bb.zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)).toNat))) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10', g3, g4, gd2, gu2, hx11', hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64
        (fOff + ((bb.zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)).toNat))) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    refine (sepConj_pure_right h).2 ⟨hflat,
      ⟨bb, List.getElem?_eq_getElem hoffb, ?_, ?_, ?_⟩⟩
    · -- listHeaderSize bb = 1 + (bb - 0xf7): long-form prefix
      unfold listHeaderSize
      rw [if_neg (by omega), hhdrN]
    · -- strictly past the header
      rw [hhdrN]
      omega
    · -- header fits inside the window
      rw [hhdrN]
      have hfit' := not_ult_le hfit
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hfit'
      have hb := bb.isLt
      bv_omega


#print axioms bansf_codeFieldInit143_spec

/-- Slot 145, taken arm (`B + 580 → B + 724`): an empty code field skips
    directly to the success stub. -/
theorem bansf_codeEmptyTaken145_spec (aB : Word) (cOff fEnd : Nat)
    (heq : cOff = fEnd) :
    cpsTripleWithin 1 (B + 580) (B + 724) bansfCode
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd)))
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd))) := by
  subst heq
  have hbeq := beq_spec_gen_within .x10 .x11 (144 : BitVec 13)
    (aB + BitVec.ofNat 64 cOff) (aB + BitVec.ofNat 64 cOff) (B + 580)
  rw [show (B + 580) + signExtend13 (144 : BitVec 13) = B + 724 from by
        rw [show signExtend13 (144 : BitVec 13) = (144 : Word) from by decide]
        bv_omega] at hbeq
  have hbeqL := cpsBranchWithin_extend_code (cr' := bansfCode)
    bansf_codeEmpty145_code hbeq
  have h := cpsBranchWithin_takenPath hbeqL
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hq) h

#print axioms bansf_codeEmptyTaken145_spec

/-- Slot 145, fall-through arm (`B + 580 → B + 584`): a nonempty code
    window enters the station-3 find-last loop. -/
theorem bansf_codeEmptyFall145_spec (aB : Word) (aLen cOff fEnd : Nat)
    (hne : cOff ≠ fEnd) (hcle : cOff ≤ aLen) (hfle : fEnd ≤ aLen)
    (hover9 : aB.toNat + aLen + 9 < 2 ^ 64) :
    cpsTripleWithin 1 (B + 580) (B + 584) bansfCode
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd)))
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd))) := by
  have hwne : aB + BitVec.ofNat 64 cOff ≠ aB + BitVec.ofNat 64 fEnd := by
    intro hc
    apply hne
    have := congrArg BitVec.toNat hc
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat] at this
    omega
  have hbeq := beq_spec_gen_within .x10 .x11 (144 : BitVec 13)
    (aB + BitVec.ofNat 64 cOff) (aB + BitVec.ofNat 64 fEnd) (B + 580)
  rw [show (B + 580) + 4 = B + 584 from by bv_omega] at hbeq
  have hbeqL := cpsBranchWithin_extend_code (cr' := bansfCode)
    bansf_codeEmpty145_code hbeq
  have h := cpsBranchWithin_ntakenPath hbeqL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd (((sepConj_pure_right _).1 h_pure).2) hwne)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hq) h

#print axioms bansf_codeEmptyFall145_spec

/-- Slots 146–147 (`B + 584 → B + 592`): spill the nonempty code window
    cursor and end for station-3's find-last loop. -/
theorem bansf_codeLoopEntry146_spec (aB newSp : Word) (cOff fEnd : Nat) :
    cpsTripleWithin 2 (B + 584) (B + 592) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd)) **
       ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) ** memOwn (newSp + 72))
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 fEnd))) := by
  have hsd1 := sd_spec_gen_own_within .x2 .x10 newSp
    (aB + BitVec.ofNat 64 cOff) (64 : BitVec 12) (B + 584)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (B + 584) + 4 = B + 588 from by bv_omega] at hsd1
  have hsd1L := liftCode (cr' := bansfCR) hsd1 bansf_codeLoopEntry_code.1
  have hsd2 := sd_spec_gen_own_within .x2 .x11 newSp
    (aB + BitVec.ofNat 64 fEnd) (72 : BitVec 12) (B + 588)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide,
      show (B + 588) + 4 = B + 592 from by bv_omega] at hsd2
  have hsd2L := liftCode (cr' := bansfCR) hsd2 bansf_codeLoopEntry_code.2
  have hsd1F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd)) ** memOwn (newSp + 72))
    (by pcf) hsd1L
  have hsd2F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)))
    (by pcf) hsd2L
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hsd1F hsd2F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hchain

#print axioms bansf_codeLoopEntry146_spec

/-- Shared reject boundary for the code station. `G` is the already-complete
    balance/nonce footprint and remains untouched. -/
def codeStationRej (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  G ** memOwn (oB + 56) ** memOwn (oB + 64) ** memOwn (oB + 72) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
  ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
  ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x11 ** regOwn .x12 **
  regOwn .x19 ** regOwn .x20 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

/-- Successful code-station boundary at the success stub. The found arm
    materializes only a relative byte window; it does not parse code bytes. -/
def codeStationPost (aB newSp oB : Word) (aLen fOff fSpanN : Nat)
    (n5 : Word) (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  fun h =>
    (((G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       memOwn (newSp + 64) ** memOwn (newSp + 72) **
       ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
       ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
       regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x19 **
       regOwn .x20 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
       bytesRegion aB acctBytes ** F) **
      ⌜FieldFinal acctBytes aB fOff fSpanN none⌝) h) ∨
    (∃ vNext vLen : Word,
      ((G ** ((oB + 56) ↦ₘ (1 : Word)) **
        ((oB + 64) ↦ₘ BitVec.ofNat 64 ((vNext - vLen - aB).toNat)) **
        ((oB + 72) ↦ₘ BitVec.ofNat 64 vLen.toNat) **
        ((newSp + 48) ↦ₘ n5) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x19 **
        regOwn .x20 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F) **
       ⌜FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))⌝) h)

/-- Reframe a Loop3 parse failure as the code-station reject boundary. -/
theorem codeLoopReject_to_stationRej (aB newSp oB n5 : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (flRej aB newSp acctBytes F **
       (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB))) h →
      codeStationRej aB newSp oB aLen acctBytes G F h := by
  intro h hq
  unfold flRej at hq
  have hq' :
      (((newSp + 48) ↦ₘ n5) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) **
       (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        regOwn .x19 ** regOwn .x20 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F ** G ** ((.x8 : Reg) ↦ᵣ aB) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB))) h := by
    xperm_hyp hq
  have hqOwn := sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn (fun _ x => x))))) h hq'
  unfold codeStationRej
  xperm_hyp hqOwn

#print axioms codeLoopReject_to_stationRej

/-- Slots 175–180 (`B + 700 → B + 724`): materialize the selected code
    value as the relative `(offset,length)` window and set `has_code`. -/
theorem bansf_codeMaterialize175_spec (aB oB vNext vLen v29 v5 : Word) :
    cpsTripleWithin 6 (B + 700) (B + 724) bansfCR
      (((.x10 : Reg) ↦ᵣ vNext) ** ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x18 : Reg) ↦ᵣ oB) **
       ((.x29 : Reg) ↦ᵣ v29) ** ((.x5 : Reg) ↦ᵣ v5) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ vNext) ** ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x18 : Reg) ↦ᵣ oB) **
       ((.x29 : Reg) ↦ᵣ (vNext - vLen - aB)) **
       ((.x5 : Reg) ↦ᵣ (1 : Word)) **
       ((oB + 56) ↦ₘ (1 : Word)) **
       ((oB + 64) ↦ₘ (vNext - vLen - aB)) **
       ((oB + 72) ↦ₘ vLen)) := by
  have s1 := sub_spec_gen_within .x29 .x10 .x12 vNext vLen v29
    (B + 700) (by decide)
  rw [show (B + 700) + 4 = B + 704 from by bv_omega] at s1
  have s1L := liftCode (cr' := bansfCR) s1 bansf_codeMaterialize_code.1
  have s2 := sub_spec_gen_rd_eq_rs1_within .x29 .x8 (vNext - vLen) aB
    (B + 704) (by decide)
  rw [show (B + 704) + 4 = B + 708 from by bv_omega] at s2
  have s2L := liftCode (cr' := bansfCR) s2 bansf_codeMaterialize_code.2.1
  have s3 := sd_spec_gen_within .x18 .x29 oB (vNext - vLen - aB)
    (0 : Word) (64 : BitVec 12) (B + 708)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (B + 708) + 4 = B + 712 from by bv_omega] at s3
  have s3L := liftCode (cr' := bansfCR) s3 bansf_codeMaterialize_code.2.2.1
  have s4 := sd_spec_gen_within .x18 .x12 oB vLen
    (0 : Word) (72 : BitVec 12) (B + 712)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide,
      show (B + 712) + 4 = B + 716 from by bv_omega] at s4
  have s4L := liftCode (cr' := bansfCR) s4 bansf_codeMaterialize_code.2.2.2.1
  have s5 := li_spec_gen_within .x5 v5 (1 : Word) (B + 716) (by decide)
  rw [show (B + 716) + 4 = B + 720 from by bv_omega] at s5
  have s5L := liftCode (cr' := bansfCR) s5 bansf_codeMaterialize_code.2.2.2.2.1
  have s6 := sd_spec_gen_within .x18 .x5 oB (1 : Word)
    (0 : Word) (56 : BitVec 12) (B + 720)
  rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide,
      show (B + 720) + 4 = B + 724 from by bv_omega] at s6
  have s6L := liftCode (cr' := bansfCR) s6 bansf_codeMaterialize_code.2.2.2.2.2
  have s1F := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ aB) ** ((.x18 : Reg) ↦ᵣ oB) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((oB + 56) ↦ₘ (0 : Word)) **
     ((oB + 64) ↦ₘ (0 : Word)) ** ((oB + 72) ↦ₘ (0 : Word)))
    (by pcf) s1L
  have s2F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ vNext) ** ((.x12 : Reg) ↦ᵣ vLen) **
     ((.x18 : Reg) ↦ᵣ oB) ** ((.x5 : Reg) ↦ᵣ v5) **
     ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
     ((oB + 72) ↦ₘ (0 : Word))) (by pcf) s2L
  have s3F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ vNext) ** ((.x12 : Reg) ↦ᵣ vLen) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x5 : Reg) ↦ᵣ v5) **
     ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 72) ↦ₘ (0 : Word)))
    (by pcf) s3L
  have s4F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ vNext) ** ((.x8 : Reg) ↦ᵣ aB) **
     ((.x29 : Reg) ↦ᵣ (vNext - vLen - aB)) ** ((.x5 : Reg) ↦ᵣ v5) **
     ((oB + 56) ↦ₘ (0 : Word)) **
     ((oB + 64) ↦ₘ (vNext - vLen - aB))) (by pcf) s4L
  have s5F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ vNext) ** ((.x12 : Reg) ↦ᵣ vLen) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x18 : Reg) ↦ᵣ oB) **
     ((.x29 : Reg) ↦ᵣ (vNext - vLen - aB)) **
     ((oB + 56) ↦ₘ (0 : Word)) **
     ((oB + 64) ↦ₘ (vNext - vLen - aB)) ** ((oB + 72) ↦ₘ vLen))
    (by pcf) s5L
  have s6F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ vNext) ** ((.x12 : Reg) ↦ᵣ vLen) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x29 : Reg) ↦ᵣ (vNext - vLen - aB)) **
     ((oB + 64) ↦ₘ (vNext - vLen - aB)) ** ((oB + 72) ↦ₘ vLen))
    (by pcf) s6L
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1F s2F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 s3F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c2 s4F
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c3 s5F
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c4 s6F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) c5

#print axioms bansf_codeMaterialize175_spec

/-- Slots 170–172 (`B + 680 → B + 692`): load the tuple value cursor/end
    and move the cursor into `a0` for `rlp_walk_next`. -/
theorem bansf_codeValueArgs170_spec (newSp cursor endW v28 v11 v10 : Word) :
    cpsTripleWithin 3 (B + 680) (B + 692) bansfCR
      (((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) **
       ((newSp + 72) ↦ₘ endW) ** ((.x28 : Reg) ↦ᵣ v28) **
       ((.x11 : Reg) ↦ᵣ v11) ** ((.x10 : Reg) ↦ᵣ v10))
      (((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) **
       ((newSp + 72) ↦ₘ endW) ** ((.x28 : Reg) ↦ᵣ cursor) **
       ((.x11 : Reg) ↦ᵣ endW) ** ((.x10 : Reg) ↦ᵣ cursor)) := by
  have s1 := ld_spec_gen_within .x28 .x2 newSp v28 cursor
    (64 : BitVec 12) (B + 680) (by decide)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (B + 680) + 4 = B + 684 from by bv_omega] at s1
  have s1L := liftCode (cr' := bansfCR) s1 bansf_codeValueArgs_code.1
  have s2 := ld_spec_gen_within .x11 .x2 newSp v11 endW
    (72 : BitVec 12) (B + 684) (by decide)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide,
      show (B + 684) + 4 = B + 688 from by bv_omega] at s2
  have s2L := liftCode (cr' := bansfCR) s2 bansf_codeValueArgs_code.2.1
  have s3 := mv_spec_gen_within .x10 .x28 cursor v10 (B + 688) (by decide)
  rw [show (B + 688) + 4 = B + 692 from by bv_omega] at s3
  have s3L := liftCode (cr' := bansfCR) s3 bansf_codeValueArgs_code.2.2
  have s1F := cpsTripleWithin_frameR
    (((newSp + 72) ↦ₘ endW) ** ((.x11 : Reg) ↦ᵣ v11) **
     ((.x10 : Reg) ↦ᵣ v10)) (by pcf) s1L
  have s2F := cpsTripleWithin_frameR
    (((newSp + 64) ↦ₘ cursor) ** ((.x28 : Reg) ↦ᵣ cursor) **
     ((.x10 : Reg) ↦ᵣ v10)) (by pcf) s2L
  have s3F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ cursor) **
     ((newSp + 72) ↦ₘ endW) ** ((.x11 : Reg) ↦ᵣ endW)) (by pcf) s3L
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1F s2F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 s3F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) c2

#print axioms bansf_codeValueArgs170_spec

/-- Status-zero continuation for the code tuple value (`B + 696 → B + 724`):
    fall through the gate and materialize its relative window. -/
theorem bansf_codeValueSuccess174_spec
    (aB oB vNext vLen v29 v5 : Word) :
    cpsTripleWithin 7 (B + 696) (B + 724) bansfCR
      (((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ vLen) ** ((.x8 : Reg) ↦ᵣ aB) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ vLen) ** ((.x8 : Reg) ↦ᵣ aB) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((.x29 : Reg) ↦ᵣ (vNext - vLen - aB)) **
       ((.x5 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((oB + 56) ↦ₘ (1 : Word)) **
       ((oB + 64) ↦ₘ (vNext - vLen - aB)) ** ((oB + 72) ↦ₘ vLen)) := by
  have hbne := bne_spec_gen_within .x11 .x0 (36 : BitVec 13)
    (0 : Word) (0 : Word) (B + 696)
  rw [show (B + 696) + 4 = B + 700 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    bansf_codeValueStatus174_code hbne
  have hfall := cpsBranchWithin_ntakenPath hbneL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  have hfallF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ vNext) ** ((.x12 : Reg) ↦ᵣ vLen) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x18 : Reg) ↦ᵣ oB) **
     ((.x29 : Reg) ↦ᵣ v29) ** ((.x5 : Reg) ↦ᵣ v5) **
     ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
     ((oB + 72) ↦ₘ (0 : Word))) (by pcf) hfall
  have hmat := bansf_codeMaterialize175_spec aB oB vNext vLen v29 v5
  have hmatF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hmat
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp') hfallF hmatF
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hchain

#print axioms bansf_codeValueSuccess174_spec

/-- Nonzero-status continuation for the code tuple value (`B + 696 → B + 736`). -/
theorem bansf_codeValueFailure174_spec (aB newSp cur k : Word)
    (tEnd off : Nat) (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) (hk : k ≠ (0 : Word)) :
    cpsTripleWithin 2 (B + 696) (B + 736) bansfCR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ k) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
       bytesRegion aB acctBytes ** F)
      (tupleRej aB newSp acctBytes F) := by
  have hbne := bne_spec_gen_within .x11 .x0 (36 : BitVec 13)
    k (0 : Word) (B + 696)
  rw [show (B + 696) + signExtend13 (36 : BitVec 13) = B + 732 from by
        rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]
        bv_omega,
      show (B + 696) + 4 = B + 700 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    bansf_codeValueStatus174_code hbne
  have hbneF := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ cur) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
     ((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hbneL
  have htaken := cpsBranchWithin_takenPath hbneF
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact hk (((sepConj_pure_right _).1 h_pure).2))
  have hrej := liftCode (cr' := bansfCR)
    (bansf_rejectTail_spec B cur bansf_item4_code.2.2.2.2)
    (fun a i h => CodeReq.union_mono_left a i h)
  have hrejF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hrej
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp') htaken hrejF
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
    hchain
  unfold tupleRej
  have hq' :
      (((.x11 : Reg) ↦ᵣ k) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
       (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F)) h := by
    xperm_hyp hq
  have hqOwn := sepConj_mono (regIs_implies_regOwn .x11)
    (sepConj_mono (regIs_implies_regOwn .x12)
      (sepConj_mono (regIs_implies_regOwn .x1)
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn (fun _ x => x))))) h hq'
  xperm_hyp hqOwn

#print axioms bansf_codeValueFailure174_spec
theorem bansf_codeTupleItem1_spec (aB newSp : Word) (aLen tEnd off : Nat)
    (acctBytes : List (BitVec 8))
    (v5 v6 v7 v10 v11 v12 v28 v29 v30 v31 vRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen)
    (hoffle : off ≤ tEnd) :
    cpsBranchWithin 93 (B + 680) bansfCR
      (((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** F)
      (B + 736) (tupleRej aB newSp acctBytes F)
      (B + 700) (tupleValOk aB newSp tEnd off acctBytes F) := by
  have hoffb : off < acctBytes.length := by omega
  have hargs := bansf_codeValueArgs170_spec newSp
    (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 tEnd) v28 v11 v10
  have hargsF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ v12) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x1 : Reg) ↦ᵣ vRa) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hargs
  -- the callee triple with ra = B + 692 + 4
  have hwn := rlp_walk_next_spec_within WN aB (aB + BitVec.ofNat 64 tEnd)
    (B + 692 + 4) v12 v5 v6 v7 (aB + BitVec.ofNat 64 off) v29 v30 v31
    acctBytes off hsalign hoffb (by omega)
    (hvalid off hoffb)
    (fun h80 hb8 => ⟨by omega, by omega, hvalid _ (by omega)⟩)
    (fun hb8 hc0 => by
      have hlo : ((acctBytes[off]'hoffb).zeroExtend 64 - (0xb7 : Word)).toNat ≤ 8 := by
        have h1 := ult_lt hc0
        have h2 := not_ult_le hb8
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
    (fun hf8 => by
      have hlo : ((acctBytes[off]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[off]'hoffb).isLt
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
  have hwn' := cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwn
    (P' := ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 tEnd)) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  have hcall := bansf_callSite173_walk_next (n := 87) vRa (by pcf) hwn'
  rw [show (B + 692) + 4 = B + 696 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) ** F)
    (by pcf; exact hF) hcall
  have hpre := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hargsF hcallF
  -- ===== ok continuation: BNE falls through only =====
  have hokc : cpsBranchWithin 1 (B + 696) bansfCR
      (fun h => ∃ next len : Word,
        ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
           (aB + BitVec.ofNat 64 tEnd) next len⌝) h)
      (B + 736) (tupleRej aB newSp acctBytes F)
      (B + 700) (tupleValOk aB newSp tEnd off acctBytes F) := by
    refine cpsBranchWithin_exists_pre (fun next => ?_)
    refine cpsBranchWithin_exists_pre (fun len => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hdec => ?_)
    have hbne := bne_spec_gen_within .x11 .x0 (36 : BitVec 13) (0 : Word) (0 : Word) (B + 696)
    rw [show (B + 696) + 4 = B + 700 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      bansf_codeValueStatus174_code hbne
    have hfall := cpsBranchWithin_ntakenPath hbneL
      (fun hp hQt => by
        obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
        exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
    have hfallF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ next) ** ((.x12 : Reg) ↦ᵣ len) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hfall
    have hout : cpsTripleWithin 1 (B + 696) (B + 700) bansfCR
        (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
         ((.x12 : Reg) ↦ᵣ len) **
         ((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
         bytesRegion aB acctBytes ** F)
        (tupleValOk aB newSp tEnd off acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hfallF
      unfold tupleValOk
      refine ⟨next, len, ?_⟩
      have hq1 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      have hq2 : ((((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
          (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
           ((.x12 : Reg) ↦ᵣ len) **
           ((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aB acctBytes ** F))) h := by
        xperm_hyp hq1
      have hq3 := sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x) h hq2
      have hq4 : ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          (((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd))) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hq3
      have hq5 := sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)
              (fun _ x => x))))) h hq4
      exact (sepConj_pure_right h).2 ⟨by xperm_hyp hq5, hdec⟩
    exact cpsTripleWithin_as_cpsBranchWithin_right _ _ hout
  -- ===== fail continuation =====
  have hfailc : cpsBranchWithin 2 (B + 696) bansfCR
      (fun h => ∃ cur k : Word,
        ((((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ k) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜k ≠ (0 : Word)⌝) h)
      (B + 736) (tupleRej aB newSp acctBytes F)
      (B + 700) (tupleValOk aB newSp tEnd off acctBytes F) := by
    refine cpsBranchWithin_exists_pre (fun cur => ?_)
    refine cpsBranchWithin_exists_pre (fun k => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hk => ?_)
    have hbne := bne_spec_gen_within .x11 .x0 (36 : BitVec 13) k (0 : Word) (B + 696)
    rw [show (B + 696) + signExtend13 (36 : BitVec 13) = B + 732 from by
          rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]
          bv_omega,
        show (B + 696) + 4 = B + 700 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      bansf_codeValueStatus174_code hbne
    have hbneF := cpsBranchWithin_frameR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hbneL
    have htaken := cpsBranchWithin_takenPath hbneF
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact hk (((sepConj_pure_right _).1 h_pure).2))
    have hrej := liftCode (cr' := bansfCR)
      (bansf_rejectTail_spec B cur bansf_item4_code.2.2.2.2)
      (fun a i h => CodeReq.union_mono_left a i h)
    have hrejF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hrej
    have hchain := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2)
      htaken hrejF
    have hout : cpsTripleWithin 2 (B + 696) (B + 736) bansfCR
        (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ k) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) **
         ((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
         bytesRegion aB acctBytes ** F)
        (tupleRej aB newSp acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      unfold tupleRej
      have hq4 : ((((.x11 : Reg) ↦ᵣ k) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
          (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aB acctBytes ** F))) h := by
        xperm_hyp hq
      have hq5 := sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x1)
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn (fun _ x => x))))) h hq4
      xperm_hyp hq5
    exact cpsTripleWithin_as_cpsBranchWithin_left _ _ hout
  -- ===== chain: loads ; call ; (ok ∨ fail) =====
  refine cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ x => x) (fun _ x => x)
    (cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_seq_branch_same_cr hpre
        (cpsBranchWithin_weaken (fun h hp => ?_) (fun _ x => x) (fun _ x => x)
          (cpsBranchWithin_pre_or
            (cpsBranchWithin_mono_nSteps (by omega) hokc) hfailc))))
  obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, hor⟩, hEx⟩ := hp
  have rebuild : ∀ (arm : Assertion), arm h4 →
      ((((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) ** bytesRegion aB acctBytes) ** arm) **
        (((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) ** F))) h :=
    fun arm ha => ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, ha⟩, hEx⟩
  rcases hor with a1 | a2 | a3 | a4 | a5 | a6
  · obtain ⟨next, len, hpins⟩ := a1
    refine Or.inl ⟨next, len, ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := hpins
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, hdec⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ len))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ len) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, hdec⟩
  · -- fail arm: status 2
    refine Or.inr ⟨aB + BitVec.ofNat 64 off, (2 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a2
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (2 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (2 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 3
    refine Or.inr ⟨aB + BitVec.ofNat 64 off, (3 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a3
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (3 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (3 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 4
    refine Or.inr ⟨aB + BitVec.ofNat 64 off, (4 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a4
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (4 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (4 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 5
    refine Or.inr ⟨aB + BitVec.ofNat 64 off, (5 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a5
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (5 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (5 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 6
    refine Or.inr ⟨aB + BitVec.ofNat 64 off, (6 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a6
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (6 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (6 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 692 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩

#print axioms bansf_codeTupleItem1_spec



end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
