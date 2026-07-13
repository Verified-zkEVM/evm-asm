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


end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
