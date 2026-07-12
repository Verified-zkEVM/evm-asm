/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainC

  Field-window `rlp_walk_init` dispatch for the `bal_account_nonstorage_finals`
  stations (bead evm-asm-4ch8f.43.5, slice 4a): the span captured by
  `s3 := a0 - a2 ; s4 := a2` is re-walked as an RLP list; the nine callee
  arms collapse (as in the outer dispatch) into failure (→ the shared reject
  epilogue) vs the unified `listHeaderSize`-anchored content cursor.  The
  side conditions and the inner 9-byte slack discharge from the OUTER region
  bounds via `rlpItemDecode_spanStart`'s nesting (`fOff + fSpan ≤ aLen`).

  Verified here at the balance-field site (slot 50); the other five field
  sites (68/97/115/143/161) instantiate by the concrete address table.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainB3

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

private theorem se1c : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide

/-- The pure residue of a successful field-window `rlp_walk_init`: the
    content cursor offset is `listHeaderSize` of the window's first byte,
    strictly past the header, within the span. -/
def FieldInitOk (bytes : List (BitVec 8)) (fOff fSpanN cOff : Nat) : Prop :=
  ∃ b, bytes[fOff]? = some b ∧ cOff = fOff + listHeaderSize b ∧
    fOff < cOff ∧ cOff ≤ fOff + fSpanN

/-- The unified continue-state after a field init status check. -/
def fieldInitPost (aB : Word) (fOff fSpanN : Nat) (acctBytes : List (BitVec 8))
    (raV : Word) (F : Assertion) : Assertion :=
  fun h => ∃ cOff : Nat,
    ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
      ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
      ((.x12 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raV) **
      bytesRegion aB acctBytes ** F) **
     ⌜FieldInitOk acctBytes fOff fSpanN cOff⌝) h

/-- The reject-side post of a field init failure. -/
def fieldRej (aB : Word) (acctBytes : List (BitVec 8)) (F : Assertion) :
    Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) **
  regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

/-- Field-window `rlp_walk_init` (slot 50, the balance field) + status
    check (slot 51): reject on any non-zero status; on success, land at
    `B + 208` with the unified content cursor.  The window is the span
    `[fOff, fOff + fSpanN)` with `fSpanW` its length as a word. -/
theorem bansf_fieldInit50_spec (aB : Word) (aLen fOff : Nat) (fSpanW : Word)
    (acctBytes : List (BitVec 8))
    (v5 v6 v7 v12 v28 v29 v30 v31 vRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hfB : fOff + fSpanW.toNat ≤ aLen) :
    cpsBranchWithin 84 (B + 200) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
       ((.x11 : Reg) ↦ᵣ fSpanW) **
       ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** F)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 208) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 200 + 4) F) := by
  have hoffb : fOff < acctBytes.length := by omega
  have hovOff : aB.toNat + fOff < 2 ^ 64 := by omega
  -- the callee triple at its entry with ra = B + 200 + 4
  have hwi := rlp_walk_init_spec_within WI aB (B + 200 + 4) fSpanW
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
    (P' := ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) ** ((.x11 : Reg) ↦ᵣ fSpanW) **
       ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  have hcall := bansf_callSite50_walk_init (n := 81) vRa (by pcf) hwi'
  rw [show (B + 200) + 4 = B + 204 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR F hF hcall
  set bb : BitVec 8 := acctBytes[fOff]'hoffb with hbb
  -- the window-end bridge: ptr + span = aB + ofNat (fOff + span.toNat)
  have hendB : (aB + BitVec.ofNat 64 fOff) + fSpanW
      = aB + BitVec.ofNat 64 (fOff + fSpanW.toNat) := by
    bv_omega
  -- ===== the success continuation (status pinned 0) =====
  have hsucc : cpsBranchWithin 2 (B + 204) bansfCR
      (fun h => ∃ cOff : Nat,
        ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜FieldInitOk acctBytes fOff fSpanW.toNat cOff⌝) h)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 208) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 200 + 4) F) := by
    refine cpsBranchWithin_exists_pre (fun cOff => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
    have hbne := bne_spec_gen_within .x12 .x0 (528 : BitVec 13) (0 : Word) (0 : Word) (B + 204)
    rw [show (B + 204) + 4 = B + 208 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 204) bansfProg 51 (.BNE .x12 .x0 (528 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
      hbne
    have hfall := cpsBranchWithin_ntakenPath hbneL
      (fun hp hQt => by
        obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
        exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
    have hfallF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hfall
    have hout : cpsTripleWithin 1 (B + 204) (B + 208) bansfCR
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
         ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
         bytesRegion aB acctBytes ** F)
        (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 200 + 4) F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hfallF
      unfold fieldInitPost
      refine ⟨cOff, ?_⟩
      have hq2 : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
          bytesRegion aB acctBytes ** F)) h := by
        have hq3 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
        xperm_hyp hq3
      exact (sepConj_pure_right h).2 ⟨hq2, hok⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right _ _ hout)
  -- ===== the failure continuation (status pinned non-zero) =====
  have hfailc : cpsBranchWithin 2 (B + 204) bansfCR
      (fun h => ∃ cur endW k : Word,
        ((((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
          ((.x12 : Reg) ↦ᵣ k) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜k ≠ (0 : Word)⌝) h)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 208) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 200 + 4) F) := by
    refine cpsBranchWithin_exists_pre (fun cur => ?_)
    refine cpsBranchWithin_exists_pre (fun endW => ?_)
    refine cpsBranchWithin_exists_pre (fun k => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hk => ?_)
    -- the BNE at slot 51: taken (status ≠ 0) to the reject stub
    have hbne := bne_spec_gen_within .x12 .x0 (528 : BitVec 13) k (0 : Word) (B + 204)
    rw [show (B + 204) + signExtend13 (528 : BitVec 13) = B + 732 from by
          rw [show signExtend13 (528 : BitVec 13) = (528 : Word) from by decide]
          bv_omega,
        show (B + 204) + 4 = B + 208 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 204) bansfProg 51 (.BNE .x12 .x0 (528 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
      hbne
    have hbneF := cpsBranchWithin_frameR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) ** bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hbneL
    have htaken := cpsBranchWithin_takenPath hbneF
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact hk (((sepConj_pure_right _).1 h_pure).2))
    have hrej := liftCode (cr' := bansfCR)
      (bansf_rejectTail_spec B cur (by decide))
      (fun a i h => CodeReq.union_mono_left a i h)
    have hrejF := cpsTripleWithin_frameR
      (((.x12 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ endW) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) ** bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hrej
    have hchain := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2)
      htaken hrejF
    have hout : cpsTripleWithin 2 (B + 204) (B + 736) bansfCR
        (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
         ((.x12 : Reg) ↦ᵣ k) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
         bytesRegion aB acctBytes ** F)
        (fieldRej aB acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      unfold fieldRej
      have hq4 : ((((.x11 : Reg) ↦ᵣ endW) ** ((.x12 : Reg) ↦ᵣ k) **
          ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
          (((.x10 : Reg) ↦ᵣ (1 : Word)) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aB acctBytes ** F))) h := by
        xperm_hyp hq
      have hq5 := sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x))) h hq4
      xperm_hyp hq5
    exact cpsTripleWithin_as_cpsBranchWithin_left _ _ hout
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
          ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) ** bytesRegion aB acctBytes) ** arm) ** F)) h :=
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
        rw [se1c]
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
        rw [← hlen1, se1c]
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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


#print axioms bansf_fieldInit50_spec

/-! ## §2  Span capture (slots 46–49): `s3/s4 := (a0 - a2, a2)`, args -/

/-- Slots 46–49 (`B + 184 → B + 200`): capture the field span into `s3`/`s4`
    and set up the `rlp_walk_init` arguments. -/
theorem bansf_spanCapture46_spec (n3 l3 v19 v20 : Word) :
    cpsTripleWithin 4 (B + 184) (B + 200) bansfCode
      (((.x10 : Reg) ↦ᵣ n3) ** ((.x12 : Reg) ↦ᵣ l3) **
       ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x11 : Reg) ↦ᵣ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ (n3 - l3)) ** ((.x12 : Reg) ↦ᵣ l3) **
       ((.x19 : Reg) ↦ᵣ (n3 - l3)) ** ((.x20 : Reg) ↦ᵣ l3) **
       ((.x11 : Reg) ↦ᵣ l3)) := by
  have s1 := sub_spec_gen_within .x19 .x10 .x12 n3 l3 v19 (B + 184) (by decide)
  have s2 := mv_spec_gen_within .x20 .x12 l3 v20 (B + 188) (by decide)
  have s3 := mv_spec_gen_within .x10 .x19 (n3 - l3) n3 (B + 192) (by decide)
  have s4 := mv_spec_gen_within .x11 .x20 l3 (0 : Word) (B + 196) (by decide)
  runBlock s1 s2 s3 s4

#print axioms bansf_spanCapture46_spec

/-! ## §3  The empty-list split (slot 52) -/

/-- The station post at the nonce-station boundary (`B + 352`) for the
    balance field: either the field list was EMPTY (out block untouched,
    `FieldFinal … none`), or the found path completed (has_balance set,
    the 32-byte right-aligned BE image in place, `FieldFinal … (some …)`
    with the value canonicality facts). -/
def balStationPost (aB newSp oB : Word) (aLen fOff fSpanN : Nat)
    (n3 : Word) (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  fun h =>
    -- EMPTY arm
    (((oB ↦ₘ (0 : Word)) **
      ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
      ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
      ((newSp + 48) ↦ₘ n3) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      ((.x2 : Reg) ↦ᵣ newSp) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
      regOwn .x19 ** regOwn .x20 **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     ⌜FieldFinal acctBytes aB fOff fSpanN none⌝) h ∨
    -- FOUND arm
    (∃ vNext vLen : Word,
      (((oB ↦ₘ (1 : Word)) **
        bytesRegion (oB + 8) (copyN (List.replicate 32 (0 : BitVec 8)) acctBytes
          (32 - vLen.toNat) ((vNext - vLen - aB).toNat) vLen.toNat) **
        ((newSp + 48) ↦ₘ n3) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x19 ** regOwn .x20 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F) **
       ⌜FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen)) ∧
        vLen.toNat ≤ 32⌝) h)


/-! ## §4  The empty-list split (slot 52) and loop entry (slots 53–54) -/

/-- The last decode of a `LastItemAt` derivation, extracted with its
    in-window position (for `rlpItemDecode_spanStart` at the tuple window). -/
theorem LastItemAt_decode {bytes : List (BitVec 8)} {base : Word}
    {off0 endOff : Nat} {n l : Word}
    (h : LastItemAt bytes base (base + BitVec.ofNat 64 endOff) off0 n l)
    (hoff0 : off0 ≤ endOff)
    (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    ∃ off : Nat, off ≤ endOff ∧
      rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
        (base + BitVec.ofNat 64 endOff) n l := by
  induction h with
  | last o nn ll hi _ => exact ⟨o, hoff0, hi⟩
  | step o nn ll n' l' hi _ _ ih =>
      have hadv := rlpItemDecode_advance hi hoff0 hover
      exact ih hadv.2.2

/-- Empty-field exit (slot 52 taken, `B + 208 → B + 352`): the content
    cursor equals the window end, so the field list is EMPTY. -/
theorem bansf_balEmptyTaken_spec (aB : Word) (cOff fEnd : Nat)
    (heq : cOff = fEnd) :
    cpsTripleWithin 1 (B + 208) (B + 352) bansfCode
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd)))
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd))) := by
  subst heq
  have hbeq := beq_spec_gen_within .x10 .x11 (144 : BitVec 13)
    (aB + BitVec.ofNat 64 cOff) (aB + BitVec.ofNat 64 cOff) (B + 208)
  rw [show (B + 208) + signExtend13 (144 : BitVec 13) = B + 352 from by
        rw [show signExtend13 (144 : BitVec 13) = (144 : Word) from by decide]
        bv_omega] at hbeq
  have hbeqL := cpsBranchWithin_extend_code (cr' := bansfCode)
    (fun a i h => CodeReq.ofProg_mem_at B (B + 208) bansfProg 52
      (.BEQ .x10 .x11 (144 : BitVec 13))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
    hbeq
  have h := cpsBranchWithin_takenPath hbeqL
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      exact sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hq) h

/-- Non-empty fall-through (slot 52 not taken, `B + 208 → B + 212`). -/
theorem bansf_balEmptyFall_spec (aB : Word) (aLen cOff fEnd : Nat)
    (hne : cOff ≠ fEnd) (hcle : cOff ≤ aLen) (hfle : fEnd ≤ aLen)
    (hover9 : aB.toNat + aLen + 9 < 2 ^ 64) :
    cpsTripleWithin 1 (B + 208) (B + 212) bansfCode
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
    (aB + BitVec.ofNat 64 cOff) (aB + BitVec.ofNat 64 fEnd) (B + 208)
  rw [show (B + 208) + 4 = B + 212 from by bv_omega] at hbeq
  have hbeqL := cpsBranchWithin_extend_code (cr' := bansfCode)
    (fun a i h => CodeReq.ofProg_mem_at B (B + 208) bansfProg 52
      (.BEQ .x10 .x11 (144 : BitVec 13))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
    hbeq
  have h := cpsBranchWithin_ntakenPath hbeqL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd (((sepConj_pure_right _).1 h_pure).2) hwne)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      exact sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hq) h

/-- Loop-entry spills (slots 53–54): store the tuple-walk cursor and end. -/
theorem bansf_loopEntry53_spec (aB newSp : Word) (cOff fEnd : Nat) :
    cpsTripleWithin 2 (B + 212) (B + 220) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 64) ** memOwn (newSp + 72))
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 fEnd))) := by
  have hsd1 := sd_spec_gen_own_within .x2 .x10 newSp (aB + BitVec.ofNat 64 cOff)
    (64 : BitVec 12) (B + 212)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (B + 212) + 4 = B + 216 from by bv_omega] at hsd1
  have hsd1L := liftCode (cr' := bansfCR) hsd1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 212) bansfProg 53 (.SD .x2 .x10 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd2 := sd_spec_gen_own_within .x2 .x11 newSp (aB + BitVec.ofNat 64 fEnd)
    (72 : BitVec 12) (B + 216)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide,
      show (B + 216) + 4 = B + 220 from by bv_omega] at hsd2
  have hsd2L := liftCode (cr' := bansfCR) hsd2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 216) bansfProg 54 (.SD .x2 .x11 (72 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd1F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd)) ** memOwn (newSp + 72))
    (by pcf) hsd1L
  have hsd2F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)))
    (by pcf) hsd2L
  have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hsd1F hsd2F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hchain

#print axioms bansf_balEmptyTaken_spec
#print axioms bansf_balEmptyFall_spec
#print axioms bansf_loopEntry53_spec

/-! ## §5  The tuple-window init (slot 68) -/

/-- Field-window `rlp_walk_init` (slot 68) + status
    check (slot 51): reject on any non-zero status; on success, land at
    `B + 280` with the unified content cursor.  The window is the span
    `[fOff, fOff + fSpanN)` with `fSpanW` its length as a word. -/
theorem bansf_fieldInit68_spec (aB : Word) (aLen fOff : Nat) (fSpanW : Word)
    (acctBytes : List (BitVec 8))
    (v5 v6 v7 v12 v28 v29 v30 v31 vRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hfB : fOff + fSpanW.toNat ≤ aLen) :
    cpsBranchWithin 84 (B + 272) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
       ((.x11 : Reg) ↦ᵣ fSpanW) **
       ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** F)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 280) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 272 + 4) F) := by
  have hoffb : fOff < acctBytes.length := by omega
  have hovOff : aB.toNat + fOff < 2 ^ 64 := by omega
  -- the callee triple at its entry with ra = B + 272 + 4
  have hwi := rlp_walk_init_spec_within WI aB (B + 272 + 4) fSpanW
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
    (P' := ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) ** ((.x11 : Reg) ↦ᵣ fSpanW) **
       ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  have hcall := bansf_callSite68_walk_init (n := 81) vRa (by pcf) hwi'
  rw [show (B + 272) + 4 = B + 276 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR F hF hcall
  set bb : BitVec 8 := acctBytes[fOff]'hoffb with hbb
  -- the window-end bridge: ptr + span = aB + ofNat (fOff + span.toNat)
  have hendB : (aB + BitVec.ofNat 64 fOff) + fSpanW
      = aB + BitVec.ofNat 64 (fOff + fSpanW.toNat) := by
    bv_omega
  -- ===== the success continuation (status pinned 0) =====
  have hsucc : cpsBranchWithin 2 (B + 276) bansfCR
      (fun h => ∃ cOff : Nat,
        ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜FieldInitOk acctBytes fOff fSpanW.toNat cOff⌝) h)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 280) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 272 + 4) F) := by
    refine cpsBranchWithin_exists_pre (fun cOff => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
    have hbne := bne_spec_gen_within .x12 .x0 (456 : BitVec 13) (0 : Word) (0 : Word) (B + 276)
    rw [show (B + 276) + 4 = B + 280 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 276) bansfProg 69 (.BNE .x12 .x0 (456 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
      hbne
    have hfall := cpsBranchWithin_ntakenPath hbneL
      (fun hp hQt => by
        obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
        exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
    have hfallF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hfall
    have hout : cpsTripleWithin 1 (B + 276) (B + 280) bansfCR
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
         ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
         bytesRegion aB acctBytes ** F)
        (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 272 + 4) F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hfallF
      unfold fieldInitPost
      refine ⟨cOff, ?_⟩
      have hq2 : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
          bytesRegion aB acctBytes ** F)) h := by
        have hq3 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
        xperm_hyp hq3
      exact (sepConj_pure_right h).2 ⟨hq2, hok⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right _ _ hout)
  -- ===== the failure continuation (status pinned non-zero) =====
  have hfailc : cpsBranchWithin 2 (B + 276) bansfCR
      (fun h => ∃ cur endW k : Word,
        ((((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
          ((.x12 : Reg) ↦ᵣ k) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜k ≠ (0 : Word)⌝) h)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 280) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 272 + 4) F) := by
    refine cpsBranchWithin_exists_pre (fun cur => ?_)
    refine cpsBranchWithin_exists_pre (fun endW => ?_)
    refine cpsBranchWithin_exists_pre (fun k => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hk => ?_)
    -- the BNE at slot 51: taken (status ≠ 0) to the reject stub
    have hbne := bne_spec_gen_within .x12 .x0 (456 : BitVec 13) k (0 : Word) (B + 276)
    rw [show (B + 276) + signExtend13 (456 : BitVec 13) = B + 732 from by
          rw [show signExtend13 (456 : BitVec 13) = (456 : Word) from by decide]
          bv_omega,
        show (B + 276) + 4 = B + 280 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 276) bansfProg 69 (.BNE .x12 .x0 (456 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
      hbne
    have hbneF := cpsBranchWithin_frameR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) ** bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hbneL
    have htaken := cpsBranchWithin_takenPath hbneF
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact hk (((sepConj_pure_right _).1 h_pure).2))
    have hrej := liftCode (cr' := bansfCR)
      (bansf_rejectTail_spec B cur (by decide))
      (fun a i h => CodeReq.union_mono_left a i h)
    have hrejF := cpsTripleWithin_frameR
      (((.x12 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ endW) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) ** bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hrej
    have hchain := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2)
      htaken hrejF
    have hout : cpsTripleWithin 2 (B + 276) (B + 736) bansfCR
        (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
         ((.x12 : Reg) ↦ᵣ k) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
         bytesRegion aB acctBytes ** F)
        (fieldRej aB acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      unfold fieldRej
      have hq4 : ((((.x11 : Reg) ↦ᵣ endW) ** ((.x12 : Reg) ↦ᵣ k) **
          ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
          (((.x10 : Reg) ↦ᵣ (1 : Word)) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aB acctBytes ** F))) h := by
        xperm_hyp hq
      have hq5 := sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x))) h hq4
      xperm_hyp hq5
    exact cpsTripleWithin_as_cpsBranchWithin_left _ _ hout
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
          ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) ** bytesRegion aB acctBytes) ** arm) ** F)) h :=
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
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
        rw [se1c]
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
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
        rw [← hlen1, se1c]
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
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


#print axioms bansf_fieldInit68_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
