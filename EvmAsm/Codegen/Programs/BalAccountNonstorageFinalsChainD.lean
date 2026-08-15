/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainD

  Balance-station glue (bead evm-asm-4ch8f.43.5, slice 4f):

    66  mv a0, s3              (loop exit → tuple span start)
    67  mv a1, s4              (tuple span length)
    70  sd a0, 64(sp)          (tuple-walk cursor spill)
    71  sd a1, 72(sp)          (tuple-walk end spill)

  plus the station-level reject shape shared by every failure path of the
  balance station (field init, find-last loop, tuple items, value capture).
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainC3

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- Slots 66–67 (`B + 264 → B + 272`): move the last tuple's span
    `(s3, s4)` into the `rlp_walk_init` argument registers. -/
theorem bansf_loopExitMove66_spec (v19 v20 v10 v11 : Word) :
    cpsTripleWithin 2 (B + 264) (B + 272) bansfCode
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11))
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x10 : Reg) ↦ᵣ v19) ** ((.x11 : Reg) ↦ᵣ v20)) := by
  have s1 := mv_spec_gen_within .x10 .x19 v19 v10 (B + 264) (by decide)
  have s2 := mv_spec_gen_within .x11 .x20 v20 v11 (B + 268) (by decide)
  runBlock s1 s2


/-- Slots 70–71 (`B + 280 → B + 288`): spill the tuple-walk cursor and
    window end for the item units. -/
theorem bansf_tupleSpill70_spec (newSp v10 v11 : Word) :
    cpsTripleWithin 2 (B + 280) (B + 288) bansfCR
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 64) ** memOwn (newSp + 72))
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ v10) ** ((newSp + 72) ↦ₘ v11)) := by
  have hsd1 := sd_spec_gen_own_within .x2 .x10 newSp v10 (64 : BitVec 12) (B + 280)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (B + 280) + 4 = B + 284 from by bv_omega] at hsd1
  have hsd1L := liftCode (cr' := bansfCR) hsd1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 280) bansfProg 70 (.SD .x2 .x10 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd2 := sd_spec_gen_own_within .x2 .x11 newSp v11 (72 : BitVec 12) (B + 284)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide,
      show (B + 284) + 4 = B + 288 from by bv_omega] at hsd2
  have hsd2L := liftCode (cr' := bansfCR) hsd2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 284) bansfProg 71 (.SD .x2 .x11 (72 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd1F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** memOwn (newSp + 72))
    (by pcf) hsd1L
  have hsd2F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ v10) ** ((newSp + 64) ↦ₘ v10))
    (by pcf) hsd2L
  have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hsd1F hsd2F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hchain


/-- The station-level reject shape at the epilogue entry (`B + 736`):
    every failure path of the balance station (field init, find-last loop,
    tuple items, value capture) weakens into this.  All station-scratch
    state is released to ownership; the callee-saved anchors survive. -/
def balStationRej (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
  ((.x18 : Reg) ↦ᵣ oB) **
  memOwn oB ** memOwnU256 (oB + 8) **
  regOwn .x19 ** regOwn .x20 **
  regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

/-- Swap the two exits of a branch (the find-last loop reports its clean
    exit FIRST; the station convention keeps the reject exit first). -/
theorem cpsBranchWithin_swap {n : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {e1 : Word} {Q1 : Assertion} {e2 : Word} {Q2 : Assertion}
    (h : cpsBranchWithin n entry cr P e1 Q1 e2 Q2) :
    cpsBranchWithin n entry cr P e2 Q2 e1 Q1 := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hcase⟩ := h R hR s hcr hPR hpc
  exact ⟨k, hk, s', hstep, hcase.symm⟩


theorem bansf_nonceTupleInit115_spec (aB : Word) (aLen fOff : Nat) (fSpanW : Word)
    (acctBytes : List (BitVec 8))
    (v5 v6 v7 v12 v28 v29 v30 v31 vRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hfB : fOff + fSpanW.toNat ≤ aLen) :
    cpsBranchWithin 84 (B + 460) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
       ((.x11 : Reg) ↦ᵣ fSpanW) **
       ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** F)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 468) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 460 + 4) F) := by
  have hoffb : fOff < acctBytes.length := by omega
  have hovOff : aB.toNat + fOff < 2 ^ 64 := by omega
  -- the callee triple at its entry with ra = B + 460 + 4
  have hwi := rlp_walk_init_spec_within WI aB (B + 460 + 4) fSpanW
    v12 v5 v6 v7 v28 v29 v30 v31 acctBytes fOff hsalign hoffb hovOff
    (hvalid fOff hoffb)
    (fun hf8 _ => by
      have hlo : ((acctBytes[fOff]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[fOff]'hoffb).isLt
        bv_omega
      omega)
    (fun hf8 _ => by
      have hlo : ((acctBytes[fOff]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[fOff]'hoffb).isLt
        bv_omega
      omega)
    (fun hf8 _ => by
      intro k hk
      have hlo : ((acctBytes[fOff]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[fOff]'hoffb).isLt
        bv_omega
      exact hvalid _ (by omega))
  have hwi' := cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwi
    (P' := ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) ** ((.x11 : Reg) ↦ᵣ fSpanW) **
       ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  have hcall := bansf_callSite115_walk_init (n := 81) vRa (by pcf) hwi'
  rw [show (B + 460) + 4 = B + 464 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR F hF hcall
  set bb : BitVec 8 := acctBytes[fOff]'hoffb with hbb
  -- the window-end bridge: ptr + span = aB + ofNat (fOff + span.toNat)
  have hendB : (aB + BitVec.ofNat 64 fOff) + fSpanW
      = aB + BitVec.ofNat 64 (fOff + fSpanW.toNat) := by
    bv_omega
  -- ===== the success continuation (status pinned 0) =====
  have hsucc : cpsBranchWithin 2 (B + 464) bansfCR
      (fun h => ∃ cOff : Nat,
        ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜FieldInitOk acctBytes fOff fSpanW.toNat cOff⌝) h)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 468) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 460 + 4) F) := by
    refine cpsBranchWithin_exists_pre (fun cOff => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
    have hbne := bne_spec_gen_within .x12 .x0 (268 : BitVec 13) (0 : Word) (0 : Word) (B + 464)
    rw [show (B + 464) + 4 = B + 468 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 464) bansfProg 116 (.BNE .x12 .x0 (268 : BitVec 13))
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
       ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hfall
    have hout : cpsTripleWithin 1 (B + 464) (B + 468) bansfCR
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
         ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
         bytesRegion aB acctBytes ** F)
        (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 460 + 4) F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hfallF
      unfold fieldInitPost
      refine ⟨cOff, ?_⟩
      have hq2 : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
          bytesRegion aB acctBytes ** F)) h := by
        have hq3 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
        xperm_hyp hq3
      exact (sepConj_pure_right h).2 ⟨hq2, hok⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right _ _ hout)
  -- ===== the failure continuation (status pinned non-zero) =====
  have hfailc : cpsBranchWithin 2 (B + 464) bansfCR
      (fun h => ∃ cur endW k : Word,
        ((((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
          ((.x12 : Reg) ↦ᵣ k) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜k ≠ (0 : Word)⌝) h)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 468) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 460 + 4) F) := by
    refine cpsBranchWithin_exists_pre (fun cur => ?_)
    refine cpsBranchWithin_exists_pre (fun endW => ?_)
    refine cpsBranchWithin_exists_pre (fun k => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hk => ?_)
    -- the BNE at slot 51: taken (status ≠ 0) to the reject stub
    have hbne := bne_spec_gen_within .x12 .x0 (268 : BitVec 13) k (0 : Word) (B + 464)
    rw [show (B + 464) + signExtend13 (268 : BitVec 13) = B + 732 from by
          rw [show signExtend13 (268 : BitVec 13) = (268 : Word) from by decide]
          bv_omega,
        show (B + 464) + 4 = B + 468 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 464) bansfProg 116 (.BNE .x12 .x0 (268 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
      hbne
    have hbneF := cpsBranchWithin_frameR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) ** bytesRegion aB acctBytes ** F)
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
       ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) ** bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hrej
    have hchain := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2)
      htaken hrejF
    have hout : cpsTripleWithin 2 (B + 464) (B + 736) bansfCR
        (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
         ((.x12 : Reg) ↦ᵣ k) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
         bytesRegion aB acctBytes ** F)
        (fieldRej aB acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      unfold fieldRej
      have hq4 : ((((.x11 : Reg) ↦ᵣ endW) ** ((.x12 : Reg) ↦ᵣ k) **
          ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
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
          ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) ** bytesRegion aB acctBytes) ** arm) ** F)) h :=
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
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
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
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




/-!
## Balance-station assembly plan (slice 4g, `bansf_balStation_spec`)

Goal shape:
```
theorem bansf_balStation_spec (aB newSp oB : Word) (aLen off3 : Nat)
    (n3 l3 v19 v20 : Word) (acctBytes) (F) (hF hsalign hoalign hslack hover
    hvalid hovout hovalid) (hoff3 : off3 ≤ aLen)
    (hdec3 : rlpItemDecode acctBytes off3 (aB+ofNat off3) (aB+ofNat aLen) n3 l3) :
  cpsBranchWithin (98 * (aLen + 1) + 700) (B + 184) bansfCR
    (x10↦n3 ** x11↦0 ** x12↦l3 ** x19↦v19 ** x20↦v20 **
     (newSp+48)↦ₘn3 ** (newSp+56)↦ₘ(aB+ofNat aLen) ** memOwn (newSp+64/72) **
     x2↦newSp ** x8↦aB ** x9↦ofNat aLen ** x18↦oB **
     oB↦ₘ0 ** (oB+8/16/24/32)↦ₘ0 ** x0↦0 ** bytesRegion aB acctBytes ** F **
     regOwn x5 x6 x7 x28 x29 x30 x31 x1)          -- owns LAST for regOwn8 intro
    (B+736) (balStationRej aB newSp oB aLen acctBytes F)
    (B+352) (balStationPost aB newSp oB aLen ((n3-l3-aB).toNat) l3.toNat n3 acctBytes F)
```
Proof skeleton:
1. `cpsBranchWithin_of_forall_regIs_to_regOwn8` (after a weaken-perm) intros
   v5 v6 v7 v28 v29 v30 v31 vRa.
2. `rlpItemDecode_spanStart hdec3 hoff3` ⇒ hrepS (n3−l3 = aB+ofNat fOff),
   hsple, hspb (fOff + l3.toNat ≤ aLen — discharges fieldInit50's hfB).
3. spanCapture46 (liftCode bansfCode→bansfCR via union_mono_left, frameR rest,
   rw [hrepS]) ; seq_branch with fieldInit50 (fOff := (n3−l3−aB).toNat,
   fSpanW := l3, vRa-old := vRa).  Reject arm: fieldRej ** frame ⇒
   balStationRej (memIs→memOwn on 48/56/64/72 + oB cells → memOwn oB +
   hmemU-style memOwnU256 (oB+8), regIs→regOwn x19 x20 x11? note fieldRej
   owns x11/x12 already).
4. At B+208: continuation branch with pre `fun h => ∃ cOff, ((fieldInitPost
   atoms ** frame) ** ⌜FieldInitOk acctBytes fOff l3.toNat cOff⌝) h` connected
   by a pointwise rebuild lambda (ChainC2-collapse style).  exists_pre +
   pure_pre_right, then `by_cases hce : cOff = fOff + l3.toNat`:
   - EMPTY: balEmptyTaken (lift, frame all) ⇒ B+352; weaken to balStationPost
     EMPTY arm (FieldFinal.empty b hb (hok.2.1 ▸ hce); regIs→regOwn
     x10 x11 x12 x19 x20).  `cpsTripleWithin_as_cpsBranchWithin_right`.
   - NONEMPTY: balEmptyFall (hne := hce, hcle/hfle by omega from FieldInitOk
     + hspb) ; loopEntry53 ; findLastLoop1 (off0 := cOff, endOff := fOff +
     l3.toNat, j := endOff − cOff; hoff0 : cOff < endOff from hok ≤ + hce;
     flInv entry: ⟨cOff, v19', v20', …, Or.inl rfl⟩; v19'/v20' are the
     spanCapture-written x19=n3−l3, x20=l3).  Loop exits are (B+264 flExit |
     B+736 flRej) — FIRST exit continues ⇒ need the swap variant (write
     `cpsBranchWithin_swap` inline: intro/rcases/Or-swap) before chain_snd.
     flRej ⇒ balStationRej (oB cells from frame).
5. At B+264 (flExit): exists_pre n l + pure (LastItemAt).  loopExitMove66
   (lift, frame) ; `LastItemAt_decode hlast (by omega) (by omega)` ⇒
   ∃ offT ≤ endOff, decode of the last tuple; `rlpItemDecode_spanStart` on it
   ⇒ hrepT (n−l = aB+ofNat tOff), tOff + l.toNat ≤ endOff ≤ aLen (fieldInit68
   hfB ✓).  rw [hrepT]; fieldInit68 (fOff := (n−l−aB).toNat, fSpanW := l).
6. At B+280: same ∃cOff2/FieldInitOk unpack; tupleSpill70 ; tupleItem0
   (aLen-param := tOff2 + l.toNat, off := cOff2, hoffle from FieldInitOk;
   hslack' : tOff2 + l.toNat + 9 ≤ length by omega).  tupleRej ⇒
   balStationRej.
7. At B+308 (tupleOk): ∃ next len + idx-decode pure; `rlpItemDecode_advance`
   ⇒ next = aB+ofNat nOff, cOff2 < nOff ≤ tEnd2.  rw; tupleItem1 (off := nOff).
8. At B+324 (tupleValOk): ∃ vNext vLen + val-decode; balCapture (tEnd :=
   tEnd2, off := nOff, hdec := val-decode; hovout/hovalid/hoalign from
   station hyps).  balCaptureRej ⇒ balStationRej.
9. At B+352 (balCaptureOk): weaken to balStationPost FOUND arm:
   FieldFinal.last b n l vNext vLen with hb (field FieldInitOk), hne (hok ▸
   hce), hlast (flExit pure, off0 rewritten to fOff + listHeaderSize b),
   hval : TupleValueWindow = ⟨b2, hb2, next, len, idx-decode (cOff2 → tOff2 +
   listHeaderSize b2), val-decode with cursor rewritten aB+ofNat nOff → next⟩;
   vLen.toNat ≤ 32 from balCaptureOk's pure; regIs→regOwn x19 x20 (+ x10 etc.
   already own in balCaptureOk); spills 48/56 & memOwn 64/72 from frame.
Step budget per path: empty 4+84+1 = 89; found 4+84+1+2+98*(j+1)+2+84+2+93+
92+260 ≤ 98*(aLen+1)+624.  `cpsBranchWithin_mono_nSteps (by omega)` at the end.
-/

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
