/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainC3

  The balance-value capture block of `bal_account_nonstorage_finals`
  (bead evm-asm-4ch8f.43.5, slice 4e): slots 81–87 —

    81  sub a0, a0, a2         (value content pointer = next - len)
    82  mv  a1, a2             (value content length)
    83  addi a2, s2, 8         (the out block's post_balance slot)
    84  jal rlp_content_to_u256_be
    85  bnez a0 → reject       (too-long / non-canonical value)
    86  li  t0, 1
    87  sd  t0, 0(s2)          (has_balance := 1)

  The callee is dispatched from its four PUBLIC per-case sub-specs with the
  case split done at the LEMMA level (the length and lead byte are
  quantified parameters here), so the success exit carries the
  `vLen.toNat ≤ 32` bound the `FinalsDerivation` balance image requires —
  the packaged four-way dispatch post cannot supply it.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainC
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainC2

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- The capture-success state at the nonce boundary (`B + 352`):
    `has_balance = 1` and the 32-byte right-aligned big-endian image of the
    value content in the `post_balance` slot. -/
def balCaptureOk (aB newSp oB : Word) (srcOff lenN : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((oB ↦ₘ (1 : Word)) **
   bytesRegion (oB + 8) (copyN (List.replicate 32 (0 : BitVec 8)) acctBytes
     (32 - lenN) srcOff lenN) **
   ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
   regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
   regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
   regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
   ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
   bytesRegion aB acctBytes ** F) **
  ⌜lenN ≤ 32⌝

/-- The capture reject: `has_balance` still 0, the balance area released. -/
def balCaptureRej (aB newSp oB : Word) (acctBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) **
  (oB ↦ₘ (0 : Word)) ** memOwnU256 (oB + 8) **
  ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
  regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

/-- Slots 81–87: capture the balance value into the out block.  The value
    window `(vNext, vLen)` decodes at `off` inside the tuple window
    `[·, tEnd]`; the length/canonicality cases are split here so each
    per-case sub-spec applies with its exact hypotheses. -/
theorem bansf_balCapture_spec (aB newSp oB : Word) (aLen tEnd off : Nat)
    (vNext vLen : Word) (acctBytes : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 vRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hoalign : oB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hovout : oB.toNat + 80 ≤ 2 ^ 64)
    (hovalid : ∀ k, k < 80 → isValidByteAccess (oB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffle : off ≤ tEnd)
    (hdec : rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
      (aB + BitVec.ofNat 64 tEnd) vNext vLen) :
    cpsBranchWithin 260 (B + 324) bansfCR
      (((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ vLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
       (oB ↦ₘ (0 : Word)) **
       ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
       ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** F)
      (B + 736) (balCaptureRej aB newSp oB acctBytes F)
      (B + 352) (balCaptureOk aB newSp oB ((vNext - vLen - aB).toNat) vLen.toNat
        acctBytes F) := by
  have hover9 : aB.toNat + aLen + 9 < 2 ^ 64 := by omega
  obtain ⟨hrepS, hsple, hspb⟩ := rlpItemDecode_spanStart hdec hoffle (by omega)
  have hsoffb : (vNext - vLen - aB).toNat < acctBytes.length := by omega
  have hlenrep : vLen = BitVec.ofNat 64 (vLen.toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hoalign8 : (oB + 8).toNat % 8 = 0 := by bv_omega
  have hoover8 : (oB + 8).toNat + 32 ≤ 2 ^ 64 := by bv_omega
  have hdval : ∀ k, k < 32 →
      isValidByteAccess ((oB + 8) + BitVec.ofNat 64 k) = true := by
    intro k hk
    have h := hovalid (8 + k) (by omega)
    rwa [show oB + BitVec.ofNat 64 (8 + k) = (oB + 8) + BitVec.ofNat 64 k from by
      bv_omega] at h
  -- ===== the three argument-setup instructions (81–83) =====
  have h81 := sub_spec_gen_rd_eq_rs1_within .x10 .x12 vNext vLen (B + 324) (by decide)
  rw [hrepS, show (B + 324) + 4 = B + 328 from by bv_omega] at h81
  have h81L := liftCode (cr' := bansfCR) h81
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 324) bansfProg 81 (.SUB .x10 .x10 .x12)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have h82 := mv_spec_gen_within .x11 .x12 vLen (0 : Word) (B + 328) (by decide)
  rw [show (B + 328) + 4 = B + 332 from by bv_omega] at h82
  have h82L := liftCode (cr' := bansfCR) h82
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 328) bansfProg 82 (.MV .x11 .x12)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have h83 := addi_spec_gen_within .x12 .x18 vLen oB (8 : BitVec 12) (B + 332) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show (B + 332) + 4 = B + 336 from by bv_omega] at h83
  have h83L := liftCode (cr' := bansfCR) h83
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 332) bansfProg 83 (.ADDI .x12 .x18 (8 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have h81F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (0 : Word)) **
     ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
     (oB ↦ₘ (0 : Word)) **
     ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
     ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) h81L
  have h82F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat))) **
     ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
     (oB ↦ₘ (0 : Word)) **
     ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
     ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) h82L
  have h83F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat))) **
     ((.x11 : Reg) ↦ᵣ vLen) **
     ((.x2 : Reg) ↦ᵣ newSp) **
     (oB ↦ₘ (0 : Word)) **
     ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
     ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) h83L
  have hsetup0 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h81F h82F
  have hsetup := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hsetup0 h83F
  -- ===== the shared success tail: BNE fall, LI, SD (85–87) =====
  have htail : ∀ (img : List (BitVec 8)),
      cpsTripleWithin 3 (B + 340) (B + 352) bansfCR
        (((.x10 : Reg) ↦ᵣ (0 : Word)) **
         (oB ↦ₘ (0 : Word)) ** bytesRegion (oB + 8) img **
         ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x5 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (((.x10 : Reg) ↦ᵣ (0 : Word)) **
         (oB ↦ₘ (1 : Word)) ** bytesRegion (oB + 8) img **
         ((.x18 : Reg) ↦ᵣ oB) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
         ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
    intro img
    -- BNE not taken (status 0)
    have hbne := bne_spec_gen_within .x10 .x0 (392 : BitVec 13) (0 : Word) (0 : Word) (B + 340)
    rw [show (B + 340) + 4 = B + 344 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 340) bansfProg 85 (.BNE .x10 .x0 (392 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
      hbne
    have hfall := cpsBranchWithin_ntakenPath hbneL
      (fun hp hQt => by
        obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
        exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
    -- LI t0, 1 at B+344 (from an owned x5)
    have hli : cpsTripleWithin 1 (B + 344) (B + 348) bansfCR
        (regOwn .x5) ((.x5 : Reg) ↦ᵣ (1 : Word)) := by
      refine cpsTripleWithin_of_forall_regIs_to_regOwn_single (fun vOld => ?_)
      have h := li_spec_gen_within .x5 vOld (1 : Word) (B + 344) (by decide)
      rw [show (B + 344) + 4 = B + 348 from by bv_omega] at h
      exact liftCode (cr' := bansfCR) h
        (fun a i hh => CodeReq.union_mono_left a i
          (CodeReq.ofProg_mem_at B (B + 344) bansfProg 86 (.LI .x5 (1 : Word))
            (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i hh))
    -- SD t0, 0(s2) at B+348
    have hsd := sd_spec_gen_within .x18 .x5 oB (1 : Word) (0 : Word) (0 : BitVec 12) (B + 348)
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show oB + (0 : Word) = oB from by bv_omega,
        show (B + 348) + 4 = B + 352 from by bv_omega] at hsd
    have hsdL := liftCode (cr' := bansfCR) hsd
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 348) bansfProg 87 (.SD .x18 .x5 (0 : BitVec 12))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    have hfallF := cpsTripleWithin_frameR
      ((oB ↦ₘ (0 : Word)) ** bytesRegion (oB + 8) img **
       ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x5)
      (by pcf) hfall
    have hliF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (oB ↦ₘ (0 : Word)) ** bytesRegion (oB + 8) img **
       ((.x18 : Reg) ↦ᵣ oB))
      (by pcf) hli
    have hsdF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion (oB + 8) img)
      (by pcf) hsdL
    have c1 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2)
      hfallF hliF
    have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hsdF
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq) c2
  -- ===== reject-route helper at the status check (B + 340) =====
  have hrejRoute : ∀ (st : Word), st ≠ (0 : Word) →
      cpsTripleWithin 2 (B + 340) (B + 736) bansfCR
        (((.x10 : Reg) ↦ᵣ st) ** ((.x11 : Reg) ↦ᵣ vLen) **
         ((.x12 : Reg) ↦ᵣ (oB + 8)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
         bytesRegion aB acctBytes ** memOwnU256 (oB + 8) **
         ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
         (oB ↦ₘ (0 : Word)) ** F)
        (balCaptureRej aB newSp oB acctBytes F) := by
    intro st hst
    have hbne := bne_spec_gen_within .x10 .x0 (392 : BitVec 13) st (0 : Word) (B + 340)
    rw [show (B + 340) + signExtend13 (392 : BitVec 13) = B + 732 from by
          rw [show signExtend13 (392 : BitVec 13) = (392 : Word) from by decide]
          bv_omega,
        show (B + 340) + 4 = B + 344 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 340) bansfProg 85 (.BNE .x10 .x0 (392 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
      hbne
    have hbneF := cpsBranchWithin_frameR
      (((.x11 : Reg) ↦ᵣ vLen) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
       bytesRegion aB acctBytes ** memOwnU256 (oB + 8) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
       (oB ↦ₘ (0 : Word)) ** F)
      (by pcf; exact hF) hbneL
    have htaken := cpsBranchWithin_takenPath hbneF
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact hst (((sepConj_pure_right _).1 h_pure).2))
    have hrej := liftCode (cr' := bansfCR)
      (bansf_rejectTail_spec B st (by decide))
      (fun a i h => CodeReq.union_mono_left a i h)
    have hrejF := cpsTripleWithin_frameR
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ vLen) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
       bytesRegion aB acctBytes ** memOwnU256 (oB + 8) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
       (oB ↦ₘ (0 : Word)) ** F)
      (by pcf; exact hF) hrej
    have hchain := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2)
      htaken hrejF
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
    unfold balCaptureRej
    have hq4 : ((((.x11 : Reg) ↦ᵣ vLen) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
        ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
        (((.x10 : Reg) ↦ᵣ (1 : Word)) **
         (oB ↦ₘ (0 : Word)) ** memOwnU256 (oB + 8) **
         ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion aB acctBytes ** F))) h := by
      xperm_hyp hq
    have hq5 := sepConj_mono (regIs_implies_regOwn .x11)
      (sepConj_mono (regIs_implies_regOwn .x12)
        (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x))) h hq4
    xperm_hyp hq5
  -- the four out cells assemble into the callee's owned output token
  have hmemU : ∀ h, ((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
      ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) h) →
      memOwnU256 (oB + 8) h := by
    intro h hp
    rw [show oB + 16 = (oB + 8) + 8 from by bv_omega,
        show oB + 24 = (oB + 8) + 16 from by bv_omega,
        show oB + 32 = (oB + 8) + 24 from by bv_omega] at hp
    exact sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)) h hp
  -- ===== the four value cases =====
  by_cases hlen32 : 32 < vLen.toNat
  · -- too-long value: callee returns status 2 → reject
    have hcs := rlp_content_to_u256_be_too_long_spec_within CB
      (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat)) vLen (oB + 8) v5 (B + 336 + 4)
      (by
        simp only [BitVec.ult, decide_eq_true_eq]
        have h32 : (32 : Word).toNat = 32 := by decide
        omega)
    have hcs' := cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hcs
      (P' := ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat))) **
         ((.x11 : Reg) ↦ᵣ vLen) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
         ((.x5 : Reg) ↦ᵣ v5) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         memOwnU256 (oB + 8)))
    have hcall := bansf_callSite84_content_to_u256_be (n := 8) vRa (by pcf) hcs'
    have hcallF := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       bytesRegion aB acctBytes **
       ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
       (oB ↦ₘ (0 : Word)) ** F)
      (by pcf; exact hF) hcall
    have hfull1 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 : (((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
            ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) **
           (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat))) **
            ((.x11 : Reg) ↦ᵣ vLen) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
            ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
            ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
            ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
            ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
            (oB ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F))) h := by
          xperm_hyp hp
        have hp3 := sepConj_mono hmemU (fun _ x => x) h hp2
        xperm_hyp hp3)
      hsetup hcallF
    have hroute := hrejRoute (2 : Word) (by decide)
    rw [show B + 340 = B + 336 + 4 from by bv_omega] at hroute
    have hfull2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 : ((((.x5 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ v6) **
            ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
            ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31)) **
           (((.x10 : Reg) ↦ᵣ (2 : Word)) ** ((.x11 : Reg) ↦ᵣ vLen) **
            ((.x12 : Reg) ↦ᵣ (oB + 8)) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
            bytesRegion aB acctBytes ** memOwnU256 (oB + 8) **
            ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
            (oB ↦ₘ (0 : Word)) ** F)) h := by
          xperm_hyp hp
        have hp3 := sepConj_mono
          (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x6)
              (sepConj_mono (regIs_implies_regOwn .x7)
                (sepConj_mono (regIs_implies_regOwn .x28)
                  (sepConj_mono (regIs_implies_regOwn .x29)
                    (sepConj_mono (regIs_implies_regOwn .x30)
                      (regIs_implies_regOwn .x31)))))))
          (fun _ x => x) h hp2
        xperm_hyp hp3)
      hfull1 hroute
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x) (fun _ x => x)
      (cpsBranchWithin_mono_nSteps (by omega)
        (cpsTripleWithin_as_cpsBranchWithin_left (B + 352)
          (balCaptureOk aB newSp oB ((vNext - vLen - aB).toNat) vLen.toNat acctBytes F)
          hfull2))
  by_cases hlen0 : vLen.toNat = 0
  · -- empty value: zero image, success
    have hvz : vLen = (0 : Word) := by bv_omega
    have hcs := rlp_content_to_u256_be_empty_spec_within CB aB (oB + 8)
      (B + 336 + 4) v5 v6 v7 v28 v29 ((vNext - vLen - aB).toNat)
    have hcs' := cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hcs
      (P' := ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat))) **
         ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
         ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** memOwnU256 (oB + 8)))
    have hcall := bansf_callSite84_content_to_u256_be (n := 9) vRa (by pcf) hcs'
    have hcallF := cpsTripleWithin_frameR
      (((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       bytesRegion aB acctBytes **
       ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
       (oB ↦ₘ (0 : Word)) ** F)
      (by pcf; exact hF) hcall
    have hfull1 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 : (((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
            ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) **
           (((.x11 : Reg) ↦ᵣ vLen) **
            (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat))) **
             ((.x12 : Reg) ↦ᵣ (oB + 8)) **
             ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
             ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
             ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
             ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
             ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
             (oB ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F)))) h := by
          xperm_hyp hp
        have hp3 := sepConj_mono hmemU
          (sepConj_mono (fun h' hx => hvz ▸ hx) (fun _ x => x)) h hp2
        xperm_hyp hp3)
      hsetup hcallF
    have ht := htail (List.replicate 32 (0 : BitVec 8))
    rw [show B + 340 = B + 336 + 4 from by bv_omega] at ht
    have htF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) ht
    have hfull2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) hfull1 htF
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x)
      (fun h hq => ?_)
      (cpsBranchWithin_mono_nSteps (by omega)
        (cpsTripleWithin_as_cpsBranchWithin_right (B + 736)
          (balCaptureRej aB newSp oB acctBytes F) hfull2))
    unfold balCaptureOk
    rw [hlen0, copyN_zero]
    have hq4 : ((((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ (oB + 8)) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
        ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
        ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
        ((oB ↦ₘ (1 : Word)) **
         bytesRegion (oB + 8) (List.replicate 32 (0 : BitVec 8)) **
         ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion aB acctBytes ** F))) h := by
      xperm_hyp hq
    have hq5 := sepConj_mono (regIs_implies_regOwn .x10)
      (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x30)
              (sepConj_mono (regIs_implies_regOwn .x31)
                (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x))))))) h hq4
    refine (sepConj_pure_right h).2 ⟨?_, by omega⟩
    xperm_hyp hq5
  by_cases hcz : acctBytes[(vNext - vLen - aB).toNat]'hsoffb = (0 : BitVec 8)
  · -- non-canonical value (leading zero byte): status 3 → reject
    have hcs := rlp_content_to_u256_be_noncanonical_spec_within CB aB (oB + 8)
      (B + 336 + 4) v5 v6 acctBytes ((vNext - vLen - aB).toNat) vLen.toNat
      (by omega) (by omega) hsalign hsoffb (by omega) (hvalid _ hsoffb) hcz
    rw [← hlenrep] at hcs
    have hcs' := cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hcs
      (P' := ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat))) **
         ((.x11 : Reg) ↦ᵣ vLen) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
         ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion aB acctBytes ** memOwnU256 (oB + 8)))
    have hcall := bansf_callSite84_content_to_u256_be (n := 11) vRa (by pcf) hcs'
    have hcallF := cpsTripleWithin_frameR
      (((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
       (oB ↦ₘ (0 : Word)) ** F)
      (by pcf; exact hF) hcall
    have hfull1 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 : (((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
            ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) **
           (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat))) **
            ((.x11 : Reg) ↦ᵣ vLen) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
            ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
            ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
            ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
            ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
            (oB ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F))) h := by
          xperm_hyp hp
        have hp3 := sepConj_mono hmemU (fun _ x => x) h hp2
        xperm_hyp hp3)
      hsetup hcallF
    have hroute := hrejRoute (3 : Word) (by decide)
    rw [show B + 340 = B + 336 + 4 from by bv_omega] at hroute
    have hfull2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 : ((((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
            ((.x29 : Reg) ↦ᵣ v29) **
            ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31)) **
           (((.x10 : Reg) ↦ᵣ (3 : Word)) ** ((.x11 : Reg) ↦ᵣ vLen) **
            ((.x12 : Reg) ↦ᵣ (oB + 8)) **
            regOwn .x5 ** regOwn .x6 **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
            bytesRegion aB acctBytes ** memOwnU256 (oB + 8) **
            ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
            (oB ↦ₘ (0 : Word)) ** F)) h := by
          xperm_hyp hp
        have hp3 := sepConj_mono
          (sepConj_mono (regIs_implies_regOwn .x7)
            (sepConj_mono (regIs_implies_regOwn .x28)
              (sepConj_mono (regIs_implies_regOwn .x29)
                (sepConj_mono (regIs_implies_regOwn .x30)
                  (regIs_implies_regOwn .x31)))))
          (fun _ x => x) h hp2
        xperm_hyp hp3)
      hfull1 hroute
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x) (fun _ x => x)
      (cpsBranchWithin_mono_nSteps (by omega)
        (cpsTripleWithin_as_cpsBranchWithin_left (B + 352)
          (balCaptureOk aB newSp oB ((vNext - vLen - aB).toNat) vLen.toNat acctBytes F)
          hfull2))
  · -- canonical non-empty value: right-aligned copy, success
    have hcs := rlp_content_to_u256_be_success_spec_within CB aB (oB + 8)
      (B + 336 + 4) v5 v6 v7 v28 v29 acctBytes ((vNext - vLen - aB).toNat) vLen.toNat
      (by omega) (by omega) hsalign hoalign8 hsoffb hcz
      (by omega) (by omega) hoover8
      (fun k hk => hvalid _ (by omega))
      (fun k hk => hdval _ (by omega))
    rw [← hlenrep] at hcs
    have hcs' := cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hcs
      (P' := ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat))) **
         ((.x11 : Reg) ↦ᵣ vLen) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
         ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion aB acctBytes ** memOwnU256 (oB + 8)))
    have hcall := bansf_callSite84_content_to_u256_be
      (n := 7 * vLen.toNat + 16) vRa (by pcf) hcs'
    have hcallF := cpsTripleWithin_frameR
      (((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
       (oB ↦ₘ (0 : Word)) ** F)
      (by pcf; exact hF) hcall
    have hfull1 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 : (((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
            ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) **
           (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((vNext - vLen - aB).toNat))) **
            ((.x11 : Reg) ↦ᵣ vLen) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
            ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
            ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
            ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
            ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
            (oB ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F))) h := by
          xperm_hyp hp
        have hp3 := sepConj_mono hmemU (fun _ x => x) h hp2
        xperm_hyp hp3)
      hsetup hcallF
    have ht := htail (copyN (List.replicate 32 (0 : BitVec 8)) acctBytes
      (32 - vLen.toNat) ((vNext - vLen - aB).toNat) vLen.toNat)
    rw [show B + 340 = B + 336 + 4 from by bv_omega] at ht
    have htF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ vLen) ** ((.x12 : Reg) ↦ᵣ (oB + 8)) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) ht
    have hfull2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) hfull1 htF
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ x => x)
      (fun h hq => ?_)
      (cpsBranchWithin_mono_nSteps (by omega)
        (cpsTripleWithin_as_cpsBranchWithin_right (B + 736)
          (balCaptureRej aB newSp oB acctBytes F) hfull2))
    unfold balCaptureOk
    have hq4 : ((((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ vLen) **
        ((.x12 : Reg) ↦ᵣ (oB + 8)) ** ((.x5 : Reg) ↦ᵣ (1 : Word)) **
        ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
        ((.x1 : Reg) ↦ᵣ (B + 336 + 4)) **
        ((oB ↦ₘ (1 : Word)) **
         bytesRegion (oB + 8) (copyN (List.replicate 32 (0 : BitVec 8)) acctBytes
           (32 - vLen.toNat) ((vNext - vLen - aB).toNat) vLen.toNat) **
         ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion aB acctBytes ** F))) h := by
      xperm_hyp hq
    have hq5 := sepConj_mono (regIs_implies_regOwn .x10)
      (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x30)
              (sepConj_mono (regIs_implies_regOwn .x31)
                (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x))))))) h hq4
    refine (sepConj_pure_right h).2 ⟨?_, by omega⟩
    xperm_hyp hq5

theorem bansf_nonceTupleItem0_spec (aB newSp : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8))
    (v5 v6 v7 v10 v11 v12 v28 v29 v30 v31 vRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoffle : off ≤ aLen) :
    cpsBranchWithin 93 (B + 476) bansfCR
      (((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** F)
      (B + 736) (tupleRej aB newSp acctBytes F)
      (B + 496) (tupleOk aB newSp aLen off acctBytes F) := by
  have hoffb : off < acctBytes.length := by omega
  -- LD a0, 48(sp) ; LD a1, 56(sp)  (B+104, B+108)
  have hld1 := ld_spec_gen_within .x10 .x2 newSp v10 (aB + BitVec.ofNat 64 off)
    (64 : BitVec 12) (B + 476) (by decide)
  rw [(show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide), show (B + 476) + 4 = B + 480 from by bv_omega] at hld1
  have hld1L := liftCode (cr' := bansfCR) hld1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 476) bansfProg 119 (.LD .x10 .x2 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hld2 := ld_spec_gen_within .x11 .x2 newSp v11 (aB + BitVec.ofNat 64 aLen)
    (72 : BitVec 12) (B + 480) (by decide)
  rw [(show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide), show (B + 480) + 4 = B + 484 from by bv_omega] at hld2
  have hld2L := liftCode (cr' := bansfCR) hld2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 480) bansfProg 120 (.LD .x11 .x2 (72 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hld1F := cpsTripleWithin_frameR
    (((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) ** ((.x11 : Reg) ↦ᵣ v11))
    (by pcf) hld1L
  have hld2F := cpsTripleWithin_frameR
    (((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)))
    (by pcf) hld2L
  have hlds := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hld1F hld2F
  have hldsF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ v12) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hlds
  -- the callee triple with ra = B + 484 + 4
  have hwn := rlp_walk_next_spec_within WN aB (aB + BitVec.ofNat 64 aLen)
    (B + 484 + 4) v12 v5 v6 v7 v28 v29 v30 v31 acctBytes off hsalign hoffb (by omega)
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
    (P' := ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  have hcall := bansf_callSite121_walk_next (n := 87) vRa (by pcf) hwn'
  rw [show (B + 484) + 4 = B + 488 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) ** F)
    (by pcf; exact hF) hcall
  have hpre := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hldsF hcallF
  -- ===== ok continuation: BNE falls through, SD spills the cursor =====
  have hokc : cpsBranchWithin 2 (B + 488) bansfCR
      (fun h => ∃ next len : Word,
        ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
           (aB + BitVec.ofNat 64 aLen) next len⌝) h)
      (B + 736) (tupleRej aB newSp acctBytes F)
      (B + 496) (tupleOk aB newSp aLen off acctBytes F) := by
    refine cpsBranchWithin_exists_pre (fun next => ?_)
    refine cpsBranchWithin_exists_pre (fun len => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hdec => ?_)
    have hbne := bne_spec_gen_within .x11 .x0 (244 : BitVec 13) (0 : Word) (0 : Word) (B + 488)
    rw [show (B + 488) + 4 = B + 492 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 488) bansfProg 122 (.BNE .x11 .x0 (244 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
      hbne
    have hfall := cpsBranchWithin_ntakenPath hbneL
      (fun hp hQt => by
        obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
        exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
    -- SD a0, 48(sp) at B+120
    have hsd := sd_spec_gen_within .x2 .x10 newSp next (aB + BitVec.ofNat 64 off)
      (64 : BitVec 12) (B + 492)
    rw [(show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide), show (B + 492) + 4 = B + 496 from by bv_omega] at hsd
    have hsdL := liftCode (cr' := bansfCR) hsd
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 492) bansfProg 123 (.SD .x2 .x10 (64 : BitVec 12))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
    have hfallF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ next) ** ((.x12 : Reg) ↦ᵣ len) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hfall
    have hsdF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ len) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hsdL
    have hout : cpsTripleWithin 2 (B + 488) (B + 496) bansfCR
        (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
         ((.x12 : Reg) ↦ᵣ len) **
         ((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
         bytesRegion aB acctBytes ** F)
        (tupleOk aB newSp aLen off acctBytes F) := by
      have hchain := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          have hp2 := sepConj_mono_left (sepConj_mono_right
            (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
          xperm_hyp hp2)
        hfallF hsdF
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      unfold tupleOk
      refine ⟨next, len, ?_⟩
      have hq2 : ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ next) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
          bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hq
      have hq3 : ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ next) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F)) h := by
        have hq4 : ((((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
            (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
             ((.x12 : Reg) ↦ᵣ len) **
             ((.x2 : Reg) ↦ᵣ newSp) **
             ((newSp + 64) ↦ₘ next) **
             ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
             regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
             regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
             ((.x0 : Reg) ↦ᵣ (0 : Word)) **
             bytesRegion aB acctBytes ** F))) h := by
          xperm_hyp hq2
        have hq5 := sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x) h hq4
        xperm_hyp hq5
      exact (sepConj_pure_right h).2 ⟨hq3, hdec⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right _ _ hout)
  -- ===== fail continuation =====
  have hfailc : cpsBranchWithin 2 (B + 488) bansfCR
      (fun h => ∃ cur k : Word,
        ((((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ k) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜k ≠ (0 : Word)⌝) h)
      (B + 736) (tupleRej aB newSp acctBytes F)
      (B + 496) (tupleOk aB newSp aLen off acctBytes F) := by
    refine cpsBranchWithin_exists_pre (fun cur => ?_)
    refine cpsBranchWithin_exists_pre (fun k => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hk => ?_)
    have hbne := bne_spec_gen_within .x11 .x0 (244 : BitVec 13) k (0 : Word) (B + 488)
    rw [show (B + 488) + signExtend13 (244 : BitVec 13) = B + 732 from by
          rw [show signExtend13 (244 : BitVec 13) = (244 : Word) from by decide]
          bv_omega,
        show (B + 488) + 4 = B + 492 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 488) bansfProg 122 (.BNE .x11 .x0 (244 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
      hbne
    have hbneF := cpsBranchWithin_frameR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hbneL
    have htaken := cpsBranchWithin_takenPath hbneF
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact hk (((sepConj_pure_right _).1 h_pure).2))
    have hrej := liftCode (cr' := bansfCR)
      (bansf_rejectTail_spec B cur (by decide))
      (fun a i h => CodeReq.union_mono_left a i h)
    have hrejF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hrej
    have hchain := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2)
      htaken hrejF
    have hout : cpsTripleWithin 2 (B + 488) (B + 736) bansfCR
        (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ k) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) **
         ((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
         bytesRegion aB acctBytes ** F)
        (tupleRej aB newSp acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      unfold tupleRej
      have hq4 : ((((.x11 : Reg) ↦ᵣ k) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
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
          (cpsBranchWithin_pre_or hokc hfailc))))
  -- pointwise: collapse the six callee arms into ok ∨ fail
  obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, hor⟩, hEx⟩ := hp
  have rebuild : ∀ (arm : Assertion), arm h4 →
      ((((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) ** bytesRegion aB acctBytes) ** arm) **
        (((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) ** F))) h :=
    fun arm ha => ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, ha⟩, hEx⟩
  rcases hor with a1 | a2 | a3 | a4 | a5 | a6
  · -- ok arm: rlpWalkNextOk
    obtain ⟨next, len, hpins⟩ := a1
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
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
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
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
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
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
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
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
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
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
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
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 484 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩


theorem bansf_nonceTupleSpill117_spec (newSp v10 v11 : Word) :
    cpsTripleWithin 2 (B + 468) (B + 476) bansfCR
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 64) ** memOwn (newSp + 72))
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ v10) ** ((newSp + 72) ↦ₘ v11)) := by
  have hsd1 := sd_spec_gen_own_within .x2 .x10 newSp v10 (64 : BitVec 12) (B + 468)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (B + 468) + 4 = B + 472 from by bv_omega] at hsd1
  have hsd1L := liftCode (cr' := bansfCR) hsd1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 468) bansfProg 117 (.SD .x2 .x10 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd2 := sd_spec_gen_own_within .x2 .x11 newSp v11 (72 : BitVec 12) (B + 472)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide,
      show (B + 472) + 4 = B + 476 from by bv_omega] at hsd2
  have hsd2L := liftCode (cr' := bansfCR) hsd2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 472) bansfProg 118 (.SD .x2 .x11 (72 : BitVec 12))
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

/-- Slots 113–114 (`B + 452 → B + 460`): move the last nonce tuple span
    into the tuple `rlp_walk_init` argument registers. -/
theorem bansf_nonceLoopExitMove113_spec (v19 v20 v10 v11 : Word) :
    cpsTripleWithin 2 (B + 452) (B + 460) bansfCode
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11))
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x10 : Reg) ↦ᵣ v19) ** ((.x11 : Reg) ↦ᵣ v20)) := by
  have s1 := mv_spec_gen_within .x10 .x19 v19 v10 (B + 452) (by decide)
  have s2 := mv_spec_gen_within .x11 .x20 v20 v11 (B + 456) (by decide)
  runBlock s1 s2

/-- Loop-entry spills (slots 100–101): store the tuple-walk cursor and end. -/
theorem bansf_nonceLoopEntry100_spec (aB newSp : Word) (cOff fEnd : Nat) :
    cpsTripleWithin 2 (B + 400) (B + 408) bansfCR
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
    (64 : BitVec 12) (B + 400)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (B + 400) + 4 = B + 404 from by bv_omega] at hsd1
  have hsd1L := liftCode (cr' := bansfCR) hsd1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 400) bansfProg 100 (.SD .x2 .x10 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd2 := sd_spec_gen_own_within .x2 .x11 newSp (aB + BitVec.ofNat 64 fEnd)
    (72 : BitVec 12) (B + 404)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide,
      show (B + 404) + 4 = B + 408 from by bv_omega] at hsd2
  have hsd2L := liftCode (cr' := bansfCR) hsd2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 404) bansfProg 101 (.SD .x2 .x11 (72 : BitVec 12))
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

/-- Slot 99, taken arm: an empty nonce list skips to the station join. -/
theorem bansf_nonceEmptyTaken_spec (aB : Word) (cOff fEnd : Nat)
    (heq : cOff = fEnd) :
    cpsTripleWithin 1 (B + 396) (B + 540) bansfCode
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd)))
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fEnd))) := by
  subst heq
  have hbeq := beq_spec_gen_within .x10 .x11 (144 : BitVec 13)
    (aB + BitVec.ofNat 64 cOff) (aB + BitVec.ofNat 64 cOff) (B + 396)
  rw [show (B + 396) + signExtend13 (144 : BitVec 13) = B + 540 from by
        rw [show signExtend13 (144 : BitVec 13) = (144 : Word) from by decide]
        bv_omega] at hbeq
  have hbeqL := cpsBranchWithin_extend_code (cr' := bansfCode)
    (fun a i h => CodeReq.ofProg_mem_at B (B + 396) bansfProg 99
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

/-- Slot 99, fall-through arm: a nonempty nonce list enters its tuple loop. -/
theorem bansf_nonceEmptyFall_spec (aB : Word) (aLen cOff fEnd : Nat)
    (hne : cOff ≠ fEnd) (hcle : cOff ≤ aLen) (hfle : fEnd ≤ aLen)
    (hover9 : aB.toNat + aLen + 9 < 2 ^ 64) :
    cpsTripleWithin 1 (B + 396) (B + 400) bansfCode
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
    (aB + BitVec.ofNat 64 cOff) (aB + BitVec.ofNat 64 fEnd) (B + 396)
  rw [show (B + 396) + 4 = B + 400 from by bv_omega] at hbeq
  have hbeqL := cpsBranchWithin_extend_code (cr' := bansfCode)
    (fun a i h => CodeReq.ofProg_mem_at B (B + 396) bansfProg 99
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

/-- Slots 92–96 (`B + 368 → B + 388`): respill the outer item-4 cursor,
    capture its span in `s3`/`s4`, and prepare `rlp_walk_init`. -/
theorem bansf_nonceSpanCapture92_spec (newSp n4 l4 v19 v20 : Word) :
    cpsTripleWithin 5 (B + 368) (B + 388) bansfCR
      (((.x10 : Reg) ↦ᵣ n4) ** ((.x12 : Reg) ↦ᵣ l4) **
       ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 48))
      (((.x10 : Reg) ↦ᵣ (n4 - l4)) ** ((.x12 : Reg) ↦ᵣ l4) **
       ((.x19 : Reg) ↦ᵣ (n4 - l4)) ** ((.x20 : Reg) ↦ᵣ l4) **
       ((.x11 : Reg) ↦ᵣ l4) ** ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 48) ↦ₘ n4)) := by
  have hsd := sd_spec_gen_own_within .x2 .x10 newSp n4
    (48 : BitVec 12) (B + 368)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide,
      show (B + 368) + 4 = B + 372 from by bv_omega] at hsd
  have hsdL := liftCode (cr' := bansfCR) hsd
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 368) bansfProg 92
        (.SD .x2 .x10 (48 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide) a i h))
  have hsdF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ l4) ** ((.x19 : Reg) ↦ᵣ v19) **
     ((.x20 : Reg) ↦ᵣ v20) ** ((.x11 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hsdL
  have s1 := sub_spec_gen_within .x19 .x10 .x12 n4 l4 v19 (B + 372) (by decide)
  have s2 := mv_spec_gen_within .x20 .x12 l4 v20 (B + 376) (by decide)
  have s3 := mv_spec_gen_within .x10 .x19 (n4 - l4) n4 (B + 380) (by decide)
  have s4 := mv_spec_gen_within .x11 .x20 l4 (0 : Word) (B + 384) (by decide)
  have hcap : cpsTripleWithin 4 (B + 372) (B + 388) bansfCode
      (((.x10 : Reg) ↦ᵣ n4) ** ((.x12 : Reg) ↦ᵣ l4) **
       ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x11 : Reg) ↦ᵣ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ (n4 - l4)) ** ((.x12 : Reg) ↦ᵣ l4) **
       ((.x19 : Reg) ↦ᵣ (n4 - l4)) ** ((.x20 : Reg) ↦ᵣ l4) **
       ((.x11 : Reg) ↦ᵣ l4)) := by
    runBlock s1 s2 s3 s4
  have hcapL := liftCode (cr' := bansfCR) hcap
    (fun a i h => CodeReq.union_mono_left a i h)
  have hcapF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 48) ↦ₘ n4))
    (by pcf) hcapL
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hsdF hcapF
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hchain

/-- Slot 98, status-zero arm (`B + 392 → B + 396`): preserve the successful
    nonce-field `rlp_walk_init` result as the unified field-init post. -/
theorem bansf_nonceFieldInitSuccess98_spec (aB : Word) (fOff fSpanN cOff : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hok : FieldInitOk acctBytes fOff fSpanN cOff) :
    cpsTripleWithin 1 (B + 392) (B + 396) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) **
       bytesRegion aB acctBytes ** F)
      (fieldInitPost aB fOff fSpanN acctBytes (B + 388 + 4) F) := by
  have hbne := bne_spec_gen_within .x12 .x0 (340 : BitVec 13)
    (0 : Word) (0 : Word) (B + 392)
  rw [show (B + 392) + 4 = B + 396 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 392) bansfProg 98
        (.BNE .x12 .x0 (340 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide) a i h)) hbne
  have hfall := cpsBranchWithin_ntakenPath hbneL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  have hfallF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
     ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hfall
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
    hfallF
  unfold fieldInitPost
  refine ⟨cOff, (sepConj_pure_right h).2 ⟨?_, hok⟩⟩
  have hq' := sepConj_mono_left (sepConj_mono_right
    (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
  xperm_hyp hq'

/-- Slot 98, nonzero-status arm (`B + 392 → B + 736`): branch through the
    shared reject stub and release the field-init registers to ownership. -/
theorem bansf_nonceFieldInitFailure98_spec (aB cur endW k : Word)
    (acctBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (hk : k ≠ (0 : Word)) :
    cpsTripleWithin 2 (B + 392) (B + 736) bansfCR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
       ((.x12 : Reg) ↦ᵣ k) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) **
       bytesRegion aB acctBytes ** F)
      (fieldRej aB acctBytes F) := by
  have hbne := bne_spec_gen_within .x12 .x0 (340 : BitVec 13)
    k (0 : Word) (B + 392)
  rw [show (B + 392) + signExtend13 (340 : BitVec 13) = B + 732 from by
        rw [show signExtend13 (340 : BitVec 13) = (340 : Word) from by decide]
        bv_omega,
      show (B + 392) + 4 = B + 396 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 392) bansfProg 98
        (.BNE .x12 .x0 (340 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide) a i h)) hbne
  have hbneF := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) ** bytesRegion aB acctBytes ** F)
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
     ((.x11 : Reg) ↦ᵣ endW) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) ** bytesRegion aB acctBytes ** F)
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
       ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) **
       (((.x10 : Reg) ↦ᵣ (1 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F)) h := by
    xperm_hyp hq
  have hqOwn := sepConj_mono (regIs_implies_regOwn .x11)
    (sepConj_mono (regIs_implies_regOwn .x12)
      (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x))) h hq'
  xperm_hyp hqOwn

/-- Concrete code witnesses for the four non-call instructions of the outer
    nonce item unit (slots 88, 89, 91, and 92). -/
theorem bansf_item4_code :
    (∀ a i, CodeReq.singleton (B + 352) (.LD .x10 .x2 (48 : BitVec 12)) a = some i →
      bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B + 356) (.LD .x11 .x2 (56 : BitVec 12)) a = some i →
      bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B + 364) (.BNE .x11 .x0 (368 : BitVec 13)) a = some i →
      bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B + 368) (.SD .x2 .x10 (48 : BitVec 12)) a = some i →
      bansfCR a = some i) ∧
    4 * bansfProg.length < 2 ^ 64 := by
  refine ⟨?_, ?_, ?_, ?_, by decide +kernel⟩
  · intro a i h
    exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 352) bansfProg 88 (.LD .x10 .x2 (48 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h
    exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 356) bansfProg 89 (.LD .x11 .x2 (56 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h
    exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 364) bansfProg 91 (.BNE .x11 .x0 (368 : BitVec 13))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h
    exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 368) bansfProg 92 (.SD .x2 .x10 (48 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)

/-- Slots 93–96 (`B + 372 → B + 388`): capture the already-respilled outer
    nonce item span and prepare the field `rlp_walk_init` arguments. -/
theorem bansf_nonceSpanCapture93_spec (n4 l4 v19 v20 : Word) :
    cpsTripleWithin 4 (B + 372) (B + 388) bansfCode
      (((.x10 : Reg) ↦ᵣ n4) ** ((.x12 : Reg) ↦ᵣ l4) **
       ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x11 : Reg) ↦ᵣ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ (n4 - l4)) ** ((.x12 : Reg) ↦ᵣ l4) **
       ((.x19 : Reg) ↦ᵣ (n4 - l4)) ** ((.x20 : Reg) ↦ᵣ l4) **
       ((.x11 : Reg) ↦ᵣ l4)) := by
  have s1 := sub_spec_gen_within .x19 .x10 .x12 n4 l4 v19 (B + 372) (by decide)
  have s2 := mv_spec_gen_within .x20 .x12 l4 v20 (B + 376) (by decide)
  have s3 := mv_spec_gen_within .x10 .x19 (n4 - l4) n4 (B + 380) (by decide)
  have s4 := mv_spec_gen_within .x11 .x20 l4 (0 : Word) (B + 384) (by decide)
  runBlock s1 s2 s3 s4

/-- Slots 139–142 (`B + 556 → B + 572`): capture the outer code item span
    and prepare the code-field `rlp_walk_init` arguments. -/
theorem bansf_codeSpanCapture139_spec (n5 l5 v19 v20 : Word) :
    cpsTripleWithin 4 (B + 556) (B + 572) bansfCode
      (((.x10 : Reg) ↦ᵣ n5) ** ((.x12 : Reg) ↦ᵣ l5) **
       ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x11 : Reg) ↦ᵣ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ (n5 - l5)) ** ((.x12 : Reg) ↦ᵣ l5) **
       ((.x19 : Reg) ↦ᵣ (n5 - l5)) ** ((.x20 : Reg) ↦ᵣ l5) **
       ((.x11 : Reg) ↦ᵣ l5)) := by
  have s1 := sub_spec_gen_within .x19 .x10 .x12 n5 l5 v19 (B + 556) (by decide)
  have s2 := mv_spec_gen_within .x20 .x12 l5 v20 (B + 560) (by decide)
  have s3 := mv_spec_gen_within .x10 .x19 (n5 - l5) n5 (B + 564) (by decide)
  have s4 := mv_spec_gen_within .x11 .x20 l5 (0 : Word) (B + 568) (by decide)
  runBlock s1 s2 s3 s4

/-- Concrete code witness for the code-field status gate at slot 144. -/
theorem bansf_codeFieldStatus144_code :
    ∀ a i, CodeReq.singleton (B + 576) (.BNE .x12 .x0 (156 : BitVec 13)) a = some i →
      bansfCR a = some i := by
  intro a i h
  exact CodeReq.union_mono_left a i
    (CodeReq.ofProg_mem_at B (B + 576) bansfProg 144
      (.BNE .x12 .x0 (156 : BitVec 13))
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide) a i h)

/-- Concrete code witness for the code-field empty split at slot 145. -/
theorem bansf_codeEmpty145_code :
    ∀ a i, CodeReq.singleton (B + 580) (.BEQ .x10 .x11 (144 : BitVec 13)) a = some i →
      bansfCode a = some i := by
  intro a i h
  exact CodeReq.ofProg_mem_at B (B + 580) bansfProg 145
    (.BEQ .x10 .x11 (144 : BitVec 13))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) a i h

/-- Concrete code witnesses for the station-3 loop-entry spills. -/
theorem bansf_codeLoopEntry_code :
    (∀ a i, CodeReq.singleton (B + 584) (.SD .x2 .x10 (64 : BitVec 12)) a = some i →
      bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B + 588) (.SD .x2 .x11 (72 : BitVec 12)) a = some i →
      bansfCR a = some i) := by
  constructor
  · intro a i h
    exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 584) bansfProg 146 (.SD .x2 .x10 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h
    exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 588) bansfProg 147 (.SD .x2 .x11 (72 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)

/-- Concrete code witnesses for the code-window materialization tail. -/
theorem bansf_codeMaterialize_code :
    (∀ a i, CodeReq.singleton (B+700) (.SUB .x29 .x10 .x12) a = some i → bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B+704) (.SUB .x29 .x29 .x8) a = some i → bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B+708) (.SD .x18 .x29 (64:BitVec 12)) a = some i → bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B+712) (.SD .x18 .x12 (72:BitVec 12)) a = some i → bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B+716) (.LI .x5 (1:Word)) a = some i → bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B+720) (.SD .x18 .x5 (56:BitVec 12)) a = some i → bansfCR a = some i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a i h; exact CodeReq.union_mono_left a i (CodeReq.ofProg_mem_at B (B+700) bansfProg 175 (.SUB .x29 .x10 .x12) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h; exact CodeReq.union_mono_left a i (CodeReq.ofProg_mem_at B (B+704) bansfProg 176 (.SUB .x29 .x29 .x8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h; exact CodeReq.union_mono_left a i (CodeReq.ofProg_mem_at B (B+708) bansfProg 177 (.SD .x18 .x29 (64:BitVec 12)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h; exact CodeReq.union_mono_left a i (CodeReq.ofProg_mem_at B (B+712) bansfProg 178 (.SD .x18 .x12 (72:BitVec 12)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h; exact CodeReq.union_mono_left a i (CodeReq.ofProg_mem_at B (B+716) bansfProg 179 (.LI .x5 (1:Word)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h; exact CodeReq.union_mono_left a i (CodeReq.ofProg_mem_at B (B+720) bansfProg 180 (.SD .x18 .x5 (56:BitVec 12)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)

/-- Concrete code witnesses for the code tuple's value-item argument setup. -/
theorem bansf_codeValueArgs_code :
    (∀ a i, CodeReq.singleton (B+680) (.LD .x28 .x2 (64:BitVec 12)) a = some i → bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B+684) (.LD .x11 .x2 (72:BitVec 12)) a = some i → bansfCR a = some i) ∧
    (∀ a i, CodeReq.singleton (B+688) (.MV .x10 .x28) a = some i → bansfCR a = some i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a i h; exact CodeReq.union_mono_left a i (CodeReq.ofProg_mem_at B (B+680) bansfProg 170 (.LD .x28 .x2 (64:BitVec 12)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h; exact CodeReq.union_mono_left a i (CodeReq.ofProg_mem_at B (B+684) bansfProg 171 (.LD .x11 .x2 (72:BitVec 12)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)
  · intro a i h; exact CodeReq.union_mono_left a i (CodeReq.ofProg_mem_at B (B+688) bansfProg 172 (.MV .x10 .x28) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)

/-- Concrete code witness for the code tuple value-item status gate. -/
theorem bansf_codeValueStatus174_code :
    ∀ a i, CodeReq.singleton (B+696) (.BNE .x11 .x0 (36:BitVec 13)) a = some i → bansfCR a = some i := by
  intro a i h
  exact CodeReq.union_mono_left a i (CodeReq.ofProg_mem_at B (B+696) bansfProg 174 (.BNE .x11 .x0 (36:BitVec 13)) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h)

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
