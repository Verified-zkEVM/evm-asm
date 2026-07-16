/-
  Per-iteration body + loop induction for `chain_validate_extra_data_length`.

  Builds on `ChainValidateExtraDataLengthSpec` (model, prologue, epilogue, exit
  blocks, `wordArray_split`).  Proves the four straight-line body blocks of one
  loop iteration:

    * `cvedlSetup`  [C+72 → C+132]  — spill + aligned array load + call-arg setup
    * `cvedlCall`   [C+72 → C+136]  — setup ;; jal ;; `rlpListNthItem_spec_within`
    * `cvedlReload` [C+140 → C+180] — reload iter state + field length, `x7 := 32`
    * `cvedlAdvance`[C+184 → C+68]  — `x18 += lengths[i]`, `x21 += 1`, loop back

  These plus the guard/exit/frame blocks in the `Spec` module are the reusable
  pieces the loop induction `cvedlLoop` (BNE/BLTU 3-way dispatch tying K20's
  `Result` to the post arms, over `N − i`) and the whole-program contract
  `chain_validate_extra_data_length_spec_within` compose — that final gluing is
  the remaining work.
-/

import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec
import EvmAsm.Evm64.StateAssertions

namespace EvmAsm.Codegen.ChainValidateExtraDataLengthSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## Ownership weakening for the K20 frame

    On K20 return, the frame slots hold the (restored) saved values; the loop
    invariant carries them merely *owned*. -/

theorem frameSlotsSaved_implies_frameSlotsOwn (frame : FrameDesc) (newSp : Word)
    (vals : Reg → Word) :
    ∀ h, frameSlotsSaved frame newSp vals h → frameSlotsOwn frame newSp h := by
  induction frame with
  | nil => intro h hp; simpa only [frameSlotsSaved_nil, frameSlotsOwn_nil] using hp
  | cons p rest ih =>
    intro h hp
    rw [frameSlotsSaved_cons] at hp
    rw [frameSlotsOwn_cons]
    exact sepConj_mono memIs_implies_memOwn ih h hp

/-- K20's saved frame, once restored, weakens to the merely-owned frame slots. -/
theorem savedFrame_implies_frameSlotsOwn (newSp : Word) (saved : Saved) :
    ∀ h, savedFrame newSp saved h → frameSlotsOwn listNthFrame newSp h := by
  intro h hp
  rw [← frameSlotsSaved_listNthFrame] at hp
  exact frameSlotsSaved_implies_frameSlotsOwn listNthFrame newSp (savedVals saved) h hp


/-! ## Setup block (instructions 18--32): spill + array load + call-arg setup

    From the loop guard fall-through (`C+72`) to just before the `jal` (`C+132`).
    Fully generic in the current header base `hbi`, the counter word `iW`, and
    the field-length value `Li`; the loop supplies `hbi = hdrBaseAt …`,
    `iW = ofNat i`, `Li = lengths[i]`. -/

set_option maxRecDepth 8000 in
theorem cvedlSetup (hbi lenBase spC iW : Word) (Li : Nat)
    (old5 o10 o11 o12 o13 o14 o28 : Word) :
    cpsTripleWithin 15 (C + 72) (C + 132) cvedlCode
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) **
        (.x13 ↦ᵣ o13) ** (.x14 ↦ᵣ o14) ** (.x28 ↦ᵣ o28) **
        memOwn IterPtr ** memOwn IterI **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
        (.x12 ↦ᵣ (12 : Word)) ** (.x13 ↦ᵣ COff) ** (.x14 ↦ᵣ CLen) **
        (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  -- [18-19] la x5, cvedl_iter_ptr
  have hla18 := la_materialize_within .x5 old5 (C + 72) IterPtr (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 72) cvedlProg 18 (.AUIPC .x5 (EvmAsm.Rv64.laHi (C + 72) IterPtr)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 76) cvedlProg 19 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (C + 72) IterPtr)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  -- [20] SD x5 x18 0 : *iter_ptr := hbi
  have s20 := sd_spec_gen_own_within .x5 .x18 IterPtr hbi (0 : BitVec 12) (C + 80)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPtr + (0 : Word) = IterPtr from by bv_omega] at s20
  have s20' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 80) cvedlProg 20 (.SD .x5 .x18 (0 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s20
  -- [21-22] la x5, cvedl_iter_i
  have hla21 := la_materialize_within .x5 IterPtr (C + 84) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 84) cvedlProg 21 (.AUIPC .x5 (EvmAsm.Rv64.laHi (C + 84) IterI)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 88) cvedlProg 22 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (C + 84) IterI)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  -- [23] SD x5 x21 0 : *iter_i := iW
  have s23 := sd_spec_gen_own_within .x5 .x21 IterI iW (0 : BitVec 12) (C + 92)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s23
  have s23' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 92) cvedlProg 23 (.SD .x5 .x21 (0 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s23
  -- [24] SLLI x28 x21 3 : x28 := iW <<< 3
  have s24 := slli_spec_gen_within .x28 .x21 o28 iW (3 : BitVec 6) (C + 96) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s24
  have s24' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 96) cvedlProg 24 (.SLLI .x28 .x21 (3 : BitVec 6)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s24
  -- [25] ADD x28 x9 x28 : x28 := lenBase + iW<<<3
  have s25 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase (iW <<< 3) (C + 100) (by decide)
  have s25' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 100) cvedlProg 25 (.ADD .x28 .x9 .x28) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s25
  -- [26] LD x11 x28 0 : x11 := *(lenBase + iW<<<3) = ofNat Li
  have s26 := ld_spec_gen_within .x11 .x28 (lenBase + (iW <<< 3)) o11 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (C + 104) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s26
  have s26' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 104) cvedlProg 26 (.LD .x11 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s26
  -- [27] MV x10 x18 : x10 := hbi
  have s27 := mv_spec_gen_within .x10 .x18 hbi o10 (C + 108) (by decide)
  have s27' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 108) cvedlProg 27 (.MV .x10 .x18) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s27
  -- [28] LI x12 12
  have s28 := li_spec_gen_within .x12 o12 (12 : Word) (C + 112) (by decide)
  have s28' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 112) cvedlProg 28 (.LI .x12 (12 : Word)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s28
  -- [29-30] la x13, cvedl_offset
  have hla29 := la_materialize_within .x13 o13 (C + 116) COff (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 116) cvedlProg 29 (.AUIPC .x13 (EvmAsm.Rv64.laHi (C + 116) COff)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 120) cvedlProg 30 (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (C + 116) COff)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  -- [31-32] la x14, cvedl_length
  have hla31 := la_materialize_within .x14 o14 (C + 124) CLen (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 124) cvedlProg 31 (.AUIPC .x14 (EvmAsm.Rv64.laHi (C + 124) CLen)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 128) cvedlProg 32 (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (C + 124) CLen)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  runBlock hla18 s20' hla21 s23' s24' s25' s26' s27' s28' hla29 hla31

#print axioms cvedlSetup

/-- K20's whole-routine step count for field index 12 (same as the template). -/
abbrev nCall : Nat := (12 + ((85 + 93 * (12 + 2)) + 6)) + 9

/-! ## Call block (instructions 18--33 + K20): setup ;; jal ;; selector

    From the loop-guard fall-through (`C+72`) to the return site (`C+136`),
    producing K20's `returnResult` for header `hbi` (field 12), with the spill
    cells, the array cell, and the chain frame carried through unchanged. -/

set_option maxRecDepth 8000 in
theorem cvedlCall (hbi lenBase spC iW : Word) (Li : Nat)
    (s0 s3 s4 oldOff oldLen oldX1 old5 o10 o11 o12 o13 o14 o28 : Word)
    (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hbi.toNat % 8 = 0)
    (hslack : Li + 9 ≤ bytes.length)
    (hover : hbi.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hbi + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (15 + 1 + nCall) (C + 72) (C + 136) fullCode
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) **
        (.x13 ↦ᵣ o13) ** (.x14 ↦ᵣ o14) ** (.x28 ↦ᵣ o28) **
        memOwn IterPtr ** memOwn IterI **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
        (.x1 ↦ᵣ oldX1) ** (.x8 ↦ᵣ s0) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)) **
        (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) ** bytesRegion hbi bytes **
        savedFrame spC csaved)
      (returnResult spC (spC + signExtend12 (-64 : BitVec 12)) hbi (12 : Word) COff CLen
          oldOff oldLen ⟨LinkRA, s0, lenBase, hbi, s3, s4, iW⟩ bytes Li 12 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  set saved : Saved := ⟨LinkRA, s0, lenBase, hbi, s3, s4, iW⟩ with hsaved
  set calleeNewSp : Word := spC + signExtend12 (-64 : BitVec 12) with hcalleeNewSp
  -- Setup block, lifted to fullCode, framed with the callee footprint.
  have hsetup := cpsTripleWithin_extend_code cvedl_mono
    (cvedlSetup hbi lenBase spC iW Li old5 o10 o11 o12 o13 o14 o28)
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ oldX1) ** (.x8 ↦ᵣ s0) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn listNthFrame calleeNewSp **
      (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) ** bytesRegion hbi bytes **
      savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _) hsetup
  -- [33] jal x1, rlp_list_nth_item
  have hjal := jal_link_spec_within
    (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.chain_validate_extra_data_length + 132)) (C + 132) oldX1
  rw [show (C + 132) + signExtend21 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.chain_validate_extra_data_length + 132)) = B from by decide,
    show (C + 132 + 4 : Word) = LinkRA from by unfold LinkRA; bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code cvedl_mono
    (cpsTripleWithin_extend_code (cr' := cvedlCode)
      (CodeReq.ofProg_mem_at C (C + 132) cvedlProg 33
        (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_list_nth_item
          (GuestAddrs.chain_validate_extra_data_length + 132))) (by bv_omega)
        (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
      (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
      (.x12 ↦ᵣ (12 : Word)) ** (.x13 ↦ᵣ COff) ** (.x14 ↦ᵣ CLen) **
      (.x28 ↦ᵣ (lenBase + (iW <<< 3))) ** (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
      (.x8 ↦ᵣ s0) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn listNthFrame calleeNewSp **
      (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) ** bytesRegion hbi bytes **
      savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _) hjalC
  -- K20 selector, lifted to fullCode, framed with the spill/array/chain payload.
  have hcallee0 := rlpListNthItem_spec_within spC calleeNewSp hbi (BitVec.ofNat 64 Li)
    (12 : Word) COff CLen oldOff oldLen saved bytes Li 12 rfl rfl (by decide) (by decide)
    hsalign hslack hover hvalid (by simp only [hsaved]; decide)
  have hcalleeC := cpsTripleWithin_extend_code k20_mono hcallee0
  -- Present K20's entry footprint as explicit atoms (regsAt/entryRest unfolded,
  -- `saved` fields reduced), with `x5`/`x28` shown owned.
  have hcallee : cpsTripleWithin nCall B (C + 136) fullCode
      (regOwn .x5 ** regOwn .x28 **
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ LinkRA) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hbi) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ iW) **
          frameSlotsOwn listNthFrame calleeNewSp ** (.x10 ↦ᵣ hbi) **
          (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (12 : Word)) ** (.x13 ↦ᵣ COff) **
          (.x14 ↦ᵣ CLen) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion hbi bytes **
          (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen)))
      (returnResult spC calleeNewSp hbi (12 : Word) COff CLen oldOff oldLen saved
        bytes Li 12) :=
    cpsTripleWithin_weaken (fun h hp => by
      rw [regsAt_listNthFrame]
      simp only [hsaved]
      unfold entryRest
      xperm_hyp hp) (fun _ hq => hq) hcalleeC
  have hcalleeF := cpsTripleWithin_frameR
    ((IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
      ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_memIs) hcallee
  -- Compose setup ;; jal ;; callee (weakening `x5`/`x28` to owned at the midpoint).
  have hsj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF hjalF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => ?_) hsj hcalleeF)
  have hp' : ((.x5 ↦ᵣ IterI) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
      ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) **
        (.x21 ↦ᵣ iW) ** (.x10 ↦ᵣ hbi) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
        (.x12 ↦ᵣ (12 : Word)) ** (.x13 ↦ᵣ COff) ** (.x14 ↦ᵣ CLen) **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** (.x8 ↦ᵣ s0) **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn listNthFrame calleeNewSp ** (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) **
        bytesRegion hbi bytes ** savedFrame spC csaved)) h := by xperm_hyp hp
  have hp'' := sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)) h hp'
  xperm_hyp hp''

#print axioms cvedlCall

/-! ## Reload block (instructions 35--44): restore iter state + load length

    Runs on the K20-success (`bne` not-taken) path from `C+140` to `C+180`:
    reload `x18 := *iter_ptr`, `x21 := *iter_i`, `x6 := *cvedl_length`, and set
    `x7 := 32` for the upcoming `bltu`. -/

set_option maxRecDepth 8000 in
theorem cvedlReload (hbi iW len : Word) (old5 o18 o21 o6 o7 : Word) :
    cpsTripleWithin 10 (C + 140) (C + 180) cvedlCode
      ((.x5 ↦ᵣ old5) ** (.x18 ↦ᵣ o18) ** (.x21 ↦ᵣ o21) ** (.x6 ↦ᵣ o6) **
        (.x7 ↦ᵣ o7) ** (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (CLen ↦ₘ len))
      ((.x5 ↦ᵣ CLen) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) ** (.x6 ↦ᵣ len) **
        (.x7 ↦ᵣ (32 : Word)) ** (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) ** (CLen ↦ₘ len)) := by
  -- [35-36] la x5, cvedl_iter_ptr
  have hla35 := la_materialize_within .x5 old5 (C + 140) IterPtr (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 140) cvedlProg 35 (.AUIPC .x5 (EvmAsm.Rv64.laHi (C + 140) IterPtr)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 144) cvedlProg 36 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (C + 140) IterPtr)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  -- [37] LD x18 x5 0 : x18 := *iter_ptr = hbi
  have s37 := ld_spec_gen_within .x18 .x5 IterPtr o18 hbi (0 : BitVec 12) (C + 148) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPtr + (0 : Word) = IterPtr from by bv_omega] at s37
  have s37' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 148) cvedlProg 37 (.LD .x18 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s37
  -- [38-39] la x5, cvedl_iter_i
  have hla38 := la_materialize_within .x5 IterPtr (C + 152) IterI (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 152) cvedlProg 38 (.AUIPC .x5 (EvmAsm.Rv64.laHi (C + 152) IterI)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 156) cvedlProg 39 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (C + 152) IterI)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  -- [40] LD x21 x5 0 : x21 := *iter_i = iW
  have s40 := ld_spec_gen_within .x21 .x5 IterI o21 iW (0 : BitVec 12) (C + 160) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s40
  have s40' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 160) cvedlProg 40 (.LD .x21 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s40
  -- [41-42] la x5, cvedl_length
  have hla41 := la_materialize_within .x5 IterI (C + 164) CLen (by decide) (by decide)
    (CodeReq.ofProg_mem_at C (C + 164) cvedlProg 41 (.AUIPC .x5 (EvmAsm.Rv64.laHi (C + 164) CLen)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
    (CodeReq.ofProg_mem_at C (C + 168) cvedlProg 42 (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (C + 164) CLen)) (by bv_omega) (by rw [cvedl_length]; decide) (by decide) (by rw [cvedl_length]; decide))
  -- [43] LD x6 x5 0 : x6 := *cvedl_length = len
  have s43 := ld_spec_gen_within .x6 .x5 CLen o6 len (0 : BitVec 12) (C + 172) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show CLen + (0 : Word) = CLen from by bv_omega] at s43
  have s43' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 172) cvedlProg 43 (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s43
  -- [44] LI x7 32
  have s44 := li_spec_gen_within .x7 o7 (32 : Word) (C + 176) (by decide)
  have s44' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 176) cvedlProg 44 (.LI .x7 (32 : Word)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s44
  runBlock hla35 s37' hla38 s40' hla41 s43' s44'

#print axioms cvedlReload

/-! ## Advance block (instructions 46--51): step the iterator, loop back

    On the length-OK (`bltu` not-taken) path from `C+184`: `x18 += lengths[i]`,
    `x21 += 1`, then `jal x0, -136` back to the loop guard at `C+68`. -/

set_option maxRecDepth 8000 in
theorem cvedlAdvance (hbi lenBase iW : Word) (Li : Nat) (o28 o29 : Word) :
    cpsTripleWithin 6 (C + 184) (C + 68) cvedlCode
      ((.x21 ↦ᵣ iW) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x28 ↦ᵣ o28) **
        (.x29 ↦ᵣ o29) ** ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x21 ↦ᵣ (iW + signExtend12 (1 : BitVec 12))) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ (hbi + BitVec.ofNat 64 Li)) ** (.x28 ↦ᵣ (lenBase + (iW <<< 3))) **
        (.x29 ↦ᵣ BitVec.ofNat 64 Li) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  -- [46] SLLI x28 x21 3
  have s46 := slli_spec_gen_within .x28 .x21 o28 iW (3 : BitVec 6) (C + 184) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s46
  have s46' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 184) cvedlProg 46 (.SLLI .x28 .x21 (3 : BitVec 6)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s46
  -- [47] ADD x28 x9 x28
  have s47 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase (iW <<< 3) (C + 188) (by decide)
  have s47' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 188) cvedlProg 47 (.ADD .x28 .x9 .x28) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s47
  -- [48] LD x29 x28 0 : x29 := *(lenBase + iW<<<3) = ofNat Li
  have s48 := ld_spec_gen_within .x29 .x28 (lenBase + (iW <<< 3)) o29 (BitVec.ofNat 64 Li)
    (0 : BitVec 12) (C + 192) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iW <<< 3)) + (0 : Word) = lenBase + (iW <<< 3) from by bv_omega] at s48
  have s48' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 192) cvedlProg 48 (.LD .x29 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s48
  -- [49] ADD x18 x18 x29 : x18 += ofNat Li
  have s49 := add_spec_gen_rd_eq_rs1_within .x18 .x29 hbi (BitVec.ofNat 64 Li) (C + 196) (by decide)
  have s49' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 196) cvedlProg 49 (.ADD .x18 .x18 .x29) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s49
  -- [50] ADDI x21 x21 1 : x21 += 1
  have s50 := addi_spec_gen_same_within .x21 iW (1 : BitVec 12) (C + 200) (by decide)
  have s50' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 200) cvedlProg 50 (.ADDI .x21 .x21 (1 : BitVec 12)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s50
  -- [51] JAL x0 -136 : loop back to the guard
  have s51 := jal_x0_spec_gen_within (-136 : BitVec 21) (C + 204)
  rw [show (C + 204) + signExtend21 (-136 : BitVec 21) = C + 68 from by
    rw [show signExtend21 (-136 : BitVec 21) = (-136 : Word) from by decide]; bv_omega] at s51
  have s51' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at C (C + 204) cvedlProg 51 (.JAL .x0 (-136 : BitVec 21)) (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) s51
  runBlock s46' s47' s48' s49' s50' s51'

#print axioms cvedlAdvance

/-! ## Arithmetic helpers for the loop induction -/

theorem hdrOff_succ (lengths : List Nat) (i : Nat) (hi : i < lengths.length) :
    hdrOff lengths (i + 1) = hdrOff lengths i + lengths[i]! := by
  unfold hdrOff
  rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem hi]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem ofNat_ne_of_lt (i N : Nat) (hi : i < N) (hN : N < 2 ^ 64) :
    BitVec.ofNat 64 i ≠ BitVec.ofNat 64 N := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hi hN),
    Nat.mod_eq_of_lt hN] at this
  omega

theorem ofNat_succ_tie (i : Nat) :
    BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 (i + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

/-- `hdrBaseAt` advances by `lengths[i]` bytes (mod 2^64). -/
theorem hdrBaseAt_succ (hdrBase : Word) (lengths : List Nat) (i : Nat)
    (hi : i < lengths.length) :
    hdrBaseAt hdrBase lengths (i + 1) =
      hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 (lengths[i]!) := by
  unfold hdrBaseAt
  rw [hdrOff_succ lengths i hi, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

/-! ## Call block with the consumed scratch registers owned

    `cvedlCall` with `x1/x5/x10/x11/x12/x13/x14/x28` presented as `regOwn` (their
    incoming values are overwritten), matching how they sit in `LoopInv`.  The
    reusable adapter the sibling accessors need most. -/

set_option maxRecDepth 8000 in
theorem cvedlCallOwned (hbi lenBase spC iW : Word) (Li : Nat)
    (s0 s3 s4 oldOff oldLen : Word) (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hbi.toNat % 8 = 0)
    (hslack : Li + 9 ≤ bytes.length)
    (hover : hbi.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hbi + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (15 + 1 + nCall) (C + 72) (C + 136) fullCode
      ((((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
          memOwn IterPtr ** memOwn IterI **
          ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
          (.x8 ↦ᵣ s0) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)) **
          (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) ** bytesRegion hbi bytes **
          savedFrame spC csaved) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28) ** regOwn .x1)
      (returnResult spC (spC + signExtend12 (-64 : BitVec 12)) hbi (12 : Word) COff CLen
          oldOff oldLen ⟨LinkRA, s0, lenBase, hbi, s3, s4, iW⟩ bytes Li 12 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v1 => ?_)
  refine cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => h)
    (show cpsTripleWithin (15 + 1 + nCall) (C + 72) (C + 136) fullCode
      ((((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) ** (.x21 ↦ᵣ iW) **
          memOwn IterPtr ** memOwn IterI **
          ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
          (.x8 ↦ᵣ s0) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)) **
          (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) ** bytesRegion hbi bytes **
          savedFrame spC csaved) ** (.x1 ↦ᵣ v1)) **
        regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x28)
      (returnResult spC (spC + signExtend12 (-64 : BitVec 12)) hbi (12 : Word) COff CLen
          oldOff oldLen ⟨LinkRA, s0, lenBase, hbi, s3, s4, iW⟩ bytes Li 12 **
        (IterPtr ↦ₘ hbi) ** (IterI ↦ₘ iW) **
        ((lenBase + (iW <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) from ?_)
  refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
    (fun v5 v10 v11 v12 v13 v14 v28 => ?_)
  exact cpsTripleWithin_weaken (fun _ h => by xperm_hyp h) (fun _ h => by xperm_hyp h)
    (cvedlCall hbi lenBase spC iW Li s0 s3 s4 oldOff oldLen v1 v5 v10 v11 v12 v13 v14 v28
      bytes csaved hsalign hslack hover hvalid)

#print axioms cvedlCallOwned

/-! ## Entry half of one iteration: guard → call → K20 returnResult

    From the loop guard (`C+68`, `i < N`) through the `jal` to K20's return
    (`C+136`), with the header slice handed to K20 and the untouched
    `wordArray`/`bytesRegion` prefixes framed. -/

set_option maxRecDepth 8000 in
theorem cvedlIterEntry (spC hdrBase lenBase validPtr firstBadPtr : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i : Nat)
    (oldOff oldLen : Word)
    (hi : i < lengths.length)
    (hN : lengths.length < 2 ^ 64)
    (hsalign : (hdrBaseAt hdrBase lengths i).toNat % 8 = 0)
    (hslack : lengths[i]! + 9 ≤ (bigBytes.drop (hdrOff lengths i)).length)
    (hover : (hdrBaseAt hdrBase lengths i).toNat +
      (bigBytes.drop (hdrOff lengths i)).length < 2 ^ 64)
    (hvalid : ∀ k, k < (bigBytes.drop (hdrOff lengths i)).length →
      isValidByteAccess (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + (15 + 1 + nCall)) (C + 68) (C + 136) fullCode
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
        (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** savedFrame spC csaved **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
        (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) ** memOwn IterPtr ** memOwn IterI **
        regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)))
      (returnResult spC (spC + signExtend12 (-64 : BitVec 12)) (hdrBaseAt hdrBase lengths i)
          (12 : Word) COff CLen oldOff oldLen
          ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
            validPtr, firstBadPtr, BitVec.ofNat 64 i⟩
          (bigBytes.drop (hdrOff lengths i)) lengths[i]! 12 **
        (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        savedFrame spC csaved) := by
  -- [17] BEQ x21 x8 : i ≠ N ⇒ not taken → C+72.
  have hbeq := beq_spec_gen_within .x21 .x8 (168 : BitVec 13) (BitVec.ofNat 64 i)
    (BitVec.ofNat 64 lengths.length) (C + 68)
  have hbeqC := cpsBranchWithin_extend_code cvedl_mono
    (cpsBranchWithin_extend_code (cr' := cvedlCode)
      (CodeReq.ofProg_mem_at C (C + 68) cvedlProg 17 (.BEQ .x21 .x8 (168 : BitVec 13))
        (by bv_omega) (by rw [cvedl_length]; decide) rfl (by rw [cvedl_length]; decide)) hbeq)
  have hguard0 := cpsBranchWithin_ntakenStripPure2 hbeqC (fun hp hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact ofNat_ne_of_lt i lengths.length hi hN ((sepConj_pure_right _).1 hrest).2)
  rw [show (C + 68 + 4 : Word) = C + 72 from by bv_omega] at hguard0
  -- Frame the guard with the untouched loop-invariant state (everything but x21/x8).
  have hguardF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) **
      (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** savedFrame spC csaved **
      (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
      wordArrayFrom lenBase 0 (lengths.take i) **
      ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
      (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) ** memOwn IterPtr ** memOwn IterI **
      regOwn .x1 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn listNthFrame (spC + signExtend12 (-64 : BitVec 12)))
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact bytesRegion_pcFree _ _
                      | exact pcFree_wordArrayFrom _ _ _) hguard0
  -- The call, framed with the untouched wordArray/bytesRegion prefixes.
  have hcall := cvedlCallOwned (hdrBaseAt hdrBase lengths i) lenBase spC (BitVec.ofNat 64 i)
    lengths[i]! (BitVec.ofNat 64 lengths.length) validPtr firstBadPtr oldOff oldLen
    (bigBytes.drop (hdrOff lengths i)) csaved hsalign hslack hover hvalid
  have hcallF := cpsTripleWithin_frameR
    (wordArrayFrom lenBase 0 (lengths.take i) **
      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
      (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)))
    (by repeat' first | apply pcFree_sepConj | exact pcFree_wordArrayFrom _ _ _
                      | exact bytesRegion_pcFree _ _ | exact pcFree_memIs) hcall
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
      rw [show (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) from shiftLeft3_ofNat i] at hq
      xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      rw [show (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) from shiftLeft3_ofNat i]
      xperm_hyp hp) hguardF hcallF)

#print axioms cvedlIterEntry

/-- pcFree discharger covering the assertion atoms used in the dispatch. -/
local macro "pcfx" : tactic =>
  `(tactic| repeat' first
      | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | exact pcFree_emp | exact pcFree_pure
      | exact bytesRegion_pcFree _ _ | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_wordArrayFrom _ _ _ | unfold savedFrame)

/-! ## Status dispatch (instructions 34 onward): tie K20's `Result` to the post

    From K20's `returnResult` at the `bne` return site (`C+136`) to the
    caller's post.  `bne x10, x0` splits on the callee status; `Result`
    inversion pins the parse-fail arm (status ≠ 0) and, on success, the
    length compare (`bltu 32, len`) routes to violation or continue+loop. -/

set_option maxRecDepth 8000 in
theorem cvedlIterDispatch
    (sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr raIn : Word)
    (csaved : Saved) (bigBytes : List (BitVec 8)) (lengths : List Nat) (i : Nat)
    (oldOff oldLen : Word) (nTail : Nat)
    (hi : i < lengths.length)
    (hN : lengths.length < 2 ^ 64)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hcns : calleeNewSp = spC + signExtend12 (-64 : BitVec 12))
    (hraSaved : csaved.ra = raIn)
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (halign : hdrOff lengths i % 8 = 0)
    (hlen : hdrOff lengths i ≤ bigBytes.length)
    (hprefix : ∀ j, j < i → hdrValidShort hdrBase bigBytes lengths j)
    (htail : (∀ j, j < i + 1 → hdrValidShort hdrBase bigBytes lengths j) →
      cpsTripleWithin nTail (C + 68) raIn fullCode
        (LoopInv sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
          bigBytes lengths (i + 1))
        (cvedlPost sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
          bigBytes lengths)) :
    cpsTripleWithin (25 + nTail) (C + 136) raIn fullCode
      (returnResult spC (spC + signExtend12 (-64 : BitVec 12)) (hdrBaseAt hdrBase lengths i)
          (12 : Word) COff CLen oldOff oldLen
          ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
            validPtr, firstBadPtr, BitVec.ofNat 64 i⟩
          (bigBytes.drop (hdrOff lengths i)) lengths[i]! 12 **
        (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
        wordArrayFrom lenBase 0 (lengths.take i) **
        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
        savedFrame spC csaved)
      (cvedlPost sp0 spC calleeNewSp hdrBase lenBase validPtr firstBadPtr csaved
        bigBytes lengths) := by
  subst hcns
  have hLi : lengths[i]! = lengths[i] := getElem!_pos lengths i hi
  have hHB : hdrBaseAt hdrBase lengths i = hdrBase + BitVec.ofNat 64 (hdrOff lengths i) := rfl
  have hsf : savedFrame spC csaved =
      ((spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) := by
    unfold savedFrame; rw [hraSaved]
  -- Strip `returnResult`'s existentials and pull out the semantic `Result`.
  refine cpsTripleWithin_weaken (fun h hp => ?hstrip) (fun _ hq => hq)
    (cpsTripleWithin_exists_assertion (fun status =>
      cpsTripleWithin_exists_assertion (fun offset =>
        cpsTripleWithin_exists_assertion (fun len =>
          cpsTripleWithin_exists_assertion (fun v11 =>
            cpsTripleWithin_exists_assertion (fun v12 =>
              (show cpsTripleWithin (25 + nTail) (C + 136) raIn fullCode
                (((((.x2 ↦ᵣ spC) **
                      regsAt listNthFrame (savedVals ⟨LinkRA, BitVec.ofNat 64 lengths.length,
                        lenBase, hdrBaseAt hdrBase lengths i, validPtr, firstBadPtr,
                        BitVec.ofNat 64 i⟩) **
                      savedFrame (spC + signExtend12 (-64 : BitVec 12))
                        ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase,
                          hdrBaseAt hdrBase lengths i, validPtr, firstBadPtr,
                          BitVec.ofNat 64 i⟩) **
                    ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
                     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
                     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                     (.x0 ↦ᵣ (0 : Word)) **
                     bytesRegion (hdrBaseAt hdrBase lengths i)
                       (bigBytes.drop (hdrOff lengths i)) **
                     (COff ↦ₘ offset) ** (CLen ↦ₘ len))) **
                   ⌜Result (bigBytes.drop (hdrOff lengths i)) (hdrBaseAt hdrBase lengths i)
                     lengths[i]! 12 oldOff oldLen status offset len⌝) **
                  ((IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                    ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                    wordArrayFrom lenBase 0 (lengths.take i) **
                    wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                    bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                    (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                    savedFrame spC csaved))
                (cvedlPost sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase
                  validPtr firstBadPtr csaved bigBytes lengths) from ?core)))))))
  case hstrip =>
    obtain ⟨h1, h2, hd, hu, hrr, hF⟩ := hp
    obtain ⟨status, offset, len, v11, v12, hbody⟩ := hrr
    exact ⟨status, offset, len, v11, v12, h1, h2, hd, hu, hbody, hF⟩
  case core =>
    -- Pull the `Result` fact out of the pre.
    refine cpsTripleWithin_weaken (fun h hp => ?hpull) (fun _ hq => hq)
      (cpsTripleWithin_pure_pre
        (P := Result (bigBytes.drop (hdrOff lengths i)) (hdrBaseAt hdrBase lengths i)
          lengths[i]! 12 oldOff oldLen status offset len)
        (H := (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
          (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
          (COff ↦ₘ offset) ** (CLen ↦ₘ len) **
          savedFrame (spC + signExtend12 (-64 : BitVec 12))
            ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
              validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
          (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
          ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
          wordArrayFrom lenBase 0 (lengths.take i) **
          wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
          bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
          (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
          savedFrame spC csaved)
        (fun hResult => ?body))
    case hpull =>
      rw [regsAt_listNthFrame] at hp
      xperm_hyp hp
    case body =>
      -- Invert the semantic result.
      rw [hsf]
      cases hResult with
      | fail hFail =>
        -- status = 1, output cells unchanged.  `bne` taken → parse-fail exit.
        have hbne := bne_spec_gen_within .x10 .x0 (88 : BitVec 13) (1 : Word) (0 : Word)
          (C + 136)
        have hbneC := cpsBranchWithin_extend_code cvedl_mono
          (cpsBranchWithin_extend_code (cr' := cvedlCode)
            (CodeReq.ofProg_mem_at C (C + 136) cvedlProg 34 (.BNE .x10 .x0 (88 : BitVec 13))
              (by bv_omega) (by rw [cvedl_length]; decide) rfl
              (by rw [cvedl_length]; decide)) hbne)
        have htaken := cpsBranchWithin_takenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd ((sepConj_pure_right _).1 hrest).2 (by decide))
        rw [show (C + 136) + signExtend13 (88 : BitVec 13) = C + 224 from by
          rw [show signExtend13 (88 : BitVec 13) = (88 : Word) from by decide]; bv_omega]
          at htaken
        have htakenF := cpsTripleWithin_frameR
          ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x11 ↦ᵣ v11) **
            (.x12 ↦ᵣ v12) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) **
            savedFrame (spC + signExtend12 (-64 : BitVec 12))
              ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)) **
            (firstBadPtr ↦ₘ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
            ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
            ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) (by pcfx) htaken
        have hpfC := cpsTripleWithin_extend_code cvedl_mono
          (retParseFail sp0 spC raIn (BitVec.ofNat 64 i) firstBadPtr csaved
            ((.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) **
              savedFrame (spC + signExtend12 (-64 : BitVec 12))
                ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                  validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
              (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)))
            (by pcfx) (1 : Word) LinkRA (BitVec.ofNat 64 lengths.length) lenBase
            (hdrBaseAt hdrBase lengths i) validPtr hspC hraSaved hret)
        have hcompose := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          have hp1 : ((firstBadPtr ↦ₘ (0 : Word)) **
              ((.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x10 ↦ᵣ (1 : Word)) **
                (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ LinkRA) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                ((.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
                  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
                  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  (COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) **
                  savedFrame (spC + signExtend12 (-64 : BitVec 12))
                    ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                      validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (validPtr ↦ₘ (1 : Word))))) h := by xperm_hyp hp
          have hp2 := sepConj_mono_left memIs_implies_memOwn h hp1
          xperm_hyp hp2) htakenF hpfC
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
          (cpsTripleWithin_mono_nSteps (show 1 + 12 ≤ 25 + nTail by omega) hcompose)
        refine Or.inr (Or.inr ⟨i, ?_⟩)
        refine (sepConj_pure_left h).mpr ⟨⟨hi, hprefix, hFail⟩, ?_⟩
        unfold commonRet payload
        rw [hsf, hraSaved, wordArray_split lenBase lengths i hi,
          EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen, ← hHB]
        have hp1 : ((COff ↦ₘ oldOff) ** (CLen ↦ₘ oldLen) **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
            savedFrame (spC + signExtend12 (-64 : BitVec 12))
              ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
            ((.x10 ↦ᵣ (1 : Word)) ** (validPtr ↦ₘ (1 : Word)) **
              (firstBadPtr ↦ₘ BitVec.ofNat 64 i) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
              (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
              (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
              (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
              regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)))) h := by
          rw [← hLi]; xperm_hyp hq
        have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
            (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
              (sepConj_mono (savedFrame_implies_frameSlotsOwn _ _) (fun _ x => x))))))) h hp1
        xperm_hyp hp2
      | ok _ _ hSucc =>
        -- status = 0.  `bne` not-taken → reload, then length compare.
        set RframeOk : Assertion :=
          ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
            (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
            (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x11 ↦ᵣ v11) **
            (.x12 ↦ᵣ v12) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
            regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
            (COff ↦ₘ offset) ** (CLen ↦ₘ len) **
            savedFrame (spC + signExtend12 (-64 : BitVec 12))
              ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
            (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
            ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
            wordArrayFrom lenBase 0 (lengths.take i) **
            wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
            bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)) **
            (firstBadPtr ↦ₘ (0 : Word)) **
            (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
            ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
            ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) with hRframeOk
        have hbne := bne_spec_gen_within .x10 .x0 (88 : BitVec 13) (0 : Word) (0 : Word)
          (C + 136)
        have hbneC := cpsBranchWithin_extend_code cvedl_mono
          (cpsBranchWithin_extend_code (cr' := cvedlCode)
            (CodeReq.ofProg_mem_at C (C + 136) cvedlProg 34 (.BNE .x10 .x0 (88 : BitVec 13))
              (by bv_omega) (by rw [cvedl_length]; decide) rfl
              (by rw [cvedl_length]; decide)) hbne)
        have hntaken := cpsBranchWithin_ntakenStripPure2 hbneC (fun hp hq => by
          obtain ⟨_, _, _, _, _, hrest⟩ := hq
          exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
        rw [show (C + 136 + 4 : Word) = C + 140 from by bv_omega] at hntaken
        -- Continue arm from `C+140`.
        have hcont : cpsTripleWithin (24 + nTail) (C + 140) raIn fullCode
            (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) ** RframeOk)
            (cvedlPost sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase
              validPtr firstBadPtr csaved bigBytes lengths) := by
          rw [hRframeOk]
          refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
            (show cpsTripleWithin (24 + nTail) (C + 140) raIn fullCode
              (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) **
                (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) **
                (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x19 ↦ᵣ validPtr) **
                (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) ** (.x11 ↦ᵣ v11) **
                (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
                bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                (COff ↦ₘ offset) ** (CLen ↦ₘ len) **
                savedFrame (spC + signExtend12 (-64 : BitVec 12))
                  ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                    validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
                (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                wordArrayFrom lenBase 0 (lengths.take i) **
                wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)) **
                (firstBadPtr ↦ₘ (0 : Word)) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5)) **
                regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
                regOwn .x30 ** regOwn .x31)
              (cvedlPost sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) from ?_)
          refine EvmAsm.Codegen.RlpListNthItemSAsm.cpsTripleWithin_of_forall_regIs_to_regOwn7
            (fun v5 v6 v7 v28 v29 v30 v31 => ?_)
          set Rreload : Assertion :=
            ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x9 ↦ᵣ lenBase) ** (.x19 ↦ᵣ validPtr) **
              (.x20 ↦ᵣ firstBadPtr) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 **
              regOwn .x14 **
              bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
              (COff ↦ₘ offset) **
              savedFrame (spC + signExtend12 (-64 : BitVec 12))
                ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                  validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
              ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
              wordArrayFrom lenBase 0 (lengths.take i) **
              wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
              bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)) **
              (firstBadPtr ↦ₘ (0 : Word)) **
              (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
              ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
              ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
              (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) with hRreload
          set Rstate2 : Assertion :=
            ((.x5 ↦ᵣ CLen) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
              (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
              (CLen ↦ₘ len)) ** Rreload with hRstate2
          have hreload := cpsTripleWithin_extend_code cvedl_mono
            (cvedlReload (hdrBaseAt hdrBase lengths i) (BitVec.ofNat 64 i) len v5
              (hdrBaseAt hdrBase lengths i) (BitVec.ofNat 64 i) v6 v7)
          have hreloadF := cpsTripleWithin_frameR Rreload (by rw [hRreload]; pcfx) hreload
          have hbltu := bltu_spec_gen_within .x7 .x6 (28 : BitVec 13) (32 : Word) len (C + 180)
          rw [show (C + 180) + signExtend13 (28 : BitVec 13) = C + 208 from by
            rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega] at hbltu
          have hbltuC := cpsBranchWithin_extend_code cvedl_mono
            (cpsBranchWithin_extend_code (cr' := cvedlCode)
              (CodeReq.ofProg_mem_at C (C + 180) cvedlProg 45 (.BLTU .x7 .x6 (28 : BitVec 13))
                (by bv_omega) (by rw [cvedl_length]; decide) rfl
                (by rw [cvedl_length]; decide)) hbltu)
          have hbltuF := cpsBranchWithin_frameR Rstate2 (by rw [hRstate2, hRreload]; pcfx) hbltuC
          have hbranch := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
            (fun h hp => by rw [hRstate2]; xperm_hyp hp) hreloadF hbltuF
          have h_t : cpsTripleWithin (13 + nTail) (C + 208) raIn fullCode
              (((.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** ⌜BitVec.ult (32 : Word) len⌝) ** Rstate2)
              (cvedlPost sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) := by
            rw [hRstate2, hRreload]
            refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
              (cpsTripleWithin_pure_pre (P := BitVec.ult (32 : Word) len)
                (H := (.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ CLen) **
                  (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  (CLen ↦ₘ len) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                  (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                  (.x9 ↦ᵣ lenBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
                  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  (COff ↦ₘ offset) **
                  savedFrame (spC + signExtend12 (-64 : BitVec 12))
                    ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                      validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)) **
                  (firstBadPtr ↦ₘ (0 : Word)) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
                (fun hult => ?_))
            have hviol := cpsTripleWithin_extend_code cvedl_mono
              (retViolation sp0 spC raIn (BitVec.ofNat 64 i) validPtr firstBadPtr csaved
                ((.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ CLen) **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  (CLen ↦ₘ len) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  (COff ↦ₘ offset) **
                  savedFrame (spC + signExtend12 (-64 : BitVec 12))
                    ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                      validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
                (by pcfx) (0 : Word) LinkRA (BitVec.ofNat 64 lengths.length) lenBase
                (hdrBaseAt hdrBase lengths i) hspC hraSaved hret)
            refine cpsTripleWithin_weaken (fun h hp => by
              have hp1 : ((validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                  ((.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
                    (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x2 ↦ᵣ spC) **
                    (.x1 ↦ᵣ LinkRA) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                    (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) **
                    (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                    ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                    ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                    ((.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ CLen) **
                      (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                      (CLen ↦ₘ len) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 **
                      regOwn .x14 **
                      bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                      (COff ↦ₘ offset) **
                      savedFrame (spC + signExtend12 (-64 : BitVec 12))
                        ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase,
                          hdrBaseAt hdrBase lengths i, validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
                      ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                      wordArrayFrom lenBase 0 (lengths.take i) **
                      wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                      bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)))) h := by
                xperm_hyp hp
              have hp2 := sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn (fun _ x => x)) h hp1
              xperm_hyp hp2) (fun h hq => ?_)
              (cpsTripleWithin_mono_nSteps (show 13 ≤ 13 + nTail by omega) hviol)
            refine Or.inr (Or.inl ⟨i, ?_⟩)
            refine (sepConj_pure_left h).mpr ⟨⟨hi, hprefix, ⟨offset, len, hSucc, hult⟩⟩, ?_⟩
            unfold commonRet payload
            rw [hsf, hraSaved, wordArray_split lenBase lengths i hi,
              EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen, ← hHB]
            have hp1 : ((.x5 ↦ᵣ CLen) ** (.x6 ↦ᵣ len) ** (.x7 ↦ᵣ (32 : Word)) ** (.x11 ↦ᵣ v11) **
                (.x12 ↦ᵣ v12) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
                (.x31 ↦ᵣ v31) ** (COff ↦ₘ offset) ** (CLen ↦ₘ len) **
                (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                savedFrame (spC + signExtend12 (-64 : BitVec 12))
                  ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                    validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
                ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
                  (firstBadPtr ↦ₘ BitVec.ofNat 64 i) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
                  (.x8 ↦ᵣ csaved.s0) ** (.x9 ↦ᵣ csaved.s1) ** (.x18 ↦ᵣ csaved.s2) **
                  (.x19 ↦ᵣ csaved.s3) ** (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  (.x0 ↦ᵣ (0 : Word)) ** regOwn .x13 ** regOwn .x14 **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)))) h := by
              rw [← hLi]; xperm_hyp hq
            have hp2 := sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono
              (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x7)
              (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
              (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
              (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x31)
              (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
              (sepConj_mono (savedFrame_implies_frameSlotsOwn _ _)
              (fun _ x => x)))))))))))))) h hp1
            xperm_hyp hp2
          have h_f : cpsTripleWithin (13 + nTail) (C + 184) raIn fullCode
              (((.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** ⌜¬ BitVec.ult (32 : Word) len⌝) ** Rstate2)
              (cvedlPost sp0 spC (spC + signExtend12 (-64 : BitVec 12)) hdrBase lenBase
                validPtr firstBadPtr csaved bigBytes lengths) := by
            rw [hRstate2, hRreload]
            refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
              (cpsTripleWithin_pure_pre (P := ¬ BitVec.ult (32 : Word) len)
                (H := (.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ CLen) **
                  (.x18 ↦ᵣ hdrBaseAt hdrBase lengths i) ** (.x21 ↦ᵣ BitVec.ofNat 64 i) **
                  (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                  (CLen ↦ₘ len) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                  (.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                  (.x9 ↦ᵣ lenBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
                  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
                  bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                  (COff ↦ₘ offset) **
                  savedFrame (spC + signExtend12 (-64 : BitVec 12))
                    ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                      validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
                  ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                  wordArrayFrom lenBase 0 (lengths.take i) **
                  wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                  bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)) **
                  (firstBadPtr ↦ₘ (0 : Word)) **
                  (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                  ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                  ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
                (fun hnult => ?_))
            have hprefix' : ∀ j, j < i + 1 → hdrValidShort hdrBase bigBytes lengths j := by
              intro j hj
              rcases (by omega : j < i ∨ j = i) with hlt | heq
              · exact hprefix j hlt
              · subst heq; exact ⟨offset, len, hSucc, hnult⟩
            have hadv := cpsTripleWithin_extend_code cvedl_mono
              (cvedlAdvance (hdrBaseAt hdrBase lengths i) lenBase (BitVec.ofNat 64 i)
                lengths[i]! v28 v29)
            rw [shiftLeft3_ofNat i] at hadv
            have hadvF := cpsTripleWithin_frameR
              ((.x7 ↦ᵣ (32 : Word)) ** (.x6 ↦ᵣ len) ** (.x5 ↦ᵣ CLen) **
                (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                (CLen ↦ₘ len) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkRA) **
                (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) ** (.x19 ↦ᵣ validPtr) **
                (.x20 ↦ᵣ firstBadPtr) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 **
                regOwn .x14 **
                bytesRegion (hdrBaseAt hdrBase lengths i) (bigBytes.drop (hdrOff lengths i)) **
                (COff ↦ₘ offset) **
                savedFrame (spC + signExtend12 (-64 : BitVec 12))
                  ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase, hdrBaseAt hdrBase lengths i,
                    validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
                wordArrayFrom lenBase 0 (lengths.take i) **
                wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) ** (validPtr ↦ₘ (1 : Word)) **
                (firstBadPtr ↦ₘ (0 : Word)) **
                (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) (by pcfx) hadv
            refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
              (cpsTripleWithin_mono_nSteps (show 6 + nTail ≤ 13 + nTail by omega)
                (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
                  unfold LoopInv payload scratchRegs
                  rw [hsf, wordArray_split lenBase lengths i hi,
                    EvmAsm.Evm64.bytesRegion_split hdrBase bigBytes (hdrOff lengths i) halign hlen,
                    ← hHB, hdrBaseAt_succ hdrBase lengths i hi, ← ofNat_succ_tie i, ← hLi]
                  have hp1 : ((.x1 ↦ᵣ LinkRA) ** (.x5 ↦ᵣ CLen) ** (.x6 ↦ᵣ len) **
                      (.x7 ↦ᵣ (32 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
                      (.x12 ↦ᵣ v12) ** (.x28 ↦ᵣ (lenBase + BitVec.ofNat 64 (8 * i))) **
                      (.x29 ↦ᵣ BitVec.ofNat 64 lengths[i]!) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
                      (COff ↦ₘ offset) ** (CLen ↦ₘ len) **
                      (IterPtr ↦ₘ hdrBaseAt hdrBase lengths i) ** (IterI ↦ₘ BitVec.ofNat 64 i) **
                      savedFrame (spC + signExtend12 (-64 : BitVec 12))
                        ⟨LinkRA, BitVec.ofNat 64 lengths.length, lenBase,
                          hdrBaseAt hdrBase lengths i, validPtr, firstBadPtr, BitVec.ofNat 64 i⟩ **
                      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ BitVec.ofNat 64 lengths.length) **
                        (.x9 ↦ᵣ lenBase) **
                        (.x18 ↦ᵣ (hdrBaseAt hdrBase lengths i + BitVec.ofNat 64 lengths[i]!)) **
                        (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) **
                        (.x21 ↦ᵣ (BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12))) **
                        (validPtr ↦ₘ (1 : Word)) ** (firstBadPtr ↦ₘ (0 : Word)) **
                        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ csaved.s0) ** ((spC + 16) ↦ₘ csaved.s1) **
                        ((spC + 24) ↦ₘ csaved.s2) ** ((spC + 32) ↦ₘ csaved.s3) **
                        ((spC + 40) ↦ₘ csaved.s4) ** ((spC + 48) ↦ₘ csaved.s5) **
                        regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
                        wordArrayFrom lenBase 0 (lengths.take i) **
                        ((lenBase + BitVec.ofNat 64 (8 * i)) ↦ₘ BitVec.ofNat 64 lengths[i]!) **
                        wordArrayFrom lenBase (i + 1) (lengths.drop (i + 1)) **
                        bytesRegion hdrBase (bigBytes.take (hdrOff lengths i)) **
                        bytesRegion (hdrBaseAt hdrBase lengths i)
                          (bigBytes.drop (hdrOff lengths i)))) h := by
                    xperm_hyp hp
                  have hp2 := sepConj_mono (regIs_implies_regOwn .x1) (sepConj_mono
                    (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
                    (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x10)
                    (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
                    (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
                    (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x31)
                    (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
                    (sepConj_mono (savedFrame_implies_frameSlotsOwn _ _)
                    (fun _ x => x)))))))))))))))) h hp1
                  xperm_hyp hp2) hadvF (htail hprefix')))
          refine cpsTripleWithin_weaken (fun h hp => by rw [hRreload]; xperm_hyp hp)
            (fun _ hq => hq)
            (cpsTripleWithin_mono_nSteps (show 10 + 1 + (13 + nTail) ≤ 24 + nTail by omega)
              (cpsBranchWithin_merge_same_cr hbranch h_t h_f))
        have hntakenF := cpsTripleWithin_frameR RframeOk (by rw [hRframeOk]; pcfx) hntaken
        refine cpsTripleWithin_weaken (fun h hp => by rw [hRframeOk]; xperm_hyp hp)
          (fun _ hq => hq)
          (cpsTripleWithin_mono_nSteps (show 1 + (24 + nTail) ≤ 25 + nTail by omega)
            (cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hntakenF hcont))

end EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
