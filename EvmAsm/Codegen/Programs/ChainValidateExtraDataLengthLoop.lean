/-
  Per-iteration body + loop induction for `chain_validate_extra_data_length`.

  Builds on `ChainValidateExtraDataLengthSpec` (model, prologue, epilogue, exit
  blocks, `wordArray_split`) to prove the loop body `[C+72 … C+204]`, the loop
  induction `cvedlLoop` (on `N − i`), and the whole-program caller contract
  `chain_validate_extra_data_length_spec_within`.
-/

import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec

namespace EvmAsm.Codegen.ChainValidateExtraDataLengthSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm


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

end EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
