/-
  Per-iteration composition for `chain_validate_post_merge_full`.

  This file deliberately stays separate from the existing exit-path contract:
  the latter pins every machine arm, while this module supplies the first
  caller-to-callee composition needed to start the nonempty loop proof.
-/

import EvmAsm.Codegen.Programs.ChainValidatePostMergeFullSpec
import EvmAsm.Codegen.Programs.RlpFieldToU64StrictFlatSAsm
import EvmAsm.Codegen.Programs.RlpFieldToU64FlatSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemSAsm
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Codegen.Programs.ChainValidateOfflineAddrs

namespace EvmAsm.Codegen.ChainValidatePostMergeFullLoop

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm
  (Saved savedFrame savedVals listNthFrame regsAt_listNthFrame
   frameSlotsSaved_listNthFrame)
open EvmAsm.Codegen.ChainValidatePostMergeFullSpec

abbrev D : Word := (ChainValidateOfflineAddrs.chain_validate_post_merge_full : Word)
abbrev cvpmfProg : Program := EvmAsm.Codegen.chainValidatePostMergeFull_prog
abbrev cvpmfCode : CodeReq := CodeReq.ofProg D cvpmfProg
abbrev IterPtr : Word := (GuestAddrs.cvpmf_iter_ptr : Word)
abbrev IterI : Word := (GuestAddrs.cvpmf_iter_i : Word)
abbrev Field : Word := (GuestAddrs.cvpmf_field : Word)
abbrev LinkRA : Word := D + 128
abbrev RfuOff : Word := (GuestAddrs.rfu_offset : Word)
abbrev RfuLen : Word := (GuestAddrs.rfu_length : Word)

/-- K34's whole-routine step count for the first field call. -/
def nCall (index _bytesLen : Nat) : Nat :=
  (7 + 4 + (1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)))
    + ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5)

/-! The first call is enough to expose the nonempty-loop composition shape. -/

def firstCallCode : CodeReq :=
  cvpmfCode.union EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code

set_option maxRecDepth 8000 in
theorem firstCall_disjoint :
    cvpmfCode.Disjoint EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code := by
  unfold cvpmfCode EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wrapperCode
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.contentCode
  refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.union_right ?_ ?_)
  · apply CodeReq.Disjoint.ofProg_ranges
    · decide
    · decide
    · decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · decide
    · decide
    · decide
  · unfold EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_code
    apply CodeReq.Disjoint.ofProg_ranges <;> decide

theorem cvpmf_mono : ∀ a i, cvpmfCode a = some i → firstCallCode a = some i := by
  intro a i hi
  exact CodeReq.union_mono_left a i hi

theorem strict_mono : ∀ a i,
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code a = some i →
      firstCallCode a = some i := by
  intro a i hi
  exact CodeReq.mono_union_right firstCall_disjoint (fun _ _ h => h) a i hi

set_option maxRecDepth 8000 in
theorem firstSetup
    (spC lenBase hdrBase iWord : Word) (Li : Nat)
    (old5 o10 o11 o12 o13 o28 : Word) :
    cpsTripleWithin 13 (D + 72) (D + 124) cvpmfCode
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
        (.x21 ↦ᵣ iWord) ** (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) **
        (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) ** (.x13 ↦ᵣ o13) **
        (.x28 ↦ᵣ o28) ** memOwn IterPtr ** memOwn IterI **
        ((lenBase + (iWord <<< 3)) ↦ₘ BitVec.ofNat 64 Li))
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
        (.x21 ↦ᵣ iWord) ** (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ hdrBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (7 : Word)) ** (.x13 ↦ᵣ Field) **
        (.x28 ↦ᵣ (lenBase + (iWord <<< 3))) ** (IterPtr ↦ₘ hdrBase) **
        (IterI ↦ₘ iWord) **
        ((lenBase + (iWord <<< 3)) ↦ₘ BitVec.ofNat 64 Li)) := by
  have hla18 := la_materialize_within .x5 old5 (D + 72) IterPtr
    (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 72) cvpmfProg 18
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 72) IterPtr))
      (by bv_omega) (by rw [cvpmf_length]; decide) rfl
      (by rw [cvpmf_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 76) cvpmfProg 19
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 72) IterPtr))
      (by bv_omega) (by rw [cvpmf_length]; decide) rfl
      (by rw [cvpmf_length]; decide))
  have s20 := sd_spec_gen_own_within .x5 .x18 IterPtr hdrBase
    (0 : BitVec 12) (D + 80)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterPtr + (0 : Word) = IterPtr from by bv_omega] at s20
  have s20' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 80) cvpmfProg 20
      (.SD .x5 .x18 (0 : BitVec 12)) (by bv_omega)
      (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)) s20
  have hla21 := la_materialize_within .x5 IterPtr (D + 84) IterI
    (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 84) cvpmfProg 21
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (D + 84) IterI))
      (by bv_omega) (by rw [cvpmf_length]; decide) rfl
      (by rw [cvpmf_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 88) cvpmfProg 22
      (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (D + 84) IterI))
      (by bv_omega) (by rw [cvpmf_length]; decide) rfl
      (by rw [cvpmf_length]; decide))
  have s23 := sd_spec_gen_own_within .x5 .x21 IterI iWord
    (0 : BitVec 12) (D + 92)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s23
  have s23' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 92) cvpmfProg 23
      (.SD .x5 .x21 (0 : BitVec 12)) (by bv_omega)
      (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)) s23
  have s24 := slli_spec_gen_within .x28 .x21 o28 iWord
    (3 : BitVec 6) (D + 96) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide] at s24
  have s24' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 96) cvpmfProg 24
      (.SLLI .x28 .x21 (3 : BitVec 6)) (by bv_omega)
      (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)) s24
  have s25 := add_spec_gen_rd_eq_rs2_within .x28 .x9 lenBase
    (iWord <<< 3) (D + 100) (by decide)
  have s25' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 100) cvpmfProg 25
      (.ADD .x28 .x9 .x28) (by bv_omega)
      (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)) s25
  have s26 := ld_spec_gen_within .x11 .x28 (lenBase + (iWord <<< 3))
    o11 (BitVec.ofNat 64 Li) (0 : BitVec 12) (D + 104) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (lenBase + (iWord <<< 3)) + (0 : Word) = lenBase + (iWord <<< 3)
      from by bv_omega] at s26
  have s26' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 104) cvpmfProg 26
      (.LD .x11 .x28 (0 : BitVec 12)) (by bv_omega)
      (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)) s26
  have s27 := mv_spec_gen_within .x10 .x18 hdrBase o10 (D + 108) (by decide)
  have s27' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 108) cvpmfProg 27
      (.MV .x10 .x18) (by bv_omega)
      (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)) s27
  have s28 := li_spec_gen_within .x12 o12 (7 : Word) (D + 112) (by decide)
  have s28' := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 112) cvpmfProg 28
      (.LI .x12 (7 : Word)) (by bv_omega)
      (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)) s28
  have hla29 := la_materialize_within .x13 o13 (D + 116) Field
    (by decide) (by decide)
    (CodeReq.ofProg_mem_at D (D + 116) cvpmfProg 29
      (.AUIPC .x13 (EvmAsm.Rv64.laHi (D + 116) Field))
      (by bv_omega) (by rw [cvpmf_length]; decide) rfl
      (by rw [cvpmf_length]; decide))
    (CodeReq.ofProg_mem_at D (D + 120) cvpmfProg 30
      (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (D + 116) Field))
      (by bv_omega) (by rw [cvpmf_length]; decide) rfl
      (by rw [cvpmf_length]; decide))
  runBlock hla18 s20' hla21 s23' s24' s25' s26' s27' s28' hla29

/-! The first nonempty-loop call, with K34's strict field-7 result exposed.

This is intentionally a call-site composition lemma rather than a claim that
the complete loop is closed.  Its precondition is the static K34 byte-window
envelope; the post retains K34's success/failure disjunction for the caller's
status branch to consume.
-/

set_option maxRecDepth 8000 in
theorem firstCall
    (hdrBase lenBase spC iWord : Word) (Li : Nat)
    (nN s3 s4 oldOut oldOff oldLen old14 oldX1 old5 o10 o11 o12 o13 o28 : Word)
    (bytes : List (BitVec 8)) (csaved : Saved)
    (hsalign : hdrBase.toNat % 8 = 0)
    (hbytes : Li ≤ bytes.length)
    (hnowrap : hdrBase.toNat + Li + 9 < 2 ^ 64)
    (hover : hdrBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (hdrBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length) :
    cpsTripleWithin (13 + 1 + nCall 7 bytes.length) (D + 72) LinkRA firstCallCode
      ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x21 ↦ᵣ iWord) **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ o10) ** (.x11 ↦ᵣ o11) ** (.x12 ↦ᵣ o12) **
        (.x13 ↦ᵣ o13) ** (.x28 ↦ᵣ o28) **
        memOwn IterPtr ** memOwn IterI **
        ((lenBase + (iWord <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
        (.x1 ↦ᵣ oldX1) ** (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame
          (spC + signExtend12 (-32 : BitVec 12)) **
        stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 **
        (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        bytesRegion hdrBase bytes ** savedFrame spC csaved)
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC
          (spC + signExtend12 (-32 : BitVec 12)) hdrBase oldOff oldLen
          (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hdrBase, Field,
            hdrBase, s3, s4, iWord⟩ : Saved)
          bytes Li 7 **
        (IterPtr ↦ₘ hdrBase) ** (IterI ↦ₘ iWord) **
        ((lenBase + (iWord <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved) := by
  set calleeNewSp : Word := spC + signExtend12 (-32 : BitVec 12) with hcalleeNewSp
  have hsetup := cpsTripleWithin_extend_code cvpmf_mono
    (firstSetup spC lenBase hdrBase iWord Li old5 o10 o11 o12 o13 o28)
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ oldX1) ** (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hdrBase bytes ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
                      | exact bytesRegion_pcFree _ _) hsetup
  have hjal := jal_link_spec_within
    (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64_strict
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 124)) (D + 124) oldX1
  rw [show (D + 124) + signExtend21 (EvmAsm.Codegen.jalOff
      GuestAddrs.rlp_field_to_u64_strict
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 124)) =
      EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B by
    change BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 124 + _ =
      BitVec.ofNat 64 GuestAddrs.rlp_field_to_u64_strict
    exact jalOff_correct_add GuestAddrs.rlp_field_to_u64_strict
      ChainValidateOfflineAddrs.chain_validate_post_merge_full 124
      (by decide) (by decide) (by decide) (by decide),
    show (D + 124 + 4 : Word) = LinkRA from by
      change (D + 124 + 4 : Word) = D + 128; bv_omega] at hjal
  have hjalC := cpsTripleWithin_extend_code cvpmf_mono
    (cpsTripleWithin_extend_code (cr' := cvpmfCode)
      (CodeReq.ofProg_mem_at D (D + 124) cvpmfProg 31
        (.JAL .x1 (EvmAsm.Codegen.jalOff GuestAddrs.rlp_field_to_u64_strict
          (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 124))) (by bv_omega)
        (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)) hjal)
  have hjalF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) ** (.x21 ↦ᵣ iWord) **
      (.x5 ↦ᵣ IterI) ** (.x10 ↦ᵣ hdrBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
      (.x12 ↦ᵣ (7 : Word)) ** (.x13 ↦ᵣ Field) **
      (.x28 ↦ᵣ (lenBase + (iWord <<< 3))) ** (IterPtr ↦ₘ hdrBase) **
      (IterI ↦ₘ iWord) ** ((lenBase + (iWord <<< 3)) ↦ₘ BitVec.ofNat 64 Li) **
      (.x8 ↦ᵣ nN) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x14 ↦ᵣ old14) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word)) **
      frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
      stackFree calleeNewSp 8 **
      (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
      bytesRegion hdrBase bytes ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
                      | exact pcFree_memIs | exact pcFree_memOwn
                      | exact pcFree_frameSlotsOwn _ _ | exact pcFree_stackFree _ _
                      | exact bytesRegion_pcFree _ _) hjalC
  have hcallee0 := EvmAsm.Codegen.RlpFieldToU64StrictSAsm.rlpFieldToU64_flat_spec_within
    spC calleeNewSp hdrBase (BitVec.ofNat 64 Li) (7 : Word) Field oldOut oldOff oldLen old14
    (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
    hdrBase s3 s4 iWord bytes Li 7 hcalleeNewSp rfl (by decide) (by decide)
    hsalign hbytes hnowrap hover hvalid hnz (by show LinkRA &&& ~~~(1 : Word) = LinkRA; decide)
  have hcalleeC := cpsTripleWithin_extend_code strict_mono hcallee0
  have hcallee : cpsTripleWithin (nCall 7 bytes.length)
      EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B LinkRA firstCallCode
      (regOwn .x5 ** regOwn .x28 **
        ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
          (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ iWord) **
          (.x10 ↦ᵣ hdrBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) **
          (.x12 ↦ᵣ (7 : Word)) ** (.x13 ↦ᵣ Field) ** (.x14 ↦ᵣ old14) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) ** frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
          stackFree calleeNewSp 8 ** bytesRegion hdrBase bytes **
          (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen)))
      ((.x1 ↦ᵣ LinkRA) **
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC calleeNewSp hdrBase oldOff oldLen
          (⟨LinkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
          (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hdrBase, Field,
            hdrBase, s3, s4, iWord⟩ : Saved) bytes Li 7) :=
    cpsTripleWithin_weaken (fun h hp => by
      unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPre
        EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wholeRest
      xperm_hyp hp) (fun _ hq => hq) hcalleeC
  have hcalleeF := cpsTripleWithin_frameR
    ((IterPtr ↦ₘ hdrBase) ** (IterI ↦ₘ iWord) **
      ((lenBase + (iWord <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)
    (by repeat' first | apply pcFree_sepConj | exact pcFree_memIs) hcallee
  have hsj := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsetupF hjalF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => ?_) hsj hcalleeF)
  have hp' : ((.x5 ↦ᵣ IterI) ** (.x28 ↦ᵣ (lenBase + (iWord <<< 3))) **
      ((.x1 ↦ᵣ LinkRA) ** (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ iWord) **
        (.x10 ↦ᵣ hdrBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 Li) ** (.x12 ↦ᵣ (7 : Word)) **
        (.x13 ↦ᵣ Field) ** (.x14 ↦ᵣ old14) ** regOwn .x6 ** regOwn .x7 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        frameSlotsOwn EvmAsm.Codegen.RlpFieldToU64StrictSAsm.frame calleeNewSp **
        stackFree calleeNewSp 8 ** bytesRegion hdrBase bytes **
        (Field ↦ₘ oldOut) ** (RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) **
        (IterPtr ↦ₘ hdrBase) ** (IterI ↦ₘ iWord) **
        ((lenBase + (iWord <<< 3)) ↦ₘ BitVec.ofNat 64 Li) ** savedFrame spC csaved)) h := by
    xperm_hyp hp
  have hp'' := sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)) h hp'
  xperm_hyp hp''

/-! Normalize the K34 post for field 7.  The loop's `bne x10, x0` consumes
    the status, while the later difficulty check consumes the `Field` value;
    keeping the semantic `Result` beside both is what makes those two uses
    independent of the representation of K34's two machine-return arms. -/

def dispNorm (spC calleeNewSp hbi validPtr firstBadPtr nN lenBase iW linkRA cell value status : Word)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) **
  (.x18 ↦ᵣ hbi) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iW) **
  (.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (cell ↦ₘ value) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  memOwn RfuOff ** memOwn RfuLen ** stackFree calleeNewSp 8 **
  bytesRegion hbi bytes **
  EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame calleeNewSp ⟨linkRA, nN, lenBase⟩

set_option maxRecDepth 8000 in
theorem firstCall_normalize
    (spC hbi validPtr firstBadPtr nN lenBase iW linkRA cell oldOff oldLen : Word)
    (bytes : List (BitVec 8)) (Li : Nat) : ∀ h,
    (EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost spC
      (spC + signExtend12 (-32 : BitVec 12)) hbi oldOff oldLen
      (⟨linkRA, nN, lenBase⟩ : EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Saved)
      (⟨EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B + 48, hbi, cell, hbi,
        validPtr, firstBadPtr, iW⟩ : Saved) bytes Li 7) h →
    (∃ status value,
      (dispNorm spC (spC + signExtend12 (-32 : BitVec 12)) hbi validPtr firstBadPtr
          nN lenBase iW linkRA cell value status bytes **
        ⌜EvmAsm.Codegen.RlpFieldToU64StrictSAsm.Result bytes hbi Li 7 status value⌝) h) := by
  intro h hp
  unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatPost at hp
  rcases hp with hs | hf
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatSuccessReturned at hs
    obtain ⟨offset, len, v12, x5v, scalarStatus, wrapperStatus, outputValue, hs⟩ := hs
    unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.successPayload at hs
    refine ⟨wrapperStatus, outputValue, ?_⟩
    obtain ⟨h1, h2, hd, hu, hO, hP⟩ := hs
    obtain ⟨hBig, hRes⟩ := (sepConj_pure_right _).1 hP
    refine (sepConj_pure_right _).2 ⟨?_, hRes⟩
    have hOB : (_ ** _) h := ⟨h1, h2, hd, hu, hO, hBig⟩
    unfold dispNorm
    have hp1 : ((RfuOff ↦ₘ offset) ** (RfuLen ↦ₘ len) ** (.x5 ↦ᵣ x5v) **
        (.x11 ↦ᵣ scalarStatus) ** (.x12 ↦ᵣ v12) **
        ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) **
          (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iW) **
          (.x10 ↦ᵣ wrapperStatus) ** (.x0 ↦ᵣ (0 : Word)) ** (cell ↦ₘ outputValue) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hbi bytes **
          EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame
            (spC + signExtend12 (-32 : BitVec 12)) ⟨linkRA, nN, lenBase⟩)) h := by
      xperm_hyp hOB
    have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x))))) h hp1
    xperm_hyp hp2
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.flatFailureReturned at hf
    obtain ⟨v11, v12, hf⟩ := hf
    unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.failurePayload at hf
    refine ⟨(1 : Word), (0 : Word), ?_⟩
    obtain ⟨h1, h2, hd, hu, hO, hP⟩ := hf
    obtain ⟨hBig, hRes⟩ := (sepConj_pure_right _).1 hP
    refine (sepConj_pure_right _).2 ⟨?_, hRes⟩
    have hOB : (_ ** _) h := ⟨h1, h2, hd, hu, hO, hBig⟩
    unfold dispNorm
    have hp1 : ((RfuOff ↦ₘ oldOff) ** (RfuLen ↦ₘ oldLen) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) **
        ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ nN) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hbi) **
          (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ firstBadPtr) ** (.x21 ↦ᵣ iW) **
          (.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (cell ↦ₘ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree (spC + signExtend12 (-32 : BitVec 12)) 8 ** bytesRegion hbi bytes **
          EvmAsm.Codegen.RlpFieldToU64StrictSAsm.savedFrame
            (spC + signExtend12 (-32 : BitVec 12)) ⟨linkRA, nN, lenBase⟩)) h := by
      xperm_hyp hOB
    have hp2 := sepConj_mono memIs_implies_memOwn (sepConj_mono memIs_implies_memOwn
      (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x12)
        (fun _ x => x)))) h hp1
    xperm_hyp hp2

/-! The status arm is intentionally gated by the static fact `status ≠ 0`.
    It closes only the propagation branch; the zero-status continuation is
    deliberately left for the later field-value and ommers checks. -/

set_option maxRecDepth 8000 in
theorem statusBranch
    (status : Word) (hstatus : status ≠ 0) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 1 (D + 128) (D + 536) firstCallCode
      ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** R)
      ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** R) := by
  have hbne := bne_spec_gen_within .x10 .x0
    (EvmAsm.Codegen.brOff
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 536)
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 128)) status (0 : Word) (D + 128)
  rw [show (D + 128) + signExtend13 (EvmAsm.Codegen.brOff
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 536)
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 128)) = D + 536 from by
    change BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 128 + _ =
      BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 536
    exact brOff_correct_base_off ChainValidateOfflineAddrs.chain_validate_post_merge_full 128 536
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at hbne
  have hbneC := cpsBranchWithin_extend_code cvpmf_mono
    (cpsBranchWithin_extend_code (cr' := cvpmfCode)
      (CodeReq.ofProg_mem_at D (D + 128) cvpmfProg 32
        (.BNE .x10 .x0 (EvmAsm.Codegen.brOff
          (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 536)
          (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 128))) (by bv_omega)
        (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)) hbne)
  have hbneF := cpsBranchWithin_frameR R hR hbneC
  have htaken := cpsBranchWithin_takenPath hbneF (fun hq hfalse => by
    obtain ⟨_, _, _, _, hstatus0, _⟩ := hfalse
    obtain ⟨_, _, _, _, _, hrest⟩ := hstatus0
    have hzero : status = (0 : Word) :=
      (sepConj_pure_right (P := (.x0 ↦ᵣ (0 : Word))) (Q := status = 0) _).1 hrest |>.2
    exact hstatus hzero)
  exact cpsTripleWithin_weaken
    (fun h hp => (sepConj_assoc h).mpr hp)
    (fun h hq =>
      (sepConj_assoc h).mp
        (sepConj_mono_left
          (P := ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜status ≠ 0⌝))
          (P' := ((.x10 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)))) (Q := R)
          (fun h' hp => sepConj_strip_pure_end2 h' hp) h hq)) htaken


/-! ## Anti-vacuity cover (#12476)

    The old `hslack` (`Li + 9 ≤ bytes.length`) was unsatisfiable on every
    exact-fit slice (`Li = |bytes|`). The repaired premise *set* of `firstCall`
    is jointly inhabited on that shape. -/

/-- Exact-fit nonempty cover: `Li = 48`, `|bytes| = 48`, `hdrBase = MEM_START`. -/
example :
    let Li := 48
    let bytes : List (BitVec 8) := List.replicate 48 (0 : BitVec 8)
    let hdrBase : Word := BitVec.ofNat 64 MEM_START
    (hdrBase.toNat % 8 = 0) ∧
    (Li ≤ bytes.length) ∧
    (hdrBase.toNat + Li + 9 < 2 ^ 64) ∧
    (hdrBase.toNat + bytes.length < 2 ^ 64) ∧
    (0 < bytes.length) ∧
    (∀ k, k < bytes.length →
      isValidByteAccess (hdrBase + BitVec.ofNat 64 k) = true) := by
  refine ⟨?hsalign, ?hbytes, ?hnowrap, ?hover, ?hnz, ?hvalid⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro k hk
    have hk48 : k < 48 := by simpa using hk
    have hsum :
        (BitVec.ofNat 64 MEM_START + BitVec.ofNat 64 k).toNat = 32 + k := by
      simp only [MEM_START]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 32 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 32 + k < 2 ^ 64)]
    simp only [isValidByteAccess, isValidMemAddr, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    refine Or.inl (Or.inl ?_)
    constructor
    · rw [hsum]; change 32 ≤ 32 + k; omega
    · rw [hsum]; change 32 + k ≤ 0x78000000; omega

end EvmAsm.Codegen.ChainValidatePostMergeFullLoop
