/-
  Decrease-route composition toward the Route-B K73 contract (#12346 item 2b).

  The increasing arm ships a fully-composed entry-to-return theorem
  (`k73_increase_entry_status_div_zero_to_return_general_spec_within`).  The
  decreasing arm only ships seams.  This file assembles them bottom-up:

    entry            (19, premise-free)              K73 .. K73 + 84
    mul call/status  (needs deployed mul callee)     K73 + 84 .. K73 + 92
    div pair         (premise-free, htargetPos)      K73 + 92 .. K73 + 124
    branch x20=0     (premise-free)                  K73 + 124 .. K73 + 172
    div-to-sub       (premise-free modulo ABI facts) K73 + 172 .. K73 + 220
    borrow branch                                    K73 + 220 .. K73 + 224
    tails            (symbolic raIn, saved-generic)  K73 + 224/+272 .. raIn

  Everything here composes already-proven seams; no new instruction is
  interpreted.  The borrow branch below is the only machine-level piece that
  was missing entirely: the decrease subtract's overflow test at K73 + 220
  branches on the callee borrow register against x0.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeEntry
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore
import EvmAsm.Rv64.BitAux

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec

/-- Overflow test of the in-place subtraction on the nonzero decrease arm:
    `bne a0, x0, +52` at K73 + 220 sends a nonzero borrow to the shared
    failure exit (li x10, 1 at K73 + 272) and falls through to the successful
    `li x10, 0` at K73 + 224 otherwise.  Value-generalized over the borrowed
    register exactly like the multiply status branch helper. -/
theorem k73_decrease_sub_borrow_branch_spec_within
    (Rest : Assertion) (hRest : Rest.pcFree) :
    cpsBranchWithin 1 (K73 + 220) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 224)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10) := by
  have hraw : ∀ old10 : Word, cpsBranchWithin 1 (K73 + 220) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest) **
        ((.x10 : Reg) ↦ᵣ old10))
      (K73 + 272) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 224) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10) := by
    intro old10
    have hbne := bne_spec_gen_within .x10 .x0 (52 : BitVec 13)
      old10 (0 : Word) (K73 + 220)
    have hbneC := cpsBranchWithin_extend_code
      (k73_whole_mem 55 (.BNE .x10 .x0 (52 : BitVec 13)) (K73 + 220)
        (by decide) (by rw [k73_length]; decide) (by rfl)) hbne
    rw [show signExtend13 (52 : BitVec 13) = (52 : Word) by decide,
      show (K73 + 220) + (52 : Word) = K73 + 272 by bv_omega,
      show (K73 + 220) + 4 = K73 + 224 by bv_omega] at hbneC
    have hbneF := cpsBranchWithin_frameR Rest hRest hbneC
    refine cpsBranchWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => ?_) (fun h hq => ?_) hbneF
    · have hq1 := sepConj_mono_left
        (sepConj_mono_left (regIs_to_regOwn .x10 old10)) h hq
      drop_pure hq1
      sep_perm hq1
    · have hq1 := sepConj_mono_left
        (sepConj_mono_left (regIs_to_regOwn .x10 old10)) h hq
      drop_pure hq1
      sep_perm hq1
  have hbr := cpsBranchWithin_of_forall_regIs_to_regOwn
    (r := .x10) (P := ((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest) hraw
  exact cpsBranchWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) (fun _ hq => by sep_perm hq) hbr

open EvmAsm.Codegen.U256MulU64Be in
/-- Deployed multiply contract specialized to the K73 call site: the callee
    runs at the deployed address, returns to `K73 + 88`, and its assertion
    parameter carries exactly what the decrease seams hand it
    (`v19`-slot := `delta`, `v13`-slot := `outPtr`).  Symbolic-address
    wrapper: alignment / bounds / byte-validity of the two regions stay as
    static premises so no concrete witness is required. -/
theorem k73_mul_callee_at_callsite
    (F : Assertion) (hF : F.pcFree)
    (spOld v8 v9 v18 delta v20 aPtr outPtr : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes outBytes : List (BitVec 8))
    (hlenA : baseBytes.length = 32)
    (hout : outBytes.length = 32)
    (halignA : aPtr.toNat % 8 = 0)
    (hoverA : aPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (aPtr + BitVec.ofNat 64 j) = true)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 3850 (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (EvmAsm.Codegen.U256MulU64Be.mulWholePre F spOld (K73 + 88)
        v8 v9 v18 delta v20 aPtr delta outPtr outPtr
        f0 f1 f2 f3 f4 f5 baseBytes
        (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32) outBytes)
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost
        (spOld + Rv64.signExtend12 (-48 : BitVec 12)) (K73 + 88)
        v8 v9 v18 delta v20 aPtr delta outPtr baseBytes
        (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
        (EvmAsm.Codegen.U256MulU64Be.copyState
          (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
          outBytes 32) ** F) := by
  have hretCall : ((K73 + 88 : Word) &&& ~~~(1 : Word)) = K73 + 88 :=
    EvmAsm.Rv64.BitAux.word_add_even_andn_one (by decide) (by decide)
  exact mulWhole_spec F hF baseBytes
    (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32)
    outBytes hlenA
    (EvmAsm.Codegen.U256MulU64Be.mulState_len baseBytes delta 32)
    hout spOld (K73 + 88) v8 v9 v18 delta v20 aPtr delta outPtr outPtr
    f0 f1 f2 f3 f4 f5 halignA hoverA hvalidA halignOut hoverOut hvalidOut
    hretCall

open EvmAsm.Codegen.U256MulU64Be in
/-- Nonzero decrease entry composed onto the multiply call-and-status stage:
    from K73 the arm runs its 19 premise-free machine steps into the linked
    multiply (whose callee contract arrives as `hcallee` and whose scratch
    frame and accumulator are caller-owned ambient resources, spelled inside
    the head precondition through `F`), and both overflow outcomes surface as
    the shared two-way branch exits at K73 + 92 / K73 + 272. -/
theorem k73_decrease_entry_mul_status_spec_within
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (G : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hnotlt : ¬ target.toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hG : G.pcFree)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (EvmAsm.Codegen.U256MulU64Be.mulWholePre
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19 v20) ** G)
        spH (K73 + 88) basePtr outPtr target (target - gasUsed) (0 : Word)
        basePtr (target - gasUsed) outPtr outPtr f0 f1 f2 f3 f4 f5
        baseBytes accBytes outBytes)
      (EvmAsm.Codegen.U256MulU64Be.mulWholeBodyPost
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word)
        basePtr (target - gasUsed) outPtr baseBytes accBytes outBytes **
        (frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19 v20) ** G))) :
    cpsBranchWithin (19 + 3852) K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outBytes
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** G))
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest spH raIn basePtr outPtr target
            (target - gasUsed) v8 v9 v18 v19 v20
            baseBytes accBytes outBytes G **
          regOwn .x10)
      (K73 + 92)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest spH raIn basePtr outPtr target
            (target - gasUsed) v8 v9 v18 v19 v20
            baseBytes accBytes outBytes G **
          regOwn .x10) := by
  have hFext :
      (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** G).pcFree := by
    pcf
    exact hG
  have hentry := k73_decrease_nonzero_entry_to_mul_spec_within
    sp0 spH raIn gasLimit gasUsed target basePtr outPtr
    v8 v9 v18 v19 v20 baseBytes outBytes
    (EvmAsm.Codegen.U256MulU64Be.frameSlots
      (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** G)
    hsp htarget hne hnotlt hnonzero hFext
  have hmuls := k73_decrease_mul_status_branch_spec_within
    spH raIn target (target - gasUsed) basePtr outPtr v8 v9 v18 v19 v20
    f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes G hG hcallee
  exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by
      dsimp only [k73MulPreNoRa]
      sep_perm hp) hentry hmuls

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute
