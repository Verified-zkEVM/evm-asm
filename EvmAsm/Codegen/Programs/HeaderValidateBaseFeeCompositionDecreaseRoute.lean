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
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeMulNativeContract
import EvmAsm.Codegen.Programs.U256MulU64Be.Arith
import EvmAsm.Codegen.Proofs.U256BeFlatTriples
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore
import EvmAsm.Rv64.BitAux
import EvmAsm.Rv64.Tactics.XPermCert

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256SubBeSAsm
open EvmAsm.Codegen.HeaderValidateBaseFeeMulNativeContract

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

open EvmAsm.Codegen.U256MulU64Be in
/-- Fall leg of the multiply stage developed to the subtraction call site:
    the divider ABI surfaces out of the multiply carry (`regOwns [.x14..x17]`
    ride in the ambient `H`, matching `k74FlatFrame`), both in-place divisions
    run premise-free under the honest divisor bound, the zero-flag shortcut is
    taken (x20 = 0 on this arm), and the subtraction setup lands at the borrow
    test K73 + 220. -/
theorem k73_decrease_mul_fall_to_sub_borrow_spec_within
    (spH raIn basePtr outPtr target gasUsed v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (H : Assertion)
    (hH : H.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hlenOut : outBytes.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (htargetPos : 0 < target.toNat)
    (hszDiv1 :
      4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
        ≤ 2 ^ 64)
    (hszDiv2 :
      4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
        ≤ 2 ^ 64)
    (hszSub :
      4 * ((u256SubBeInPlaceFn basePtr outPtr baseBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes outBytes outBytes target)
          (u256DivU64BeQuotBytes outBytes outBytes target) 8)).body.size + 1)
        ≤ 2 ^ 64) :
    cpsTripleWithin
      ((10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
          (u256DivU64BeInPlaceFn outPtr 8
            (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps +
        1) +
        (1 + (5 + (u256SubBeInPlaceFn basePtr outPtr baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)).body.steps)))
      (K73 + 92) (K73 + 220) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20
          baseBytes accBytes outBytes
          (regOwns [.x14, .x15, .x16, .x17] ** H) ** regOwn .x10))
      (((.x1 : Reg) ↦ᵣ (K73 + 220)) **
        ((.x10 : Reg) ↦ᵣ u256SubBeBorrow baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
        ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion outPtr
          (u256SubBeBytes baseBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
        bytesRegion basePtr baseBytes ** ((.x8 : Reg) ↦ᵣ basePtr) **
        ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ target) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ spH) **
        ((.x19 : Reg) ↦ᵣ (target - gasUsed)) **
        ((.x20 : Reg) ↦ᵣ (0 : Word)) **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
        frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19 v20) ** H) := by
  have hret1 : (((K73 + 104) + 4 : Word) &&& ~~~(1 : Word)) = (K73 + 104) + 4 :=
    EvmAsm.Rv64.BitAux.word_add_even_andn_one (by decide) (by decide)
  have hret2 : (((K73 + 120) + 4 : Word) &&& ~~~(1 : Word)) = (K73 + 120) + 4 :=
    EvmAsm.Rv64.BitAux.word_add_even_andn_one (by decide) (by decide)
  have hretS : (((K73 + 216) + 4 : Word) &&& ~~~(1 : Word)) = K73 + 216 + 4 :=
    EvmAsm.Rv64.BitAux.word_add_even_andn_one (by decide) (by decide)
  have hFframe :
      (k73DecreaseDivPairFrame spH raIn basePtr outPtr target (target - gasUsed)
        v8 v9 v18 v19 v20 baseBytes accBytes H).pcFree := by
    dsimp [k73DecreaseDivPairFrame]
    pcf
    exact hH
  have hdivpair := k73_decrease_div_pair_spec_within
    outPtr target (target - gasUsed) (K73 + 88) outBytes
    (k73DecreaseDivPairFrame spH raIn basePtr outPtr target (target - gasUsed)
      v8 v9 v18 v19 v20 baseBytes accBytes H)
    hFframe hrw hlenOut hovOut htargetPos hszDiv1 hszDiv2 hret1 hret2
  have hx20 := k73_decrease_div_to_sub_branch_spec_within
    spH raIn basePtr outPtr target (target - gasUsed) v8 v9 v18 v19 v20
    baseBytes accBytes outBytes H hH
  have hsub := k73_decrease_div_to_sub_spec_within
    spH raIn basePtr outPtr target (target - gasUsed) v8 v9 v18 v19 v20
    baseBytes accBytes outBytes H hH
    hrw hroBase hlenBase hlenOut hovBase hovOut hdisj hszSub hretS
  -- Segment A: multiply carry shape -> divider pre, then both divisions.
  have hsegA := cpsTripleWithin_weaken
    (fun s hp => by
      have h1 := k73_decrease_mul_carry_to_div_pre
        spH raIn basePtr outPtr target (target - gasUsed) v8 v9 v18 v19 v20
        baseBytes accBytes outBytes H s hp
      dsimp only [k73DecreaseDivPairPre, k73DecreaseDivPairFrame] at h1 ⊢
      xperm_hyp h1)
    (fun _ hq => hq)
    hdivpair
  -- Segment B: x20 = 0 shortcut into the subtraction arm.
  have hsegB := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp only [k73DecreaseDivPairPost, k73DecreaseDivPairFrame] at hp ⊢
      sep_perm hp) hsegA hx20
  -- Segment C: subtraction setup and call to the borrow test.
  exact cpsTripleWithin_seq_same_cr hsegB hsub

/-! ### Local composition helpers

    Small copies of the separation-lifting helpers used by the equal-route
    adapter (they are file-private there), plus the fall-through twin of
    `cpsBranchWithin_seq_cpsTripleWithin_taken_same_cr`. -/

private theorem decr_under_id {P P' B : Assertion}
    (hT : ∀ q, P q → P' q) :
    ∀ q : PartialState, ((B ** P) q) → ((B ** P') q) :=
  fun _ hp => by
    obtain ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    exact ⟨h1, h2, hd, hunion, hl, hT _ hr⟩

private theorem decr_sep_pin_lift {r v Z} :
    ∀ q : PartialState, (((r : Reg) ↦ᵣ v) ** Z) q → ((regOwn r) ** Z) q :=
  fun _ hp => by
    obtain ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    exact ⟨h1, h2, hd, hunion,
      regIs_implies_regOwn (r := r) (v := v) _ hl, hr⟩

private theorem decr_sep_pair_congr {A A' B B' : Assertion}
    (hA : ∀ q, A q → A' q) (hB : ∀ q, B q → B' q) :
    ∀ q : PartialState, ((A ** B) q) → ((A' ** B') q) :=
  fun _ hp => by
    obtain ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    exact ⟨h1, h2, hd, hunion, hA _ hl, hB _ hr⟩

private theorem decr_or_left_lift {A B R : Assertion} :
    ∀ q : PartialState, ((A ** R) q) → (((fun s => A s ∨ B s) ** R) q) :=
  fun _ hp => by
    obtain ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    exact ⟨h1, h2, hd, hunion, Or.inl hl, hr⟩

private theorem decr_or_right_lift {A B R : Assertion} :
    ∀ q : PartialState, ((B ** R) q) → (((fun s => A s ∨ B s) ** R) q) :=
  fun _ hp => by
    obtain ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    exact ⟨h1, h2, hd, hunion, Or.inr hl, hr⟩

theorem cpsBranchWithin_seq_cpsTripleWithin_notTaken_same_cr
    {nSteps1 nSteps2 : Nat} {entry mid target exit_t : Word} {cr : CodeReq}
    {P Q_t Q_f1 Q_f2 : Assertion}
    (h1 : cpsBranchWithin nSteps1 entry cr P exit_t Q_t mid Q_f1)
    (h2 : cpsTripleWithin nSteps2 mid target cr Q_f1 Q_f2) :
    cpsBranchWithin (nSteps1 + nSteps2) entry cr P exit_t Q_t target Q_f2 :=
  cpsBranchWithin_swap
    (cpsBranchWithin_seq_cpsTripleWithin_taken_same_cr (cpsBranchWithin_swap h1) h2)

/-! The multiply-status branch's taken exit jumps past the subtract setup, so
    on this route both legs reach their dispatch points carrying the full
    subtract-context; we only need the pinned variant here, generalized over
    the borrowed register exactly like the owning version above. -/
theorem k73_decrease_sub_borrow_branch_pinned_spec_within
    (Rest : Assertion) (hRest : Rest.pcFree) (old10 : Word) :
    cpsBranchWithin 1 (K73 + 220) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest) ** (.x10 ↦ᵣ old10))
      (K73 + 272) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 224) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10) := by
  have hbne := bne_spec_gen_within .x10 .x0 (52 : BitVec 13)
    old10 (0 : Word) (K73 + 220)
  have hbneC := cpsBranchWithin_extend_code
    (k73_whole_mem 55 (.BNE .x10 .x0 (52 : BitVec 13)) (K73 + 220)
      (by decide) (by rw [k73_length]; decide) (by rfl)) hbne
  rw [show signExtend13 (52 : BitVec 13) = (52 : Word) by decide,
    show (K73 + 220) + (52 : Word) = K73 + 272 by bv_omega,
    show (K73 + 220) + 4 = K73 + 224 by bv_omega] at hbneC
  have hbneF := cpsBranchWithin_frameR Rest hRest hbneC
  refine cpsBranchWithin_weaken (fun _ hp => by sep_perm hp)
    (fun h hq => ?_) (fun h hq => ?_) hbneF
  · have hq1 := sepConj_mono_left
      (sepConj_mono_left (regIs_to_regOwn .x10 old10)) h hq
    drop_pure hq1
    sep_perm hq1
  · have hq1 := sepConj_mono_left
      (sepConj_mono_left (regIs_to_regOwn .x10 old10)) h hq
    drop_pure hq1
    sep_perm hq1

/-! ### Return composition of the subtraction legs

    Glues the four-seam fall leg (`k73_decrease_mul_fall_to_sub_borrow_spec_within`)
    into the pinned borrow test, then extends the taken exit through the shared
    failure tail and the fall-through exit through the decrease success tail.
    Both tails stay symbolic in `raIn` / frame-saved values; only the status
    differs between the legs.  The ambient junk each exit carries forward is
    the subtract context itself (accumulator bytes, base bytes, multiply
    scratch frame, `H`). -/

/-- Pointwise reshuffle of a borrow-test exit into the generic tail premise:
    the pinned frame registers become register ownerships, the pinned `x2`,
    `x0`, and owned `x10` slot around, and the subtract-context junk rides in
    `P`.  Stated with `regsOwnAt k73Frame` unfolded so the positional ladder
    never meets definition-unfolding inside the certificate step. -/
private theorem k73_decr_exit_to_tail_pre
    (spH raIn basePtr outPtr target gasUsed v8 v9 v18 v19 v20 : Word)
    {baseBytes accBytes outBytes : List (BitVec 8)} (H : Assertion) :
    ∀ u : PartialState,
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 220)) ** (.x8 ↦ᵣ basePtr) **
        (.x9 ↦ᵣ outPtr) ** (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ (target - gasUsed)) **
        (.x20 ↦ᵣ (0 : Word)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion outPtr
          (u256SubBeBytes baseBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
        bytesRegion basePtr baseBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** H **
        regOwn .x10) u →
      ((.x2 ↦ᵣ spH) ** regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256SubBeInPlaceScratch **
        bytesRegion outPtr
          (u256SubBeBytes baseBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
        bytesRegion basePtr baseBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** H) u := by
  intro u hu
  -- Positional pin-lift ladder against the flat source order; each step
  -- lifts exactly one pin in place, then one AC-certified rotation lands in
  -- goal order.
  have c1 : ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x1 ** (.x8 ↦ᵣ basePtr) **
      (.x9 ↦ᵣ outPtr) ** (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ (target - gasUsed)) **
      (.x20 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (.x2 ↦ᵣ spH) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr
        (u256SubBeBytes baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
      bytesRegion basePtr baseBytes **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** H **
      regOwn .x10) u :=
    decr_under_id (B := (.x0 : Reg) ↦ᵣ (0 : Word))
      (decr_sep_pin_lift (r := .x1) (v := K73 + 220)) u hu
  have c2 : ((.x0 ↦ᵣ (0 : Word)) **
      regOwn .x1 **
      regOwn .x8 **
      (.x9 ↦ᵣ outPtr) **
      (.x18 ↦ᵣ target) **
      (.x19 ↦ᵣ (target - gasUsed)) **
      (.x20 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (.x2 ↦ᵣ spH) **
      (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr
        (u256SubBeBytes baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
      bytesRegion basePtr baseBytes **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      H ** regOwn .x10) u :=
    decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
      (decr_under_id (B := regOwn .x1)
      (decr_sep_pin_lift (r := .x8) (v := basePtr))) u c1

  have c3 : ((.x0 ↦ᵣ (0 : Word)) **
      regOwn .x1 **
      regOwn .x8 **
      regOwn .x9 **
      (.x18 ↦ᵣ target) **
      (.x19 ↦ᵣ (target - gasUsed)) **
      (.x20 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (.x2 ↦ᵣ spH) **
      (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr
        (u256SubBeBytes baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
      bytesRegion basePtr baseBytes **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      H ** regOwn .x10) u :=
    decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
      (decr_under_id (B := regOwn .x1)
      (decr_under_id (B := regOwn .x8)
      (decr_sep_pin_lift (r := .x9) (v := outPtr)))) u c2

  have c4 : ((.x0 ↦ᵣ (0 : Word)) **
      regOwn .x1 **
      regOwn .x8 **
      regOwn .x9 **
      regOwn .x18 **
      (.x19 ↦ᵣ (target - gasUsed)) **
      (.x20 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (.x2 ↦ᵣ spH) **
      (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr
        (u256SubBeBytes baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
      bytesRegion basePtr baseBytes **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      H ** regOwn .x10) u :=
    decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
      (decr_under_id (B := regOwn .x1)
      (decr_under_id (B := regOwn .x8)
      (decr_under_id (B := regOwn .x9)
      (decr_sep_pin_lift (r := .x18) (v := target))))) u c3

  have c5 : ((.x0 ↦ᵣ (0 : Word)) **
      regOwn .x1 **
      regOwn .x8 **
      regOwn .x9 **
      regOwn .x18 **
      regOwn .x19 **
      (.x20 ↦ᵣ (0 : Word)) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (.x2 ↦ᵣ spH) **
      (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr
        (u256SubBeBytes baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
      bytesRegion basePtr baseBytes **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      H ** regOwn .x10) u :=
    decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
      (decr_under_id (B := regOwn .x1)
      (decr_under_id (B := regOwn .x8)
      (decr_under_id (B := regOwn .x9)
      (decr_under_id (B := regOwn .x18)
      (decr_sep_pin_lift (r := .x19) (v := target - gasUsed)))))) u c4

  have c6 : ((.x0 ↦ᵣ (0 : Word)) **
      regOwn .x1 **
      regOwn .x8 **
      regOwn .x9 **
      regOwn .x18 **
      regOwn .x19 **
      regOwn .x20 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (.x2 ↦ᵣ spH) **
      (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr
        (u256SubBeBytes baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
      bytesRegion basePtr baseBytes **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      H ** regOwn .x10) u :=
    decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
      (decr_under_id (B := regOwn .x1)
      (decr_under_id (B := regOwn .x8)
      (decr_under_id (B := regOwn .x9)
      (decr_under_id (B := regOwn .x18)
      (decr_under_id (B := regOwn .x19)
      (decr_sep_pin_lift (r := .x20) (v := (0 : Word)))))))) u c5
  have gs : (((.x0 ↦ᵣ (0 : Word)) **
      regOwn .x1 **
      regOwn .x8 **
      regOwn .x9 **
      regOwn .x18 **
      regOwn .x19 **
      regOwn .x20 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      (.x2 ↦ᵣ spH) **
      (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr
        (u256SubBeBytes baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
      bytesRegion basePtr baseBytes **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      H **
      regOwn .x10)
      =
      ((.x2 ↦ᵣ spH) **
      regOwn .x1 **
      regOwn .x8 **
      regOwn .x9 **
      regOwn .x18 **
      regOwn .x19 **
      regOwn .x20 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x10 **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ outPtr) **
      (.x12 ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr
        (u256SubBeBytes baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
      bytesRegion basePtr baseBytes **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes **
      H)) := by
    xperm_cert_eq
  exact gs ▸ c6

/-! ### Entry-to-return assembly of the decrease fall leg

    Everything below composes the four-seam fall leg into the pinned borrow
    test and onward into the two shared return tails.  The ambient junk each
    tail carries forward is the subtract context itself: `x0`, `x11`, `x12`,
    scratch ownership, the written output window, the read-only base window,
    the multiply scratch frame, accumulator region, and the caller's `H`. -/

/-- Definitional bridge between the tails' folded frame ownership and the
    positional regOwn chain produced by the exit conversion above. -/
private theorem decr_tailpre_unfold {spH raIn v8 v9 v18 v19 v20 : Word}
    (P : Assertion) :
    ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x10 ** P) =
    ((.x2 ↦ᵣ spH) ** regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
      regOwn .x19 ** regOwn .x20 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x10 ** P) := by
  rw [show regsOwnAt k73Frame =
      (regOwn Reg.x1 ** regOwn Reg.x8 ** regOwn Reg.x9 ** regOwn Reg.x18 **
        regOwn Reg.x19 ** regOwn Reg.x20)
      from by simp [k73Frame, regsOwnAt_cons, regsOwnAt_nil, sepConj_emp_right']]
  xperm_cert_eq

/-! ### Decrease-arm written-image algebra (Route-B success arm, stage 1)

The spec recurrence (`Uint := Nat`) computes `fee - ((fee * δ) / t) / 8` over
unbounded naturals while the guest truncates the multiply first.  The two agree
exactly when the fixed-width product fits 256 bits (`hMulFit`); runs whose
product overflows report status ≠ 0 and take the Route-B failure arm instead,
so the disjunction stays sound without this condition being a machine fact. -/

/-- Numeric value of one divider step's quotient window. -/
private theorem k73_decr_quot_val
    (A : List (BitVec 8)) (target : Word)
    (htargetPos : 0 < target.toNat) (hleTarget : target.toNat ≤ 2 ^ 56)
    (halen : A.length = 32) :
    EvmAsm.Crypto.beBytesToNat (u256DivU64BeQuotBytes A A target)
      = EvmAsm.Crypto.beBytesToNat A / target.toNat := by
  have hq1 := k73_quot_bytes_natToBytesBE A A target halen halen htargetPos hleTarget
  rw [hq1]
  have hb0 := k73_fixed_bytes_bound A
  rw [k73_bytesBEtoNat_eq_beBytesToNat, halen] at hb0
  have hvv := k73_fixed_bytes_value 32
    (EvmAsm.Crypto.beBytesToNat A / target.toNat)
  exact hvv.trans (Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb0))

/-- Numeric value of the twice-divided accumulator window the subtract reads. -/
private theorem k73_decr_quot2_value
    (A : List (BitVec 8)) (target : Word)
    (htargetPos : 0 < target.toNat) (hleTarget : target.toNat ≤ 2 ^ 56)
    (halen : A.length = 32) :
    EvmAsm.Crypto.beBytesToNat
        (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
          (u256DivU64BeQuotBytes A A target) 8)
      = (EvmAsm.Crypto.beBytesToNat A / target.toNat) / 8 := by
  have hvq1 := k73_decr_quot_val A target htargetPos hleTarget halen
  have hq1 := k73_quot_bytes_natToBytesBE A A target halen halen htargetPos hleTarget
  have hlq1 : (u256DivU64BeQuotBytes A A target).length = 32 := by
    rw [hq1]
    simp
  have hq2 := k73_quot_bytes_natToBytesBE
      (u256DivU64BeQuotBytes A A target)
      (u256DivU64BeQuotBytes A A target) 8 hlq1 hlq1 (by decide) (by decide)
  rw [hq2, hvq1]
  have hb0 := k73_fixed_bytes_bound A
  rw [k73_bytesBEtoNat_eq_beBytesToNat, halen] at hb0
  have hvv := k73_fixed_bytes_value 32
    (EvmAsm.Crypto.beBytesToNat A / target.toNat / 8)
  refine hvv.trans ?_
  refine Nat.mod_eq_of_lt ?_
  have hle := Nat.div_le_self
    (EvmAsm.Crypto.beBytesToNat A) target.toNat
  omega

/-- Borrow-free subtract value: when the subtrahend does not exceed the
    minuend the output encodes exactly `a - b`. -/
private theorem k73_decr_sub_value
    {a b orig : List (BitVec 8)} (hla : a.length = 32)
    (hlb : b.length = 32) (hlo : orig.length = 32)
    (hle : EvmAsm.Crypto.beBytesToNat b <= EvmAsm.Crypto.beBytesToNat a) :
    EvmAsm.Crypto.beBytesToNat (u256SubBeBytes a b orig)
      = EvmAsm.Crypto.beBytesToNat a - EvmAsm.Crypto.beBytesToNat b := by
  have hk := EvmAsm.Codegen.U256BeFlat.u256SubBe_mod_and_borrow a b orig hla hlb hlo
  obtain ⟨_, hval⟩ := hk
  rw [hval]
  have hb0 := k73_fixed_bytes_bound a
  rw [k73_bytesBEtoNat_eq_beBytesToNat, hla] at hb0
  omega

/-- Word-level delta unwrap on the decrease arm: when the used gas sits
    strictly below the target, the register subtraction `target - gasUsed`
    does not wrap, so its numeric value is the plain difference. -/
private theorem k73_decr_word_delta_toNat (target gasUsed : Word)
    (hlt : gasUsed.toNat < target.toNat) :
    (target - gasUsed).toNat = target.toNat - gasUsed.toNat := by
  rw [BitVec.toNat_sub]
  have h1 : target.toNat < 2 ^ 64 := BitVec.isLt target
  have h2 : gasUsed.toNat < 2 ^ 64 := BitVec.isLt gasUsed
  omega

/-- The machine's byte image on the successful decrease arm equals the
    written-image content Route-B pins in the postcondition.  The static
    guard `hMulFit` excludes multiply overflow: runs whose product exceeds
    256 bits report status ≠ 0 and take the failure arm instead, so this
    condition is caller-data-static rather than a runtime decision. -/
theorem k73_decr_machine_bytes_eq_written
    {gasLimit gasUsed target : Word} {parentBytes A : List (BitVec 8)}
    (htgtDef : target.toNat = gasLimit.toNat / 2)
    (hdecr : gasUsed.toNat < gasLimit.toNat / 2)
    (htargetPos : 0 < target.toNat)
    (hleTarget : target.toNat ≤ 2 ^ 56)
    (hlenP : parentBytes.length = 32) (halenA : A.length = 32)
    (hMulFit : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes *
        (target - gasUsed).toNat < 2 ^ 256)
    (hvalA : EvmAsm.Crypto.beBytesToNat A
        = (EvmAsm.Crypto.beBytesToNat parentBytes * (target - gasUsed).toNat)
          % 2 ^ 256) :
    u256SubBeBytes parentBytes
        (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
          (u256DivU64BeQuotBytes A A target) 8)
        (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
          (u256DivU64BeQuotBytes A A target) 8)
      = hvbfWrittenImage gasLimit gasUsed parentBytes := by
  have hdw : (target - gasUsed).toNat = target.toNat - gasUsed.toNat := by
    refine k73_decr_word_delta_toNat target gasUsed ?_
    rw [htgtDef]
    exact hdecr
  rw [hdw] at hvalA hMulFit
  have hbB : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes
      = EvmAsm.Crypto.beBytesToNat parentBytes :=
    k73_bytesBEtoNat_eq_beBytesToNat parentBytes
  rw [hbB] at hMulFit
  have hval2 : EvmAsm.Crypto.beBytesToNat A
      = EvmAsm.Crypto.beBytesToNat parentBytes * (target.toNat - gasUsed.toNat) :=
    hvalA.trans (Nat.mod_eq_of_lt hMulFit)
  have hb0 := k73_fixed_bytes_bound parentBytes
  rw [k73_bytesBEtoNat_eq_beBytesToNat, hlenP] at hb0
  have hvq2 := k73_decr_quot2_value A target htargetPos hleTarget halenA
  have hq1 := k73_quot_bytes_natToBytesBE A A target halenA halenA htargetPos hleTarget
  have hlq1 : (u256DivU64BeQuotBytes A A target).length = 32 := by
    rw [hq1]; simp
  have hq2 := k73_quot_bytes_natToBytesBE
      (u256DivU64BeQuotBytes A A target)
      (u256DivU64BeQuotBytes A A target) 8 hlq1 hlq1 (by decide) (by decide)
  have hlq2 : (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
      (u256DivU64BeQuotBytes A A target) 8).length = 32 := by
    rw [hq2]; simp
  -- the twice-divided window does not exceed the fee (borrow-free subtract)
  have hleSub : EvmAsm.Crypto.beBytesToNat
        (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
          (u256DivU64BeQuotBytes A A target) 8) ≤
      EvmAsm.Crypto.beBytesToNat parentBytes := by
    rw [hvq2, hval2]
    have d1 : ((EvmAsm.Crypto.beBytesToNat parentBytes *
            (target.toNat - gasUsed.toNat)) / target.toNat) / 8
        ≤ EvmAsm.Crypto.beBytesToNat parentBytes *
          (target.toNat - gasUsed.toNat) / target.toNat :=
      Nat.div_le_self _ _
    have d2 : EvmAsm.Crypto.beBytesToNat parentBytes *
          (target.toNat - gasUsed.toNat) / target.toNat
        ≤ EvmAsm.Crypto.beBytesToNat parentBytes * target.toNat / target.toNat :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _
        (show target.toNat - gasUsed.toNat ≤ target.toNat from Nat.sub_le _ _))
    have d3 : EvmAsm.Crypto.beBytesToNat parentBytes * target.toNat /
        target.toNat ≤ EvmAsm.Crypto.beBytesToNat parentBytes := by
      rw [Nat.mul_comm]
      exact Nat.le_of_eq (Nat.mul_div_cancel_left _ htargetPos)
    exact le_trans (le_trans d1 d2) d3
  -- spec reduction: the decrease arm of the recurrence fires
  have hneInner : ¬(gasUsed.toNat > gasLimit.toNat / 2) := by
    intro hh; have := hdecr; omega
  have hneOuter : ¬((gasUsed.toNat == gasLimit.toNat / 2) = true) := by
    intro hc
    have hge := beq_iff_eq.mp hc
    have := hdecr
    omega
  -- value of the machine output
  have e1 : EvmAsm.Crypto.beBytesToNat
        (u256SubBeBytes parentBytes
          (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
            (u256DivU64BeQuotBytes A A target) 8)
          (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
            (u256DivU64BeQuotBytes A A target) 8)) =
      EvmAsm.Crypto.beBytesToNat parentBytes -
        (EvmAsm.Crypto.beBytesToNat parentBytes *
          (target.toNat - gasUsed.toNat) / target.toNat) / 8 := by
    rw [k73_decr_sub_value hlenP hlq2 hlq2 hleSub, hvq2, hval2]
  -- value of the written image
  have e2 : EvmAsm.Crypto.beBytesToNat
        (hvbfWrittenImage gasLimit gasUsed parentBytes) =
      EvmAsm.Crypto.beBytesToNat parentBytes -
        (EvmAsm.Crypto.beBytesToNat parentBytes *
          (target.toNat - gasUsed.toNat) / target.toNat) / 8 := by
    show EvmAsm.Crypto.beBytesToNat
        (EvmAsm.Stateless.SpecRef.natToBytesBE 32
          (EvmAsm.Stateless.SpecRef.baseFeeRecurrenceWide gasUsed.toNat
            (gasLimit.toNat / 2)
            (EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes))) = _
    have hswap : EvmAsm.Stateless.SpecRef.baseFeeRecurrenceWide gasUsed.toNat
        (gasLimit.toNat / 2)
        (EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes)
        = EvmAsm.Stateless.SpecRef.baseFeeRecurrenceWide gasUsed.toNat
          (gasLimit.toNat / 2)
          (EvmAsm.Crypto.beBytesToNat parentBytes) := by
      rw [k73_bytesBEtoNat_eq_beBytesToNat parentBytes]
    rw [hswap, EvmAsm.Stateless.SpecRef.baseFeeRecurrenceWide,
      if_neg hneOuter, if_neg hneInner, ← htgtDef]
    have hvv := k73_fixed_bytes_value 32
      (EvmAsm.Crypto.beBytesToNat parentBytes -
        EvmAsm.Stateless.SpecRef.baseFeeDecreaseDelta
          (EvmAsm.Crypto.beBytesToNat parentBytes)
          (target.toNat - gasUsed.toNat) target.toNat)
    have hblt : EvmAsm.Crypto.beBytesToNat parentBytes -
        EvmAsm.Stateless.SpecRef.baseFeeDecreaseDelta
          (EvmAsm.Crypto.beBytesToNat parentBytes)
          (target.toNat - gasUsed.toNat) target.toNat < 256 ^ 32 :=
      lt_of_le_of_lt (Nat.sub_le _ _) hb0
    have hred : EvmAsm.Crypto.beBytesToNat parentBytes -
        EvmAsm.Stateless.SpecRef.baseFeeDecreaseDelta
          (EvmAsm.Crypto.beBytesToNat parentBytes)
          (target.toNat - gasUsed.toNat) target.toNat
        = EvmAsm.Crypto.beBytesToNat parentBytes -
          EvmAsm.Crypto.beBytesToNat parentBytes *
            (target.toNat - gasUsed.toNat) / target.toNat / 8 := by
      rw [EvmAsm.Stateless.SpecRef.baseFeeDecreaseDelta_eq_reference]
    exact Eq.trans hvv (Eq.trans (Nat.mod_eq_of_lt hblt) hred)
  apply k73_bytes_inj_same_length
  · rw [EvmAsm.Codegen.U256BeFlat.u256SubBeBytes_length
      parentBytes
      (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
        (u256DivU64BeQuotBytes A A target) 8)
      (u256DivU64BeQuotBytes (u256DivU64BeQuotBytes A A target)
        (u256DivU64BeQuotBytes A A target) 8) hlq2]
    exact (hvbfWrittenImage_length gasLimit gasUsed parentBytes).symm
  · rw [e2]
    exact e1

/-- Full nonzero-decrease run from the divider entry to a symbolic return:
    the fall leg reaches the borrow test at K73 + 220; a zero borrow falls
    through to `li x10, 0` and returns with status 0 while any other borrow
    jumps to `li x10, 1` and returns with status 1.  Both exits stay symbolic
    in `raIn` / frame-saved values, so the caller reads back the callee-saved
    frame generically like every other composed arm. -/
theorem k73_decrease_mul_fall_to_return_spec_within
    (sp0 spH raIn basePtr outPtr target gasUsed v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (H : Assertion)
    (hH : H.pcFree)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hlenOut : outBytes.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (htargetPos : 0 < target.toNat)
    (hszDiv1 :
      4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
        ≤ 2 ^ 64)
    (hszDiv2 :
      4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
        ≤ 2 ^ 64)
    (hszSub :
      4 * ((u256SubBeInPlaceFn basePtr outPtr baseBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes outBytes outBytes target)
          (u256DivU64BeQuotBytes outBytes outBytes target) 8)).body.size + 1)
        ≤ 2 ^ 64)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsBranchWithin
      (((((10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
            (u256DivU64BeInPlaceFn outPtr 8
              (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps +
          1) +
          (1 + (5 + (u256SubBeInPlaceFn basePtr outPtr baseBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target)
                8)).body.steps))) + 1) + 9) + 10)
      (K73 + 92) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20
          baseBytes accBytes outBytes
          (regOwns [.x14, .x15, .x16, .x17] ** H) ** regOwn .x10))
      raIn
        ((.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          (.x10 ↦ᵣ 1) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
          regOwns u256SubBeInPlaceScratch **
          bytesRegion outPtr
            (u256SubBeBytes baseBytes
              (u256DivU64BeQuotBytes
                (u256DivU64BeQuotBytes outBytes outBytes target)
                (u256DivU64BeQuotBytes outBytes outBytes target) 8)
              (u256DivU64BeQuotBytes
                (u256DivU64BeQuotBytes outBytes outBytes target)
                (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
          bytesRegion basePtr baseBytes **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
            basePtr outPtr target (target - gasUsed) (0 : Word) **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** H)
      raIn
        ((.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          (.x10 ↦ᵣ 0) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
          regOwns u256SubBeInPlaceScratch **
          bytesRegion outPtr
            (u256SubBeBytes baseBytes
              (u256DivU64BeQuotBytes
                (u256DivU64BeQuotBytes outBytes outBytes target)
                (u256DivU64BeQuotBytes outBytes outBytes target) 8)
              (u256DivU64BeQuotBytes
                (u256DivU64BeQuotBytes outBytes outBytes target)
                (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
          bytesRegion basePtr baseBytes **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
            basePtr outPtr target (target - gasUsed) (0 : Word) **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** H) := by
  have hsub4 := k73_decrease_mul_fall_to_sub_borrow_spec_within
    spH raIn basePtr outPtr target gasUsed v8 v9 v18 v19 v20
    baseBytes accBytes outBytes H hH hrw hroBase hlenBase hlenOut
    hovBase hovOut hdisj htargetPos hszDiv1 hszDiv2 hszSub
  -- Ambient subtract-context assertion riding through the borrow test.
  have hRestI :
      ((.x1 ↦ᵣ (K73 + 220)) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ (target - gasUsed)) **
        (.x20 ↦ᵣ (0 : Word)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion outPtr
          (u256SubBeBytes baseBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
        bytesRegion basePtr baseBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** H).pcFree := by
    pcf
    exact hH
  have hbPin := k73_decrease_sub_borrow_branch_pinned_spec_within
    ((.x1 ↦ᵣ (K73 + 220)) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ (target - gasUsed)) **
        (.x20 ↦ᵣ (0 : Word)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion outPtr
          (u256SubBeBytes baseBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
        bytesRegion basePtr baseBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** H)
    hRestI
    (u256SubBeBorrow baseBytes
      (u256DivU64BeQuotBytes
        (u256DivU64BeQuotBytes outBytes outBytes target)
        (u256DivU64BeQuotBytes outBytes outBytes target) 8)
      (u256DivU64BeQuotBytes
        (u256DivU64BeQuotBytes outBytes outBytes target)
        (u256DivU64BeQuotBytes outBytes outBytes target) 8))
  -- Reshape both borrow-test exits into the generic tail premise.
  have hbrT := cpsBranchWithin_weaken (fun _ hp => hp)
    (fun s hp => by
      refine k73_decr_exit_to_tail_pre
        (baseBytes := baseBytes) (accBytes := accBytes) (outBytes := outBytes)
        spH raIn basePtr outPtr target gasUsed
        v8 v9 v18 v19 v20 H s ?_
      sep_perm hp)
    (fun s hp => by
      refine k73_decr_exit_to_tail_pre
        (baseBytes := baseBytes) (accBytes := accBytes) (outBytes := outBytes)
        spH raIn basePtr outPtr target gasUsed
        v8 v9 v18 v19 v20 H s ?_
      sep_perm hp) hbPin
  have hglue := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by sep_perm hp) hsub4 hbrT
  have hsavedInst :
      (k73Saved raIn v8 v9 v18 v19 v20) .x1 = raIn := rfl
  have hPtail :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion outPtr
          (u256SubBeBytes baseBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes outBytes outBytes target)
              (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
        bytesRegion basePtr baseBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          basePtr outPtr target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** H).pcFree := by
    pcf
    exact hH
  have hfailT := k73_failure_tail_spec_within sp0 spH raIn
    (k73Saved raIn v8 v9 v18 v19 v20)
    ((.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr
        (u256SubBeBytes baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
      bytesRegion basePtr baseBytes **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** H)
    hsp hret hsavedInst hPtail
  have hsuccT := k73_decrease_success_tail_spec_within sp0 spH raIn
    (k73Saved raIn v8 v9 v18 v19 v20)
    ((.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
      regOwns u256SubBeInPlaceScratch **
      bytesRegion outPtr
        (u256SubBeBytes baseBytes
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)
          (u256DivU64BeQuotBytes
            (u256DivU64BeQuotBytes outBytes outBytes target)
            (u256DivU64BeQuotBytes outBytes outBytes target) 8)) **
      bytesRegion basePtr baseBytes **
      EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (target - gasUsed) (0 : Word) **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accBytes ** H)
    hsp hret hsavedInst hPtail
  have hfext := cpsBranchWithin_seq_cpsTripleWithin_taken_same_cr hglue
    (decr_tailpre_unfold _ ▸ hfailT)
  exact cpsBranchWithin_seq_cpsTripleWithin_notTaken_same_cr hfext
    (decr_tailpre_unfold _ ▸ hsuccT)

open EvmAsm.Codegen.U256MulU64Be in
/-- Entry composed into the multiply stage with the callee contract
discharged from the deployed flat whole-routine triple through the native
asymmetric shape (`k73_mul_status_branch_native_spec_within`): the scratch
windows are owned premises at `accWin` / `outWin`, the image lists thread
into both branch exits, and no new caller precondition appears. -/
theorem k73_decrease_entry_status_native_discharged
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accWin outWin : List (BitVec 8)) (G : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hnotlt : ¬ target.toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hG : G.pcFree)
    (hlenA : baseBytes.length = 32)
    (hlenAcc : accWin.length = 40)
    (houtW : outWin.length = 32)
    (halignA : basePtr.toNat % 8 = 0)
    (hoverA : basePtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (basePtr + BitVec.ofNat 64 j) = true)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true) :
    cpsBranchWithin (19 + 3852) K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outWin
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin ** G))
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest spH raIn basePtr outPtr target
            (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
            (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes (target - gasUsed) 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes (target - gasUsed) 32)
              outWin 32) G **
          regOwn .x10)
      (K73 + 92)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest spH raIn basePtr outPtr target
            (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
            (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes (target - gasUsed) 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState baseBytes (target - gasUsed) 32)
              outWin 32) G **
          regOwn .x10) := by
  have hFamb :
      (frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G).pcFree := by
    pcf
    exact hG
  have hretCall : ((K73 + 88 : Word) &&& ~~~(1 : Word)) = K73 + 88 :=
    EvmAsm.Rv64.BitAux.word_add_even_andn_one (by decide) (by decide)
  have hcallee := mulWhole_spec
    (F := frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) ** G)
    hFamb baseBytes accWin outWin hlenA hlenAcc houtW
    spH (K73 + 88) basePtr outPtr target (target - gasUsed) (0 : Word)
    basePtr (target - gasUsed) outPtr outPtr
    f0 f1 f2 f3 f4 f5 halignA hoverA hvalidA halignOut hoverOut hvalidOut
    hretCall
  have htwin := k73_mul_status_branch_native_spec_within
    spH raIn target (target - gasUsed) basePtr outPtr v8 v9 v18 v19 v20
    f0 f1 f2 f3 f4 f5 baseBytes accWin outWin G hG hcallee
  have hFext :
      (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin ** G).pcFree := by
    pcf
    exact hG
  have hentry := k73_decrease_nonzero_entry_to_mul_spec_within
    sp0 spH raIn gasLimit gasUsed target basePtr outPtr
    v8 v9 v18 v19 v20 baseBytes outWin
    (EvmAsm.Codegen.U256MulU64Be.frameSlots
      (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
      bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin ** G)
    hsp htarget hne hnotlt hnonzero hFext
  exact cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by
      dsimp only [k73MulPreNoRa]
      sep_perm hp) hentry htwin

/-! `regsOwnAt k73Frame` written as the flat ownership chain (the fold's
    trailing unit is not a definitional equality, so callers bridge through
    this lemma instead of `rfl`). -/
private theorem k73_regsOwnAt_k73Frame_flat :
    regsOwnAt k73Frame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20) := by
  simp [k73Frame, regsOwnAt_cons, regsOwnAt_nil, sepConj_emp_right']

/-- Outer overflow failure returning to the caller: the multiply stage exit
    at K73 + 272 (multiply carry junk carried in `P`) runs the shared
    `li x10, 1` plus epilogue tail.  The source pins the registers the
    epilogue overwrites (`w8..w20` are the mid-body values the multiply left,
    supplied by the feeder window); the proof lifts them to ownerships since
    the tail machinery only needs to own what it rewrites.  Values reloaded
    from the frame land per `k73Saved`, and the junk `P` rides through
    untouched. -/
theorem k73_decrease_mulfail_outer_return_spec_within
    (sp0 spH raIn v8 v9 v18 v19 v20 w8 w9 w18 w19 w20 : Word) (P : Assertion)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hP : P.pcFree) :
    cpsTripleWithin 9 (K73 + 272) raIn wholeCode
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ w8) ** (.x9 ↦ᵣ w9) ** (.x18 ↦ᵣ w18) **
        (.x19 ↦ᵣ w19) ** (.x20 ↦ᵣ w20) ** regOwn .x10 ** P)
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) ** P) := by
  have hsavedU : (k73Saved raIn v8 v9 v18 v19 v20) .x1 = raIn := rfl
  have hPi : (((.x0 : Reg) ↦ᵣ (0 : Word)) ** P).pcFree := by
    pcf
    exact hP
  have ht := k73_failure_tail_spec_within sp0 spH raIn
    (k73Saved raIn v8 v9 v18 v19 v20) ((.x0 ↦ᵣ (0 : Word)) ** P)
    hsp hret hsavedU hPi
  -- Flat spelling of the shared failure-tail premise.
  have htFlat :
      cpsTripleWithin 9 (K73 + 272) raIn wholeCode
        ((.x2 ↦ᵣ spH) ** (regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
            regOwn .x18 ** regOwn .x19 ** regOwn .x20) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P)
        ((.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) ** P) :=
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [k73_regsOwnAt_k73Frame_flat]
        xperm_hyp hp)
      (fun _ hq => hq) ht
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun _ hq => hq) htFlat
  -- Lift the incoming pins to the ownerships the tail machinery consumes,
  -- deepest first (each tower descends the chain heads to its pin).
  have c20 :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ w8) ** (.x9 ↦ᵣ w9) ** (.x18 ↦ᵣ w18) **
        (.x19 ↦ᵣ w19) ** regOwn .x20 ** regOwn .x10 ** P) s :=
    decr_under_id (decr_under_id (decr_under_id (decr_under_id (decr_under_id
      (decr_under_id (decr_under_id (decr_under_id
        (decr_sep_pin_lift (r := Reg.x20) (v := w20))))))))) s hp
  have c19 :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ w8) ** (.x9 ↦ᵣ w9) ** (.x18 ↦ᵣ w18) **
        regOwn .x19 ** regOwn .x20 ** regOwn .x10 ** P) s :=
    decr_under_id (decr_under_id (decr_under_id (decr_under_id (decr_under_id
      (decr_under_id (decr_under_id
        (decr_sep_pin_lift (r := Reg.x19) (v := w19)))))))) s c20
  have c18 :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ w8) ** (.x9 ↦ᵣ w9) **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** regOwn .x10 ** P) s :=
    decr_under_id (decr_under_id (decr_under_id (decr_under_id (decr_under_id
      (decr_under_id
        (decr_sep_pin_lift (r := Reg.x18) (v := w18))))))) s c19
  have c9 :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ w8) ** regOwn .x9 ** regOwn .x18 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x10 ** P) s :=
    decr_under_id (decr_under_id (decr_under_id (decr_under_id (decr_under_id
      (decr_sep_pin_lift (r := Reg.x9) (v := w9)))))) s c18
  have c8 :
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x10 ** P) s :=
    decr_under_id (decr_under_id (decr_under_id (decr_under_id
      (decr_sep_pin_lift (r := Reg.x8) (v := w8))))) s c9
  -- Regroup with the link-register pin at the head ...
  have egrpa :
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          (.x2 ↦ᵣ spH) ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
          regOwn .x19 ** regOwn .x20 ** regOwn .x10 ** P)) =
      (((.x1 ↦ᵣ (K73 + 88)) ** ((.x2 ↦ᵣ spH) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P))) := by
    xperm_cert_eq
  have hx1 : ((.x1 ↦ᵣ (K73 + 88)) ** ((.x2 ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P)) s := egrpa ▸ c8
  -- ... lift the pin to an ownership (the value is dead: the epilogue
  -- reloads `x1` from the saved slot, and `hsavedU` pins that to `raIn`) ...
  have hl : (regOwn .x1 ** ((.x2 ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P)) s :=
    decr_sep_pin_lift _ hx1
  -- ... and finish by pure permutation against the flat tail premise.
  exact (by xperm_cert_eq :
    ((regOwn .x1 ** ((.x2 ↦ᵣ spH) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P))) =
    (((.x2 ↦ᵣ spH) ** (regOwn .x1 ** regOwn .x8 ** regOwn .x9 **
        regOwn .x18 ** regOwn .x19 ** regOwn .x20) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      regOwn .x10 ** (.x0 ↦ᵣ (0 : Word)) ** P))) ▸ hl

/-- An existential projection never owns the program counter when no
    instance does: eliminate the binder on the holding state and reuse the
    witness-level fact.  Stated over the bare `∀` form because generalized
    field notation on a lambda head resolves `pcFree` against `Function`,
    not `Assertion`. -/
private theorem k73_pcFree_exists {A : Nat → Assertion}
    (hW : ∀ k, (A k).pcFree) :
    ∀ h, ((fun s => ∃ k, (A k) s : Assertion) h) → h.pc = none := by
  intro h hs
  obtain ⟨k, hk⟩ := hs
  exact hW k h hk

/-- Computed multiply accumulator image on the decrease arm (40 bytes). -/
private def k73_decr_img1 (baseBytes : List (BitVec 8)) (delta : Word) :
    List (BitVec 8) :=
  EvmAsm.Codegen.U256MulU64Be.mulState baseBytes delta 32

/-- Computed multiply output image on the decrease arm: the low 32 bytes of
    the accumulator copied over the initial window; independent of that
    window's content. -/
private def k73_decr_img2 (baseBytes : List (BitVec 8)) (delta : Word)
    (outWin : List (BitVec 8)) : List (BitVec 8) :=
  EvmAsm.Codegen.U256MulU64Be.copyState (k73_decr_img1 baseBytes delta)
    outWin 32

/-- The whole-route ambient envelope for this arm: the wrapper-world
    register ownerships that the carry rest does not already speak about,
    kept as one opaque token so permutation certificates match.  Deliberately
    pin-free: at K73 entry the machine stack pointer is `sp0` (`k73HeadPre`
    pins `.x2 ↦ sp0`), and at every return the shared epilogue rewrites it to
    `sp0`; a `x2` claim here would make the premise unsatisfiable.  The
    mid-body `.x2 ↦ spH` fact is extracted from the multiply epilogue window
    by `k73_decr_mulfail_twinfeed` instead. -/
private def k73_decr_ghole (_spH : Word) (G : Assertion) : Assertion :=
  regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** G

/-- Memory-visible leftovers of any multiply-stage outcome: the scratch-frame
    dwords, the output window, and the overflow core (whose `x5/x6/x28`
    claims persist - the shared epilogue loads only `x1, x8..x20` and
    rewrites `x2`).  Deliberately free of the multiply epilogue's `.x2` pin
    and of its `x8..x20` pins: the epilogue reloads those registers from the
    frame, so mid-body register claims must not survive into exit junk. -/
private def k73_decr_mulfail_win (spH deltaV target basePtr outPtr : Word)
    (baseBytes outWin : List (BitVec 8)) : Assertion :=
  fun s => ∃ k,
    (U256MulU64Be.frameSlots (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target deltaV (0 : Word) **
      bytesRegion outPtr (k73_decr_img2 baseBytes deltaV outWin) **
      k73MulOverflowCoreNoStatus (k73_decr_img1 baseBytes deltaV) k) s

/-- The ambient junk carried through the outer failure leg: tail extras,
    overflow window, caller ambience. -/
private def k73_decr_mulfail_junk (spH deltaV target basePtr outPtr : Word)
    (baseBytes outWin : List (BitVec 8)) (Grest : Assertion) : Assertion :=
  EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes **
    k73_decr_mulfail_win spH deltaV target basePtr outPtr baseBytes outWin **
    Grest

/-- Feed the mul-stage carry exit into the shared failure epilogue.  The
    mid-body `.x2 ↦ spH` fact rides INSIDE the multiply epilogue window (its
    `spNew + signExtend12 48` value reduces to `spH`); the epilogue's other
    register claims pass through as pins over the feeder values; and only the
    memory-visible leftovers survive as junk (`k73_decr_mulfail_win`), since
    the shared epilogue reloads the callee-saved registers from the frame and
    rewrites `x2` to `sp0`. -/
private theorem k73_decr_mulfail_twinfeed
    (spH raIn basePtr outPtr target deltaV v8 v9 v18 v19 v20 : Word)
    (baseBytes outWin : List (BitVec 8)) (Grest : Assertion) :
    ∀ s : PartialState,
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target deltaV
          v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes deltaV)
          (k73_decr_img2 baseBytes deltaV outWin)
          (k73_decr_ghole spH Grest) ** regOwn .x10) s →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
        (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ deltaV) ** (.x20 ↦ᵣ (0 : Word)) **
        regOwn .x10 **
        (U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes **
          k73_decr_mulfail_win spH deltaV target basePtr outPtr
            baseBytes outWin **
          (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
            regOwn .x20 ** Grest))) s := by
  have hsp48 :
      (spH + signExtend12 (-48 : BitVec 12)) + signExtend12 (48 : BitVec 12) =
        spH := by
    have h1 : signExtend12 (-48 : BitVec 12) =
        (18446744073709551568 : Word) := by decide
    have h2 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
    rw [h1, h2]
    bv_omega
  intro s hp
  -- Flatten the carry rest (the ghole token unfolds to plain ownerships);
  -- the image tokens stay folded so every later spelling matches.
  dsimp only [k73DecreaseMulCarryRest, k73_decr_ghole] at hp
  -- Pull the existential window out of the chain.
  have hpW :
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
            frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
            U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes) **
          ((fun u => ∃ k,
              (k73MulEpilogueNoRa (spH + signExtend12 (-48 : BitVec 12))
                  (K73 + 88) basePtr outPtr target deltaV (0 : Word) **
                bytesRegion outPtr (k73_decr_img2 baseBytes deltaV outWin) **
                k73MulOverflowCoreNoStatus
                  (k73_decr_img1 baseBytes deltaV) k) u) **
            (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
              regOwn .x20 ** Grest ** regOwn .x10))) s := by
    xperm_hyp hp
  have hpE :
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
            frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
            U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes) **
          ((fun u =>
              ∃ k,
                ((k73MulEpilogueNoRa (spH + signExtend12 (-48 : BitVec 12))
                      (K73 + 88) basePtr outPtr target deltaV (0 : Word) **
                    bytesRegion outPtr
                      (k73_decr_img2 baseBytes deltaV outWin) **
                    k73MulOverflowCoreNoStatus
                      (k73_decr_img1 baseBytes deltaV) k) **
                  (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
                    regOwn .x20 ** Grest ** regOwn .x10)) u))) s :=
    sepConj_mono_right
      (fun h' hq => (sepConj_exists_left h').mp hq) s hpW
  obtain ⟨k, hk⟩ := sepConj_exists_right s hpE
  -- Reduce the epilogue's `x2` pin value to `spH`.
  dsimp only [k73MulEpilogueNoRa] at hk
  rw [hsp48] at hk
  -- Regroup once: the fixed-`k` memory window moves into the junk slot where
  -- the existential re-wrap happens (every later split stays inside the
  -- original partition tree, so no cross-block recombination is needed).
  have hkFlat :
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
          frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
          (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
          (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ deltaV) **
          (.x20 ↦ᵣ (0 : Word)) ** regOwn .x10 **
          (U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes **
            (((U256MulU64Be.frameSlots (spH + signExtend12 (-48 : BitVec 12))
                  (K73 + 88) basePtr outPtr target deltaV (0 : Word)) **
                (bytesRegion outPtr
                    (k73_decr_img2 baseBytes deltaV outWin) **
                  k73MulOverflowCoreNoStatus
                    (k73_decr_img1 baseBytes deltaV) k)) **
              (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
                regOwn .x20 ** Grest)))) s := by
    have hEq :
        ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
              frameSlotsSaved k73Frame spH
                (k73Saved raIn v8 v9 v18 v19 v20) **
              U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes) **
            ((((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
                    (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ deltaV) **
                    (.x20 ↦ᵣ (0 : Word)) **
                    U256MulU64Be.frameSlots
                      (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
                      basePtr outPtr target deltaV (0 : Word)) **
                  (bytesRegion outPtr
                      (k73_decr_img2 baseBytes deltaV outWin) **
                    k73MulOverflowCoreNoStatus
                      (k73_decr_img1 baseBytes deltaV) k)) **
              (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
                regOwn .x20 ** (Grest ** regOwn .x10)))) =
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (K73 + 88)) **
            frameSlotsSaved k73Frame spH
              (k73Saved raIn v8 v9 v18 v19 v20) **
            (.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ basePtr) ** (.x9 ↦ᵣ outPtr) **
            (.x18 ↦ᵣ target) ** (.x19 ↦ᵣ deltaV) **
            (.x20 ↦ᵣ (0 : Word)) ** regOwn .x10 **
            (U256MulU64Be.mulTailExtra basePtr deltaV outPtr baseBytes **
              (((U256MulU64Be.frameSlots
                    (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
                    basePtr outPtr target deltaV (0 : Word)) **
                  (bytesRegion outPtr
                      (k73_decr_img2 baseBytes deltaV outWin) **
                    k73MulOverflowCoreNoStatus
                      (k73_decr_img1 baseBytes deltaV) k)) **
                (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
                  regOwn .x20 ** Grest)))) := by
      xperm_cert_eq
    exact hEq ▸ hk
  -- Re-wrap the fixed-`k` window existentially: single-layer rebuilds, each
  -- split a sibling of an original one, and the witness state already
  -- separates the window group from the ownership tail.
  obtain ⟨u1, u2, hd1, hu1, hx0, r1⟩ := hkFlat
  obtain ⟨u3, u4, hd3, hu3, hx1, r2⟩ := r1
  obtain ⟨u5, u6, hd5, hu5, hFSS, r3⟩ := r2
  obtain ⟨u7, u8, hd7, hu7, hx2, r4⟩ := r3
  obtain ⟨u9, u10, hd9, hu9, hp8, r5⟩ := r4
  obtain ⟨u11, u12, hd11, hu11, hp9, r6⟩ := r5
  obtain ⟨u13, u14, hd13, hu13, hp18, r7⟩ := r6
  obtain ⟨u15, u16, hd15, hu15, hp19, r8⟩ := r7
  obtain ⟨u17, u18, hd17, hu17, hp20, r9⟩ := r8
  obtain ⟨u19, u20, hd19, hu19, ho10, r10⟩ := r9
  obtain ⟨u21, u22, hd21, hu21, hT, r11⟩ := r10
  obtain ⟨u23, u24, hd23, hu23, hWinG, hOwnG⟩ := r11
  exact ⟨u1, u2, hd1, hu1, hx0, ⟨u3, u4, hd3, hu3, hx1,
    ⟨u5, u6, hd5, hu5, hFSS, ⟨u7, u8, hd7, hu7, hx2,
    ⟨u9, u10, hd9, hu9, hp8, ⟨u11, u12, hd11, hu11, hp9,
    ⟨u13, u14, hd13, hu13, hp18, ⟨u15, u16, hd15, hu15, hp19,
    ⟨u17, u18, hd17, hu17, hp20, ⟨u19, u20, hd19, hu19, ho10,
    ⟨u21, u22, hd21, hu21, hT, ⟨u23, u24, hd23, hu23,
      ⟨k, hWinG⟩, hOwnG⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩


/-- The outer multiply-overflow failure leg, from whole-route entry to the
    shared-epilogue return: charges the native-discharge corollary onto
    `k73_decrease_mulfail_outer_return_spec_within`, leaving every leftover
    atom of the carry rest inside the junk abbreviation. -/
theorem k73_decr_mulfail_entry_to_return_spec_within
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accWin outWin : List (BitVec 8)) (Grest : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hnotlt : ¬ target.toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hG : Grest.pcFree)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hlenA : baseBytes.length = 32)
    (hlenAcc : accWin.length = 40)
    (houtW : outWin.length = 32)
    (halignA : basePtr.toNat % 8 = 0)
    (hoverA : basePtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (basePtr + BitVec.ofNat 64 j) = true)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true) :
    cpsBranchWithin (19 + 3852 + 9) K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outWin
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin **
          k73_decr_ghole spH Grest))
      raIn
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        k73_decr_mulfail_junk spH (target - gasUsed) target basePtr outPtr
          baseBytes outWin (k73_decr_ghole spH Grest))
      (K73 + 92)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes (target - gasUsed))
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (k73_decr_ghole spH Grest) **
        regOwn .x10) := by
  have hGH :
      ((k73_decr_ghole spH Grest)).pcFree := by
    pcf
    exact hG
  have hciii := k73_decrease_entry_status_native_discharged
    sp0 spH raIn gasLimit gasUsed target basePtr outPtr
    v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 baseBytes accWin outWin
    (k73_decr_ghole spH Grest)
    hsp htarget hne hnotlt hnonzero hGH hlenA hlenAcc houtW
    halignA hoverA hvalidA halignOut hoverOut hvalidOut
  -- Re-typed at the statement's image-token spelling so the final combinator
  -- unifies against the goal syntactically.
  have hciiiT : cpsBranchWithin (19 + 3852) K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outWin
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin **
          k73_decr_ghole spH Grest))
      (K73 + 272)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes (target - gasUsed))
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (k73_decr_ghole spH Grest) ** regOwn .x10)
      (K73 + 92)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes (target - gasUsed))
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (k73_decr_ghole spH Grest) ** regOwn .x10) := hciii
  -- pcFree of the junk parameter: standard atoms plus one existential window.
  have hTEpc :
      (EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr (target - gasUsed)
        outPtr baseBytes).pcFree := by
    dsimp only [EvmAsm.Codegen.U256MulU64Be.mulTailExtra]
    pcf
  have hWinpc :
      (k73_decr_mulfail_win spH (target - gasUsed) target basePtr outPtr
        baseBytes outWin).pcFree :=
    k73_pcFree_exists (A := fun k =>
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48 : BitVec 12))
            (K73 + 88) basePtr outPtr target (target - gasUsed) (0 : Word) **
          bytesRegion outPtr
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) **
          k73MulOverflowCoreNoStatus
            (k73_decr_img1 baseBytes (target - gasUsed)) k))
      (fun k => by pcf)
  have hPjunk :
      (k73_decr_mulfail_junk spH (target - gasUsed) target basePtr outPtr
        baseBytes outWin (k73_decr_ghole spH Grest)).pcFree :=
    pcFree_sepConj hTEpc (pcFree_sepConj hWinpc hGH)
  -- The twin, run at the junk parameter.
  have hspF : spH + signExtend12 (56 : BitVec 12) = sp0 := by
    have hx : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide
    rw [hsp, hx]
    have hy : signExtend12 (-56 : BitVec 12) =
        (18446744073709551560 : Word) := by decide
    rw [hy]
    bv_omega
  have htwin := k73_decrease_mulfail_outer_return_spec_within
    sp0 spH raIn v8 v9 v18 v19 v20
    basePtr outPtr target (target - gasUsed) (0 : Word)
    (k73_decr_mulfail_junk spH (target - gasUsed) target basePtr outPtr
      baseBytes outWin (k73_decr_ghole spH Grest)) hspF hret hPjunk
  -- Premise alignment: the feeder extracts the epilogue's `.x2` pin and
  -- register pins from the carry-rest window and re-wraps the fixed-`k`
  -- memory junk existentially (see `k73_decr_mulfail_twinfeed`).
  have htf := k73_decr_mulfail_twinfeed spH raIn basePtr outPtr target
    (target - gasUsed) v8 v9 v18 v19 v20 baseBytes outWin Grest
  have htw' := cpsTripleWithin_weaken (fun s hp => htf s hp)
    (fun _ hq => hq) htwin
  exact cpsBranchWithin_seq_cpsTripleWithin_taken_same_cr hciiiT htw'

/-- The divide-scratch ownerships ride in the corollary's ambient parameter,
    so the ghole envelope over the enriched environment equals the fall leg's
    `regOwns [.x14..x17] ** H` token spelling.  Both sides are pin-free: the
    `.x2 ↦ spH` fact lives inside the carry-rest window mid-body (where
    `sp = spH` genuinely) and is re-derived by the fall leg's own frame
    machinery, never claimed at a return exit. -/
private theorem k73_decr_ghole_env_eq (spH : Word) (G : Assertion) :
    (k73_decr_ghole spH
        (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** G)) =
      (regOwns [.x14, .x15, .x16, .x17] **
        (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** G)) := by
  simp only [k73_decr_ghole, regOwns_cons, regOwns_nil, sepConj_emp_right']
  xperm_cert_eq

/-- Subtractor-return post, shared by the borrow-failure taken exit and the
    success fall exit (status 1 / 0). -/
private def k73_decr_sub_return_post
    (sp0 spH raIn target basePtr outPtr gasUsed v8 v9 v18 v19 v20 : Word)
    (baseBytes outWin : List (BitVec 8)) (Genv : Assertion) (status : Word) :
    Assertion :=
  (.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (.x10 ↦ᵣ status) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
    regOwns u256SubBeInPlaceScratch **
    bytesRegion outPtr
      (u256SubBeBytes baseBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          8)
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          8)) **
    bytesRegion basePtr baseBytes **
    EvmAsm.Codegen.U256MulU64Be.frameSlots
      (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
      basePtr outPtr target (target - gasUsed) (0 : Word) **
    bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
      (k73_decr_img1 baseBytes (target - gasUsed)) **
    (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** Genv)

/-- Multiply-overflow failure post (the taken exit of the mul-status branch,
    routed through the shared failure epilogue). -/
private def k73_decr_mulfail_taken_post
    (sp0 spH raIn target basePtr outPtr gasUsed v8 v9 v18 v19 v20 : Word)
    (baseBytes outWin : List (BitVec 8)) (Genv : Assertion) : Assertion :=
  (.x2 ↦ᵣ sp0) ** regsAt k73Frame (k73Saved raIn v8 v9 v18 v19 v20) **
    frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
    (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
    k73_decr_mulfail_junk spH (target - gasUsed) target basePtr outPtr
      baseBytes outWin
      (k73_decr_ghole spH
        (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Genv))

/-! Whole nonzero-decrease route: the mul-status branch is extended past its
    not-taken exit (the fall leg into the divider/subtractor chain) with the
    mul-overflow taken exit retargeted through the shared failure epilogue.
    All divider window claims are threaded at the computed image lists
    (`mulState` / `copyState`), so the divider quotient premises speak about
    exactly the bytes the multiply leaves behind. -/
theorem k73_decrease_route_machine_spec_within
    (sp0 spH raIn gasLimit gasUsed target basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accWin outWin : List (BitVec 8)) (Genv : Assertion)
    (hsp : spH = sp0 + signExtend12 (-56 : BitVec 12))
    (htarget : target = gasLimit >>> 1)
    (hne : gasUsed ≠ target)
    (hnotlt : ¬ target.toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hG : Genv.pcFree)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hlenA : baseBytes.length = 32)
    (hlenAcc : accWin.length = 40)
    (houtW : outWin.length = 32)
    (halignA : basePtr.toNat % 8 = 0)
    (hoverA : basePtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (basePtr + BitVec.ofNat 64 j) = true)
    (halignOut : outPtr.toNat % 8 = 0)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (outPtr + BitVec.ofNat 64 j) = true)
    (htargetPos : 0 < target.toNat)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hszDiv1 :
      4 * ((u256DivU64BeInPlaceFn outPtr target
        (k73_decr_img2 baseBytes (target - gasUsed) outWin)).body.size + 1)
        ≤ 2 ^ 64)
    (hszDiv2 :
      4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)).body.size
          + 1)
        ≤ 2 ^ 64)
    (hszSub :
      4 * ((u256SubBeInPlaceFn basePtr outPtr baseBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          (u256DivU64BeQuotBytes
            (k73_decr_img2 baseBytes (target - gasUsed) outWin)
            (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
          8)).body.size + 1)
        ≤ 2 ^ 64) :
    cpsBranchWithin ((19 + 3852 + 9) +
        (((((10 +
              (u256DivU64BeInPlaceFn outPtr target
                (k73_decr_img2 baseBytes (target - gasUsed) outWin)).body.steps +
            (u256DivU64BeInPlaceFn outPtr 8
              (u256DivU64BeQuotBytes
                (k73_decr_img2 baseBytes (target - gasUsed) outWin)
                (k73_decr_img2 baseBytes (target - gasUsed) outWin)
                target)).body.steps +
          1) +
          (1 + (5 + (u256SubBeInPlaceFn basePtr outPtr baseBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes
                (k73_decr_img2 baseBytes (target - gasUsed) outWin)
                (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
              (u256DivU64BeQuotBytes
                (k73_decr_img2 baseBytes (target - gasUsed) outWin)
                (k73_decr_img2 baseBytes (target - gasUsed) outWin) target)
              8)).body.steps))) + 1) + 9) + 10))
      K73 wholeCode
      (k73HeadPre sp0 spH raIn gasLimit gasUsed basePtr outPtr
        v8 v9 v18 v19 v20 baseBytes outWin
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spH + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin **
        k73_decr_ghole spH
          (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Genv)))
      raIn
      (fun st =>
        ((k73_decr_mulfail_taken_post sp0 spH raIn target basePtr outPtr
            gasUsed v8 v9 v18 v19 v20 baseBytes outWin Genv) st ∨
          (k73_decr_sub_return_post sp0 spH raIn target basePtr outPtr gasUsed
            v8 v9 v18 v19 v20 baseBytes outWin Genv (1 : Word)) st))
      raIn
      (k73_decr_sub_return_post sp0 spH raIn target basePtr outPtr gasUsed
        v8 v9 v18 v19 v20 baseBytes outWin Genv (0 : Word)) := by
  have hspF : spH + signExtend12 (56 : BitVec 12) = sp0 := by
    have hx : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide
    rw [hsp, hx]
    have hy : signExtend12 (-56 : BitVec 12) =
        (18446744073709551560 : Word) := by decide
    rw [hy]
    bv_omega
  have hGr :
      (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Genv).pcFree := by
    pcf
    exact hG
  have hHp :
      (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
        regOwn .x20 ** Genv).pcFree := by
    pcf
    exact hG
  have hlenI2 :
      (k73_decr_img2 baseBytes (target - gasUsed) outWin).length = 32 :=
    EvmAsm.Codegen.U256MulU64Be.copyState_len _ _ 32 houtW
  have hfall := k73_decrease_mul_fall_to_return_spec_within
    sp0 spH raIn basePtr outPtr target gasUsed v8 v9 v18 v19 v20
    baseBytes (k73_decr_img1 baseBytes (target - gasUsed))
      (k73_decr_img2 baseBytes (target - gasUsed) outWin)
    (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** Genv)
    hHp hrw hroBase hlenA hlenI2 hoverA hoverOut hdisj htargetPos
    hszDiv1 hszDiv2 hszSub hspF hret
  have hperm : ∀ h : PartialState,
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes (target - gasUsed))
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (k73_decr_ghole spH
            (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Genv)) **
        regOwn .x10) h →
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73DecreaseMulCarryRest spH raIn basePtr outPtr target
          (target - gasUsed) v8 v9 v18 v19 v20 baseBytes
          (k73_decr_img1 baseBytes (target - gasUsed))
          (k73_decr_img2 baseBytes (target - gasUsed) outWin)
          (regOwns [.x14, .x15, .x16, .x17] **
            (regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
              regOwn .x20 ** Genv)) ** regOwn .x10) h := by
    intro h hp
    rw [k73_decr_ghole_env_eq] at hp
    exact hp
  have hmf := k73_decr_mulfail_entry_to_return_spec_within
    sp0 spH raIn gasLimit gasUsed target basePtr outPtr
    v8 v9 v18 v19 v20 f0 f1 f2 f3 f4 f5 baseBytes accWin outWin
    (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Genv)
    hsp htarget hne hnotlt hnonzero hGr hret hlenA hlenAcc houtW
    halignA hoverA hvalidA halignOut hoverOut hvalidOut
  exact cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr hmf hperm hfall
    (fun _ hp => Or.inl hp) (fun _ hp => Or.inr hp)

/-- CONSTRUCTED non-vacuity inhabitance of the native-discharge corollary
    (adopted standard for #12346: a whole-route theorem does not count until a
    closed-proposition witness exists at corollary level - an unsatisfiable
    premise cannot admit a constructed witness, so this check catches the
    vacuity class by construction rather than by vigilance).  Concrete
    literals: `sp0 - spH = 56`, decrease guard family `target = 5000 >
    gasUsed = 2500`, `gasLimit = 10000`, zero scratch windows, empty
    ambience.  Discharged by direct application - no hypotheses, no sorry. -/
theorem k73_decr_entry_status_native_inhabited :
    cpsBranchWithin (19 + 3852) K73 wholeCode
      (k73HeadPre (0xa0050038 : Word) 0xa0050000 0 10000 2500 0xa0000000
        0xa0000100 0 0 0 0 0 (List.replicate 32 0) (List.replicate 32 0)
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (0xa0050000 + signExtend12 (-48 : BitVec 12)) 0 0 0 0 0 0 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (List.replicate 40 0) ** empAssertion))
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest 0xa0050000 0 0xa0000000 0xa0000100 5000
            (5000 - 2500 : Word) 0 0 0 0 0 (List.replicate 32 0)
            (EvmAsm.Codegen.U256MulU64Be.mulState (List.replicate 32 0)
              (5000 - 2500 : Word) 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState (List.replicate 32 0)
                (5000 - 2500 : Word) 32) (List.replicate 32 0) 32)
            empAssertion **
          regOwn .x10)
      (K73 + 92)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73DecreaseMulCarryRest 0xa0050000 0 0xa0000000 0xa0000100 5000
            (5000 - 2500 : Word) 0 0 0 0 0 (List.replicate 32 0)
            (EvmAsm.Codegen.U256MulU64Be.mulState (List.replicate 32 0)
              (5000 - 2500 : Word) 32)
            (EvmAsm.Codegen.U256MulU64Be.copyState
              (EvmAsm.Codegen.U256MulU64Be.mulState (List.replicate 32 0)
                (5000 - 2500 : Word) 32) (List.replicate 32 0) 32)
            empAssertion **
          regOwn .x10) := by
  exact k73_decrease_entry_status_native_discharged
    (0xa0050038 : Word) 0xa0050000 0 10000 2500 5000 0xa0000000 0xa0000100
    0 0 0 0 0 0 0 0 0 0 0
    (List.replicate 32 0) (List.replicate 40 0) (List.replicate 32 0)
    empAssertion
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by pcf)
    (by simp) (by simp) (by simp)
    (by decide) (by decide)
    (by intro j _; interval_cases j <;> decide)
    (by decide) (by decide)
    (by intro j _; interval_cases j <;> decide)

/-! ### Route-B junction casts

    The whole-route exits live in machine vocabulary; the wrapper's Route-B
    contract (`k73RouteBCallPost` / `k73PostOwn` / `k73FailurePost`) lives in
    wrapper vocabulary.  Each cast is a pointwise implication from one exit
    instance to its Route-B arm.  The wrapper-world atoms the machine route
    never speaks about (`hvbfFrame` save slots, the header region, ownership
    of `x5/x6/x7/x13/x28..x31`) ride through every seam inside the ambient
    `Genv` instantiation - the piggyback below - exactly like the equal-route
    adapter's `k73_piggyback`.  Exit atoms with no Route-B home (the subtract
    scratch ownerships, the multiply scratch frame, the accumulator window,
    the restored-register ownerships) are absorbed into the trailing `F`
    slot, which the discharger instantiates freely. -/

/-- The subtract's written bytes at `Expected`: the base minus the twice-
    halved accumulator image.  Defined as one token (body identical to the
    inline spelling inside `k73_decr_sub_return_post`) so the content cast
    can be stated without quadruple-spelling the quotient windows. -/
private def k73_decr_sub_bytes (baseBytes : List (BitVec 8)) (deltaV target : Word)
    (outWin : List (BitVec 8)) : List (BitVec 8) :=
  u256SubBeBytes baseBytes
    (u256DivU64BeQuotBytes
      (u256DivU64BeQuotBytes (k73_decr_img2 baseBytes deltaV outWin)
        (k73_decr_img2 baseBytes deltaV outWin) target)
      (u256DivU64BeQuotBytes (k73_decr_img2 baseBytes deltaV outWin)
        (k73_decr_img2 baseBytes deltaV outWin) target) 8)
    (u256DivU64BeQuotBytes
      (u256DivU64BeQuotBytes (k73_decr_img2 baseBytes deltaV outWin)
        (k73_decr_img2 baseBytes deltaV outWin) target)
      (u256DivU64BeQuotBytes (k73_decr_img2 baseBytes deltaV outWin)
        (k73_decr_img2 baseBytes deltaV outWin) target) 8)

/-- The wrapper-world ambient carried through the decrease route: the
    `hvbfFrame` save slots, the header region, and ownership of every register
    the machine route's exits leave unclaimed but `k73PostOwn` /
    `k73FailurePost` demand.  Top-level def, not a body-local let (certificate
    tactics fail on let-zeta free variables). -/
private def k73_decr_piggyback (wspH old8 headerPtr : Word)
    (headerBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  frameSlotsSaved hvbfFrame wspH (hvbfSaved (H + 40) old8) **
    bytesRegion headerPtr headerBytes **
    regOwn .x13 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F

/-- Pointwise content swap of an `Expected` window (uses `▸`; `rw` fails
    under implicit transparency). -/
private theorem decr_br_cast {le le' : List (BitVec 8)} {Z : Assertion}
    (heq : le = le') :
    ∀ q : PartialState, ((bytesRegion Expected le ** Z) q) →
      ((bytesRegion Expected le' ** Z) q) :=
  fun _ hp => heq ▸ hp

/-- Success-arm junction cast: the fall exit of the decrease route (status
    `0`, output = the subtract's written bytes) yields the Route-B success
    arm `k73PostOwn` with `Expected` pinned at the spec's written image.
    `hcast` is the arithmetic identity `k73_decr_sub_bytes = hvbfWrittenImage`
    (discharged at the adapter from `k73_decr_machine_bytes_eq_written`). -/
private theorem k73_decr_sub_return_routeB_succ
    (wspH wspK headerPtr parentPtr v9 old18 v19 v20 gasLimit gasUsed target : Word)
    (parentBytes outWin headerBytes : List (BitVec 8)) (Frest : Assertion)
    (hcast : k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin
      = hvbfWrittenImage gasLimit gasUsed parentBytes) :
    ∀ s : PartialState,
      (k73_decr_sub_return_post wspH wspK (H + 40) target parentPtr Expected
        gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
        (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest)
        (0 : Word)) s →
      (((.x1 ↦ᵣ (H + 40)) ** k73PostOwn wspH wspK headerPtr v9 old18 target
        v19 v20 gasUsed parentPtr parentBytes
        (hvbfWrittenImage gasLimit gasUsed parentBytes) headerBytes
        (H + 40) old8
        (regOwns u256SubBeInPlaceScratch **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
            parentPtr Expected target (target - gasUsed) (0 : Word) **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (k73_decr_img1 parentBytes (target - gasUsed)) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** Frest)) s) := by
  intro s hp
  -- Unfold the exit (`regsAt` into its six pins, the sub-bytes token) and
  -- regroup: the three register pins and the output window up front.
  have hEq1 : (k73_decr_sub_return_post wspH wspK (H + 40) target parentPtr Expected
      gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
      (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) (0 : Word)) =
      ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ Expected) **
        (.x12 ↦ᵣ Expected) **
        bytesRegion Expected
          (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) := by
    simp only [k73_decr_sub_return_post, k73Frame, regsAt_cons, regsAt_nil,
      k73Saved, sepConj_emp_right', k73_decr_sub_bytes]
    xperm_cert_eq
  have hp1 : (((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ Expected) **
        (.x12 ↦ᵣ Expected) **
        bytesRegion Expected
          (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s) :=
    hEq1 ▸ hp
  -- Lifts: x10, x11, x12 (positions 2, 3, 4 under the x2 head).
  have hc10 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_sep_pin_lift (r := Reg.x10) (v := (0 : Word))) s hp1
  have hc11 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := regOwn .x10)
      (decr_sep_pin_lift (r := Reg.x11) (v := Expected))) s hc10
  have hc12 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := regOwn .x10)
      (decr_under_id (B := regOwn .x11)
        (decr_sep_pin_lift (r := Reg.x12) (v := Expected)))) s hc11
  -- Window content cast: the subtract's bytes are the spec's written image.
  have hcbr := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := regOwn .x10)
      (decr_under_id (B := regOwn .x11)
        (decr_under_id (B := regOwn .x12)
          (decr_br_cast hcast)))) s hc12
  -- Finale: permutation into the unfolded `k73PostOwn` spelling.
  have hEq2 :
      ((.x2 ↦ᵣ wspH) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x0 ↦ᵣ (0 : Word)) ** regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      (((.x1 ↦ᵣ (H + 40)) ** k73PostOwn wspH wspK headerPtr v9 old18 target
        v19 v20 gasUsed parentPtr parentBytes
        (hvbfWrittenImage gasLimit gasUsed parentBytes) headerBytes
        (H + 40) old8
        (regOwns u256SubBeInPlaceScratch **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
            parentPtr Expected target (target - gasUsed) (0 : Word) **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (k73_decr_img1 parentBytes (target - gasUsed)) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** Frest))) := by
    dsimp only [k73PostOwn, tailRest, tailRestCore, k73_decr_piggyback]
    xperm_cert_eq
  exact hEq2 ▸ hcbr


/-- Borrow-failure junction cast: the borrow-taken exit (routed through the
    shared failure epilogue, status `1`) yields the Route-B failure arm with
    the subtract's written bytes as the scratch image. -/
private theorem k73_decr_sub_return_routeB_fail
    (wspH wspK headerPtr parentPtr v9 old18 v19 v20 _gasLimit gasUsed target : Word)
    (parentBytes outWin headerBytes : List (BitVec 8)) (Frest : Assertion) :
    ∀ s : PartialState,
      (k73_decr_sub_return_post wspH wspK (H + 40) target parentPtr Expected
        gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
        (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest)
        (1 : Word)) s →
      (((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)),
        status ≠ (0 : Word) ∧
        k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed
          parentPtr status parentBytes scratchBytes headerBytes
          (H + 40) old8
          (regOwns u256SubBeInPlaceScratch **
            EvmAsm.Codegen.U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
              (k73_decr_img1 parentBytes (target - gasUsed)) **
            regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
            regOwn .x20 ** Frest) u)) s) := by
  intro s hp
  have hEq1 : (k73_decr_sub_return_post wspH wspK (H + 40) target parentPtr Expected
      gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
      (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) (1 : Word)) =
      ((.x2 ↦ᵣ wspH) ** (.x11 ↦ᵣ Expected) ** (.x12 ↦ᵣ Expected) **
        bytesRegion Expected
          (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) := by
    simp only [k73_decr_sub_return_post, k73Frame, regsAt_cons, regsAt_nil,
      k73Saved, sepConj_emp_right', k73_decr_sub_bytes]
    xperm_cert_eq
  have hp1 : (((.x2 ↦ᵣ wspH) ** (.x11 ↦ᵣ Expected) ** (.x12 ↦ᵣ Expected) **
        bytesRegion Expected
          (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s) :=
    hEq1 ▸ hp
  have hc11 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_sep_pin_lift (r := Reg.x11) (v := Expected)) s hp1
  have hc12 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := regOwn .x11)
      (decr_sep_pin_lift (r := Reg.x12) (v := Expected))) s hc11
  have hEq2 :
      ((.x2 ↦ᵣ wspH) ** regOwn .x11 ** regOwn .x12 **
        bytesRegion Expected
          (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns u256SubBeInPlaceScratch **
        bytesRegion parentPtr parentBytes **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      (((.x1 ↦ᵣ (H + 40)) ** k73FailurePost wspH wspK headerPtr v9 old18 target
        v19 v20 gasUsed parentPtr (1 : Word) parentBytes
        (k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin)
        headerBytes (H + 40) old8
        (regOwns u256SubBeInPlaceScratch **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
            parentPtr Expected target (target - gasUsed) (0 : Word) **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (k73_decr_img1 parentBytes (target - gasUsed)) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** Frest))) := by
    dsimp only [k73FailurePost, tailRest, tailRestScratch, tailRestCore,
      k73_decr_piggyback]
    xperm_cert_eq
  obtain ⟨sa, sb, had, hud, hx1, hFP⟩ := hEq2 ▸ hc12
  exact ⟨sa, sb, had, hud, hx1, ⟨(1 : Word),
    k73_decr_sub_bytes parentBytes (target - gasUsed) target outWin, by decide,
    hFP⟩⟩


/-- Multiply-overflow failure junction cast: the mul-status taken exit
    (routed through the shared failure epilogue, status `1`) yields the
    Route-B failure arm with the multiply's output image as the scratch
    bytes; the overflow window's existential index is fixed and its window
    atoms join the absorbed junk. -/
private theorem k73_decr_mulfail_routeB_fail
    (wspH wspK headerPtr parentPtr v9 old18 v19 v20 _gasLimit gasUsed target : Word)
    (parentBytes outWin headerBytes : List (BitVec 8)) (Frest : Assertion) :
    ∀ s : PartialState,
      (k73_decr_mulfail_taken_post wspH wspK (H + 40) target parentPtr Expected
        gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
        (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest)) s →
      (((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)) (k : Nat),
        status ≠ (0 : Word) ∧
        k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed
          parentPtr status parentBytes scratchBytes headerBytes
          (H + 40) old8
          (EvmAsm.Codegen.U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            k73MulOverflowCoreNoStatus
              (k73_decr_img1 parentBytes (target - gasUsed)) k **
            regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
            regOwn .x19 ** regOwn .x20 ** regOwn .x14 ** regOwn .x15 **
            regOwn .x16 ** regOwn .x17 ** Frest) u)) s) := by
  intro s hp
  have hEq1 : (k73_decr_mulfail_taken_post wspH wspK (H + 40) target parentPtr
      Expected gasUsed headerPtr v9 old18 v19 v20 parentBytes outWin
      (k73_decr_piggyback wspH old8 headerPtr headerBytes Frest)) =
      ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        k73_decr_mulfail_win wspK (target - gasUsed) target parentPtr Expected
          parentBytes outWin **
        EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
          Expected parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) := by
    simp only [k73_decr_mulfail_taken_post, k73Frame, regsAt_cons, regsAt_nil,
      k73Saved, sepConj_emp_right', k73_decr_mulfail_junk, k73_decr_ghole,
      EvmAsm.Codegen.U256MulU64Be.mulTailExtra]
    xperm_cert_eq
  have hp1 : (((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        k73_decr_mulfail_win wspK (target - gasUsed) target parentPtr Expected
          parentBytes outWin **
        EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
          Expected parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s) :=
    hEq1 ▸ hp
  -- Fix the overflow window's existential index.
  have hp2 : (((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (fun u => ∃ k,
          (U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            bytesRegion Expected
              (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
            k73MulOverflowCoreNoStatus
              (k73_decr_img1 parentBytes (target - gasUsed)) k) u) **
        EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
          Expected parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s) := hp1
  -- Rotate the existential window to the front, then crack it in one step.
  have hrot : ((        (.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        (fun u => ∃ k,
          (U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            bytesRegion Expected
              (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
            k73MulOverflowCoreNoStatus
              (k73_decr_img1 parentBytes (target - gasUsed)) k) u) **
        EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
          Expected parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      ((fun u => ∃ k,
          (U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            bytesRegion Expected
              (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
            k73MulOverflowCoreNoStatus
              (k73_decr_img1 parentBytes (target - gasUsed)) k) u) **
        (        (.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
          Expected parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest))) := by
    xperm_cert_eq
  obtain ⟨k, hk⟩ := (sepConj_exists_left s).mp (hrot ▸ hp2)
  -- Bridge the folded mulTailExtra token to its expanded atoms.
  have hE : ((U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        parentPtr Expected target (target - gasUsed) (0 : Word) **
      bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
      k73MulOverflowCoreNoStatus
        (k73_decr_img1 parentBytes (target - gasUsed)) k) **
      (.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      frameSlotsSaved k73Frame wspK
        (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
      EvmAsm.Codegen.U256MulU64Be.mulTailExtra parentPtr (target - gasUsed)
        Expected parentBytes **
      regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        parentPtr Expected target (target - gasUsed) (0 : Word) **
      bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
      k73MulOverflowCoreNoStatus
        (k73_decr_img1 parentBytes (target - gasUsed)) k **
      (.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
      (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
      frameSlotsSaved k73Frame wspK
        (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
      bytesRegion parentPtr parentBytes **
      (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
      (.x12 ↦ᵣ Expected) ** regOwn .x13 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
      regOwn .x20 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) := by
    dsimp only [EvmAsm.Codegen.U256MulU64Be.mulTailExtra]
    xperm_cert_eq
  have hkEq : ((        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
                (.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        bytesRegion parentPtr parentBytes **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) ** regOwn .x13 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) ** regOwn .x13 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest)) := by
    xperm_cert_eq
  have hk0X := by
    have hk' := hk
    rw [hE] at hk'
    exact hk'
  have hk0 : (((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) ** regOwn .x13 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s)  := by
    have hx := hk0X
    rw [hkEq] at hx
    exact hx
  have hEqR : ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) ** regOwn .x13 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) := by
    xperm_cert_eq
  have hk1 : (((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (target - gasUsed)) **
        (.x12 ↦ᵣ Expected) **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) s) :=
    hEqR ▸ hk0
  have hc7 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := (.x10 ↦ᵣ 1))
      (decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
        (decr_sep_pin_lift (r := Reg.x7) (v := (0 : Word))))) s hk1
  have hc11 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := (.x10 ↦ᵣ 1))
      (decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
        (decr_under_id (B := regOwn .x7)
          (decr_sep_pin_lift (r := Reg.x11) (v := (target - gasUsed)))))) s hc7
  have hc12 := decr_under_id (B := (.x2 ↦ᵣ wspH))
    (decr_under_id (B := (.x10 ↦ᵣ 1))
      (decr_under_id (B := (.x0 ↦ᵣ (0 : Word)))
        (decr_under_id (B := regOwn .x7)
          (decr_under_id (B := regOwn .x11)
            (decr_sep_pin_lift (r := Reg.x12) (v := Expected)))))) s hc11
  have hEq2 :
      ((.x2 ↦ᵣ wspH) ** (.x10 ↦ᵣ 1) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 **
        U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion Expected (k73_decr_img2 parentBytes (target - gasUsed) outWin) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        (.x1 ↦ᵣ (H + 40)) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
        frameSlotsSaved k73Frame wspK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        regOwn .x13 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion parentPtr parentBytes **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        k73_decr_piggyback wspH old8 headerPtr headerBytes Frest) =
      (((.x1 ↦ᵣ (H + 40)) ** k73FailurePost wspH wspK headerPtr v9 old18 target
        v19 v20 gasUsed parentPtr (1 : Word) parentBytes
        (k73_decr_img2 parentBytes (target - gasUsed) outWin) headerBytes
        (H + 40) old8
        (U256MulU64Be.frameSlots (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        k73MulOverflowCoreNoStatus
          (k73_decr_img1 parentBytes (target - gasUsed)) k **
        regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** Frest))) := by
    dsimp only [k73FailurePost, tailRest, tailRestScratch, tailRestCore,
      k73_decr_piggyback]
    xperm_cert_eq
  obtain ⟨sa, sb, had, hud, hx1, hFP⟩ := hEq2 ▸ hc12
  exact ⟨sa, sb, had, hud, hx1, ⟨(1 : Word),
    k73_decr_img2 parentBytes (target - gasUsed) outWin, k, by decide,
    hFP⟩⟩


/- ## Wrapper-vocabulary Route-B adapter for the decrease route (#12346 residual 2b)

The three machine exits (multiply-overflow failure, borrow failure, success)
are folded into the single `k73RouteBCallPost` disjunction whose `F` slot is
`k73_decr_outj`: the junk every decrease exit genuinely leaves behind (the
subtract/multiply scratch-register ownerships, the multiply scratch frame, the
accumulator image) and the caller's ambient `F`.  The multiply-overflow arm's
proof-artifact step index `k` is eliminated because `k73MulOverflowCoreNoStatus`
pins `x5`/`x6` to `k`-dependent *values*; lifting those pins to ownership
(`regIs_implies_regOwn`) makes the arm `k`-free and lands exactly on the
`regOwns u256SubBeInPlaceScratch` the unified junk demands. -/

/-- The wrapper-world atoms the decrease machine route consumes at entry but
    the wrapper premise (`k73PreRest`) supplies beyond its fixed atoms. -/
private def k73_decr_env (wspK : Word) (f0 f1 f2 f3 f4 f5 : Word)
    (accWin : List (BitVec 8)) (F : Assertion) : Assertion :=
  regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 **
    EvmAsm.Codegen.U256MulU64Be.frameSlots
      (wspK + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
    bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin **
    regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
    regOwn .x13 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** F

/-- The unified decrease-route junk: every exit leaves these atoms behind and
    nothing more; the caller's ambient `F` rides at the tail. -/
private def k73_decr_outj (wspK _headerPtr parentPtr _v9 _old18 _v19 _v20 gasUsed
    target : Word) (parentBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  regOwns u256SubBeInPlaceScratch **
    EvmAsm.Codegen.U256MulU64Be.frameSlots
      (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
      parentPtr Expected target (target - gasUsed) (0 : Word) **
    bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
      (k73_decr_img1 parentBytes (target - gasUsed)) **
    regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 ** regOwn .x20 ** F

/-- A two-way branch whose taken and fall exits are the *same* point (both
    legs have already returned) is a triple with disjunctive post. -/
private theorem k73_decr_branch_to_triple {n : Nat} {entry pt : Word}
    {cr : CodeReq} {P Qt Qf : Assertion}
    (h : cpsBranchWithin n entry cr P pt Qt pt Qf) :
    cpsTripleWithin n entry pt cr P (fun s => Qt s ∨ Qf s) := by
  intro R hR s hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hbranch⟩ := h R hR s hcr hPR hpc
  refine ⟨k, hk, s', hstep, ?_⟩
  rcases hbranch with ⟨hpc', hQR⟩ | ⟨hpc', hQR⟩
  · obtain ⟨hst, hcomp, hhold⟩ := hQR
    exact ⟨hpc', hst, hcomp, decr_or_left_lift _ hhold⟩
  · obtain ⟨hst, hcomp, hhold⟩ := hQR
    exact ⟨hpc', hst, hcomp, decr_or_right_lift _ hhold⟩

/-- The multiply-overflow failure arm carries a proof-artifact `k` (the
    overflow window's step index).  `k73MulOverflowCoreNoStatus` pins `x5` and
    `x6` to `k`-dependent values; lifting those pins to ownership makes the
    arm `k`-free with junk exactly `k73_decr_outj`'s body. -/
private theorem k73_decr_mulfail_arm_unify
    (wspH wspK headerPtr parentPtr v9 old18 v19 v20 _gasLimit gasUsed target : Word)
    (parentBytes _outWin headerBytes : List (BitVec 8)) (F : Assertion) :
    ∀ s : PartialState,
      ((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)) (k : Nat),
        status ≠ (0 : Word) ∧
        k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed
          parentPtr status parentBytes scratchBytes headerBytes
          (H + 40) old8
          (EvmAsm.Codegen.U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            k73MulOverflowCoreNoStatus
              (k73_decr_img1 parentBytes (target - gasUsed)) k **
            regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
            regOwn .x19 ** regOwn .x20 ** regOwn .x14 ** regOwn .x15 **
            regOwn .x16 ** regOwn .x17 ** F) u)) s →
      (((.x1 ↦ᵣ (H + 40)) ** (fun u => ∃ (status : Word)
        (scratchBytes : List (BitVec 8)),
        status ≠ (0 : Word) ∧
        k73FailurePost wspH wspK headerPtr v9 old18 target v19 v20 gasUsed
          parentPtr status parentBytes scratchBytes headerBytes
          (H + 40) old8
          (regOwns u256SubBeInPlaceScratch **
            EvmAsm.Codegen.U256MulU64Be.frameSlots
              (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
              parentPtr Expected target (target - gasUsed) (0 : Word) **
            bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
              (k73_decr_img1 parentBytes (target - gasUsed)) **
            regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
            regOwn .x20 ** F) u)) s) := by
  intro s hp
  obtain ⟨sa, sb, had, hud, hx1, harm⟩ := hp
  obtain ⟨st, scr, k, hne, hFP⟩ := harm
  refine ⟨sa, sb, had, hud, hx1, ⟨st, scr, hne, ?_⟩⟩
  dsimp only [k73FailurePost, tailRest, tailRestScratch, tailRestCore,
    k73MulOverflowCoreNoStatus] at hFP ⊢
  have hR : ∀ q : PartialState,
      ((EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        (((.x5 ↦ᵣ (EvmAsm.Codegen.U256MulU64Be.accBase +
              BitVec.ofNat 64 (32 + k))) **
          (.x6 ↦ᵣ BitVec.ofNat 64 (8 - k)) **
          regOwn .x28 **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (k73_decr_img1 parentBytes (target - gasUsed))) **
        (regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
          regOwn .x19 ** regOwn .x20 ** regOwn .x14 ** regOwn .x15 **
          regOwn .x16 ** regOwn .x17 ** F))) q) →
      ((regOwns u256SubBeInPlaceScratch **
        EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
          (k73_decr_img1 parentBytes (target - gasUsed)) **
        regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
        regOwn .x20 ** F) q) := by
    intro q hq
    have t1 := decr_under_id
      (B := EvmAsm.Codegen.U256MulU64Be.frameSlots
        (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        parentPtr Expected target (target - gasUsed) (0 : Word))
      (decr_sep_pair_congr
        (decr_sep_pin_lift (r := Reg.x5)
          (v := EvmAsm.Codegen.U256MulU64Be.accBase + BitVec.ofNat 64 (32 + k)))
        (fun _ h => h)) q hq
    have t2 := decr_under_id
      (B := EvmAsm.Codegen.U256MulU64Be.frameSlots
        (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        parentPtr Expected target (target - gasUsed) (0 : Word))
      (decr_sep_pair_congr
        (decr_sep_pair_congr (fun _ h => h)
          (decr_sep_pin_lift (r := Reg.x6) (v := BitVec.ofNat 64 (8 - k))))
        (fun _ h => h)) q t1
    have hE : ((EvmAsm.Codegen.U256MulU64Be.frameSlots
          (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
          parentPtr Expected target (target - gasUsed) (0 : Word) **
        ((regOwn .x5 ** (regOwn .x6 ** (regOwn .x28 **
            bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
              (k73_decr_img1 parentBytes (target - gasUsed))))) **
          (regOwn .x13 ** regOwn .x7 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
            regOwn .x19 ** regOwn .x20 ** regOwn .x14 ** regOwn .x15 **
            regOwn .x16 ** regOwn .x17 ** F))) =
        (regOwns u256SubBeInPlaceScratch **
          EvmAsm.Codegen.U256MulU64Be.frameSlots
            (wspK + signExtend12 (-48 : BitVec 12)) (K73 + 88)
            parentPtr Expected target (target - gasUsed) (0 : Word) **
          bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase
            (k73_decr_img1 parentBytes (target - gasUsed)) **
          regOwn .x8 ** regOwn .x9 ** regOwn .x18 ** regOwn .x19 **
          regOwn .x20 ** F)) := by
      simp only [u256SubBeInPlaceScratch, regOwns_cons, regOwns_nil,
        sepConj_emp_right']
      xperm_cert_eq
    exact hE ▸ t2

  have hc := decr_under_id (B := ((.x2 ↦ᵣ wspH))) (decr_under_id (B := ((.x8 ↦ᵣ headerPtr))) (decr_under_id (B := ((.x10 ↦ᵣ st))) (decr_under_id (B := (regOwn .x11)) (decr_under_id (B := ((.x0 ↦ᵣ (0 : Word)))) (decr_under_id (B := (frameSlotsSaved hvbfFrame wspH (hvbfSaved (H + 40) old8))) (decr_under_id (B := ((.x9 ↦ᵣ v9))) (decr_under_id (B := ((.x18 ↦ᵣ old18))) (decr_under_id (B := ((.x19 ↦ᵣ v19))) (decr_under_id (B := ((.x20 ↦ᵣ v20))) (decr_under_id (B := (regOwn .x12)) (decr_under_id (B := (regOwn .x13)) (decr_under_id (B := (regOwn .x5)) (decr_under_id (B := (regOwn .x6)) (decr_under_id (B := (regOwn .x7)) (decr_under_id (B := (regOwn .x28)) (decr_under_id (B := (regOwn .x29)) (decr_under_id (B := (regOwn .x30)) (decr_under_id (B := (regOwn .x31)) (decr_under_id (B := (frameSlotsSaved k73Frame wspK (k73Saved (H + 40) headerPtr v9 old18 v19 v20))) (decr_under_id (B := (bytesRegion headerPtr headerBytes)) (decr_under_id (B := (bytesRegion parentPtr parentBytes)) (decr_under_id (B := (bytesRegion Expected scr)) (hR))))))))))))))))))))))) sb hFP
  exact hc


/-- The whole nonzero-decrease route, assembled in the wrapper's vocabulary:
    from `k73PreRest` at the wrapper's stack frame to the Route-B callee post
    `k73RouteBCallPost`.  The success arm pins the expected buffer at
    `hvbfWrittenImage`; both failure flavours fold into the existential
    failure arm; the fixed exit junk rides in the trailing `F` slot as
    `k73_decr_outj`. -/
theorem k73_decr_route_adapter {cr : CodeReq}
    (spH spK old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes accWin : List (BitVec 8))
    (f0 f1 f2 f3 f4 f5 : Word) (F : Assertion)
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (hne : gasUsed ≠ gasLimit >>> 1)
    (hnotlt : ¬ (gasLimit >>> 1).toNat < gasUsed.toNat)
    (hnonzero : gasUsed ≠ 0)
    (hret : ((H + 40 : Word) &&& ~~~(1 : Word)) = H + 40)
    (hF : F.pcFree)
    (htargetPos : 0 < (gasLimit >>> 1).toNat)
    (hleTarget : (gasLimit >>> 1).toNat ≤ 2 ^ 56)
    (hMulFit : EvmAsm.Stateless.SpecRef.bytesBEtoNat parentBytes *
      ((gasLimit >>> 1) - gasUsed).toNat < 2 ^ 256)
    (hlenP : parentBytes.length = 32)
    (hExpectedLen : expectedBytes.length = 32)
    (hlenAcc : accWin.length = 40)
    (halignA : parentPtr.toNat % 8 = 0)
    (hoverA : parentPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ j, j < 32 →
      isValidByteAccess (parentPtr + BitVec.ofNat 64 j) = true)
    (halignOut : Expected.toNat % 8 = 0)
    (hoverOut : Expected.toNat + 32 < 2 ^ 64)
    (hvalidOut : ∀ j, j < 32 →
      isValidByteAccess (Expected + BitVec.ofNat 64 j) = true)
    (hdisj : parentPtr.toNat + 32 ≤ Expected.toNat ∨
      Expected.toNat + 32 ≤ parentPtr.toNat)
    (hrw : RwRegion.wf ⟨Expected, 32⟩)
    (hroBase : Region.wf ⟨parentPtr, parentBytes⟩)
    (hszDiv1 :
      4 * ((u256DivU64BeInPlaceFn Expected (gasLimit >>> 1)
        (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)).body.size + 1)
        ≤ 2 ^ 64)
    (hszDiv2 :
      4 * ((u256DivU64BeInPlaceFn Expected 8
        (u256DivU64BeQuotBytes
          (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
          (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
          (gasLimit >>> 1))).body.size
          + 1)
        ≤ 2 ^ 64)
    (hszSub :
      4 * ((u256SubBeInPlaceFn parentPtr Expected parentBytes
        (u256DivU64BeQuotBytes
          (u256DivU64BeQuotBytes
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (gasLimit >>> 1))
          (u256DivU64BeQuotBytes
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
            (gasLimit >>> 1))
          8)).body.size + 1)
        ≤ 2 ^ 64)
    (hk73Mono : ∀ a i, wholeCode a = some i → cr a = some i) :
    cpsTripleWithin
      ((19 + 3852 + 9) +
        (((((10 +
              (u256DivU64BeInPlaceFn Expected (gasLimit >>> 1)
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)).body.steps +
            (u256DivU64BeInPlaceFn Expected 8
              (u256DivU64BeQuotBytes
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (gasLimit >>> 1))).body.steps +
          1) +
          (1 + (5 + (u256SubBeInPlaceFn parentPtr Expected parentBytes
            (u256DivU64BeQuotBytes
              (u256DivU64BeQuotBytes
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (gasLimit >>> 1))
              (u256DivU64BeQuotBytes
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
                (gasLimit >>> 1))
              8)).body.steps))) + 1) + 9) + 10))
      K73 (H + 40) cr
      ((.x1 ↦ᵣ (H + 40)) ** k73PreRest spH spK headerPtr v9 old18 v19 v20
        gasLimit gasUsed parentPtr parentBytes expectedBytes headerBytes
        (H + 40) old8
        (k73_decr_env spK f0 f1 f2 f3 f4 f5 accWin F))
      ((.x1 ↦ᵣ (H + 40)) ** k73RouteBCallPost spH spK (H + 40) old8 headerPtr
        v9 old18 (gasLimit >>> 1) v19 v20 gasUsed gasLimit parentPtr
        parentBytes headerBytes
        (k73_decr_outj spK headerPtr parentPtr v9 old18 v19 v20 gasUsed
          (gasLimit >>> 1) parentBytes F)) := by
  have hGenv : (k73_decr_piggyback spH old8 headerPtr headerBytes F).pcFree := by
    dsimp only [k73_decr_piggyback]
    pcf
    exact hF
  have ht2 : (gasLimit >>> 1).toNat = gasLimit.toNat / 2 := rfl
  have hne' : gasUsed.toNat ≠ (gasLimit >>> 1).toNat :=
    fun h => hne (BitVec.eq_of_toNat_eq h)
  have hdecr : gasUsed.toNat < gasLimit.toNat / 2 := by omega
  have halenA2 :
      ((k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)).length = 32 := by
    rw [k73_decr_img2]
    exact EvmAsm.Codegen.U256MulU64Be.copyState_len _ _ 32 hExpectedLen
  have hvalA2 :
      EvmAsm.Crypto.beBytesToNat (k73_decr_img2 parentBytes ((gasLimit >>> 1) - gasUsed) expectedBytes)
        = (EvmAsm.Crypto.beBytesToNat parentBytes *
            ((gasLimit >>> 1) - gasUsed).toNat) % 2 ^ 256 :=
    EvmAsm.Codegen.U256MulU64Be.beBytesToNat_mulOutput parentBytes expectedBytes ((gasLimit >>> 1) - gasUsed)
      hlenP hExpectedLen
  have hcast : k73_decr_sub_bytes parentBytes ((gasLimit >>> 1) - gasUsed)
      (gasLimit >>> 1) expectedBytes
      = hvbfWrittenImage gasLimit gasUsed parentBytes :=
    k73_decr_machine_bytes_eq_written rfl hdecr htargetPos hleTarget hlenP
      halenA2 hMulFit hvalA2
  have hw := k73_decrease_route_machine_spec_within spH spK (H + 40) gasLimit
    gasUsed (gasLimit >>> 1) parentPtr Expected headerPtr v9 old18 v19 v20
    f0 f1 f2 f3 f4 f5 parentBytes accWin expectedBytes
    (k73_decr_piggyback spH old8 headerPtr headerBytes F)
    hspK rfl hne hnotlt hnonzero hGenv hret hlenP hlenAcc hExpectedLen
    halignA hoverA hvalidA halignOut hoverOut hvalidOut htargetPos hdisj hrw
    hroBase hszDiv1 hszDiv2 hszSub
  have htri := k73_decr_branch_to_triple hw
  have htriC := cpsTripleWithin_extend_code hk73Mono htri
  have hpreEq :
      ((.x1 ↦ᵣ (H + 40)) ** k73PreRest spH spK headerPtr v9 old18 v19 v20
          gasLimit gasUsed parentPtr parentBytes expectedBytes headerBytes
          (H + 40) old8 (k73_decr_env spK f0 f1 f2 f3 f4 f5 accWin F)) =
      k73HeadPre spH spK (H + 40) gasLimit gasUsed parentPtr Expected
        headerPtr v9 old18 v19 v20 parentBytes expectedBytes
        (EvmAsm.Codegen.U256MulU64Be.frameSlots
          (spK + signExtend12 (-48 : BitVec 12)) f0 f1 f2 f3 f4 f5 **
        bytesRegion EvmAsm.Codegen.U256MulU64Be.accBase accWin **
        k73_decr_ghole spK
          (regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            k73_decr_piggyback spH old8 headerPtr headerBytes F)) := by
    dsimp only [k73HeadPre, k73PreRest]
    dsimp only [k73_decr_env, k73_decr_ghole, k73_decr_piggyback]
    xperm
  refine cpsTripleWithin_weaken (fun s hp => hpreEq ▸ hp) (fun s hq => ?_) htriC
  rcases hq with hm | hs0
  · rcases hm with hm | hs1
    · have hM := k73_decr_mulfail_routeB_fail spH spK headerPtr parentPtr v9
        old18 v19 v20 gasLimit gasUsed (gasLimit >>> 1) parentBytes expectedBytes
        headerBytes F s hm
      have hMu := k73_decr_mulfail_arm_unify spH spK headerPtr parentPtr v9
        old18 v19 v20 gasLimit gasUsed (gasLimit >>> 1) parentBytes expectedBytes
        headerBytes F s hM
      obtain ⟨sa, sb, had, hud, hx1, harm⟩ := hMu
      exact ⟨sa, sb, had, hud, hx1, Or.inr harm⟩
    · have hB := k73_decr_sub_return_routeB_fail spH spK headerPtr parentPtr v9
        old18 v19 v20 gasLimit gasUsed (gasLimit >>> 1) parentBytes expectedBytes
        headerBytes F s hs1
      obtain ⟨sa, sb, had, hud, hx1, harm⟩ := hB
      exact ⟨sa, sb, had, hud, hx1, Or.inr harm⟩
  · have hS := k73_decr_sub_return_routeB_succ spH spK headerPtr parentPtr v9
      old18 v19 v20 gasLimit gasUsed (gasLimit >>> 1) parentBytes expectedBytes
      headerBytes F hcast s hs0
    obtain ⟨sa, sb, had, hud, hx1, hPO⟩ := hS
    exact ⟨sa, sb, had, hud, hx1, Or.inl hPO⟩

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute
