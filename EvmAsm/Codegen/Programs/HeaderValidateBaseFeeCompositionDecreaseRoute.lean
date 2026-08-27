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

theorem decr_under_id {P P' B : Assertion}
    (hT : ∀ q, P q → P' q) :
    ∀ q : PartialState, ((B ** P) q) → ((B ** P') q) :=
  fun _ hp => by
    obtain ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    exact ⟨h1, h2, hd, hunion, hl, hT _ hr⟩

theorem decr_sep_pin_lift {r v Z} :
    ∀ q : PartialState, (((r : Reg) ↦ᵣ v) ** Z) q → ((regOwn r) ** Z) q :=
  fun _ hp => by
    obtain ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    exact ⟨h1, h2, hd, hunion,
      regIs_implies_regOwn (r := r) (v := v) _ hl, hr⟩

theorem decr_sep_pair_congr {A A' B B' : Assertion}
    (hA : ∀ q, A q → A' q) (hB : ∀ q, B q → B' q) :
    ∀ q : PartialState, ((A ** B) q) → ((A' ** B') q) :=
  fun _ hp => by
    obtain ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    exact ⟨h1, h2, hd, hunion, hA _ hl, hB _ hr⟩

theorem decr_or_left_lift {A B R : Assertion} :
    ∀ q : PartialState, ((A ** R) q) → (((fun s => A s ∨ B s) ** R) q) :=
  fun _ hp => by
    obtain ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    exact ⟨h1, h2, hd, hunion, Or.inl hl, hr⟩

theorem decr_or_right_lift {A B R : Assertion} :
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
end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute
