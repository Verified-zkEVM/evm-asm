/-
  EvmAsm.Codegen.Programs.HeaderBaseFeeWholeRoutes

  K73 route-specific compositions. The shared setup and branch machinery
  lives in HeaderBaseFeeWholeTop; this module keeps the return and dispatcher
  compositions separate so both files remain within the codegen file cap.
  The x14--x17 atoms passed through the shared flat arithmetic seams are a
  deliberate over-approximation; exact K73 footprint is [x5, x6, x7, x28,
  x29, x30, x31] plus genuine x13 clobber. Item 12 tracks the shared
  cancellation needed before Route B can claim the narrower pre.
-/

import EvmAsm.Rv64.Tactics.XCancelStruct
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeTop

set_option maxRecDepth 8000

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

set_option linter.defProp false in
def k73_increase_first_div_source_branch_for_return :=
  k73_increase_first_div_source_branch

set_option linter.defProp false in
def k73_increase_second_add_branch_for_return :=
  k73_increase_second_add_branch

set_option linter.defProp false in
def k73_increase_second_div_source_branch_for_return :=
  k73_increase_second_div_source_branch

set_option linter.defProp false in
def k73_increase_status_div_zero_spec_within_for_return :=
  k73_increase_status_div_zero_spec_within

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.U256DivU64BeSAsm
open EvmAsm.Codegen.U256AddBeSAsm
open EvmAsm.Codegen.U256AddBeBInPlaceSAsm
private theorem k73_increase_carry_to_failure_pre
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (F : Assertion) : ∀ s,
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes F ** regOwn .x10) s →
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        regOwn .x10 ** k73IncreaseCarryTail spH gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes F) s := by
  intro s hs
  let Core : Nat → Assertion := fun k =>
    k73MulEpilogueNoRa
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion outPtr outBytes ** k73MulOverflowCoreNoStatus accBytes k
  let CoreOwn : Nat → Assertion := fun k =>
    EvmAsm.Codegen.U256MulU64Be.frameSlots
        (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
        basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion outPtr outBytes ** k73MulOverflowCoreNoStatus accBytes k
  let C : Assertion := F
  let A : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 88)) **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
        (gasUsed - target) outPtr baseBytes ** regOwn .x10
  have hsource : (A ** ((fun u => ∃ k, Core k u) ** C)) s := by
    dsimp [A, C, Core, k73IncreaseCarryTail,
      k73IncreaseMulCarryRest, k73MulEpilogueNoRa] at hs ⊢
    xperm_hyp hs
  have hcoreOwn : ∀ k h, Core k h →
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest1 ** CoreOwn k) h := by
    intro k h hk
    let vals : Reg → Word := fun r => match r with
      | .x8 => basePtr
      | .x9 => outPtr
      | .x18 => target
      | .x19 => gasUsed - target
      | .x20 => 1
      | _ => 0
    have hreg := regsAt_implies_regsOwnAt k73FrameRest1 vals
    have hraw :
        (((.x2 : Reg) ↦ᵣ spH) ** regsAt k73FrameRest1 vals ** CoreOwn k) h := by
      dsimp [Core] at hk
      unfold CoreOwn at ⊢
      have hsp :
          (spH + signExtend12 (-48 : BitVec 12)) +
              signExtend12 (48 : BitVec 12) = spH := by
        have hneg : signExtend12 (-48 : BitVec 12) =
            (18446744073709551568 : Word) := by decide
        rw [hneg, signExtend12_48]
        bv_omega
      have hregx2 :
          ((.x2 : Reg) ↦ᵣ
              ((spH + signExtend12 (-48 : BitVec 12)) +
                signExtend12 (48 : BitVec 12))) =
            ((.x2 : Reg) ↦ᵣ spH) := congrArg (fun v => (.x2 : Reg) ↦ᵣ v) hsp
      have haddr :
          signExtend12 (4048 : BitVec 12) =
            signExtend12 (-48 : BitVec 12) := by decide
      have hepi :
          k73MulEpilogueNoRa
              (spH + signExtend12 (4048 : BitVec 12)) (K73 + 88)
              basePtr outPtr target (gasUsed - target) (1 : Word) =
            (((.x2 : Reg) ↦ᵣ spH) ** ((.x8 : Reg) ↦ᵣ basePtr) **
              ((.x9 : Reg) ↦ᵣ outPtr) ** ((.x18 : Reg) ↦ᵣ target) **
              ((.x19 : Reg) ↦ᵣ (gasUsed - target)) **
              ((.x20 : Reg) ↦ᵣ (1 : Word)) **
              EvmAsm.Codegen.U256MulU64Be.frameSlots
                (spH + signExtend12 (-48 : BitVec 12)) (K73 + 88)
                basePtr outPtr target (gasUsed - target) (1 : Word)) := by
        unfold k73MulEpilogueNoRa
        rw [haddr, hregx2]
      have hk' :
          (k73MulEpilogueNoRa
                (spH + signExtend12 (4048 : BitVec 12)) (K73 + 88)
                basePtr outPtr target (gasUsed - target) (1 : Word) **
              bytesRegion outPtr outBytes **
              k73MulOverflowCoreNoStatus accBytes k) h := by
        exact hk
      rw [hepi] at hk'
      simp only [regsAt, k73FrameRest1, List.foldr,
        sepConj_emp_right'] at hk' ⊢
      simp only [vals, K73] at hk' ⊢
      xperm_hyp hk'
    have hown := sepConj_mono_right
      (sepConj_mono_left hreg) h hraw
    exact hown
  have pull_nested : ∀ (X : Assertion) (Y : Nat → Assertion)
      (Z : Assertion) h,
      (X ** ((fun u => ∃ k, Y k u) ** Z)) h →
      ∃ k, (X ** (Y k ** Z)) h := by
    intro X Y Z h hh
    exact sepConj_exists_right h
      (sepConj_mono_right (fun h' hq => (sepConj_exists_left h').mp hq)
        h hh)
  obtain ⟨k, hk⟩ := pull_nested A Core C s hsource
  have hk' : (A ** (Core k ** C)) s := hk
  have hkOwn :
      (A ** (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest1 **
        CoreOwn k) ** C) s := by
    exact sepConj_mono_right
      (fun h hq => sepConj_mono_left (hcoreOwn k) h hq) s hk'
  have hinner : ∀ h,
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest1 ** CoreOwn k) h →
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest1 **
        (fun u => ∃ j, CoreOwn j u)) h := by
    intro h hh
    exact sepConj_mono_right
      (sepConj_mono_right (fun _ hcore => ⟨k, hcore⟩)) h hh
  have houter : ∀ h,
      ((((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest1 ** CoreOwn k) ** C) h →
      ((((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest1 **
        (fun u => ∃ j, CoreOwn j u)) ** C) h := by
    intro h hh
    exact sepConj_mono_left hinner h hh
  have hkExist :
      (A ** ((((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest1 **
        (fun u => ∃ j, CoreOwn j u)) ** C)) s := by
    exact sepConj_mono_right houter s hkOwn
  let Aown : Assertion :=
    ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
        (gasUsed - target) outPtr baseBytes ** regOwn .x10
  have hAown : ∀ h, A h → Aown h := by
    intro h hh
    dsimp [A, Aown]
    exact sepConj_mono_right
      (sepConj_mono_left (regIs_implies_regOwn .x1)) h hh
  have hkOwned :
      (Aown ** ((((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest1 **
        (fun u => ∃ j, CoreOwn j u)) ** C)) s := by
    exact sepConj_mono_left hAown s hkExist
  dsimp [Aown, C] at hkOwned ⊢
  let TailCore : Assertion := fun s =>
    ∃ k, (CoreOwn k) s
  have htail_def :
      k73IncreaseCarryTail spH gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes F =
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
            (gasUsed - target) outPtr baseBytes ** TailCore ** F) := by
    unfold k73IncreaseCarryTail
    dsimp [TailCore, CoreOwn]
  rw [htail_def] at ⊢
  let hkOwned' : Assertion :=
    (((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
      EvmAsm.Codegen.U256MulU64Be.mulTailExtra basePtr
        (gasUsed - target) outPtr baseBytes ** regOwn .x10) **
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest1 ** TailCore) ** F
  have hkOwnedAt : hkOwned' s := by
    have hzeroWord : (0 : Word) = BitVec.ofNat 64 0 := by rfl
    simpa only [hkOwned', TailCore, hzeroWord, sepConj_assoc'] using hkOwned
  simp only [hkOwned', regsOwnAt, k73Frame, k73FrameRest1, List.foldr,
    sepConj_emp_right'] at hkOwnedAt ⊢
  have hzeroWord : (0 : Word) = BitVec.ofNat 64 0 := by rfl
  simp only [hzeroWord] at hkOwnedAt ⊢
  xperm_hyp hkOwnedAt

private theorem k73_increase_first_div_to_return
    (sp0 spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : (k73Saved raIn v8 v9 v18 v19 v20) .x1 = raIn)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hlenQ2 : q2.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hszAdd : k73AddBSize basePtr outPtr baseBytes q2 ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = K73 + 188 + 4)
    (k : Nat) :
    cpsBranchWithin (1 + k73AddBTailSteps basePtr outPtr baseBytes q2)
      (K73 + 172) wholeCode
      (k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G k)
      (K73 + 204) (fun _ => False) raIn
      (fun s =>
        (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
            (k73Saved raIn v8 v9 v18 v19 v20) **
          frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19 v20) **
          ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes baseBytes q2 q2) **
          bytesRegion basePtr baseBytes **
          U256MulU64Be.frameSlots (spH + signExtend12 (-48))
            (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
          bytesRegion U256MulU64Be.accBase accBytes ** G) s ∨
        (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
            (k73Saved raIn v8 v9 v18 v19 v20) **
          frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19 v20) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes baseBytes q2 q2) **
          bytesRegion basePtr baseBytes **
          U256MulU64Be.frameSlots (spH + signExtend12 (-48))
            (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
          bytesRegion U256MulU64Be.accBase accBytes ** G) s) := by
  have hdiv := k73_increase_first_div_source_branch_for_return
    spH raIn gasUsed basePtr outPtr target v8 v9 v18 v19 v20
    baseBytes accBytes q2 G hG k
  have hF :
      (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
        bytesRegion U256MulU64Be.accBase accBytes ** G).pcFree := by
    pcf
    exact hG
  have hadd := k73_in_place_add_tail_spec_within
    sp0 spH raIn (k73Saved raIn v8 v9 v18 v19 v20)
    basePtr outPtr (K73 + 136) (0 : Word) (8 : Word) outPtr
    baseBytes q2
    (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G)
    hsp hret hsaved hF hrw hroBase hlenBase hlenQ2 hovBase hovOut hdisj
    hszAdd hcallRet
  have hdiv' : cpsBranchWithin 1 (K73 + 172) wholeCode
      (k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G k)
      (K73 + 204) (fun _ => False) (K73 + 176)
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (K73 + 136)) **
        ((.x8 : Reg) ↦ᵣ basePtr) ** ((.x9 : Reg) ↦ᵣ outPtr) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr q2 ** bytesRegion basePtr baseBytes **
        ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
        frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20) **
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48))
          (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
          bytesRegion U256MulU64Be.accBase accBytes ** G)) := by
    refine cpsBranchWithin_weaken
      (fun _ hp => hp) (fun _ hq => hq) (fun _ hq => ?_) hdiv
    simpa only [k73IncreaseFirstAddPre] using hq
  refine cpsBranchWithin_seq_cpsTripleWithin_same_cr hdiv' hadd ?_
  intro _ hq
  exact False.elim hq

private theorem k73_increase_second_add_to_return
    (sp0 spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes orig : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : (k73Saved raIn v8 v9 v18 v19 v20) .x1 = raIn)
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hszAdd : k73AddBSize basePtr outPtr baseBytes orig ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = K73 + 188 + 4) :
    cpsTripleWithin (k73AddBTailSteps basePtr outPtr baseBytes orig)
      (K73 + 176) raIn wholeCode
      (k73IncreaseSecondAddPre spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes orig G)
      (fun s =>
        (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
            (k73Saved raIn v8 v9 v18 v19 v20) **
          frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19 v20) **
          ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes baseBytes orig orig) **
          bytesRegion basePtr baseBytes **
          U256MulU64Be.frameSlots (spH + signExtend12 (-48))
            (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
          bytesRegion U256MulU64Be.accBase accBytes ** G) s ∨
        (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
            (k73Saved raIn v8 v9 v18 v19 v20) **
          frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19 v20) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          regOwns u256AddBeBInPlaceScratch **
          bytesRegion outPtr (u256AddBeBytes baseBytes orig orig) **
          bytesRegion basePtr baseBytes **
          U256MulU64Be.frameSlots (spH + signExtend12 (-48))
            (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
          bytesRegion U256MulU64Be.accBase accBytes ** G) s) := by
  let F : Assertion :=
    U256MulU64Be.frameSlots (spH + signExtend12 (-48))
      (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G
  let FrameRest : Assertion :=
    ((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73FrameRest3 **
      frameSlotsSaved k73Frame spH (k73Saved raIn v8 v9 v18 v19 v20)
  let Fadd : Assertion := FrameRest ** F
  let TailP : Assertion := k73IncreaseAddTailP
    spH basePtr outPtr baseBytes orig F
  have hFrameRest : FrameRest.pcFree := by
    dsimp [FrameRest]
    pcf
  have hFadd : Fadd.pcFree := by
    dsimp [Fadd]
    exact pcFree_sepConj hFrameRest (by dsimp [F]; pcf; exact hG)
  have hTailP : TailP.pcFree := by
    unfold TailP k73IncreaseAddTailP
    pcf
    exact hG
  have hbranch := k73_increase_second_add_branch_for_return
    spH raIn gasUsed basePtr outPtr target v8 v9 v18 v19 v20
    baseBytes accBytes orig G hG hrw hroBase hlenBase hlenOrig hovBase hovOut
    hdisj hszAdd hcallRet
  have hfail := k73_failure_tail_spec_within
    sp0 spH raIn (k73Saved raIn v8 v9 v18 v19 v20) TailP
    hsp hret hsaved hTailP
  have hsucc := k73_success_tail_spec_within
    sp0 spH raIn (k73Saved raIn v8 v9 v18 v19 v20) TailP
    hsp hret hsaved hTailP
  have hbudget :
      k73AddBBranchSteps basePtr outPtr baseBytes orig + 10 ≤
        k73AddBTailSteps basePtr outPtr baseBytes orig := by
    simp only [k73AddBBranchSteps, k73AddBTailSteps]
    omega
  let Qout : Assertion := fun s =>
    (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
        (k73Saved raIn v8 v9 v18 v19 v20) **
      frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19 v20) **
      ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes baseBytes orig orig) **
      bytesRegion basePtr baseBytes **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G) s ∨
    (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
        (k73Saved raIn v8 v9 v18 v19 v20) **
      frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19 v20) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes baseBytes orig orig) **
      bytesRegion basePtr baseBytes **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G) s
  intro R hR s hcr hP hpc
  obtain ⟨k1, hk1, s1, hs1, hcase⟩ := hbranch R hR s hcr hP hpc
  rcases hcase with ⟨hpcFail, hFailPre⟩ | ⟨hpcSucc, hSuccPre⟩
  · have hFailPre' :
        ((((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19 v20) ** regOwn .x10 ** TailP) ** R).holdsFor s1 := by
      simpa only [k73IncreaseAddTailPost, k73AddBTailPost, TailP,
        k73IncreaseAddTailP, F] using hFailPre
    obtain ⟨k2, hk2, s2, hs2, hFailPost⟩ :=
      hfail R hR s1 (CodeReq.SatisfiedBy_preserved hs1 hcr)
        hFailPre' hpcFail
    refine ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2, ?_⟩
    refine ⟨hFailPost.1, ?_⟩
    rcases hFailPost.2 with ⟨hmem, hcompat, hpost⟩
    have hQout : (Qout ** R).holdsFor s2 := by
      have hmap : ∀ h,
          (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
            (k73Saved raIn v8 v9 v18 v19 v20) **
            frameSlotsSaved k73Frame spH
              (k73Saved raIn v8 v9 v18 v19 v20) **
            ((.x10 : Reg) ↦ᵣ (1 : Word)) ** TailP) h →
          Qout h := by
        intro h hp
        left
        simpa only [Qout, TailP, k73IncreaseAddTailP, F] using hp
      exact ⟨hmem, hcompat,
        sepConj_mono_left hmap hmem hpost⟩
    simpa only [Qout] using hQout
  · have hSuccPre' :
        ((((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
          frameSlotsSaved k73Frame spH
            (k73Saved raIn v8 v9 v18 v19 v20) ** regOwn .x10 ** TailP) ** R).holdsFor s1 := by
      simpa only [k73IncreaseAddTailPost, k73AddBTailPost, TailP,
        k73IncreaseAddTailP, F] using hSuccPre
    obtain ⟨k2, hk2, s2, hs2, hSuccPost⟩ :=
      hsucc R hR s1 (CodeReq.SatisfiedBy_preserved hs1 hcr)
        hSuccPre' hpcSucc
    refine ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2, ?_⟩
    refine ⟨hSuccPost.1, ?_⟩
    rcases hSuccPost.2 with ⟨hmem, hcompat, hpost⟩
    have hQout : (Qout ** R).holdsFor s2 := by
      have hmap : ∀ h,
          (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
            (k73Saved raIn v8 v9 v18 v19 v20) **
            frameSlotsSaved k73Frame spH
              (k73Saved raIn v8 v9 v18 v19 v20) **
            ((.x10 : Reg) ↦ᵣ (0 : Word)) ** TailP) h →
          Qout h := by
        intro h hp
        right
        simpa only [Qout, TailP, k73IncreaseAddTailP, F] using hp
      exact ⟨hmem, hcompat,
        sepConj_mono_left hmap hmem hpost⟩
    simpa only [Qout] using hQout

private theorem k73_increase_second_div_to_return
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes orig : List (BitVec 8)) (G : Assertion)
    (hG : G.pcFree) (k : Nat) (Q : Assertion)
    (hadd : cpsTripleWithin
      (k73AddBTailSteps basePtr outPtr baseBytes orig)
      (K73 + 176) raIn wholeCode
      (k73IncreaseSecondAddPre spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes orig G) Q) :
    cpsBranchWithin
      (1 + k73AddBTailSteps basePtr outPtr baseBytes orig)
      (K73 + 172) wholeCode
      (k73IncreaseSecondDivToAddSource spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes orig G k)
      (K73 + 204) (fun _ => False) raIn Q := by
  have hdiv := k73_increase_second_div_source_branch_for_return
    spH raIn gasUsed basePtr outPtr target v8 v9 v18 v19 v20
    baseBytes accBytes orig G hG k
  refine cpsBranchWithin_seq_cpsTripleWithin_same_cr hdiv hadd ?_
  intro _ hq
  exact False.elim hq

private theorem k73_increase_carry_to_return
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8))
    (F Q : Assertion)
    (hQ : cpsTripleWithin 9 (K73 + 272) raIn wholeCode
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19 v20) ** regOwn .x10 **
        k73IncreaseCarryTail spH gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes F)
      Q) :
    cpsTripleWithin 9 (K73 + 272) raIn wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) **
        k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes F ** regOwn .x10)
      Q := by
  intro R hR s hcr hP hpc
  obtain ⟨hmem, hcompat, hP⟩ := hP
  have hP' :
      ((((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19 v20) ** regOwn .x10 **
        k73IncreaseCarryTail spH gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes F) ** R) hmem := by
    exact sepConj_mono_left
      (fun h hp => k73_increase_carry_to_failure_pre
        spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes outBytes F h hp)
      hmem hP
  exact hQ R hR s hcr ⟨hmem, hcompat, hP'⟩ hpc

private theorem k73_increase_div_zero_dispatch
    (spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion)
    (N N1 N2 : Nat) (Q1 Q2 Q : Assertion)
    (hfirst : ∀ k, cpsBranchWithin N1 (K73 + 172) wholeCode
      (k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G k)
      (K73 + 204) (fun _ => False) raIn Q1)
    (hsecond : ∀ k, cpsBranchWithin N2 (K73 + 172) wholeCode
      (k73IncreaseSecondDivToAddSource spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G k)
      (K73 + 204) (fun _ => False) raIn Q2)
    (hQ1 : Crypto.beBytesToNat q2 ≠ 0 → ∀ h, Q1 h → Q h)
    (hQ2 : Crypto.beBytesToNat q2 = 0 → ∀ h, Q2 h → Q h)
    (hN1 : N1 ≤ N) (hN2 : N2 ≤ N) :
    cpsBranchWithin N (K73 + 172) wholeCode
      (k73IncreaseDivZeroPost spH raIn gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes q2 G)
      (K73 + 204) (fun _ => False) raIn Q := by
  intro R hR s hcr hP hpc
  obtain ⟨hmem, hcompat, hPR⟩ := hP
  rcases hPR with ⟨hleft, hright, hdisj, hunion, hpost, hRpost⟩
  unfold k73IncreaseDivZeroPost at hpost
  rcases hpost with ⟨k, hroutePost⟩
  rcases hroutePost with hfirstPost | hsecondPost
  · obtain ⟨hfp, hn⟩ := (sepConj_pure_right _).1 hfirstPost
    have hroute :
        (k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes q2 G k ** R) hmem := by
      have hfirstPost' :
          k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes q2 G k hleft := by
        simpa only [k73IncreaseFirstDivToAddSource] using hfp
      exact ⟨hleft, hright, hdisj, hunion, hfirstPost', hRpost⟩
    obtain ⟨k', hk', s', hstep', hcase⟩ :=
      (cpsBranchWithin_mono_nSteps hN1 (hfirst k)) R hR s hcr
        ⟨hmem, hcompat, hroute⟩ hpc
    rcases hcase with ⟨hpcFail, hFail⟩ | ⟨hpcReturn, hReturn⟩
    · exact ⟨k', hk', s', hstep', Or.inl ⟨hpcFail, hFail⟩⟩
    · obtain ⟨hmem', hcompat', hQ1post⟩ := hReturn
      exact ⟨k', hk', s', hstep', Or.inr ⟨hpcReturn,
        ⟨hmem', hcompat', sepConj_mono_left (hQ1 hn) hmem' hQ1post⟩⟩⟩
  · obtain ⟨hfp, hz⟩ := (sepConj_pure_right _).1 hsecondPost
    have hroute :
        (k73IncreaseSecondDivToAddSource spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes
          (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G k ** R) hmem := by
      have hsecondPost' :
          k73IncreaseSecondDivToAddSource spH raIn gasUsed basePtr outPtr target
            v8 v9 v18 v19 v20 baseBytes accBytes
            (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G k hleft := by
        simpa only [k73IncreaseSecondDivToAddSource] using hfp
      exact ⟨hleft, hright, hdisj, hunion, hsecondPost', hRpost⟩
    obtain ⟨k', hk', s', hstep', hcase⟩ :=
      (cpsBranchWithin_mono_nSteps hN2 (hsecond k)) R hR s hcr
        ⟨hmem, hcompat, hroute⟩ hpc
    rcases hcase with ⟨hpcFail, hFail⟩ | ⟨hpcReturn, hReturn⟩
    · exact ⟨k', hk', s', hstep', Or.inl ⟨hpcFail, hFail⟩⟩
    · obtain ⟨hmem', hcompat', hQ2post⟩ := hReturn
      exact ⟨k', hk', s', hstep', Or.inr ⟨hpcReturn,
        ⟨hmem', hcompat', sepConj_mono_left (hQ2 hz) hmem' hQ2post⟩⟩⟩

private theorem k73_increase_status_finish
    {Nstatus Ncarry Nzero Ntail : Nat}
    (raIn : Word)
    (P Pcarry Pzero Qcarry Qzero Q : Assertion)
    (hstatus : cpsBranchWithin Nstatus K73 wholeCode P
      (K73 + 272) Pcarry (K73 + 172) Pzero)
    (hcarry : cpsTripleWithin Ncarry (K73 + 272) raIn wholeCode
      Pcarry Qcarry)
    (hzero : cpsBranchWithin Nzero (K73 + 172) wholeCode
      Pzero (K73 + 204) (fun _ => False) raIn Qzero)
    (hcarryQ : ∀ h, Qcarry h → Q h)
    (hzeroQ : ∀ h, Qzero h → Q h)
    (hNcarry : Ncarry ≤ Ntail) (hNzero : Nzero ≤ Ntail) :
    cpsBranchWithin (Nstatus + Ntail) K73 wholeCode P
      (K73 + 204) (fun _ => False) raIn Q := by
  intro R hR s hcr hP hpc
  obtain ⟨k1, hk1, s1, hs1, hcase⟩ := hstatus R hR s hcr hP hpc
  rcases hcase with ⟨hpcCarry, hCarryPre⟩ | ⟨hpcZero, hZeroPre⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hs1 hcr
    obtain ⟨k2, hk2, s2, hs2, hpc2, hCarryPost⟩ :=
      hcarry R hR s1 hcr' hCarryPre hpcCarry
    obtain ⟨hm, hc, hq⟩ := hCarryPost
    exact ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2,
      Or.inr ⟨hpc2, ⟨hm, hc, sepConj_mono_left hcarryQ hm hq⟩⟩⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hs1 hcr
    obtain ⟨k2, hk2, s2, hs2, hcase2⟩ :=
      hzero R hR s1 hcr' hZeroPre hpcZero
    rcases hcase2 with ⟨hpcFail, hFailPost⟩ | ⟨hpcSuccess, hSuccessPost⟩
    · exact ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2,
        Or.inl ⟨hpcFail, hFailPost⟩⟩
    · obtain ⟨hm, hc, hq⟩ := hSuccessPost
      exact ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2,
        Or.inr ⟨hpcSuccess, ⟨hm, hc, sepConj_mono_left hzeroQ hm hq⟩⟩⟩

private theorem k73_increase_status_finish_from_mul
    {Nstatus Ncarry Nzero Ntail : Nat}
    (raIn : Word)
    (P Pcarry Pzero Qcarry Qzero Q : Assertion)
    (hstatus : cpsBranchWithin Nstatus (K73 + 64) wholeCode P
      (K73 + 272) Pcarry (K73 + 172) Pzero)
    (hcarry : cpsTripleWithin Ncarry (K73 + 272) raIn wholeCode
      Pcarry Qcarry)
    (hzero : cpsBranchWithin Nzero (K73 + 172) wholeCode
      Pzero (K73 + 204) (fun _ => False) raIn Qzero)
    (hcarryQ : ∀ h, Qcarry h → Q h)
    (hzeroQ : ∀ h, Qzero h → Q h)
    (hNcarry : Ncarry ≤ Ntail) (hNzero : Nzero ≤ Ntail) :
    cpsBranchWithin (Nstatus + Ntail) (K73 + 64) wholeCode P
      (K73 + 204) (fun _ => False) raIn Q := by
  intro R hR s hcr hP hpc
  obtain ⟨k1, hk1, s1, hs1, hcase⟩ := hstatus R hR s hcr hP hpc
  rcases hcase with ⟨hpcCarry, hCarryPre⟩ | ⟨hpcZero, hZeroPre⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hs1 hcr
    obtain ⟨k2, hk2, s2, hs2, hpc2, hCarryPost⟩ :=
      hcarry R hR s1 hcr' hCarryPre hpcCarry
    obtain ⟨hm, hc, hq⟩ := hCarryPost
    exact ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2,
      Or.inr ⟨hpc2, ⟨hm, hc, sepConj_mono_left hcarryQ hm hq⟩⟩⟩
  · have hcr' := CodeReq.SatisfiedBy_preserved hs1 hcr
    obtain ⟨k2, hk2, s2, hs2, hcase2⟩ :=
      hzero R hR s1 hcr' hZeroPre hpcZero
    rcases hcase2 with ⟨hpcFail, hFailPost⟩ | ⟨hpcSuccess, hSuccessPost⟩
    · exact ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2,
        Or.inl ⟨hpcFail, hFailPost⟩⟩
    · obtain ⟨hm, hc, hq⟩ := hSuccessPost
      exact ⟨k1 + k2, by omega, s2, stepN_add_eq hs1 hs2,
        Or.inr ⟨hpcSuccess, ⟨hm, hc, sepConj_mono_left hzeroQ hm hq⟩⟩⟩

@[irreducible] def k73IncreaseFirstFinalPost
    (sp0 spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes q2 : List (BitVec 8)) (G : Assertion) : Assertion :=
  fun s =>
    (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
        (k73Saved raIn v8 v9 v18 v19 v20) **
      frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19 v20) **
      ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes baseBytes q2 q2) **
      bytesRegion basePtr baseBytes **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G) s ∨
    (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
        (k73Saved raIn v8 v9 v18 v19 v20) **
      frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19 v20) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes baseBytes q2 q2) **
      bytesRegion basePtr baseBytes **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G) s

@[irreducible] def k73IncreaseSecondFinalPost
    (sp0 spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes orig : List (BitVec 8)) (G : Assertion) : Assertion :=
  fun s =>
    (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
        (k73Saved raIn v8 v9 v18 v19 v20) **
      frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19 v20) **
      ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes baseBytes orig orig) **
      bytesRegion basePtr baseBytes **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G) s ∨
    (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
        (k73Saved raIn v8 v9 v18 v19 v20) **
      frameSlotsSaved k73Frame spH
        (k73Saved raIn v8 v9 v18 v19 v20) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      regOwns u256AddBeBInPlaceScratch **
      bytesRegion outPtr (u256AddBeBytes baseBytes orig orig) **
      bytesRegion basePtr baseBytes **
      U256MulU64Be.frameSlots (spH + signExtend12 (-48))
        (K73 + 88) basePtr outPtr target (gasUsed - target) (1 : Word) **
      bytesRegion U256MulU64Be.accBase accBytes ** G) s

@[irreducible] def k73IncreaseCarryFinalPost
    (sp0 spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes : List (BitVec 8)) (G : Assertion) : Assertion :=
  (((.x2 : Reg) ↦ᵣ sp0) ** regsAt k73Frame
      (k73Saved raIn v8 v9 v18 v19 v20) **
    frameSlotsSaved k73Frame spH
      (k73Saved raIn v8 v9 v18 v19 v20) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
    k73IncreaseCarryTail spH gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes outBytes
      (regOwns [.x14, .x15, .x16, .x17] ** G))

/-- The three-way route outcome carries the window-value pures
`beBytesToNat q2 = 0` / `≠ 0`: the zero-test controls WHICH BYTES the window
holds (keep window = `AddBe p q2 q2` vs replace image = `AddBe p 1 1`), so
without the pures the post is PATH-BLIND, and a path-blind post admits
countermodel states that no local window algebra can kill, because the
implication quantifies over all states satisfying the post rather than the
reachable ones. Do not weaken the pures back out. -/
@[irreducible] def k73IncreaseStatusFinalPost
    (sp0 spH raIn gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (baseBytes accBytes outBytes q2 : List (BitVec 8)) (G : Assertion) : Assertion :=
  fun s =>
    ((fun s' => k73IncreaseCarryFinalPost sp0 spH raIn gasUsed basePtr outPtr
        target v8 v9 v18 v19 v20 baseBytes accBytes outBytes G s' ∨
        k73IncreaseSecondFinalPost sp0 spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes
          (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G s') **
      ⌜Crypto.beBytesToNat q2 = 0⌝) s ∨
    ((fun s' => k73IncreaseCarryFinalPost sp0 spH raIn gasUsed basePtr outPtr
        target v8 v9 v18 v19 v20 baseBytes accBytes outBytes G s' ∨
        k73IncreaseFirstFinalPost sp0 spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes q2 G s') **
      ⌜Crypto.beBytesToNat q2 ≠ 0⌝) s

/-! The route-specific adapters now compose through the status split.  This
    theorem deliberately keeps the arithmetic/resource premises explicit: a
    later caller must discharge them from its input contract rather than
    hiding them in a stronger post. -/
private theorem k73_increase_status_div_zero_to_return
    (sp0 spH raIn gasLimit gasUsed basePtr outPtr target : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes q1 q2 : List (BitVec 8)) (G : Assertion)
    (Nstatus Ntail : Nat)
    (hG : G.pcFree)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : (k73Saved raIn v8 v9 v18 v19 v20) .x1 = raIn)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr target gasUsed
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))
      (k73IncreaseMulCalleePost spH basePtr outPtr target gasUsed
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G)))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hlenOut : outBytes.length = 32)
    (hq1 : q1 = u256DivU64BeQuotBytes outBytes outBytes target)
    (hq2 : q2 = u256DivU64BeQuotBytes q1 q1 8)
    (hlen1 : q1.length = 32) (hlen2 : q2.length = 32)
    (hoverOut : outPtr.toNat + 32 < 2 ^ 64)
    (htargetPos : 0 < target.toNat)
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn outPtr target outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes target)).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 104) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4)
    (hret2 : ((K73 + 120) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hlenQ2 : q2.length = 32)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hszAddQ2 : k73AddBSize basePtr outPtr baseBytes q2 ≤ 2 ^ 64)
    (hszAddOne : k73AddBSize basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = K73 + 188 + 4)
    (hNstatus : Nstatus =
      3857 + (10 + (u256DivU64BeInPlaceFn outPtr target outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes target)).body.steps +
        (12 + (1 + (((1 + 1) + (1 +
          (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) outPtr q2).body.steps
            + 1)) + 1)))))
    (hNq2 : 1 + k73AddBTailSteps basePtr outPtr baseBytes q2 ≤ Ntail)
    (hNq1 : 1 + k73AddBTailSteps basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ Ntail)
    (hNcarry : 9 ≤ Ntail) :
    cpsBranchWithin (Nstatus + Ntail) (K73 + 64) wholeCode
      (k73IncreaseMulPre spH raIn gasLimit gasUsed
        basePtr outPtr target v8 v9 v18 v19 (0 : Word) v20
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** G))
      (K73 + 204) (fun _ => False) raIn
      (k73IncreaseStatusFinalPost sp0 spH raIn gasUsed
        basePtr outPtr target v8 v9 v18 v19 v20
        baseBytes accBytes outBytes q2 G) := by
  let Fstatus : Assertion := regOwns [.x14, .x15, .x16, .x17] ** G
  let Q1 : Assertion := k73IncreaseFirstFinalPost
    sp0 spH raIn gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 baseBytes accBytes q2 G
  let Q2 : Assertion := k73IncreaseSecondFinalPost
    sp0 spH raIn gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 baseBytes accBytes
      (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G
  let Qcarry : Assertion := k73IncreaseCarryFinalPost
    sp0 spH raIn gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 baseBytes accBytes outBytes G
  let Qzero : Assertion := fun s =>
    ((fun s' => k73IncreaseCarryFinalPost sp0 spH raIn gasUsed basePtr
        outPtr target v8 v9 v18 v19 v20 baseBytes accBytes outBytes G s' ∨
        k73IncreaseSecondFinalPost sp0 spH raIn gasUsed basePtr outPtr
          target v8 v9 v18 v19 v20 baseBytes accBytes
          (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G s') **
      ⌜Crypto.beBytesToNat q2 = 0⌝) s ∨
    ((fun s' => k73IncreaseCarryFinalPost sp0 spH raIn gasUsed basePtr
        outPtr target v8 v9 v18 v19 v20 baseBytes accBytes outBytes G s' ∨
        k73IncreaseFirstFinalPost sp0 spH raIn gasUsed basePtr outPtr
          target v8 v9 v18 v19 v20 baseBytes accBytes q2 G s') **
      ⌜Crypto.beBytesToNat q2 ≠ 0⌝) s
  have hFstatus : Fstatus.pcFree := by
    dsimp [Fstatus]
    pcf
    exact hG
  have hstatus0 := k73_increase_status_div_zero_spec_within_for_return
    (spH := spH) (raIn := raIn) (gasLimit := gasLimit) (gasUsed := gasUsed)
    (basePtr := basePtr) (outPtr := outPtr) (target := target)
    (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (v20 := v20)
    (f0 := f0) (f1 := f1) (f2 := f2) (f3 := f3) (f4 := f4) (f5 := f5)
    (baseBytes := baseBytes) (accBytes := accBytes) (outBytes := outBytes)
    (q1 := q1) (q2 := q2) (G := G) hG hcallee
    hrw hlenOut hq1 hq2 hlen1 hlen2 hoverOut htargetPos
    hsz1 hsz2 hret1 hret2
  have hstatus : cpsBranchWithin Nstatus (K73 + 64) wholeCode
      (k73IncreaseMulPre spH raIn gasLimit gasUsed
        basePtr outPtr target v8 v9 v18 v19 (0 : Word) v20
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes Fstatus)
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) **
          k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr
            target v8 v9 v18 v19 v20 baseBytes accBytes outBytes Fstatus **
          regOwn .x10)
      (K73 + 172)
        (k73IncreaseDivZeroPost spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes q2 G) := by
    simpa only [Fstatus, hNstatus] using hstatus0
  have hfirst : ∀ k, cpsBranchWithin
      (1 + k73AddBTailSteps basePtr outPtr baseBytes q2)
      (K73 + 172) wholeCode
      (k73IncreaseFirstDivToAddSource spH raIn gasUsed basePtr outPtr
        target v8 v9 v18 v19 v20 baseBytes accBytes q2 G k)
      (K73 + 204) (fun _ => False) raIn Q1 := by
    intro k
    have h := k73_increase_first_div_to_return
      sp0 spH raIn gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes q2 G hG hsp hret hsaved
      hrw hroBase hlenBase hlenQ2 hovBase hovOut hdisj hszAddQ2 hcallRet k
    unfold Q1 k73IncreaseFirstFinalPost
    exact h
  have hone :
      (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)).length = 32 := by
    exact U256FromU64BeSAsm.length_u256FromU64Bytes (1 : Word)
  have hsecond : ∀ k, cpsBranchWithin
      (1 + k73AddBTailSteps basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)))
      (K73 + 172) wholeCode
      (k73IncreaseSecondDivToAddSource spH raIn gasUsed basePtr outPtr
        target v8 v9 v18 v19 v20 baseBytes accBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G k)
      (K73 + 204) (fun _ => False) raIn Q2 := by
    intro k
    have hadd := k73_increase_second_add_to_return
      sp0 spH raIn gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes
      (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G hG hsp hret hsaved
      hrw hroBase hlenBase hone hovBase hovOut hdisj hszAddOne hcallRet
    have hadd' : cpsTripleWithin
        (k73AddBTailSteps basePtr outPtr baseBytes
          (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)))
        (K73 + 176) raIn wholeCode
        (k73IncreaseSecondAddPre spH raIn gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes
          (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G) Q2 := by
      unfold Q2 k73IncreaseSecondFinalPost
      exact hadd
    have h := k73_increase_second_div_to_return
      spH raIn gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes
      (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) G hG k (Q := Q2) hadd'
    unfold Q2 k73IncreaseSecondFinalPost at h ⊢
    exact h
  have hzero := k73_increase_div_zero_dispatch
    spH raIn gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 baseBytes accBytes q2 G
    Ntail (1 + k73AddBTailSteps basePtr outPtr baseBytes q2)
      (1 + k73AddBTailSteps basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)))
      Q1 Q2 Qzero hfirst hsecond
      (by
        intro hn h hp
        exact Or.inr ((sepConj_pure_right _).2 ⟨Or.inr hp, hn⟩))
      (by
        intro hz h hp
        exact Or.inl ((sepConj_pure_right _).2 ⟨Or.inr hp, hz⟩))
      (by omega) (by omega)
  have hcarryP : cpsTripleWithin 9 (K73 + 272) raIn wholeCode
      (((.x2 : Reg) ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH
          (k73Saved raIn v8 v9 v18 v19 v20) ** regOwn .x10 **
        k73IncreaseCarryTail spH gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes Fstatus)
      Qcarry := by
    have htail :
        (k73IncreaseCarryTail spH gasUsed basePtr outPtr target
          v8 v9 v18 v19 v20 baseBytes accBytes outBytes Fstatus).pcFree := by
      unfold k73IncreaseCarryTail
      apply pcFree_sepConj
      · pcf
      apply pcFree_sepConj
      · pcf
      apply pcFree_sepConj
      · apply pcFree_exists
        intro k
        pcf
      · exact hFstatus
    have hfail := k73_failure_tail_spec_within
      sp0 spH raIn (k73Saved raIn v8 v9 v18 v19 v20)
      (k73IncreaseCarryTail spH gasUsed basePtr outPtr target
        v8 v9 v18 v19 v20 baseBytes accBytes outBytes Fstatus)
      hsp hret hsaved htail
    unfold Qcarry k73IncreaseCarryFinalPost
    exact hfail
  have hcarry := k73_increase_carry_to_return
    spH raIn gasUsed basePtr outPtr target
    v8 v9 v18 v19 v20 baseBytes accBytes outBytes Fstatus Qcarry hcarryP
  have hfinal := k73_increase_status_finish_from_mul
    (Nstatus := Nstatus) (Ncarry := 9) (Nzero := Ntail)
    (Ntail := Ntail) raIn
    (k73IncreaseMulPre spH raIn gasLimit gasUsed
      basePtr outPtr target v8 v9 v18 v19 (0 : Word) v20
      f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes Fstatus)
    (((.x0 : Reg) ↦ᵣ (0 : Word)) **
      k73IncreaseMulCarryRest spH raIn gasUsed basePtr outPtr
        target v8 v9 v18 v19 v20 baseBytes accBytes outBytes Fstatus **
      regOwn .x10)
    (k73IncreaseDivZeroPost spH raIn gasUsed basePtr outPtr target
      v8 v9 v18 v19 v20 baseBytes accBytes q2 G)
    Qcarry Qzero Qzero
      hstatus hcarry hzero
    (by
      intro h hp
      rcases Classical.em (Crypto.beBytesToNat q2 = 0) with hz | hn
      · exact Or.inl ((sepConj_pure_right _).2 ⟨Or.inl hp, hz⟩)
      · exact Or.inr ((sepConj_pure_right _).2 ⟨Or.inl hp, hn⟩))
    (by
      intro h hp
      exact hp)
    (by exact hNcarry) (by exact le_refl Ntail)
  unfold k73IncreaseStatusFinalPost k73IncreaseCarryFinalPost
    k73IncreaseFirstFinalPost k73IncreaseSecondFinalPost at ⊢
  unfold Qzero k73IncreaseCarryFinalPost
    k73IncreaseFirstFinalPost k73IncreaseSecondFinalPost at hfinal
  exact hfinal

/-! Public alias for the generic increasing-route composition.  The older
    wrapper below fixes the historical 5000/2500 witness, while this alias
    preserves the caller-supplied gas-limit/gas-used relation for whole-route
    composition. -/
set_option linter.defProp false in
def k73_increase_status_div_zero_to_return_general :=
  k73_increase_status_div_zero_to_return

/-! The entry wrapper only supplies the fixed target selected by the prefix.
    All route-specific arithmetic and memory obligations remain explicit in
    the preceding theorem, so this wrapper cannot hide an uninhabited route
    contract behind the entry composition. -/
theorem k73_increase_entry_status_div_zero_to_return_spec_within
    (sp0 spH raIn basePtr outPtr : Word)
    (v8 v9 v18 v19 v20 : Word)
    (f0 f1 f2 f3 f4 f5 : Word)
    (baseBytes accBytes outBytes q1 q2 : List (BitVec 8)) (F : Assertion)
    (Nstatus Ntail : Nat)
    (hG : F.pcFree)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : (k73Saved raIn v8 v9 v18 v19 v20) .x1 = raIn)
    (hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre spH basePtr outPtr (2500 : Word) (5000 : Word)
        f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** F))
      (k73IncreaseMulCalleePost spH basePtr outPtr (2500 : Word) (5000 : Word)
        baseBytes accBytes outBytes
        (regOwns [.x14, .x15, .x16, .x17] ** F)))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hlenOut : outBytes.length = 32)
    (hq1 : q1 = u256DivU64BeQuotBytes outBytes outBytes (2500 : Word))
    (hq2 : q2 = u256DivU64BeQuotBytes q1 q1 8)
    (hlen1 : q1.length = 32) (hlen2 : q2.length = 32)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hsz1 : 4 * ((u256DivU64BeInPlaceFn outPtr (2500 : Word) outBytes).body.size + 1)
      ≤ 2 ^ 64)
    (hsz2 : 4 * ((u256DivU64BeInPlaceFn outPtr 8
        (u256DivU64BeQuotBytes outBytes outBytes (2500 : Word))).body.size + 1)
      ≤ 2 ^ 64)
    (hret1 : ((K73 + 104) + 4) &&& ~~~(1 : Word) = (K73 + 104) + 4)
    (hret2 : ((K73 + 120) + 4) &&& ~~~(1 : Word) = (K73 + 120) + 4)
    (hroBase : Region.wf ⟨basePtr, baseBytes⟩)
    (hlenBase : baseBytes.length = 32)
    (hovBase : basePtr.toNat + 32 < 2 ^ 64)
    (hdisj : basePtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ basePtr.toNat)
    (hszAddQ2 : k73AddBSize basePtr outPtr baseBytes q2 ≤ 2 ^ 64)
    (hszAddOne : k73AddBSize basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ 2 ^ 64)
    (hcallRet : ((K73 + 188) + 4) &&& ~~~(1 : Word) = K73 + 188 + 4)
    (hNstatus : Nstatus =
      3857 + (10 + (u256DivU64BeInPlaceFn outPtr (2500 : Word) outBytes).body.steps +
        (u256DivU64BeInPlaceFn outPtr 8
          (u256DivU64BeQuotBytes outBytes outBytes (2500 : Word))).body.steps +
        (12 + (1 + (((1 + 1) + (1 +
          (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) outPtr q2).body.steps
            + 1)) + 1)))))
    (hNq2 : 1 + k73AddBTailSteps basePtr outPtr baseBytes q2 ≤ Ntail)
    (hNq1 : 1 + k73AddBTailSteps basePtr outPtr baseBytes
        (U256FromU64BeSAsm.u256FromU64Bytes (1 : Word)) ≤ Ntail)
    (hNcarry : 9 ≤ Ntail) :
    cpsBranchWithin (13 + Nstatus + Ntail) K73 wholeCode
      (k73HeadPre sp0 spH raIn (5000 : Word) (5000 : Word)
        basePtr outPtr v8 v9 v18 v19 v20 baseBytes outBytes
        (U256MulU64Be.frameSlots (spH + signExtend12 (-48)) f0 f1 f2 f3 f4 f5 **
          bytesRegion U256MulU64Be.accBase accBytes **
          (regOwns [.x14, .x15, .x16, .x17] ** F)))
      (K73 + 204) (fun _ => False) raIn
      (k73IncreaseStatusFinalPost sp0 spH raIn (5000 : Word)
        basePtr outPtr (2500 : Word) v8 v9 v18 v19 v20
        baseBytes accBytes outBytes q2 F) := by
  let Fstatus : Assertion := regOwns [.x14, .x15, .x16, .x17] ** F
  have hFstatus : Fstatus.pcFree := by
    dsimp [Fstatus]
    pcf
    exact hG
  have hspEntry : spH = sp0 + signExtend12 (-56 : BitVec 12) := by
    have hplus : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide
    have hminus : signExtend12 (-56 : BitVec 12) =
        (18446744073709551560 : Word) := by decide
    rw [hplus] at hsp
    rw [hminus]
    bv_omega
  have hprefix := k73_increase_entry_to_mul_spec_within
    sp0 spH raIn (5000 : Word) (5000 : Word) (2500 : Word)
    basePtr outPtr v8 v9 v18 v19 v20
    f0 f1 f2 f3 f4 f5 baseBytes accBytes outBytes Fstatus hspEntry
    (by decide) (by decide) (by decide) hFstatus
  have hroute := k73_increase_status_div_zero_to_return
    (sp0 := sp0) (spH := spH) (raIn := raIn)
    (gasLimit := (5000 : Word)) (gasUsed := (5000 : Word))
    (basePtr := basePtr) (outPtr := outPtr) (target := (2500 : Word))
    (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) (v20 := v20)
    (f0 := f0) (f1 := f1) (f2 := f2) (f3 := f3) (f4 := f4) (f5 := f5)
    (baseBytes := baseBytes) (accBytes := accBytes) (outBytes := outBytes)
    (q1 := q1) (q2 := q2) (G := F)
    (Nstatus := Nstatus) (Ntail := Ntail)
    (hG := hG) (hsp := hsp) (hret := hret) (hsaved := hsaved)
    (hcallee := hcallee) (hrw := hrw) (hlenOut := hlenOut)
    (hq1 := hq1) (hq2 := hq2) (hlen1 := hlen1) (hlen2 := hlen2)
    (hoverOut := hovOut) (htargetPos := by decide)
    (hovOut := hovOut)
    (hsz1 := hsz1) (hsz2 := hsz2) (hret1 := hret1) (hret2 := hret2)
    (hroBase := hroBase) (hlenBase := hlenBase) (hlenQ2 := hlen2)
    (hovBase := hovBase) (hdisj := hdisj) (hszAddQ2 := hszAddQ2)
    (hszAddOne := hszAddOne) (hcallRet := hcallRet)
    (hNstatus := hNstatus) (hNq2 := hNq2) (hNq1 := hNq1)
    (hNcarry := hNcarry)
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by
      unfold k73IncreaseMulPre at ⊢
      dsimp [Fstatus] at hp ⊢
      xperm_chunked hp) hprefix hroute
  simpa only [Nat.add_assoc] using hseq

/-! A live arm-4 clamp inhabitant.  The base-fee bytes encode 7 and the
    selected gas delta is 2500, so the first quotient is 7 and the second
    quotient floors to zero.  This deliberately witnesses the max-with-one
    clamp arm rather than pretending that it traverses the nonzero second
    divide. -/
def k73Arm4ClampBaseBytes : List (BitVec 8) :=
  List.replicate 31 0 ++ [7]
def k73Arm4ClampAccBytes : List (BitVec 8) :=
  [92, 68, 0, 0] ++ List.replicate 36 0
def k73Arm4ClampOutBytes : List (BitVec 8) :=
  List.replicate 28 0 ++ [0, 0, 68, 92]
def k73Arm4ClampQ1 : List (BitVec 8) :=
  u256DivU64BeQuotBytes k73Arm4ClampOutBytes k73Arm4ClampOutBytes (2500 : Word)
def k73Arm4ClampQ2 : List (BitVec 8) :=
  u256DivU64BeQuotBytes k73Arm4ClampQ1 k73Arm4ClampQ1 8
def k73Arm4ClampN1 : Nat :=
  (u256DivU64BeInPlaceFn (0xa0000100 : Word) (2500 : Word)
    k73Arm4ClampOutBytes).body.steps
def k73Arm4ClampN2 : Nat :=
  (u256DivU64BeInPlaceFn (0xa0000100 : Word) 8 k73Arm4ClampQ1).body.steps
def k73Arm4ClampN3 : Nat :=
  (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) (0xa0000100 : Word)
    k73Arm4ClampQ2).body.steps
def k73Arm4ClampNstatus : Nat := 3857 + (10 + k73Arm4ClampN1 +
  k73Arm4ClampN2 + (12 + (1 + (((1 + 1) +
    (1 + k73Arm4ClampN3 + 1)) + 1))))
def k73Arm4ClampNtail : Nat := 100000

theorem k73_increase_entry_status_div_zero_clamp_live_spec_within :
    cpsBranchWithin (13 + k73Arm4ClampNstatus + k73Arm4ClampNtail) K73 wholeCode
      (k73HeadPre (0xa0050038 : Word) (0xa0050000 : Word) (0 : Word)
        (5000 : Word) (5000 : Word) (0xa0000000 : Word) (0xa0000100 : Word)
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        k73Arm4ClampBaseBytes k73Arm4ClampOutBytes
        (U256MulU64Be.frameSlots (0xa0050000 + signExtend12 (-48))
          0 1 2 3 4 5 ** bytesRegion U256MulU64Be.accBase
          k73Arm4ClampAccBytes **
          (regOwns [.x14, .x15, .x16, .x17] ** empAssertion)))
      (K73 + 204) (fun _ => False) (0 : Word)
      (k73IncreaseStatusFinalPost (0xa0050038 : Word) (0xa0050000 : Word)
        (0 : Word) (5000 : Word) (0xa0000000 : Word) (0xa0000100 : Word)
        (2500 : Word) 0 0 0 0 0 k73Arm4ClampBaseBytes k73Arm4ClampAccBytes
        k73Arm4ClampOutBytes k73Arm4ClampQ2 empAssertion) := by
  have hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre (0xa0050000 : Word) (0xa0000000 : Word)
        (0xa0000100 : Word) (2500 : Word) (5000 : Word)
        0 1 2 3 4 5 k73Arm4ClampBaseBytes k73Arm4ClampAccBytes
        k73Arm4ClampOutBytes
        (regOwns [.x14, .x15, .x16, .x17] ** empAssertion))
      (k73IncreaseMulCalleePost (0xa0050000 : Word) (0xa0000000 : Word)
        (0xa0000100 : Word) (2500 : Word) (5000 : Word)
        k73Arm4ClampBaseBytes k73Arm4ClampAccBytes k73Arm4ClampOutBytes
        (regOwns [.x14, .x15, .x16, .x17] ** empAssertion)) := by
    have hmul := EvmAsm.Codegen.U256MulU64Be.mulWhole_spec
      (F := regOwns [.x14, .x15, .x16, .x17] ** empAssertion) (hF := by pcf)
      (aBytes := k73Arm4ClampBaseBytes) (accBytes := k73Arm4ClampAccBytes)
      (outBytes := k73Arm4ClampOutBytes)
      (hlenA := by simp [k73Arm4ClampBaseBytes])
      (hlenAcc := by simp [k73Arm4ClampAccBytes])
      (hout := by simp [k73Arm4ClampOutBytes])
      (spOld := (0xa0050000 : Word)) (vRa := (K73 + 88))
      (v8 := (0xa0000000 : Word)) (v9 := (0xa0000100 : Word))
      (v18 := (2500 : Word)) (v19 := ((5000 : Word) - 2500))
      (v20 := (1 : Word)) (aPtr := (0xa0000000 : Word))
      (b := ((5000 : Word) - 2500)) (outPtr := (0xa0000100 : Word))
      (v13 := (0xa0000100 : Word))
      (f0 := (0 : Word)) (f1 := (1 : Word)) (f2 := (2 : Word))
      (f3 := (3 : Word)) (f4 := (4 : Word)) (f5 := (5 : Word))
      (halignA := by decide) (hoverA := by decide) (hvalidA := by decide)
      (halignOut := by decide) (hoverOut := by decide)
      (hvalidOut := by decide) (hret := by decide)
    unfold k73IncreaseMulCalleePre k73IncreaseMulCalleePost
    exact hmul
  exact k73_increase_entry_status_div_zero_to_return_spec_within
    (sp0 := (0xa0050038 : Word)) (spH := (0xa0050000 : Word))
    (raIn := (0 : Word)) (basePtr := (0xa0000000 : Word))
    (outPtr := (0xa0000100 : Word))
    (v8 := (0 : Word)) (v9 := (0 : Word)) (v18 := (0 : Word))
    (v19 := (0 : Word)) (v20 := (0 : Word))
    (f0 := (0 : Word)) (f1 := (1 : Word)) (f2 := (2 : Word))
    (f3 := (3 : Word)) (f4 := (4 : Word)) (f5 := (5 : Word))
    (baseBytes := k73Arm4ClampBaseBytes) (accBytes := k73Arm4ClampAccBytes)
    (outBytes := k73Arm4ClampOutBytes) (q1 := k73Arm4ClampQ1)
    (q2 := k73Arm4ClampQ2) (F := empAssertion)
    (Nstatus := k73Arm4ClampNstatus) (Ntail := k73Arm4ClampNtail)
    (hG := by pcf) (hsp := by decide) (hret := by decide)
    (hsaved := by simp [k73Saved]) (hcallee := hcallee)
    (hrw := by decide) (hlenOut := by simp [k73Arm4ClampOutBytes])
    (hq1 := by rfl) (hq2 := by rfl)
    (hlen1 := by decide) (hlen2 := by decide)
    (hovOut := by decide) (hsz1 := by decide) (hsz2 := by decide)
    (hret1 := by decide) (hret2 := by decide)
    (hroBase := by decide)
    (hlenBase := by simp [k73Arm4ClampBaseBytes]) (hovBase := by decide)
    (hdisj := by decide)
    (hszAddQ2 := by
      unfold k73AddBSize
      decide)
    (hszAddOne := by
      unfold k73AddBSize
      decide)
    (hcallRet := by decide) (hNstatus := by rfl)
    (hNq2 := by simp [k73AddBTailSteps, k73Arm4ClampNtail]; decide)
    (hNq1 := by simp [k73AddBTailSteps, k73Arm4ClampNtail]; decide)
    (hNcarry := by decide)

/-! A live arm-4 inhabitant.  The base-fee bytes encode 1,000,000 and the
    selected gas delta is 2500, so the two quotient stages produce 1,000,000
    and 125,000 rather than taking the max-with-one clamp.  The accumulator
    and output lists are the fixed point of `mulState` followed by `copyState`
    for that input, so this witnesses the full callee contract rather than
    merely its static shell. -/
def k73Arm4LiveBaseBytes : List (BitVec 8) :=
  List.replicate 29 0 ++ [0x0f, 0x42, 0x40]
def k73Arm4LiveAccBytes : List (BitVec 8) :=
  [0, 249, 2, 149] ++ List.replicate 36 0
def k73Arm4LiveOutBytes : List (BitVec 8) :=
  List.replicate 28 0 ++ [149, 2, 249, 0]
def k73Arm4LiveQ1 : List (BitVec 8) :=
  u256DivU64BeQuotBytes k73Arm4LiveOutBytes k73Arm4LiveOutBytes (2500 : Word)
def k73Arm4LiveQ2 : List (BitVec 8) :=
  u256DivU64BeQuotBytes k73Arm4LiveQ1 k73Arm4LiveQ1 8
def k73Arm4LiveN1 : Nat :=
  (u256DivU64BeInPlaceFn (0xa0000100 : Word) (2500 : Word)
    k73Arm4LiveOutBytes).body.steps
def k73Arm4LiveN2 : Nat :=
  (u256DivU64BeInPlaceFn (0xa0000100 : Word) 8 k73Arm4LiveQ1).body.steps
def k73Arm4LiveN3 : Nat :=
  (U256FromU64BeSAsm.u256FromU64BeFn (1 : Word) (0xa0000100 : Word)
    k73Arm4LiveQ2).body.steps
def k73Arm4LiveNstatus : Nat := 3857 + (10 + k73Arm4LiveN1 +
  k73Arm4LiveN2 + (12 + (1 + (((1 + 1) +
    (1 + k73Arm4LiveN3 + 1)) + 1))))
def k73Arm4LiveNtail : Nat := 100000

theorem k73_increase_entry_status_div_zero_live_spec_within :
    cpsBranchWithin (13 + k73Arm4LiveNstatus + k73Arm4LiveNtail) K73 wholeCode
      (k73HeadPre (0xa0050038 : Word) (0xa0050000 : Word) (0 : Word)
        (5000 : Word) (5000 : Word) (0xa0000000 : Word) (0xa0000100 : Word)
        (0 : Word) (0 : Word) (0 : Word) (0 : Word) (0 : Word)
        k73Arm4LiveBaseBytes k73Arm4LiveOutBytes
        (U256MulU64Be.frameSlots (0xa0050000 + signExtend12 (-48))
          0 1 2 3 4 5 ** bytesRegion U256MulU64Be.accBase
          k73Arm4LiveAccBytes **
          (regOwns [.x14, .x15, .x16, .x17] ** empAssertion)))
      (K73 + 204) (fun _ => False) (0 : Word)
      (k73IncreaseStatusFinalPost (0xa0050038 : Word) (0xa0050000 : Word)
        (0 : Word) (5000 : Word) (0xa0000000 : Word) (0xa0000100 : Word)
        (2500 : Word) 0 0 0 0 0 k73Arm4LiveBaseBytes k73Arm4LiveAccBytes
        k73Arm4LiveOutBytes k73Arm4LiveQ2 empAssertion) := by
  have hcallee : cpsTripleWithin 3850
      (GuestAddrs.u256_mul_u64_be : Word) (K73 + 88) mulCode
      (k73IncreaseMulCalleePre (0xa0050000 : Word) (0xa0000000 : Word)
        (0xa0000100 : Word) (2500 : Word) (5000 : Word)
        0 1 2 3 4 5 k73Arm4LiveBaseBytes k73Arm4LiveAccBytes
        k73Arm4LiveOutBytes
        (regOwns [.x14, .x15, .x16, .x17] ** empAssertion))
      (k73IncreaseMulCalleePost (0xa0050000 : Word) (0xa0000000 : Word)
        (0xa0000100 : Word) (2500 : Word) (5000 : Word)
        k73Arm4LiveBaseBytes k73Arm4LiveAccBytes k73Arm4LiveOutBytes
        (regOwns [.x14, .x15, .x16, .x17] ** empAssertion)) := by
    have hmul := EvmAsm.Codegen.U256MulU64Be.mulWhole_spec
      (F := regOwns [.x14, .x15, .x16, .x17] ** empAssertion) (hF := by pcf)
      (aBytes := k73Arm4LiveBaseBytes) (accBytes := k73Arm4LiveAccBytes)
      (outBytes := k73Arm4LiveOutBytes)
      (hlenA := by simp [k73Arm4LiveBaseBytes])
      (hlenAcc := by simp [k73Arm4LiveAccBytes])
      (hout := by simp [k73Arm4LiveOutBytes])
      (spOld := (0xa0050000 : Word)) (vRa := (K73 + 88))
      (v8 := (0xa0000000 : Word)) (v9 := (0xa0000100 : Word))
      (v18 := (2500 : Word)) (v19 := ((5000 : Word) - 2500))
      (v20 := (1 : Word)) (aPtr := (0xa0000000 : Word))
      (b := ((5000 : Word) - 2500)) (outPtr := (0xa0000100 : Word))
      (v13 := (0xa0000100 : Word))
      (f0 := (0 : Word)) (f1 := (1 : Word)) (f2 := (2 : Word))
      (f3 := (3 : Word)) (f4 := (4 : Word)) (f5 := (5 : Word))
      (halignA := by decide) (hoverA := by decide) (hvalidA := by decide)
      (halignOut := by decide) (hoverOut := by decide)
      (hvalidOut := by decide) (hret := by decide)
    unfold k73IncreaseMulCalleePre k73IncreaseMulCalleePost
    exact hmul
  exact k73_increase_entry_status_div_zero_to_return_spec_within
    (sp0 := (0xa0050038 : Word)) (spH := (0xa0050000 : Word))
    (raIn := (0 : Word)) (basePtr := (0xa0000000 : Word))
    (outPtr := (0xa0000100 : Word))
    (v8 := (0 : Word)) (v9 := (0 : Word)) (v18 := (0 : Word))
    (v19 := (0 : Word)) (v20 := (0 : Word))
    (f0 := (0 : Word)) (f1 := (1 : Word)) (f2 := (2 : Word))
    (f3 := (3 : Word)) (f4 := (4 : Word)) (f5 := (5 : Word))
    (baseBytes := k73Arm4LiveBaseBytes) (accBytes := k73Arm4LiveAccBytes)
    (outBytes := k73Arm4LiveOutBytes) (q1 := k73Arm4LiveQ1)
    (q2 := k73Arm4LiveQ2) (F := empAssertion)
    (Nstatus := k73Arm4LiveNstatus) (Ntail := k73Arm4LiveNtail)
    (hG := by pcf) (hsp := by decide) (hret := by decide)
    (hsaved := by simp [k73Saved]) (hcallee := hcallee)
    (hrw := by decide) (hlenOut := by simp [k73Arm4LiveOutBytes])
    (hq1 := by rfl) (hq2 := by rfl)
    (hlen1 := by decide) (hlen2 := by decide)
    (hovOut := by decide) (hsz1 := by decide) (hsz2 := by decide)
    (hret1 := by decide) (hret2 := by decide)
    (hroBase := by decide)
    (hlenBase := by simp [k73Arm4LiveBaseBytes]) (hovBase := by decide)
    (hdisj := by decide)
    (hszAddQ2 := by
      unfold k73AddBSize
      decide)
    (hszAddOne := by
      unfold k73AddBSize
      decide)
    (hcallRet := by decide) (hNstatus := by rfl)
    (hNq2 := by simp [k73AddBTailSteps]; decide)
    (hNq1 := by simp [k73AddBTailSteps]; decide)
    (hNcarry := by decide)

