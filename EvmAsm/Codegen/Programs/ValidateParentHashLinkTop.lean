import EvmAsm.Codegen.Programs.ValidateParentHashLinkSpec

/-!
  Top-level composition for `validate_parent_hash_link`.

  The body file carries the routine-local contracts and the compare module
  carries the four-dword branch.  Keeping this composition separate keeps the
  source file below the Codegen/Programs line cap while the final theorem still
  quantifies over the linked union `vphlFullCode`.
-/

namespace EvmAsm.Codegen.ValidateParentHashLinkSpec
set_option maxRecDepth 8000
open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpListNthItemSAsm

private theorem top_reg12_to_regOwn
    (v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 : Word) : ∀ h,
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) h →
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14) h := by
  intro h hp
  exact sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x15)
          (sepConj_mono (regIs_implies_regOwn .x16)
            (sepConj_mono (regIs_implies_regOwn .x17)
              (sepConj_mono (regIs_implies_regOwn .x28)
                (sepConj_mono (regIs_implies_regOwn .x29)
                  (sepConj_mono (regIs_implies_regOwn .x30)
                    (sepConj_mono (regIs_implies_regOwn .x31)
                      (sepConj_mono (regIs_implies_regOwn .x13)
                        (regIs_implies_regOwn .x14))))))))))) h hp

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_frameSlotsSaved _ _ _)

@[irreducible] private def vphlTopKFrame
    (spC retHdr outPtr : Word) (cs0 cs1 cs2 cs3 cs4 v21 : Word)
    (parentBase : Word) (parentBytes claimedOld : List (BitVec 8))
    (os : List (BitVec 8)) : Assertion :=
  regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
    (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
    ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
    bytesRegion parentBase parentBytes ** (outPtr ↦ₘ (0 : Word)) **
    bytesRegion vphlClaimedAddr claimedOld **
    bytesRegion vphlComputedAddr (List.replicate 32 (0 : BitVec 8)) **
    bytesRegion vphlZk3 os

@[irreducible] private def vphlTopContinuationPre
    (spC parentBase parentLenW childBase childLenW outPtr v21 status v11 v12 offset len : Word)
    (childBytes : List (BitVec 8))
    (kFrame F : Assertion) : Assertion :=
  ((.x1 ↦ᵣ (vphlBase + 84)) **
    (((.x2 ↦ᵣ spC) ** stackFree spC 8 **
      savedRegTail { ra := vphlBase + 84, s0 := parentBase, s1 := parentLenW,
        s2 := childBase, s3 := childLenW, s4 := outPtr, s5 := v21 }) **
     ((.x10 ↦ᵣ status) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion childBase childBytes **
      (vphlOffsetAddr ↦ₘ offset) ** (vphlLengthAddr ↦ₘ len)))) **
   (kFrame ** F)

@[irreducible] private def vphlTopHashPost
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word)
    (parentBytes childBytes claimedB computedB zk3B : List (BitVec 8))
    (fo ln : Word) : Assertion :=
  ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ retPC) **
    (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
    (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
    (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ v21) ** (.x10 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
    regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
    regOwn .x16 ** regOwn .x17 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
    (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
    ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
    ((spC + 40) ↦ₘ cs4) ** stackFree spC 8 **
    memOwn (spC - BitVec.ofNat 64 8) **
    ((spC + signExtend12 (-16 : BitVec 12)) ↦ₘ retPC) **
    frameSlotsSaved keccakFrame
      (spC + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12))
      (keccakEntryVals parentBase parentLenW childBase outPtr) **
    memOwn (spC - BitVec.ofNat 64 56) ** memOwn (spC - BitVec.ofNat 64 64) **
    bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
    (outPtr ↦ₘ (0 : Word)) ** (vphlOffsetAddr ↦ₘ fo) **
    (vphlLengthAddr ↦ₘ ln) ** bytesRegion vphlClaimedAddr claimedB **
    bytesRegion vphlComputedAddr computedB ** bytesRegion vphlZk3 zk3B)

@[irreducible] private def vphlTopHashRest
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word)
    (parentBytes childBytes claimedB computedB zk3B : List (BitVec 8))
    (fo ln : Word) : Assertion :=
  ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ retPC) **
    (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
    (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
    (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ v21) ** (.x10 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) **
    ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
    ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** stackFree spC 8 **
    memOwn (spC - BitVec.ofNat 64 8) **
    ((spC + signExtend12 (-16 : BitVec 12)) ↦ₘ retPC) **
    frameSlotsSaved keccakFrame
      (spC + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12))
      (keccakEntryVals parentBase parentLenW childBase outPtr) **
    memOwn (spC - BitVec.ofNat 64 56) ** memOwn (spC - BitVec.ofNat 64 64) **
    bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
    (outPtr ↦ₘ (0 : Word)) ** (vphlOffsetAddr ↦ₘ fo) **
    (vphlLengthAddr ↦ₘ ln) ** bytesRegion vphlClaimedAddr claimedB **
    bytesRegion vphlComputedAddr computedB ** bytesRegion vphlZk3 zk3B)

@[irreducible] private def vphlTopCompareBase
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word)
    (parentBytes childBytes : List (BitVec 8)) (fo ln : Word)
    (zk3B : List (BitVec 8)) : Assertion :=
  ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ retPC) **
    (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
    (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
    (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
    (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
    (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
    (.x17 ↦ᵣ v17) ** (.x29 ↦ᵣ v29) **
    (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
    (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
    ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
    ((spC + 40) ↦ₘ cs4) ** stackFree spC 8 **
    memOwn (spC - BitVec.ofNat 64 8) **
    ((spC + signExtend12 (-16 : BitVec 12)) ↦ₘ retPC) **
    frameSlotsSaved keccakFrame
      (spC + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12))
      (keccakEntryVals parentBase parentLenW childBase outPtr) **
    memOwn (spC - BitVec.ofNat 64 56) ** memOwn (spC - BitVec.ofNat 64 64) **
    bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
    (vphlOffsetAddr ↦ₘ fo) ** (vphlLengthAddr ↦ₘ ln) ** bytesRegion vphlZk3 zk3B)

@[irreducible] private def vphlTopCompareDword
    (claimedBytes computedBytes : List (BitVec 8)) (q : Nat)
    (compareBase : Assertion) : Assertion :=
  (.x6 ↦ᵣ vphlComputedAddr) **
    (.x7 ↦ᵣ vphlDwordAt claimedBytes q) **
    (.x28 ↦ᵣ vphlDwordAt computedBytes q) **
    bytesRegion vphlClaimedAddr claimedBytes **
    bytesRegion vphlComputedAddr computedBytes ** compareBase

theorem validate_parent_hash_link_spec_within
    (sp0 spC retHdr parentBase parentLenW childBase childLenW outPtr : Word)
    (cs0 cs1 cs2 cs3 cs4 v21 oldOut oldOffset oldLen : Word)
    (parentBytes childBytes claimedOld : List (BitVec 8)) (childLen N rem : Nat)
    (os : List (BitVec 8)) (F : Assertion)
    (hret : retHdr &&& ~~~(1 : Word) = retHdr)
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hplenW : parentLenW = BitVec.ofNat 64 parentBytes.length)
    (hclenW : childLenW = BitVec.ofNat 64 childLen)
    (hpalign : parentBase.toNat % 8 = 0)
    (hpover : parentBase.toNat + parentBytes.length < 2 ^ 64)
    (hpvalid : ∀ k, k < parentBytes.length →
      isValidByteAccess (parentBase + BitVec.ofNat 64 k) = true)
    (hcalign : childBase.toNat % 8 = 0)
    (hbytes : childLen ≤ childBytes.length)
    (hchildNonempty : 0 < childBytes.length)
    (hnowrap : childBase.toNat + childLen + 9 < 2 ^ 64)
    (hcover : childBase.toNat + childBytes.length < 2 ^ 64)
    (hcvalid : ∀ k, k < childBytes.length →
      isValidByteAccess (childBase + BitVec.ofNat 64 k) = true)
    (hfieldBound : ∀ fo ln,
      RlpListNthItemSAsm.Success childBytes childBase childLen 0 fo ln →
      ln = (32 : Word) → fo.toNat + 32 ≤ childBytes.length)
    (hfieldAlign : ∀ fo ln,
      RlpListNthItemSAsm.Success childBytes childBase childLen 0 fo ln →
      ln = (32 : Word) → (childBase + fo).toNat % 8 = 0)
    (houtAlign : outPtr.toNat % 8 = 0)
    (houtValid : isValidDwordAccess outPtr = true)
    (hkeccakLen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hb8i : (keccakAbsorbCursor parentBase N).toNat % 8 = 0)
    (hos : os.length = 200)
    (hclaimedLen : claimedOld.length = 32)
    (hF : F.pcFree) :
    cpsTripleWithin (389 + keccakBodyFuel N rem) vphlBase retHdr vphlFullCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ retHdr) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) **
        (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ parentBase) ** (.x11 ↦ᵣ parentLenW) ** (.x12 ↦ᵣ childBase) **
        (.x13 ↦ᵣ childLenW) ** (.x14 ↦ᵣ outPtr) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x17 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) **
        memOwn (spC + 24) ** memOwn (spC + 32) ** memOwn (spC + 40) **
        stackFree spC 8 ** bytesRegion parentBase parentBytes **
        bytesRegion childBase childBytes ** (outPtr ↦ₘ oldOut) **
        (vphlOffsetAddr ↦ₘ oldOffset) ** (vphlLengthAddr ↦ₘ oldLen) **
        bytesRegion vphlClaimedAddr claimedOld **
        bytesRegion vphlComputedAddr (List.replicate 32 (0 : BitVec 8)) **
        bytesRegion vphlZk3 os ** F)
      (vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
        parentBase childBase parentBytes childBytes claimedOld childLen
        oldOffset oldLen os ** F) := by
  have hbody_sub : ∀ a i, vphlBodyCode a = some i → vphlFullCode a = some i := by
    intro a i h
    exact CodeReq.union_mono_left a i (vphlCode_subsumes_body a i h)
  have hpro0 := vphl_prologue_spec_within sp0 spC retHdr cs0 cs1 cs2 cs3 cs4 v21
    parentBase parentLenW childBase childLenW outPtr oldOut oldOffset oldLen
    parentBytes childBytes claimedOld os hspC
  have hpro := cpsTripleWithin_extend_code hbody_sub hpro0
  have hproF := cpsTripleWithin_frameR F hF hpro
  let kFrame : Assertion :=
    vphlTopKFrame spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21 parentBase parentBytes
      claimedOld os
  have hk := vphl_k20_call_spec_within spC retHdr parentBase parentLenW
    childBase childLenW outPtr v21 oldOffset oldLen parentBytes childBytes claimedOld os
    childLen cs0 cs1 cs2 cs3 cs4 hclenW hcalign hbytes hchildNonempty hnowrap hcover hcvalid
  have hkF := cpsTripleWithin_frameR F hF hk
  have hcont : ∀ status offset len v11 v12,
      RlpListNthItemSAsm.Result childBytes childBase childLen 0 oldOffset oldLen
        status offset len →
      cpsTripleWithin (70 + keccakBodyFuel N rem) (vphlBase + 84) retHdr vphlFullCode
        (((.x1 ↦ᵣ (vphlBase + 84)) **
          (((.x2 ↦ᵣ spC) ** stackFree spC 8 **
            savedRegTail { ra := vphlBase + 84, s0 := parentBase, s1 := parentLenW,
              s2 := childBase, s3 := childLenW, s4 := outPtr, s5 := v21 }) **
           ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion childBase childBytes **
            (vphlOffsetAddr ↦ₘ offset) ** (vphlLengthAddr ↦ₘ len)))) **
         (kFrame ** F))
        (vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
          parentBase childBase parentBytes childBytes claimedOld childLen
          oldOffset oldLen os ** F) := by
    intro status offset len v11 v12 hres
    rcases hres with hfail | ⟨fo, ln, hsucc⟩
    · let pFail : Assertion :=
        vphlTopContinuationPre spC parentBase parentLenW childBase childLenW outPtr v21
          (1 : Word) v11 v12 oldOffset oldLen childBytes kFrame F
      have hFailVals := vphl_arm_fail_spec_within sp0 spC retHdr parentBase
        parentLenW childBase childLenW outPtr v21 cs0 cs1 cs2 cs3 cs4
        (v5 := (0 : Word)) (v6 := (0 : Word)) (v7 := (0 : Word))
        (v15 := (0 : Word)) (v16 := (0 : Word)) (v17 := (0 : Word))
        (v28 := (0 : Word)) (v29 := (0 : Word)) (v30 := (0 : Word))
        (v31 := (0 : Word)) (v13 := (0 : Word)) (v14 := (0 : Word))
        v11 v12 parentBytes childBytes claimedOld childLen oldOffset oldLen os
        hspC hret hfail
      have hFailOwn := vphl_of_forall_regIs_to_regOwn12
        (P := pFail) (Q := vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
          parentBase childBase parentBytes childBytes claimedOld childLen
          oldOffset oldLen os)
        (hspec := by
          intro v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14
          have h := vphl_arm_fail_spec_within sp0 spC retHdr parentBase
            parentLenW childBase childLenW outPtr v21 cs0 cs1 cs2 cs3 cs4
            v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 v11 v12
            parentBytes childBytes claimedOld childLen oldOffset oldLen os
            hspC hret hfail
          exact cpsTripleWithin_weaken (fun _ hp => by unfold pFail vphlTopContinuationPre; xperm_chunked hp)
            (fun _ hq => hq) h)
      have hFailBound := cpsTripleWithin_mono_nSteps (by omega) hFailOwn
      exact cpsTripleWithin_weaken (fun _ hp => by unfold pFail vphlTopContinuationPre kFrame vphlTopKFrame savedRegTail; xperm_chunked hp)
        (fun _ hq => hq) hFailBound
    · by_cases hne : ln ≠ (32 : Word)
      · let pSucc : Assertion :=
          vphlTopContinuationPre spC parentBase parentLenW childBase childLenW outPtr v21
            (0 : Word) v11 v12 fo ln childBytes kFrame F
        have hOwn := vphl_of_forall_regIs_to_regOwn12
          (P := pSucc) (Q := vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
            parentBase childBase parentBytes childBytes claimedOld childLen fo ln os)
          (hspec := by
            intro v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14
            have h := vphl_arm_len_ne32_spec_within sp0 spC retHdr parentLenW
              childLenW outPtr cs0 cs1 cs2 cs3 cs4 v21 parentBase childBase
              parentBytes childBytes claimedOld childLen fo ln v5 v6 v7 v15 v16
              v17 v28 v29 v30 v31 v13 v14 v11 v12 os hspC hret hsucc hne
            exact cpsTripleWithin_weaken
              (fun _ hp => by unfold pSucc vphlTopContinuationPre; xperm_chunked hp) (fun _ hq => hq) h)
        have hOwnBound := cpsTripleWithin_mono_nSteps (by omega) hOwn
        exact cpsTripleWithin_weaken
          (fun _ hp => by unfold pSucc vphlTopContinuationPre kFrame vphlTopKFrame savedRegTail; xperm_chunked hp)
          (fun _ hq => hq) hOwnBound
      · by omega
      · have hln32 : ln = (32 : Word) := not_not.mp hne
        let p32 : Assertion :=
          vphlTopContinuationPre spC parentBase parentLenW childBase childLenW outPtr v21
            (0 : Word) v11 v12 fo ln childBytes kFrame F
        let finalPost :=
          vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
            parentBase childBase parentBytes childBytes claimedOld childLen
            fo ln os ** F
        have hWhole : ∀ v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14,
            cpsTripleWithin (70 + keccakBodyFuel N rem) (vphlBase + 84) retHdr vphlFullCode
              (p32 ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
                (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
                (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
              (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) finalPost := by
          intro v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14
          have hprefix0 := vphl_arm_len_eq32_prefix_spec_within
            sp0 spC retHdr parentLenW childLenW outPtr cs0 cs1 cs2 cs3 cs4 v21
            parentBase childBase parentBytes childBytes claimedOld childLen fo ln
            v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 v11 v12 os
            hspC hret hsucc hln32
          have hprefix := cpsTripleWithin_weaken
            (fun _ hp => by unfold p32 vphlTopContinuationPre kFrame vphlTopKFrame savedRegTail; xperm_chunked hp)
            (fun _ hq => hq) hprefix0
          have hfb : fo.toNat + 32 ≤ childBytes.length :=
            hfieldBound fo ln hsucc hln32
          have hfa : (childBase + fo).toNat % 8 = 0 :=
            hfieldAlign fo ln hsucc hln32
          have hcopy0 := vphl_copy_claimed_spec_within
            sp0 spC retHdr parentLenW childLenW outPtr cs0 cs1 cs2 cs3 cs4 v21
            parentBase childBase parentBytes childBytes claimedOld childLen fo ln
            v15 v16 v17 v28 v29 v30 v31 v13 v14 v11 v12 os
            hfb hfa hcalign hcover hclaimedLen
          have hcopy := cpsTripleWithin_weaken
            (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hcopy0
          have hprep0 := vphl_hash_prep_spec_within
            sp0 spC retHdr parentLenW childLenW outPtr cs0 cs1 cs2 cs3 cs4 v21
            parentBase childBase parentBytes childBytes claimedOld fo ln
            v15 v16 v17 v28 v29 v30 v31 v13 v14 v11 v12 os
          have hprep := cpsTripleWithin_weaken
            (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hprep0
          have hclaimed32 : ((childBytes.drop fo.toNat).take 32).length = 32 := by
            rw [List.length_take]
            omega
          have hhash0 := vphl_hash_call_spec_within
            spC retHdr parentLenW childLenW outPtr cs0 cs1 cs2 cs3 cs4 v21
            parentBase childBase parentBytes childBytes N rem fo ln os
            hkeccakLen hrem_le hNbound hb8i hos hpover hpvalid
          have hhash := cpsTripleWithin_weaken
            (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hhash0
          have hpc := cpsTripleWithin_seq_perm_same_cr
            (fun _ hp => by xperm_chunked hp) hprefix hcopy
          have hpcp := cpsTripleWithin_seq_perm_same_cr
            (fun _ hp => by xperm_chunked hp) hpc hprep
          have hpch := cpsTripleWithin_seq_perm_same_cr
            (fun _ hp => by xperm_chunked hp) hpcp hhash
          let hashPost : Assertion :=
            vphlTopHashPost spC (vphlBase + 184) retHdr parentLenW childLenW outPtr v21
              cs0 cs1 cs2 cs3 cs4 parentBase childBase parentBytes childBytes
              ((childBytes.drop fo.toNat).take 32)
              (EvmAsm.Stateless.SpecRef.keccak256 parentBytes)
              (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0))
              fo ln
          have hTail : cpsTripleWithin 28 (vphlBase + 184) retHdr vphlFullCode
              hashPost finalPost := by
            intro R hR s hcr hPR hpc
            let hashRest : Assertion :=
              vphlTopHashRest spC (vphlBase + 184) retHdr parentLenW childLenW outPtr v21
                cs0 cs1 cs2 cs3 cs4 parentBase childBase parentBytes childBytes
                ((childBytes.drop fo.toNat).take 32)
                (EvmAsm.Stateless.SpecRef.keccak256 parentBytes)
                (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                  (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0))
                fo ln
            have hOwnedAll :
                (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
                  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
                  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                  (regOwn .x11 ** regOwn .x12 ** hashRest)) s := by
              unfold hashPost vphlTopHashPost
              unfold hashRest vphlTopHashRest
              xperm_hyp hPR
            obtain ⟨v5, v6, v7, v13, v14, v15, v16, v17, v28, v29, v30, v31,
              hVals⟩ := vphl_choose12 hOwnedAll
            obtain ⟨v11, hPair⟩ := sepConj_choose_regOwn (B := regOwn .x12 ** hashRest)
              (by xperm_hyp hVals)
            obtain ⟨v12, hRest⟩ := sepConj_choose_regOwn (B := hashRest)
              (by xperm_hyp hPair)
            let pVal : Assertion :=
              ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
                (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) **
                (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) ** (.x28 ↦ᵣ v28) **
                (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
                (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** hashRest)
            have hVal : cpsTripleWithin 28 (vphlBase + 184) retHdr vphlFullCode
                pVal finalPost := by
              let g5 : Assertion :=
                ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
                  (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
                  (.x31 ↦ᵣ v31) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** hashRest)
              let g6 : Assertion :=
                ((.x7 ↦ᵣ v7) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
                  (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
                  (.x31 ↦ᵣ v31) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** hashRest)
              have h5 := cpsTripleWithin_frameR g5 (by unfold g5; pcf)
                (vphlLa_claimed_5c v5)
              have h5' := cpsTripleWithin_weaken
                (fun _ hp => by unfold pVal g5; xperm_chunked hp)
                (fun _ hq => by unfold g5; xperm_chunked hq) h5
              have h6 := cpsTripleWithin_frameR g6 (by unfold g6; pcf)
                (vphlLa_computed_6 v6)
              have h6' := cpsTripleWithin_weaken
                (fun _ hp => by unfold g6; xperm_chunked hp)
                (fun _ hq => by unfold g6; xperm_chunked hq) h6
              have h56 := cpsTripleWithin_seq_perm_same_cr
                (fun _ hp => by xperm_chunked hp) h5' h6'
              let claimedB := (childBytes.drop fo.toNat).take 32
              let computedB := EvmAsm.Stateless.SpecRef.keccak256 parentBytes
              have hclen : claimedB.length = 32 := by
                unfold claimedB
                exact hclaimed32
              have hcdlen : computedB.length = 32 := by
                unfold computedB
                exact EvmAsm.Stateless.SpecRef.keccak256_length _
              let G0 : Assertion :=
                vphlTopCompareBase spC (vphlBase + 184) retHdr parentLenW childLenW outPtr v21
                  v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 cs0 cs1 cs2 cs3 cs4
                  parentBase childBase parentBytes childBytes fo ln
                  (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                    (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0))
              have hG0 : G0.pcFree := by unfold G0 vphlTopCompareBase; pcf
              let Gcmp : Assertion :=
                (.x20 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) **
                  (outPtr ↦ₘ (0 : Word)) ** G0
              have hGcmp : Gcmp.pcFree := by unfold Gcmp; pcf
              let GmatchEq : Assertion :=
                vphlTopCompareDword claimedB computedB 3 G0
              have hEqTail : cpsTripleWithin 24 (vphlBase + 200) retHdr vphlFullCode
                  ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
                    (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
                    bytesRegion vphlClaimedAddr claimedB **
                    bytesRegion vphlComputedAddr computedB ** Gcmp)
                  finalPost := by
                by_cases h0 : vphlDwordAt claimedB 0 = vphlDwordAt computedB 0
                · by_cases h1 : vphlDwordAt claimedB 1 = vphlDwordAt computedB 1
                  · by_cases h2 : vphlDwordAt claimedB 2 = vphlDwordAt computedB 2
                    · by_cases h3 : vphlDwordAt claimedB 3 = vphlDwordAt computedB 3
                      · have hEq0 := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareAllEq claimedB computedB v7 v28 hclen hcdlen h0 h1 h2 h3)
                        have hEq := cpsTripleWithin_frameR Gcmp hGcmp hEq0
                        have hMatch := vphlCompareMatchTail outPtr (0 : Word) GmatchEq
                          (by unfold GmatchEq vphlTopCompareDword; pcf)
                        have hEqBytes : claimedB = computedB := by
                          apply (vphl_dwords_eq_iff claimedB computedB hclen hcdlen).mp
                          intro q hq
                          interval_cases q <;> assumption
                        exact cpsTripleWithin_weaken
                          (fun _ hp => by
                            unfold GmatchEq vphlTopCompareDword Gcmp G0 vphlTopCompareBase
                            xperm_chunked hp)
                          (fun _ hq => by
                            unfold finalPost
                            simp only [vphlRetPost]
                            refine ⟨0, 1, fo, ln, claimedB, computedB, osPost, ?_⟩
                            refine (sepConj_pure_right _).2 ⟨?_, ?_⟩
                            · xperm_hyp hq
                            · exact Or.inr (Or.inr ⟨rfl, hsucc, hln32, rfl, rfl, rfl, rfl, rfl, by simp [hEqBytes]⟩)) hMatch
                      · have h0eq := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound0Eq claimedB computedB v7 v28 hclen hcdlen h0)
                        have h0eqF := cpsTripleWithin_frameR Gcmp hGcmp h0eq
                        have h1eq := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound1Eq claimedB computedB
                            (vphlDwordAt claimedB 0) (vphlDwordAt computedB 0)
                            hclen hcdlen h1)
                        have h1eqF := cpsTripleWithin_frameR Gcmp hGcmp h1eq
                        have h01 := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h0eqF h1eqF
                        have h2eq := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound2Eq claimedB computedB
                            (vphlDwordAt claimedB 1) (vphlDwordAt computedB 1)
                            hclen hcdlen h2)
                        have h2eqF := cpsTripleWithin_frameR Gcmp hGcmp h2eq
                        have h012 := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h01 h2eqF
                        have h3ne := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound3Ne claimedB computedB
                            (vphlDwordAt claimedB 2) (vphlDwordAt computedB 2)
                            hclen hcdlen h3)
                        have h3neF := cpsTripleWithin_frameR Gcmp hGcmp h3ne
                        have h0123 := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h012 h3neF
                        let Gne3 : Assertion := vphlTopCompareDword claimedB computedB 3 G0
                        have hGne3 : Gne3.pcFree := by unfold Gne3 vphlTopCompareDword; pcf
                        have hm := vphlCompareMismatchTail outPtr (0 : Word) Gne3 hGne3
                        have hseq := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h0123 hm
                        have hbound := cpsTripleWithin_mono_nSteps (by omega) hseq
                        exact cpsTripleWithin_weaken
                          (fun _ hp => by xperm_chunked hp)
                          (fun _ hq => by
                            unfold finalPost
                            simp only [vphlRetPost]
                            refine ⟨0, 0, fo, ln, claimedB, computedB, osPost, ?_⟩
                            refine (sepConj_pure_right _).2 ⟨?_, ?_⟩
                            · xperm_hyp hq
                            · exact Or.inr (Or.inr ⟨rfl, hsucc, hln32, rfl, rfl, rfl, by simp⟩)) hbound
                    · have h0eq := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound0Eq claimedB computedB v7 v28 hclen hcdlen h0)
                        have h0eqF := cpsTripleWithin_frameR Gcmp hGcmp h0eq
                        have h1ne := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound1Eq claimedB computedB
                            (vphlDwordAt claimedB 0) (vphlDwordAt computedB 0)
                            hclen hcdlen h1)
                        have h1neF := cpsTripleWithin_frameR Gcmp hGcmp h1ne
                        have h01 := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h0eqF h1neF
                        have h2ne := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound2Ne claimedB computedB
                            (vphlDwordAt claimedB 1) (vphlDwordAt computedB 1)
                            hclen hcdlen h2)
                        have h2neF := cpsTripleWithin_frameR Gcmp hGcmp h2ne
                        have h012 := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h01 h2neF
                        let Gne2 : Assertion := vphlTopCompareDword claimedB computedB 2 G0
                        have hGne2 : Gne2.pcFree := by unfold Gne2 vphlTopCompareDword; pcf
                        have hm := vphlCompareMismatchTail outPtr (0 : Word) Gne2 hGne2
                        have hseq := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h012 hm
                        have hbound := cpsTripleWithin_mono_nSteps (by omega) hseq
                        exact cpsTripleWithin_weaken
                          (fun _ hp => by xperm_chunked hp)
                          (fun _ hq => by
                            unfold finalPost
                            simp only [vphlRetPost]
                            refine ⟨0, 0, fo, ln, claimedB, computedB, osPost, ?_⟩
                            refine (sepConj_pure_right _).2 ⟨?_, ?_⟩
                            · xperm_hyp hq
                            · exact Or.inr (Or.inr ⟨rfl, hsucc, hln32, rfl, rfl, rfl, by simp⟩)) hbound
                  · have h0eq := cpsTripleWithin_extend_code hbody_sub
                        (vphlCompareRound0Eq claimedB computedB v7 v28 hclen hcdlen h0)
                    have h0eqF := cpsTripleWithin_frameR Gcmp hGcmp h0eq
                    have h1ne := cpsTripleWithin_extend_code hbody_sub
                      (vphlCompareRound1Ne claimedB computedB
                        (vphlDwordAt claimedB 0) (vphlDwordAt computedB 0)
                        hclen hcdlen h1)
                    have h1neF := cpsTripleWithin_frameR Gcmp hGcmp h1ne
                    have h01 := cpsTripleWithin_seq_perm_same_cr
                      (fun _ hp => by xperm_chunked hp) h0eqF h1neF
                    let Gne1 : Assertion := vphlTopCompareDword claimedB computedB 1 G0
                    have hGne1 : Gne1.pcFree := by unfold Gne1 vphlTopCompareDword; pcf
                    have hm := vphlCompareMismatchTail outPtr (0 : Word) Gne1 hGne1
                    have hseq := cpsTripleWithin_seq_perm_same_cr
                      (fun _ hp => by xperm_chunked hp) h01 hm
                    have hbound := cpsTripleWithin_mono_nSteps (by omega) hseq
                    exact cpsTripleWithin_weaken
                      (fun _ hp => by xperm_chunked hp)
                      (fun _ hq => by
                        unfold finalPost
                        simp only [vphlRetPost]
                        refine ⟨0, 0, fo, ln, claimedB, computedB, osPost, ?_⟩
                        refine (sepConj_pure_right _).2 ⟨?_, ?_⟩
                        · xperm_hyp hq
                        · exact Or.inr (Or.inr ⟨rfl, hsucc, hln32, rfl, rfl, rfl, by simp⟩)) hbound
                · have h0ne := cpsTripleWithin_extend_code hbody_sub
                      (vphlCompareRound0Ne claimedB computedB v7 v28 hclen hcdlen h0)
                  have h0neF := cpsTripleWithin_frameR Gcmp hGcmp h0ne
                  let Gne0 : Assertion := vphlTopCompareDword claimedB computedB 0 G0
                  have hGne0 : Gne0.pcFree := by unfold Gne0 vphlTopCompareDword; pcf
                  have hm := vphlCompareMismatchTail outPtr (0 : Word) Gne0 hGne0
                  have hseq := cpsTripleWithin_seq_perm_same_cr
                    (fun _ hp => by xperm_chunked hp) h0neF hm
                  have hbound := cpsTripleWithin_mono_nSteps (by omega) hseq
                  exact cpsTripleWithin_weaken
                    (fun _ hp => by xperm_chunked hp)
                    (fun _ hq => by
                      unfold finalPost
                      simp only [vphlRetPost]
                      refine ⟨0, 0, fo, ln, claimedB, computedB, osPost, ?_⟩
                      refine (sepConj_pure_right _).2 ⟨?_, ?_⟩
                      · xperm_hyp hq
                      · exact Or.inr (Or.inr ⟨rfl, hsucc, hln32, rfl, rfl, rfl, by simp⟩)) hbound
              have hAll := cpsTripleWithin_seq_perm_same_cr
                (fun _ hp => by xperm_chunked hp) h56 hEqTail
              exact hAll
            exact hVal R hR s hcr (by unfold pVal; xperm_hyp hRest) hpc
          have hAll := cpsTripleWithin_seq_perm_same_cr
            (fun _ hp => by unfold hashPost vphlTopHashPost; xperm_chunked hp) hpch hTail
          exact hAll
        have hOwn := vphl_of_forall_regIs_to_regOwn12
          (P := p32) (Q := finalPost) hWhole
        exact cpsTripleWithin_weaken
          (fun _ hp => by unfold p32 vphlTopContinuationPre kFrame vphlTopKFrame savedRegTail; xperm_chunked hp)
          (fun _ hq => hq) hOwn
  have hcall := vphl_callReturn_pre (F := kFrame ** F)
    (Q := vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
      parentBase childBase parentBytes childBytes claimedOld childLen oldOffset oldLen os ** F)
    spC childBase vphlOffsetAddr vphlLengthAddr oldOffset oldLen
    { ra := vphlBase + 84, s0 := parentBase, s1 := parentLenW,
      s2 := childBase, s3 := childLenW, s4 := outPtr, s5 := v21 }
    childBytes childLen hcont
  have hkcall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by unfold kFrame vphlTopKFrame; xperm_chunked hp) hkF hcall
  have hpre := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hproF hkcall
  exact hpre

end EvmAsm.Codegen.ValidateParentHashLinkSpec
