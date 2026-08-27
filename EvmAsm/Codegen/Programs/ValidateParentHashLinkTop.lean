import EvmAsm.Codegen.Programs.ValidateParentHashLinkTopPrelude
import EvmAsm.Codegen.Programs.ValidateParentHashLinkTopContinuation

/-!
  Top-level composition for `validate_parent_hash_link`.

  The prelude contains shared frame/post definitions, and the continuation
  module contains the hash/equality/continuation contracts.  This file keeps
  only the final whole-routine composition theorem.
-/

namespace EvmAsm.Codegen.ValidateParentHashLinkSpec
set_option maxRecDepth 8000
open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpListNthItemSAsm
theorem validate_parent_hash_link_spec_within
    (sp0 spC retHdr parentBase parentLenW childBase childLenW outPtr : Word)
    (cs0 cs1 cs2 cs3 cs4 v21 oldOut oldOffset oldLen : Word)
    (parentBytes childBytes claimedOld : List (BitVec 8))
    (childLen N rem : Nat) (os : List (BitVec 8)) (F : Assertion)
    (hret : retHdr &&& ~~~(1 : Word) = retHdr)
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hplenW : parentLenW = BitVec.ofNat 64 parentBytes.length)
    (hclenW : childLenW = BitVec.ofNat 64 childLen)
    (hpover : parentBase.toNat + parentBytes.length < 2 ^ 64)
    (hpvalid : ∀ k, k < parentBytes.length →
      isValidByteAccess (parentBase + BitVec.ofNat 64 k) = true)
    (hcalign : childBase.toNat % 8 = 0)
    (hcslack : childLen + 9 ≤ childBytes.length)
    (hcover : childBase.toNat + childBytes.length < 2 ^ 64)
    (hcvalid : ∀ k, k < childBytes.length →
      isValidByteAccess (childBase + BitVec.ofNat 64 k) = true)
    (hkeccakLen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hb8i : (keccakAbsorbCursor parentBase N).toNat % 8 = 0)
    (hos : os.length = 200)
    (hclaimedLen : claimedOld.length = 32)
    (hF : F.pcFree) :
    cpsTripleWithin (583 + keccakBodyFuel N rem) vphlBase retHdr vphlCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ retHdr) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) **
        (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ v21) **
        (.x10 ↦ᵣ parentBase) ** (.x11 ↦ᵣ parentLenW) ** (.x12 ↦ᵣ childBase) **
        (.x13 ↦ᵣ childLenW) ** (.x14 ↦ᵣ outPtr) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x17 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
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
  have hbody_sub : ∀ a i, vphlCompareBodyCode a = some i → vphlCode a = some i := by
    intro a i h
    exact vphlCode_vphl a i h
  have hpro0 := vphl_prologue_spec_within sp0 spC retHdr cs0 cs1 cs2 cs3 cs4 v21
    parentBase parentLenW childBase childLenW outPtr oldOut oldOffset oldLen
    parentBytes childBytes claimedOld os hspC
  have hpro := cpsTripleWithin_extend_code hbody_sub hpro0
  have hproF := cpsTripleWithin_frameR F hF hpro
  let kFrame : Assertion :=
    vphlTopKFrame spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 parentBase parentBytes
      claimedOld os
  let kFrameCore : Assertion :=
    vphlTopKFrameCore spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 parentBase parentBytes
      claimedOld os
  have hcover_le : childBase.toNat + childBytes.length ≤ 2 ^ 64 := Nat.le_of_lt hcover
  have hk := vphl_k20_call_spec_within spC retHdr parentBase parentLenW
    childBase childLenW outPtr v21 oldOffset oldLen parentBytes childBytes claimedOld os
    childLen cs0 cs1 cs2 cs3 cs4 hclenW hcalign hcslack hcover_le hcvalid
  have hkF := cpsTripleWithin_frameR F hF hk
  have hcont := vphl_continuation_spec
    sp0 spC retHdr parentBase parentLenW childBase childLenW outPtr
    cs0 cs1 cs2 cs3 cs4 v21 oldOffset oldLen parentBytes childBytes claimedOld
    childLen N rem os kFrame kFrameCore F rfl rfl hret hspC hplenW hcalign hcslack hcover hcvalid hpover hpvalid hkeccakLen hrem_le hNbound hb8i hos
    hclaimedLen hF
  have hcall := vphl_callReturn_pre (F := kFrame ** F)
    (Q := vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
      parentBase childBase parentBytes childBytes claimedOld childLen oldOffset oldLen os ** F)
    spC childBase vphlOffsetAddr vphlLengthAddr oldOffset oldLen
    { ra := vphlBase + 84, s0 := parentBase, s1 := parentLenW,
      s2 := childBase, s3 := childLenW, s4 := outPtr, s5 := v21 }
    childBytes childLen hcont
  have hkcall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [kFrame, vphlTopKFrame] at hp ⊢
      xperm_chunked hp) hkF hcall
  have hpre := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hproF hkcall
  have hpreBound := cpsTripleWithin_mono_nSteps
    (nSteps' := 583 + keccakBodyFuel N rem) (by omega) hpre
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => hq) hpreBound


end EvmAsm.Codegen.ValidateParentHashLinkSpec
