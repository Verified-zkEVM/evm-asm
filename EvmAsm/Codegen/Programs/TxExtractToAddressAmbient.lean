/-
  Multi-tx Option A substrate for `tx_extract_to_address`.

  Slice form owns `bytesRegion txBase txBytes` (txBase % 8 = 0).
  Array multi-tx has ambient `bytesRegion regionBase blob` with
  `loadPtr = regionBase + off` (SSZ offs 4-align, not 8) — cannot peel via
  `bytesRegion_split`. Ambient re-spec (BgvOffset-style) keeps the full region.

  General `success_flat` is the ambient Assumed hyp (body packaging residual).
  off=0 recovers from slice ExtractAssumed.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbientTop
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.DualReadByteScan (validByteRange)
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps nExtractStackDwords ExtractAssumed extractToBufOwn teaScratchOwn
    fullCode)
open EvmAsm.Codegen.TxExtractToAddressModel (extractSuccess)
open EvmAsm.Codegen.TxTypeDispatchSpec
  (txSlice txSlice_off0 TypeDispatchAssumedAmbientFull
    typeDispatchAssumedAmbient_fullCode)

/-- Ambient Assumed success contract for extract (multi-tx Option A).

    ABI: a0=loadPtr, a1=len, a2=to_buf, a3=is_creation → a0=0 on success.
    Owns ambient `bytesRegion regionBase bs`; pure model on `txSlice bs off len`.
    General off/len body packaging residual; off=0 filled from slice Assumed. -/
structure ExtractAssumedAmbient (cr : CodeReq) where
  entry : Word
  success_flat :
    ∀ (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
      (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
      (bs : List (BitVec 8)) (off len : Nat),
      (ret &&& ~~~(1 : Word)) = ret →
      loadPtr = regionBase + BitVec.ofNat 64 off →
      lenW = BitVec.ofNat 64 len →
      extractSuccess (txSlice bs off len) →
      regionBase.toNat % 8 = 0 →
      off + len ≤ bs.length →
      regionBase.toNat + bs.length < 2 ^ 64 →
      validByteRange regionBase bs.length →
      toBuf.toNat % 8 = 0 →
      toBuf.toNat + 16 < 2 ^ 64 →
      isValidMemAccess (toBuf + (16 : Word)) = true →
      cpsTripleWithin nExtractSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          stackFree spVal nExtractStackDwords **
          (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
          (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
          bytesRegion regionBase bs **
          extractToBufOwn toBuf ** memOwn isCreationPtr ** teaScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
          stackFree spVal nExtractStackDwords **
          (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
          (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
          (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs **
          extractToBufOwn toBuf ** memOwn isCreationPtr ** teaScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))

/-- off=0 ambient application from slice ExtractAssumed. classical-3. -/
theorem extractAssumed_ambient_off0
    (asm : ExtractAssumed fullCode)
    (ret spVal regionBase lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 bs.length)
    (hextractOk : extractSuccess bs)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    cpsTripleWithin nExtractSteps asm.entry ret fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nExtractStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ regionBase) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
        bytesRegion regionBase bs **
        extractToBufOwn toBuf ** memOwn isCreationPtr ** teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nExtractStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        extractToBufOwn toBuf ** memOwn isCreationPtr ** teaScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) :=
  asm.success_flat ret spVal regionBase lenW toBuf isCreationPtr
    s0 s1 s2 s3 s4 s5 s6 s7 bs
    hret hlen hextractOk halign hover hvalidBuf htalign htover htvalid

/-- Combined ambient callee assumptions for multi-tx intrinsic discharge.

    `extract.success_flat` general off is residual body packaging;
    `typeDispatch` is discharged (`typeDispatchAssumedAmbient_fullCode`). -/
structure TisCalleeAssumptionsAmbient (cr : CodeReq) where
  extract : ExtractAssumedAmbient cr
  typeDispatch : TypeDispatchAssumedAmbientFull cr

#print axioms extractAssumed_ambient_off0

/-- Dualization strategy for general-off ExtractAssumedAmbient body:

    Walk leaves (`rlp_walk_init_*`, `rlp_walk_next_*`) are already ambient-capable:
    they take `listBase`/`srcBase` with `% 8 = 0` + `bytesRegion base bs` + absolute
    `listOff`/`srcOff` into the blob. Ambient packaging sets:
      listBase := regionBase
      listOff  := off + sliceRel   -- `ambientAbsOff`
      a0       := loadPtr + sliceRel = regionBase + (off + sliceRel)
    Pure models stay on `txSlice bs off len`; byte equality via `txSlice_getElem`.
    Type call dual uses `typeDispatchAssumedAmbient_fullCode` (DONE).
    Residual: dualize extract Top packaging chain (~124 files) by offset-shift
    (not leaf rewrite); pure honesty shortListSrcOff → ambientAbsOff. -/
def extractAmbientBodyDualStrategy : True := trivial

end EvmAsm.Codegen.TxExtractToAddressSpec
