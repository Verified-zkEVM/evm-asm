/-
  Multi-tx Option A substrate for `tx_extract_to_address`.

  Slice form owns `bytesRegion txBase txBytes` (txBase % 8 = 0).
  Array multi-tx has ambient `bytesRegion regionBase blob` with
  `loadPtr = regionBase + off` (SSZ offs 4-align, not 8) — cannot peel via
  `bytesRegion_split`. Ambient re-spec (BgvOffset-style) keeps the full region.

  This file: ambient Assumed structure + off=0 recovery from slice ExtractAssumed.
  Residual: general off/len extract body ambient packaging (LBU/LD/walks/type call).
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
    fullCode TypeDispatchAssumed)
open EvmAsm.Codegen.TxExtractToAddressModel (extractSuccess)
open EvmAsm.Codegen.TxTypeDispatchSpec
  (txSlice TypeDispatchAssumedAmbientFull typeDispatchAssumedAmbient_fullCode)

/-- Ambient Assumed success contract for extract (multi-tx Option A).

    off=0 arm recovers slice ExtractAssumed (loadPtr = regionBase, full blob).
    General off/len residual (extract body ambient re-spec). -/
structure ExtractAssumedAmbient (cr : CodeReq) where
  entry : Word
  /-- Slice-eq-ambient: off=0, len=bs.length, loadPtr=regionBase. -/
  success_flat_off0 :
    ∀ (ret spVal regionBase lenW toBuf isCreationPtr : Word)
      (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
      (bs : List (BitVec 8)),
      (ret &&& ~~~(1 : Word)) = ret →
      lenW = BitVec.ofNat 64 bs.length →
      extractSuccess bs →
      regionBase.toNat % 8 = 0 →
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
          (.x0 ↦ᵣ (0 : Word)))

/-- off=0 ambient Assumed from any slice ExtractAssumed. classical-3. -/
def extractAssumedAmbient_off0_pkg (asm : ExtractAssumed fullCode) :
    ExtractAssumedAmbient fullCode where
  entry := asm.entry
  success_flat_off0 := fun ret spVal regionBase lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs
      hret hlen hextractOk halign hover hvalidBuf htalign htover htvalid =>
    asm.success_flat ret spVal regionBase lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs
      hret hlen hextractOk halign hover hvalidBuf htalign htover htvalid

/-- Combined ambient callee assumptions for multi-tx intrinsic discharge. -/
structure TisCalleeAssumptionsAmbient (cr : CodeReq) where
  extract : ExtractAssumedAmbient cr
  typeDispatch : TypeDispatchAssumedAmbientFull cr

/-- Package ambient callees from slice extract Assumed + ambient type full. -/
def tisCalleeAssumptionsAmbient_off0
    (hextract : ExtractAssumed fullCode) :
    TisCalleeAssumptionsAmbient fullCode where
  extract := extractAssumedAmbient_off0_pkg hextract
  typeDispatch := typeDispatchAssumedAmbient_fullCode

#print axioms extractAssumedAmbient_off0_pkg
#print axioms tisCalleeAssumptionsAmbient_off0

end EvmAsm.Codegen.TxExtractToAddressSpec
