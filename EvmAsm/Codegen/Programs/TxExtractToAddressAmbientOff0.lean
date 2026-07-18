/-
  Ambient ExtractAssumed applications at off=0 from slice path Props.

  When off=0, loadPtr=regionBase and txSlice=bs, so slice ExtractAssumed
  footprint coincides with ambient. General off residual (body dualization).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressExtractAssumedDischarge
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.DualReadByteScan (validByteRange)
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps nExtractStackDwords ExtractAssumed extractToBufOwn teaScratchOwn
    fullCode)
open EvmAsm.Codegen.TxTypeDispatchSpec
  (txSlice txSlice_off0 teerTxTypeDispatch)
open EvmAsm.Codegen.TxExtractToAddressModel (extractSuccess)
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
/-- Ambient Assumed footprint at off=0 under short type234 creation path.
    classical-3. Slice path Prop is ambient when loadPtr=regionBase. -/
theorem extractAssumed_ambient_creation_type234_short_off0
    (ret spVal regionBase loadPtr lenW toBuf isCreationPtr : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 0)
    (hlen : lenW = BitVec.ofNat 64 bs.length)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hpath : extractCreationType234ShortPath bs items) :
    cpsTripleWithin nExtractSteps E ret fullCode
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
        (.x0 ↦ᵣ (0 : Word))) := by
  have hload : loadPtr = regionBase := by
    rw [hptr]
    apply BitVec.eq_of_toNat_eq
    have hlt : regionBase.toNat < 2 ^ 64 := by exact regionBase.isLt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
      Nat.mod_eq_of_lt hlt]
  have hslice :=
    extractAssumed_success_flat_creation_type234_short
      ret spVal regionBase lenW toBuf isCreationPtr
      s0 s1 s2 s3 s4 s5 s6 s7 bs items
      hret hlen halign hover hvalidBuf htalign htover htvalid hpath
  refine cpsTripleWithin_weaken
    (fun _ hp => by
      -- ambient pre (x10↦loadPtr) → extractAssumedPre (x10↦regionBase)
      rw [hload] at hp
      simp only [extractAssumedPre]
      xperm_hyp hp)
    (fun _ hq => by
      simp only [extractAssumedPost] at hq
      xperm_hyp hq) hslice

#print axioms extractAssumed_ambient_creation_type234_short_off0

end EvmAsm.Codegen.TxExtractToAddressSpec
