/-
  Discharge packaging hvalid*/hvalid1_*/hlover/hlvalid via validByteRange
  for long-list legacy creation.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Codegen.Programs.TxExtractToAddressTopAssumedLongConcretePureHdecLegacy
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nExtractSteps fullCode extractLinked_mono)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.Codegen.TxExtractToAddressHonesty
open EvmAsm.Codegen.TxExtractToAddressModel
open EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_longConcrete_pureHvalid_legacy
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (htype0 : (teerTxTypeDispatch txBytes).2.1 = (0 : Word))
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hlong : 55 < (encode.encodeItems items).length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hge5 : 5 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra extractLinkedCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) := by
  have htx := extractSuccess_hvalid_tx0_inner txBytes txBase hsuccess hvalidBuf
  have hinover := extractSuccess_hinover txBytes txBase hsuccess hover
  have hv :=
    extractSuccess_creation_legacy_hvalid_srcOff_long txBytes txBase hsuccess
      hcreFlag htype0 items hdecL hlong hge5 hvalidBuf
  have hll :=
    extractSuccess_long_hlover_hlvalid txBytes txBase hsuccess items hdecL hlong
      hover hvalidBuf
  exact extractAssumed_creation_longConcrete_pureHdec_legacy
    sp0 spC s txBase lenW toBuf isCreationPtr txBytes items
    hspC hret htalign htover htvalid hlen hsuccess hcreFlag htype0 hdecL hlong
    halign hover htx.1 hinover htx.2 hll.1 hll.2
    hitem0 hv.1 hv.2.1
    hitem1 hv.2.2.1 hv.2.2.2.1
    hitem2 hv.2.2.2.2.1 hv.2.2.2.2.2.1
    hitem3 hv.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.2
    hge5

set_option maxRecDepth 8000 in
theorem extractAssumed_creation_longConcrete_pureHvalid_legacy_fullCode
    (sp0 spC : Word) (s : ExtractSaved)
    (txBase lenW toBuf isCreationPtr : Word)
    (txBytes : List (BitVec 8))
    (items : List EL.RLP.RLPItem)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12))
    (hret : s.ra &&& ~~~(1 : Word) = s.ra)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : extractSuccess txBytes)
    (hcreFlag : (teerExtractToAddress txBytes).2.2 = (1 : Word))
    (htype0 : (teerTxTypeDispatch txBytes).2.1 = (0 : Word))
    (hdecL : decodeListItems (txBytes.drop (teerTxTypeDispatch txBytes).2.2.toNat) =
      some items)
    (hlong : 55 < (encode.encodeItems items).length)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalidBuf : validByteRange txBase txBytes.length)
    (hitem0 : (encode (items[0]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hitem1 : (encode (items[1]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hitem2 : (encode (items[2]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hitem3 : (encode (items[3]'(by
        have := extractSuccess_creation_legacy_items_length_long txBytes hsuccess
          hcreFlag htype0 items hdecL hlong; omega))).length ≤ 55)
    (hge5 : 5 ≤ items.length) :
    cpsTripleWithin nExtractSteps E s.ra fullCode
      (extractAssumedPre s.ra sp0 txBase lenW toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes)
      (extractAssumedPost s.ra sp0 txBase toBuf isCreationPtr
        s.s0 s.s1 s.s2 s.s3 s.s4 s.s5 s.s6 s.s7 txBytes) :=
  cpsTripleWithin_extend_code extractLinked_mono
    (extractAssumed_creation_longConcrete_pureHvalid_legacy
      sp0 spC s txBase lenW toBuf isCreationPtr txBytes items
      hspC hret htalign htover htvalid hlen hsuccess hcreFlag htype0 hdecL hlong
      halign hover hvalidBuf
      hitem0 hitem1 hitem2 hitem3 hge5)

#print axioms extractAssumed_creation_longConcrete_pureHvalid_legacy
#print axioms extractAssumed_creation_longConcrete_pureHvalid_legacy_fullCode

end EvmAsm.Codegen.TxExtractToAddressSpec
