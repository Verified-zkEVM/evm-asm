/-
  hrunA wire: applied_as_postEx_is @ srcOffA9=0 → free26 empty-short ExitPack (Is-path).

  Standalone inhabit of residual hrunA packaging. Does NOT clone walk binders into
  packaging structures; calls applied_as_postEx_is then free26_to_exitPack_of_hrun.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontAuthContentHrun
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopEmptyExit
import EvmAsm.Codegen.Programs.TxEip7702TeerFrontAuthCount
import EvmAsm.Codegen.Programs.TxEip7702TeerFrontListCount
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArraySpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch txSlice loadPtr_add_rel_eq)
open EvmAsm.Codegen.TxExtractToAddressHonesty
  (rlpItemDecode_single_byte rlpItemDecode_single_byte_next
    rlpItemDecode_empty_short rlpItemDecode_pfx80_imp_next rlpItemDecode_pfx80_imp_len0
    rlpItemDecode_addr20_short rlpItemDecode_pfx94_imp_next rlpItemDecode_pfx94_imp_len20
    rlpItemDecode_short_string_next hnext_short_string_of_decode
    rlpItemDecode_short_list)
open EvmAsm.Rv64.SAsm (toNat_zeroExtend_byte)

set_option maxRecDepth 8000

/-- Wire `applied_as_postEx_is` at `srcOffA9 = 0` into free26 empty-short ExitPack (Is-path).
    Residual ABI wire + domain fixture on the empty-short identity path. -/
theorem teerEmptyAuth_free26_to_exitPack_of_applied_as_postEx_is_empty_short
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
(hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hover0 : regionBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0I : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hover1 : regionBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hoverA : regionBase.toNat + srcOffA < 2 ^ 64)
    (hvalidA : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA) = true)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hoverA1 : regionBase.toNat + srcOffA1 < 2 ^ 64)
    (hvalidA1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA1) = true)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hoverA2 : regionBase.toNat + srcOffA2 < 2 ^ 64)
    (hvalidA2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA2) = true)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hoverA3 : regionBase.toNat + srcOffA3 < 2 ^ 64)
    (hvalidA3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA3) = true)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hoverA4 : regionBase.toNat + srcOffA4 < 2 ^ 64)
    (hvalidA4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA4) = true)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hoverA5 : regionBase.toNat + srcOffA5 < 2 ^ 64)
    (hvalidA5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA5) = true)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hoverA6 : regionBase.toNat + srcOffA6 < 2 ^ 64)
    (hvalidA6 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA6) = true)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hoverA7 : regionBase.toNat + srcOffA7 < 2 ^ 64)
    (hvalidA7 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA7) = true)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hoverA8 : regionBase.toNat + srcOffA8 < 2 ^ 64)
    (hvalidA8 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA8) = true)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hoverA9 : regionBase.toNat + srcOffA9 < 2 ^ 64)
    (hvalidA9 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA9) = true)
    (hssA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA9 + 1 < bs.length ∧ regionBase.toNat + (srcOffA9 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1)) = true)
    (hlsA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hllA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hoff0c : (0 : Nat) < bs.length)
    (h0c : bs[0]'hoff0c = (0xc0 : BitVec 8))
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (hs0w : s0 = loadPtr) (hs1w : s1 = lenW)
    (hs2w : s2 = balPtr) (hs3w : s3 = balLenW)
    (hs4w : chainIdW = s4)
    (hs9w :
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = s9)
    (hv24w : s8 = regionBase + BitVec.ofNat 64 srcOffV)
    (hslack : 1 + 9 ≤ bs.length)
    (hvalidB : ∀ k, k < bs.length →
      isValidByteAccess (regionBase + BitVec.ofNat 64 k) = true) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1)
      E AfterAuthLoopLi teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun h =>
        ∃ (refund t0Old t1Old baiW' : Word),
          teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur regionBase)
            (teerAuthLoopEmptyWalkEnd regionBase (BitVec.ofNat 64 1))
            refund
            (teerAuthLoopEmptyWalkCur regionBase)
            (teerAuthLoopEmptyWalkEnd regionBase (BitVec.ofNat 64 1))
            t0Old t1Old baiW'
            regionBase bs balBytes balPtr h) := by
  intro s
  let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
  let listLen := lenW - innerVal
  let endL := (regionBase + BitVec.ofNat 64 listOff) + listLen
  let endW := endL
  let cursorV := regionBase + BitVec.ofNat 64 srcOffV
  have hrun0 :=
    teerAuthContent_applied_as_postEx_is
      ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW s0 s1 s2 s3
      s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs balBytes off len hspC hnez
      hptr hlenW hsuccess htype4 halign hbound hover hvalid0 listOff ha0
      hoffL hoverL hvalidL hlenL h_ge h_hi h_exact srcOff0 hcur0 hoff0
      hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0 srcOff1 hoff1 hover1
      hvalid1 hss1 hls1 hll1 hdec1 hinb1 srcOff2 hoff2 hover2 hvalid2 hss2
      hls2 hll2 hdec2 hinb2 srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3
      hdec3 hinb3 srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
      srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5 hbridge
      hbridge1 hbridge2 hbridge3 hbridge4 srcOffV hoffV hoverV hvalidV hssV
      hlsV hllV hdecV hinbV hbridge5 srcOffA hcurA hoffA hoverA hvalidA
      hssA hlsA hllA hdecA hinbA srcOffA1 hoffA1 hoverA1 hvalidA1 hssA1
      hlsA1 hllA1 hdecA1 hinbA1 hbridgeA srcOffA2 hoffA2 hoverA2 hvalidA2
      hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1 srcOffA3 hoffA3 hoverA3
      hvalidA3 hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2 srcOffA4 hoffA4
      hoverA4 hvalidA4 hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3 srcOffA5
      hoffA5 hoverA5 hvalidA5 hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
      srcOffA6 hoffA6 hoverA6 hvalidA6 hssA6 hlsA6 hllA6 hdecA6 hinbA6
      hbridgeA5 srcOffA7 hoffA7 hoverA7 hvalidA7 hssA7 hlsA7 hllA7 hdecA7
      hinbA7 hbridgeA6 srcOffA8 hoffA8 hoverA8 hvalidA8 hssA8 hlsA8 hllA8
      hdecA8 hinbA8 hbridgeA7 srcOffA9 hoffA9 hoverA9 hvalidA9 hssA9 hlsA9
      hllA9 hdecA9 hinbA9 hbridgeA8
  have hrun : cpsTripleWithin nFrontToAtListCount E AtListCount teerLinkedCount
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
        (.x27 ↦ᵣ s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (teerAuthContentAppliedPostExIs spVal spC loadPtr lenW balPtr balLenW chainIdW
        s7 cursorV endW s11 s innerVal endL regionBase bs balBytes 0) := by
    simpa [hA9, s, innerVal, listLen, endL, endW, cursorV] using hrun0
  exact teerEmptyAuth_free26_to_exitPack_of_hrun_empty_short_decode_is
    ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s bs balBytes hspC
    innerVal endL endW cursorV hoff0c h0c asm
    hs0w hs1w hs2w hs3w
    (by rfl) (by rfl) (by rfl) (by rfl)
    (by simpa [s] using hs4w)
    (by simpa [s, endW, endL, listLen, innerVal] using hs9w)
    (by rfl)
    (by simpa [cursorV] using hv24w)
    (by simpa using halign) hslack (by simpa using hover) hvalidB
    hrun

#print axioms teerEmptyAuth_free26_to_exitPack_of_applied_as_postEx_is_empty_short

/-- ABI-pinned specialization of of_applied: s0=loadPtr, s1=lenW, s2=balPtr, s3=balLenW,
    s4=chainIdW, s8=cursorV, s9=endW — wire hyps discharge by rfl.
    Residual: empty-short domain (0xc0/slack/valid) + walk guards + list_count asm. -/
theorem teerEmptyAuth_free26_to_exitPack_of_applied_as_postEx_is_empty_short_abi
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s5 s6 s7 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hover0 : regionBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0I : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hover1 : regionBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hoverA : regionBase.toNat + srcOffA < 2 ^ 64)
    (hvalidA : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA) = true)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hoverA1 : regionBase.toNat + srcOffA1 < 2 ^ 64)
    (hvalidA1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA1) = true)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hoverA2 : regionBase.toNat + srcOffA2 < 2 ^ 64)
    (hvalidA2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA2) = true)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hoverA3 : regionBase.toNat + srcOffA3 < 2 ^ 64)
    (hvalidA3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA3) = true)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hoverA4 : regionBase.toNat + srcOffA4 < 2 ^ 64)
    (hvalidA4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA4) = true)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hoverA5 : regionBase.toNat + srcOffA5 < 2 ^ 64)
    (hvalidA5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA5) = true)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hoverA6 : regionBase.toNat + srcOffA6 < 2 ^ 64)
    (hvalidA6 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA6) = true)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hoverA7 : regionBase.toNat + srcOffA7 < 2 ^ 64)
    (hvalidA7 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA7) = true)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hoverA8 : regionBase.toNat + srcOffA8 < 2 ^ 64)
    (hvalidA8 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA8) = true)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hoverA9 : regionBase.toNat + srcOffA9 < 2 ^ 64)
    (hvalidA9 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA9) = true)
    (hssA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA9 + 1 < bs.length ∧ regionBase.toNat + (srcOffA9 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1)) = true)
    (hlsA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hllA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hoff0c : (0 : Nat) < bs.length)
    (h0c : bs[0]'hoff0c = (0xc0 : BitVec 8))
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (hslack : 1 + 9 ≤ bs.length)
    (hvalidB : ∀ k, k < bs.length →
      isValidByteAccess (regionBase + BitVec.ofNat 64 k) = true) :
    let s0 := loadPtr
    let s1 := lenW
    let s2 := balPtr
    let s3 := balLenW
    let s4 := chainIdW
    let s8 := regionBase + BitVec.ofNat 64 srcOffV
    let s9 :=
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1)
      E AfterAuthLoopLi teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun h =>
        ∃ (refund t0Old t1Old baiW' : Word),
          teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur regionBase)
            (teerAuthLoopEmptyWalkEnd regionBase (BitVec.ofNat 64 1))
            refund
            (teerAuthLoopEmptyWalkCur regionBase)
            (teerAuthLoopEmptyWalkEnd regionBase (BitVec.ofNat 64 1))
            t0Old t1Old baiW'
            regionBase bs balBytes balPtr h) := by
  intro s0 s1 s2 s3 s4 s8 s9 s
  exact teerEmptyAuth_free26_to_exitPack_of_applied_as_postEx_is_empty_short
    ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact
    srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV hoverV hvalidV hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA hoverA hvalidA hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 hoverA1 hvalidA1 hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
    srcOffA2 hoffA2 hoverA2 hvalidA2 hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1
    srcOffA3 hoffA3 hoverA3 hvalidA3 hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2
    srcOffA4 hoffA4 hoverA4 hvalidA4 hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3
    srcOffA5 hoffA5 hoverA5 hvalidA5 hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
    srcOffA6 hoffA6 hoverA6 hvalidA6 hssA6 hlsA6 hllA6 hdecA6 hinbA6 hbridgeA5
    srcOffA7 hoffA7 hoverA7 hvalidA7 hssA7 hlsA7 hllA7 hdecA7 hinbA7 hbridgeA6
    srcOffA8 hoffA8 hoverA8 hvalidA8 hssA8 hlsA8 hllA8 hdecA8 hinbA8 hbridgeA7
    srcOffA9 hoffA9 hoverA9 hvalidA9 hssA9 hlsA9 hllA9 hdecA9 hinbA9 hbridgeA8
    hA9 hoff0c h0c asm
    rfl rfl rfl rfl rfl rfl rfl
    hslack hvalidB

#print axioms teerEmptyAuth_free26_to_exitPack_of_applied_as_postEx_is_empty_short_abi

theorem teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
(hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hover0 : regionBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0I : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hover1 : regionBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hoverA : regionBase.toNat + srcOffA < 2 ^ 64)
    (hvalidA : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA) = true)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hoverA1 : regionBase.toNat + srcOffA1 < 2 ^ 64)
    (hvalidA1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA1) = true)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hoverA2 : regionBase.toNat + srcOffA2 < 2 ^ 64)
    (hvalidA2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA2) = true)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hoverA3 : regionBase.toNat + srcOffA3 < 2 ^ 64)
    (hvalidA3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA3) = true)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hoverA4 : regionBase.toNat + srcOffA4 < 2 ^ 64)
    (hvalidA4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA4) = true)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hoverA5 : regionBase.toNat + srcOffA5 < 2 ^ 64)
    (hvalidA5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA5) = true)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hoverA6 : regionBase.toNat + srcOffA6 < 2 ^ 64)
    (hvalidA6 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA6) = true)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hoverA7 : regionBase.toNat + srcOffA7 < 2 ^ 64)
    (hvalidA7 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA7) = true)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hoverA8 : regionBase.toNat + srcOffA8 < 2 ^ 64)
    (hvalidA8 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA8) = true)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hoverA9 : regionBase.toNat + srcOffA9 < 2 ^ 64)
    (hvalidA9 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA9) = true)
    (hssA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA9 + 1 < bs.length ∧ regionBase.toNat + (srcOffA9 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1)) = true)
    (hlsA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hllA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hoff0c : (0 : Nat) < bs.length)
    (h0c : bs[0]'hoff0c = (0xc0 : BitVec 8))
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (hs0w : s0 = loadPtr) (hs1w : s1 = lenW)
    (hs2w : s2 = balPtr) (hs3w : s3 = balLenW)
    (hs4w : chainIdW = s4)
    (hs9w :
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = s9)
    (hv24w : s8 = regionBase + BitVec.ofNat 64 srcOffV)
    (hslack : 1 + 9 ≤ bs.length)
    (hvalidB : ∀ k, k < bs.length →
      isValidByteAccess (regionBase + BitVec.ofNat 64 k) = true)
    (hret : (ret &&& ~~~(1 : Word)) = ret) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1 + 30)
      E ret teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (refund _t0Old _t1Old baiW' : Word),
          ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
              frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
              (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
              (RolledBackAddr ↦ₘ (0 : Word))) **
              teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
            stackFree spC 6) hp) := by
  intro s
  let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
  let listLen := lenW - innerVal
  let endL := (regionBase + BitVec.ofNat 64 listOff) + listLen
  let endW := endL
  let cursorV := regionBase + BitVec.ofNat 64 srcOffV
  have hrun0 :=
    teerAuthContent_applied_as_postEx_is
      ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW s0 s1 s2 s3
      s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs balBytes off len hspC hnez
      hptr hlenW hsuccess htype4 halign hbound hover hvalid0 listOff ha0
      hoffL hoverL hvalidL hlenL h_ge h_hi h_exact srcOff0 hcur0 hoff0
      hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0 srcOff1 hoff1 hover1
      hvalid1 hss1 hls1 hll1 hdec1 hinb1 srcOff2 hoff2 hover2 hvalid2 hss2
      hls2 hll2 hdec2 hinb2 srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3
      hdec3 hinb3 srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
      srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5 hbridge
      hbridge1 hbridge2 hbridge3 hbridge4 srcOffV hoffV hoverV hvalidV hssV
      hlsV hllV hdecV hinbV hbridge5 srcOffA hcurA hoffA hoverA hvalidA
      hssA hlsA hllA hdecA hinbA srcOffA1 hoffA1 hoverA1 hvalidA1 hssA1
      hlsA1 hllA1 hdecA1 hinbA1 hbridgeA srcOffA2 hoffA2 hoverA2 hvalidA2
      hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1 srcOffA3 hoffA3 hoverA3
      hvalidA3 hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2 srcOffA4 hoffA4
      hoverA4 hvalidA4 hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3 srcOffA5
      hoffA5 hoverA5 hvalidA5 hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
      srcOffA6 hoffA6 hoverA6 hvalidA6 hssA6 hlsA6 hllA6 hdecA6 hinbA6
      hbridgeA5 srcOffA7 hoffA7 hoverA7 hvalidA7 hssA7 hlsA7 hllA7 hdecA7
      hinbA7 hbridgeA6 srcOffA8 hoffA8 hoverA8 hvalidA8 hssA8 hlsA8 hllA8
      hdecA8 hinbA8 hbridgeA7 srcOffA9 hoffA9 hoverA9 hvalidA9 hssA9 hlsA9
      hllA9 hdecA9 hinbA9 hbridgeA8
  have hrun : cpsTripleWithin nFrontToAtListCount E AtListCount teerLinkedCount
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
        (.x27 ↦ᵣ s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (teerAuthContentAppliedPostExIs spVal spC loadPtr lenW balPtr balLenW chainIdW
        s7 cursorV endW s11 s innerVal endL regionBase bs balBytes 0) := by
    simpa [hA9, s, innerVal, listLen, endL, endW, cursorV] using hrun0
  exact teerEmptyAuth_free26_toRet_of_hrun_empty_short_decode_is
    ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s bs balBytes hspC
    innerVal endL endW cursorV hoff0c h0c asm
    hs0w hs1w hs2w hs3w
    (by rfl) (by rfl) (by rfl) (by rfl)
    (by simpa [s] using hs4w)
    (by simpa [s, endW, endL, listLen, innerVal] using hs9w)
    (by rfl)
    (by simpa [cursorV] using hv24w)
    (by simpa using halign) hslack (by simpa using hover) hvalidB
    hret (by rfl : s.ra = ret)
    hrun

#print axioms teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short

/-- ABI-pinned specialization of of_applied: s0=loadPtr, s1=lenW, s2=balPtr, s3=balLenW,
    s4=chainIdW, s8=cursorV, s9=endW — wire hyps discharge by rfl.
    Residual: empty-short domain (0xc0/slack/valid) + walk guards + list_count asm. -/

theorem teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_zero
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
(hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hover0 : regionBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0I : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hover1 : regionBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hoverA : regionBase.toNat + srcOffA < 2 ^ 64)
    (hvalidA : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA) = true)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hoverA1 : regionBase.toNat + srcOffA1 < 2 ^ 64)
    (hvalidA1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA1) = true)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hoverA2 : regionBase.toNat + srcOffA2 < 2 ^ 64)
    (hvalidA2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA2) = true)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hoverA3 : regionBase.toNat + srcOffA3 < 2 ^ 64)
    (hvalidA3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA3) = true)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hoverA4 : regionBase.toNat + srcOffA4 < 2 ^ 64)
    (hvalidA4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA4) = true)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hoverA5 : regionBase.toNat + srcOffA5 < 2 ^ 64)
    (hvalidA5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA5) = true)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hoverA6 : regionBase.toNat + srcOffA6 < 2 ^ 64)
    (hvalidA6 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA6) = true)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hoverA7 : regionBase.toNat + srcOffA7 < 2 ^ 64)
    (hvalidA7 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA7) = true)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hoverA8 : regionBase.toNat + srcOffA8 < 2 ^ 64)
    (hvalidA8 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA8) = true)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hoverA9 : regionBase.toNat + srcOffA9 < 2 ^ 64)
    (hvalidA9 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA9) = true)
    (hssA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA9 + 1 < bs.length ∧ regionBase.toNat + (srcOffA9 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1)) = true)
    (hlsA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hllA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hoff0c : (0 : Nat) < bs.length)
    (h0c : bs[0]'hoff0c = (0xc0 : BitVec 8))
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (hs0w : s0 = loadPtr) (hs1w : s1 = lenW)
    (hs2w : s2 = balPtr) (hs3w : s3 = balLenW)
    (hs4w : chainIdW = s4)
    (hs9w :
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = s9)
    (hv24w : s8 = regionBase + BitVec.ofNat 64 srcOffV)
    (hslack : 1 + 9 ≤ bs.length)
    (hvalidB : ∀ k, k < bs.length →
      isValidByteAccess (regionBase + BitVec.ofNat 64 k) = true)
    (hret : (ret &&& ~~~(1 : Word)) = ret) :
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1 + 30)
      E ret teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (_refund _baiW' : Word),
          (((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              stackFree spVal nTeerStackDwords **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
              (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
              (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
              (.x27 ↦ᵣ s.s11) **
              (.x10 ↦ᵣ (0 : Word)) **
              regOwn .x11 **
              bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
              teerScratchOwn **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
              regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
              regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) **
            stackFree spC 6) hp) := by
  intro s
  let innerVal := (teerTxTypeDispatch (txSlice bs off len)).2.2
  let listLen := lenW - innerVal
  let endL := (regionBase + BitVec.ofNat 64 listOff) + listLen
  let endW := endL
  let cursorV := regionBase + BitVec.ofNat 64 srcOffV
  have hrun0 :=
    teerAuthContent_applied_as_postEx_is
      ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW s0 s1 s2 s3
      s4 s5 s6 s7 s8 s9 s10 s11 regionBase bs balBytes off len hspC hnez
      hptr hlenW hsuccess htype4 halign hbound hover hvalid0 listOff ha0
      hoffL hoverL hvalidL hlenL h_ge h_hi h_exact srcOff0 hcur0 hoff0
      hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0 srcOff1 hoff1 hover1
      hvalid1 hss1 hls1 hll1 hdec1 hinb1 srcOff2 hoff2 hover2 hvalid2 hss2
      hls2 hll2 hdec2 hinb2 srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3
      hdec3 hinb3 srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
      srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5 hbridge
      hbridge1 hbridge2 hbridge3 hbridge4 srcOffV hoffV hoverV hvalidV hssV
      hlsV hllV hdecV hinbV hbridge5 srcOffA hcurA hoffA hoverA hvalidA
      hssA hlsA hllA hdecA hinbA srcOffA1 hoffA1 hoverA1 hvalidA1 hssA1
      hlsA1 hllA1 hdecA1 hinbA1 hbridgeA srcOffA2 hoffA2 hoverA2 hvalidA2
      hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1 srcOffA3 hoffA3 hoverA3
      hvalidA3 hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2 srcOffA4 hoffA4
      hoverA4 hvalidA4 hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3 srcOffA5
      hoffA5 hoverA5 hvalidA5 hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
      srcOffA6 hoffA6 hoverA6 hvalidA6 hssA6 hlsA6 hllA6 hdecA6 hinbA6
      hbridgeA5 srcOffA7 hoffA7 hoverA7 hvalidA7 hssA7 hlsA7 hllA7 hdecA7
      hinbA7 hbridgeA6 srcOffA8 hoffA8 hoverA8 hvalidA8 hssA8 hlsA8 hllA8
      hdecA8 hinbA8 hbridgeA7 srcOffA9 hoffA9 hoverA9 hvalidA9 hssA9 hlsA9
      hllA9 hdecA9 hinbA9 hbridgeA8
  have hrun : cpsTripleWithin nFrontToAtListCount E AtListCount teerLinkedCount
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nTeerStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (.x23 ↦ᵣ s7) **
        (.x24 ↦ᵣ s8) ** (.x25 ↦ᵣ s9) ** (.x26 ↦ᵣ s10) **
        (.x27 ↦ᵣ s11) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ balPtr) ** (.x13 ↦ᵣ balLenW) **
        (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        teerScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (teerAuthContentAppliedPostExIs spVal spC loadPtr lenW balPtr balLenW chainIdW
        s7 cursorV endW s11 s innerVal endL regionBase bs balBytes 0) := by
    simpa [hA9, s, innerVal, listLen, endL, endW, cursorV] using hrun0
  exact teerEmptyAuth_free26_to_applied_flat_of_hrun_empty_short_decode_is_zero
    ret spVal spC regionBase loadPtr lenW balPtr balLenW chainIdW baiW
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s bs balBytes off len
    (0 : Nat) (0 : Nat) hspC
    innerVal endL endW cursorV hoff0c h0c asm
    hs0w hs1w hs2w hs3w
    (by rfl) (by rfl) (by rfl) (by rfl)
    (by simpa [s] using hs4w)
    (by simpa [s, endW, endL, listLen, innerVal] using hs9w)
    (by rfl)
    (by simpa [cursorV] using hv24w)
    (by simpa using halign) hslack (by simpa using hover) hvalidB
    hbound hret (by rfl : s.ra = ret)
    hrun

#print axioms teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_zero

/-- ABI-pinned specialization of of_applied: s0=loadPtr, s1=lenW, s2=balPtr, s3=balLenW,
    s4=chainIdW, s8=cursorV, s9=endW — wire hyps discharge by rfl.
    Residual: empty-short domain (0xc0/slack/valid) + walk guards + list_count asm. -/

theorem teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short_abi
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s5 s6 s7 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hover0 : regionBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0I : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hover1 : regionBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hoverA : regionBase.toNat + srcOffA < 2 ^ 64)
    (hvalidA : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA) = true)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hoverA1 : regionBase.toNat + srcOffA1 < 2 ^ 64)
    (hvalidA1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA1) = true)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hoverA2 : regionBase.toNat + srcOffA2 < 2 ^ 64)
    (hvalidA2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA2) = true)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hoverA3 : regionBase.toNat + srcOffA3 < 2 ^ 64)
    (hvalidA3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA3) = true)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hoverA4 : regionBase.toNat + srcOffA4 < 2 ^ 64)
    (hvalidA4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA4) = true)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hoverA5 : regionBase.toNat + srcOffA5 < 2 ^ 64)
    (hvalidA5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA5) = true)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hoverA6 : regionBase.toNat + srcOffA6 < 2 ^ 64)
    (hvalidA6 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA6) = true)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hoverA7 : regionBase.toNat + srcOffA7 < 2 ^ 64)
    (hvalidA7 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA7) = true)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hoverA8 : regionBase.toNat + srcOffA8 < 2 ^ 64)
    (hvalidA8 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA8) = true)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hoverA9 : regionBase.toNat + srcOffA9 < 2 ^ 64)
    (hvalidA9 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA9) = true)
    (hssA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA9 + 1 < bs.length ∧ regionBase.toNat + (srcOffA9 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1)) = true)
    (hlsA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hllA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hoff0c : (0 : Nat) < bs.length)
    (h0c : bs[0]'hoff0c = (0xc0 : BitVec 8))
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (hslack : 1 + 9 ≤ bs.length)
    (hvalidB : ∀ k, k < bs.length →
      isValidByteAccess (regionBase + BitVec.ofNat 64 k) = true)
    (hret : (ret &&& ~~~(1 : Word)) = ret) :
    let s0 := loadPtr
    let s1 := lenW
    let s2 := balPtr
    let s3 := balLenW
    let s4 := chainIdW
    let s8 := regionBase + BitVec.ofNat 64 srcOffV
    let s9 :=
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1 + 30)
      E ret teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (refund _t0Old _t1Old baiW' : Word),
          ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
              frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
              (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
              (RolledBackAddr ↦ₘ (0 : Word))) **
              teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
            stackFree spC 6) hp) := by
  intro s0 s1 s2 s3 s4 s8 s9 s
  exact teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short
    ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact
    srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV hoverV hvalidV hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA hoverA hvalidA hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 hoverA1 hvalidA1 hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
    srcOffA2 hoffA2 hoverA2 hvalidA2 hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1
    srcOffA3 hoffA3 hoverA3 hvalidA3 hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2
    srcOffA4 hoffA4 hoverA4 hvalidA4 hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3
    srcOffA5 hoffA5 hoverA5 hvalidA5 hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
    srcOffA6 hoffA6 hoverA6 hvalidA6 hssA6 hlsA6 hllA6 hdecA6 hinbA6 hbridgeA5
    srcOffA7 hoffA7 hoverA7 hvalidA7 hssA7 hlsA7 hllA7 hdecA7 hinbA7 hbridgeA6
    srcOffA8 hoffA8 hoverA8 hvalidA8 hssA8 hlsA8 hllA8 hdecA8 hinbA8 hbridgeA7
    srcOffA9 hoffA9 hoverA9 hvalidA9 hssA9 hlsA9 hllA9 hdecA9 hinbA9 hbridgeA8
    hA9 hoff0c h0c asm
    rfl rfl rfl rfl rfl rfl rfl
    hslack hvalidB hret


theorem teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_zero
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s5 s6 s7 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hoverL : regionBase.toNat + listOff < 2 ^ 64)
    (hvalidL : isValidByteAccess (regionBase + BitVec.ofNat 64 listOff) = true)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hover0 : regionBase.toNat + srcOff0 < 2 ^ 64)
    (hvalid0I : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff0) = true)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hover1 : regionBase.toNat + srcOff1 < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff1) = true)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hover2 : regionBase.toNat + srcOff2 < 2 ^ 64)
    (hvalid2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff2) = true)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hover3 : regionBase.toNat + srcOff3 < 2 ^ 64)
    (hvalid3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff3) = true)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hover4 : regionBase.toNat + srcOff4 < 2 ^ 64)
    (hvalid4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff4) = true)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hover5 : regionBase.toNat + srcOff5 < 2 ^ 64)
    (hvalid5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOff5) = true)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hoverV : regionBase.toNat + srcOffV < 2 ^ 64)
    (hvalidV : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffV) = true)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hoverA : regionBase.toNat + srcOffA < 2 ^ 64)
    (hvalidA : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA) = true)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hoverA1 : regionBase.toNat + srcOffA1 < 2 ^ 64)
    (hvalidA1 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA1) = true)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hoverA2 : regionBase.toNat + srcOffA2 < 2 ^ 64)
    (hvalidA2 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA2) = true)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hoverA3 : regionBase.toNat + srcOffA3 < 2 ^ 64)
    (hvalidA3 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA3) = true)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hoverA4 : regionBase.toNat + srcOffA4 < 2 ^ 64)
    (hvalidA4 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA4) = true)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hoverA5 : regionBase.toNat + srcOffA5 < 2 ^ 64)
    (hvalidA5 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA5) = true)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hoverA6 : regionBase.toNat + srcOffA6 < 2 ^ 64)
    (hvalidA6 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA6) = true)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hoverA7 : regionBase.toNat + srcOffA7 < 2 ^ 64)
    (hvalidA7 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA7) = true)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hoverA8 : regionBase.toNat + srcOffA8 < 2 ^ 64)
    (hvalidA8 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA8) = true)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hoverA9 : regionBase.toNat + srcOffA9 < 2 ^ 64)
    (hvalidA9 : isValidByteAccess (regionBase + BitVec.ofNat 64 srcOffA9) = true)
    (hssA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA9 + 1 < bs.length ∧ regionBase.toNat + (srcOffA9 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1)) = true)
    (hlsA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hllA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hoff0c : (0 : Nat) < bs.length)
    (h0c : bs[0]'hoff0c = (0xc0 : BitVec 8))
    (asm : TeerListCountAuthLoopAssumed teerLinkedCount)
    (hslack : 1 + 9 ≤ bs.length)
    (hvalidB : ∀ k, k < bs.length →
      isValidByteAccess (regionBase + BitVec.ofNat 64 k) = true)
    (hret : (ret &&& ~~~(1 : Word)) = ret) :
    let s0 := loadPtr
    let s1 := lenW
    let s2 := balPtr
    let s3 := balLenW
    let s4 := chainIdW
    let s8 := regionBase + BitVec.ofNat 64 srcOffV
    let s9 :=
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1 + 30)
      E ret teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (_refund _baiW' : Word),
          (((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              stackFree spVal nTeerStackDwords **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
              (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
              (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
              (.x27 ↦ᵣ s.s11) **
              (.x10 ↦ᵣ (0 : Word)) **
              regOwn .x11 **
              bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
              teerScratchOwn **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
              regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
              regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) **
            stackFree spC 6) hp) := by
  intro s0 s1 s2 s3 s4 s8 s9 s
  exact teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_zero
    ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    halign hbound hover hvalid0 listOff ha0 hoffL hoverL hvalidL hlenL
    h_ge h_hi h_exact
    srcOff0 hcur0 hoff0 hover0 hvalid0I hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 hover1 hvalid1 hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 hover2 hvalid2 hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 hover3 hvalid3 hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 hover4 hvalid4 hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 hover5 hvalid5 hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV hoverV hvalidV hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA hoverA hvalidA hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 hoverA1 hvalidA1 hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
    srcOffA2 hoffA2 hoverA2 hvalidA2 hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1
    srcOffA3 hoffA3 hoverA3 hvalidA3 hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2
    srcOffA4 hoffA4 hoverA4 hvalidA4 hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3
    srcOffA5 hoffA5 hoverA5 hvalidA5 hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
    srcOffA6 hoffA6 hoverA6 hvalidA6 hssA6 hlsA6 hllA6 hdecA6 hinbA6 hbridgeA5
    srcOffA7 hoffA7 hoverA7 hvalidA7 hssA7 hlsA7 hllA7 hdecA7 hinbA7 hbridgeA6
    srcOffA8 hoffA8 hoverA8 hvalidA8 hssA8 hlsA8 hllA8 hdecA8 hinbA8 hbridgeA7
    srcOffA9 hoffA9 hoverA9 hvalidA9 hssA9 hlsA9 hllA9 hdecA9 hinbA9 hbridgeA8
    hA9 hoff0c h0c asm
    rfl rfl rfl rfl rfl rfl rfl
    hslack hvalidB hret


#print axioms teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short_abi
#print axioms teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_zero


/-! ## Thin residual packaging: hoff0 free from slack; domain-on-run bundle -/

/-- `1 + 9 ≤ bs.length` ⇒ `0 < bs.length` (empty-short slack implies non-empty). -/
theorem teer_hoff0_of_empty_short_slack
    {bs : List (BitVec 8)} (hslack : 1 + 9 ≤ bs.length) :
    (0 : Nat) < bs.length := by omega

#print axioms teer_hoff0_of_empty_short_slack

/-- On-run empty-short domain fixture (not global `∀`). Residual: caller fixture. -/
structure TeerEmptyAuthDomainEmptyShortRun
    (regionBase : Word) (bs : List (BitVec 8)) : Prop where
  halign : regionBase.toNat % 8 = 0
  hslack : 1 + 9 ≤ bs.length
  hover : regionBase.toNat + bs.length < 2 ^ 64
  hvalid : ∀ k, k < bs.length →
    isValidByteAccess (regionBase + BitVec.ofNat 64 k) = true
  h0 : bs[0]'(teer_hoff0_of_empty_short_slack hslack) = (0xc0 : BitVec 8)

/-- Unpack domain-on-run into separate hyps. -/
theorem TeerEmptyAuthDomainEmptyShortRun.to_hyps
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs) :
    regionBase.toNat % 8 = 0 ∧
      1 + 9 ≤ bs.length ∧
      regionBase.toNat + bs.length < 2 ^ 64 ∧
      (∀ k, k < bs.length →
        isValidByteAccess (regionBase + BitVec.ofNat 64 k) = true) ∧
      (0 : Nat) < bs.length ∧
      bs[0]'(teer_hoff0_of_empty_short_slack dom.hslack) = (0xc0 : BitVec 8) :=
  ⟨dom.halign, dom.hslack, dom.hover, dom.hvalid,
    teer_hoff0_of_empty_short_slack dom.hslack, dom.h0⟩

#print axioms TeerEmptyAuthDomainEmptyShortRun.to_hyps


/-- Index in-blob ⇒ valid byte access from domain. -/
theorem teer_hvalid_of_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    {k : Nat} (hk : k < bs.length) :
    isValidByteAccess (regionBase + BitVec.ofNat 64 k) = true :=
  dom.hvalid k hk

/-- Index in-blob ⇒ regionBase + k fits in 64 bits from domain span. -/
theorem teer_hover_of_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    {k : Nat} (hk : k < bs.length) :
    regionBase.toNat + k < 2 ^ 64 := by
  have hlen := Nat.le_of_lt hk
  have hover := dom.hover
  omega

#print axioms teer_hvalid_of_dom
#print axioms teer_hover_of_dom


/-- Empty take ⇒ empty slice. -/
theorem teer_txSlice_zero (bs : List (BitVec 8)) (off : Nat) :
    txSlice bs off 0 = [] := by
  simp only [txSlice, List.take_zero]

/-- teer success status 0 ⇒ nonempty slice length. -/
theorem teer_success_len_pos
    {bs : List (BitVec 8)} {off len : Nat}
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word)) :
    0 < len := by
  by_contra h
  have h0 : len = 0 := Nat.eq_zero_of_not_pos h
  subst h0
  have hs := teer_txSlice_zero bs off
  rw [hs] at hsuccess
  simp only [teerTxTypeDispatch] at hsuccess
  exact absurd hsuccess (by decide)

/-- teer success + bound ⇒ off in-blob (frees hoffOff). -/
theorem teer_hoffOff_of_success_bound
    {bs : List (BitVec 8)} {off len : Nat}
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (hbound : off + len ≤ bs.length) :
    off < bs.length := by
  have hpos := teer_success_len_pos hsuccess
  omega

#print axioms teer_success_len_pos
#print axioms teer_hoffOff_of_success_bound


/-! ## Per-guard free lemmas (coord: decompose walk package, not one block) -/

/-- `signExtend12 1 = ofNat 1`. -/
theorem teer_se12_one : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := by decide

#print axioms teer_se12_one

/-- Short-list first-item cursor: `listBase + 1 = regionBase + (listOff + 1)`.
    Via `loadPtr_add_rel_eq` with `rel = 1`. -/
theorem teer_hcur_of_srcOff_succ
    (regionBase : Word) (listOff srcOff : Nat)
    (hsrc : srcOff = listOff + 1)
    (hover : regionBase.toNat + listOff + 1 < 2 ^ 64) :
    (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff := by
  subst hsrc
  have hse : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := teer_se12_one
  rw [hse]
  exact loadPtr_add_rel_eq regionBase (regionBase + BitVec.ofNat 64 listOff) listOff 1
    rfl hover

#print axioms teer_hcur_of_srcOff_succ

/-- Single-byte head (`ult 0x80`) ⇒ short-string room hyp vacuous. -/
theorem teer_hss_vacuous_of_ult_80
    {bs : List (BitVec 8)} {srcOff : Nat} (hoff : srcOff < bs.length)
    (h : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    {P : Prop} :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true → P) :=
  fun hne _ => absurd h hne

/-- Short-string-or-single head (`ult 0xb8`) ⇒ long-string room hyp vacuous. -/
theorem teer_hls_vacuous_of_ult_b8
    {bs : List (BitVec 8)} {srcOff : Nat} (hoff : srcOff < bs.length)
    (h : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    {P : Prop} :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → P) :=
  fun hne _ => absurd h hne

/-- Not-long-list head (`ult 0xf8`) ⇒ long-list room hyp vacuous. -/
theorem teer_hll_vacuous_of_ult_f8
    {bs : List (BitVec 8)} {srcOff : Nat} (hoff : srcOff < bs.length)
    (h : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    {P : Prop} :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → P) :=
  fun hne => absurd h hne

#print axioms teer_hss_vacuous_of_ult_80
#print axioms teer_hls_vacuous_of_ult_b8
#print axioms teer_hll_vacuous_of_ult_f8

/-- Concrete `0xc0` head ⇒ short-list walk_init `h_ge` (`¬ult 0xc0`). -/
theorem teer_h_ge_of_byte_c0
    {bs : List (BitVec 8)} {listOff : Nat} (hoff : listOff < bs.length)
    (h0 : bs[listOff]'hoff = (0xc0 : BitVec 8)) :
    ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
  intro h
  rw [h0] at h
  exact absurd h (by decide)

/-- Concrete `0xc0` head ⇒ short-list walk_init `h_hi` (`ult 0xf8`). -/
theorem teer_h_hi_of_byte_c0
    {bs : List (BitVec 8)} {listOff : Nat} (hoff : listOff < bs.length)
    (h0 : bs[listOff]'hoff = (0xc0 : BitVec 8)) :
    BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
  rw [h0]
  decide

#print axioms teer_h_ge_of_byte_c0
#print axioms teer_h_hi_of_byte_c0

/-- Domain `bs[0]=0xc0` + `listOff=0` ⇒ walk_init `h_ge` free. -/
theorem teer_h_ge_listOff0_of_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (listOff : Nat) (hL : listOff = 0)
    (hoffL : listOff < bs.length) :
    ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true := by
  subst hL
  exact teer_h_ge_of_byte_c0 hoffL (by
    simpa using dom.h0)

/-- Domain `bs[0]=0xc0` + `listOff=0` ⇒ walk_init `h_hi` free. -/
theorem teer_h_hi_listOff0_of_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (listOff : Nat) (hL : listOff = 0)
    (hoffL : listOff < bs.length) :
    BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true := by
  subst hL
  exact teer_h_hi_of_byte_c0 hoffL (by
    simpa using dom.h0)

#print axioms teer_h_ge_listOff0_of_dom
#print axioms teer_h_hi_listOff0_of_dom

/-- `0xc0` head + `listLenW = 1` ⇒ walk_init `h_exact` free. -/
theorem teer_h_exact_of_byte_c0_listLen1
    (regionBase : Word) (bs : List (BitVec 8)) (listOff : Nat)
    (hoff : listOff < bs.length)
    (h0 : bs[listOff]'hoff = (0xc0 : BitVec 8))
    (listLenW : Word)
    (hlen1 : listLenW = BitVec.ofNat 64 1)
    (hover : regionBase.toNat + listOff + 1 < 2 ^ 64) :
    (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) + listLenW := by
  -- Reduce head byte to 0xc0, length to 1, se12 to ofNat 1.
  simp only [h0, hlen1, teer_se12_one]
  have hzext : BitVec.zeroExtend 64 (0xc0 : BitVec 8) = BitVec.ofNat 64 0xc0 := by decide
  have hz : BitVec.ofNat 64 0xc0 - BitVec.ofNat 64 0xc0 = BitVec.ofNat 64 0 := by decide
  simp only [hzext, hz, BitVec.zero_add]
  -- listBase + ofNat 1 = listBase + listLenW (listLenW = ofNat 1)
  change (regionBase + BitVec.ofNat 64 listOff) + BitVec.ofNat 64 1 =
    (regionBase + BitVec.ofNat 64 listOff) + BitVec.ofNat 64 1
  rfl

#print axioms teer_h_exact_of_byte_c0_listLen1

/-- Domain `bs[0]=0xc0` + `listOff=0` + `listLenW=1` ⇒ `h_exact` free. -/
theorem teer_h_exact_listOff0_of_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (listOff : Nat) (hL : listOff = 0)
    (hoffL : listOff < bs.length)
    (listLenW : Word) (hlen1 : listLenW = BitVec.ofNat 64 1) :
    (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) + listLenW := by
  subst hL
  have hover : regionBase.toNat + 1 < 2 ^ 64 := by
    have h := dom.hover
    have hs := dom.hslack
    omega
  exact teer_h_exact_of_byte_c0_listLen1 regionBase bs 0 hoffL
    (by simpa using dom.h0) listLenW hlen1 hover

#print axioms teer_h_exact_listOff0_of_dom

/-- `srcOff = listOff + 1` + strict bound ⇒ `hoff` free. -/
theorem teer_hoff_of_srcOff_succ
    {bs : List (BitVec 8)} (listOff srcOff : Nat)
    (hsrc : srcOff = listOff + 1)
    (hlo : listOff + 1 < bs.length) :
    srcOff < bs.length := by
  simpa [hsrc] using hlo

#print axioms teer_hoff_of_srcOff_succ



/-- Concrete `0xc0` head ⇒ all three room hyps vacuous (list short form). -/
theorem teer_hss_vacuous_of_byte_c0
    {bs : List (BitVec 8)} {srcOff : Nat} (hoff : srcOff < bs.length)
    (h0 : bs[srcOff]'hoff = (0xc0 : BitVec 8))
    {P : Prop} :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true → P) := by
  have hnb : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    intro h; rw [h0] at h; exact absurd h (by decide)
  exact fun _ h2 => absurd h2 hnb

theorem teer_hls_vacuous_of_byte_c0
    {bs : List (BitVec 8)} {srcOff : Nat} (hoff : srcOff < bs.length)
    (h0 : bs[srcOff]'hoff = (0xc0 : BitVec 8))
    {P : Prop} :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → P) := by
  have hnc : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
    intro h; rw [h0] at h; exact absurd h (by decide)
  exact fun _ h2 => absurd h2 hnc

theorem teer_hll_vacuous_of_byte_c0
    {bs : List (BitVec 8)} {srcOff : Nat} (hoff : srcOff < bs.length)
    (h0 : bs[srcOff]'hoff = (0xc0 : BitVec 8))
    {P : Prop} :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → P) :=
  teer_hll_vacuous_of_ult_f8 hoff (teer_h_hi_of_byte_c0 hoff h0)

/-- Domain `bs[0]=0xc0` + `srcOff=0` ⇒ room hyps free at offset 0. -/
theorem teer_hss_vacuous_srcOff0_of_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (srcOff : Nat) (hS : srcOff = 0) (hoff : srcOff < bs.length) {P : Prop} :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true → P) := by
  subst hS
  exact teer_hss_vacuous_of_byte_c0 hoff (by simpa using dom.h0)

theorem teer_hls_vacuous_srcOff0_of_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (srcOff : Nat) (hS : srcOff = 0) (hoff : srcOff < bs.length) {P : Prop} :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → P) := by
  subst hS
  exact teer_hls_vacuous_of_byte_c0 hoff (by simpa using dom.h0)

theorem teer_hll_vacuous_srcOff0_of_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (srcOff : Nat) (hS : srcOff = 0) (hoff : srcOff < bs.length) {P : Prop} :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → P) := by
  subst hS
  exact teer_hll_vacuous_of_byte_c0 hoff (by simpa using dom.h0)

#print axioms teer_hss_vacuous_of_byte_c0
#print axioms teer_hls_vacuous_of_byte_c0
#print axioms teer_hll_vacuous_of_byte_c0
#print axioms teer_hss_vacuous_srcOff0_of_dom
#print axioms teer_hls_vacuous_srcOff0_of_dom
#print axioms teer_hll_vacuous_srcOff0_of_dom

/-- `ret` 2-aligned packaging alias (ABI residual; free only for concrete PCs via `decide`). -/
abbrev teer_ret_aligned (ret : Word) : Prop :=
  (ret &&& ~~~(1 : Word)) = ret

theorem teer_ret_aligned_of (ret : Word)
    (h : (ret &&& ~~~(1 : Word)) = ret) : teer_ret_aligned ret := h

#print axioms teer_ret_aligned_of

/-- Concrete teer entry PC is 2-aligned (`0x8002d3b4`). -/
theorem teer_ret_aligned_E : teer_ret_aligned E := by
  decide

#print axioms teer_ret_aligned_E

/-- List-count link PC is 2-aligned (`E+680`). -/
theorem teer_ret_aligned_LinkListCount : teer_ret_aligned LinkListCount := by
  decide

#print axioms teer_ret_aligned_LinkListCount

/-- Single-byte head (`toNat < 0x80`) ⇒ all three room hyps vacuous. -/
theorem teer_room_vacuous_of_single_byte
    {bs : List (BitVec 8)} {srcOff : Nat} (hoff : srcOff < bs.length)
    (hb : (bs[srcOff]'hoff).toNat < 0x80) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) := by
  have hze : ((bs[srcOff]'hoff).zeroExtend 64).toNat = (bs[srcOff]'hoff).toNat :=
    toNat_zeroExtend_byte _
  have h80 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    have h80n : (0x80 : Word).toNat = 0x80 := by decide
    exact (BitVec.ult_iff_lt).2 (by
      have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0x80 := by rw [hze]; exact hb
      simpa [BitVec.lt_def, h80n] using this)
  have hb8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    have hb8n : (0xb8 : Word).toNat = 0xb8 := by decide
    exact (BitVec.ult_iff_lt).2 (by
      have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0xb8 := by rw [hze]; omega
      simpa [BitVec.lt_def, hb8n] using this)
  have hf8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    have hf8n : (0xf8 : Word).toNat = 0xf8 := by decide
    exact (BitVec.ult_iff_lt).2 (by
      have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0xf8 := by rw [hze]; omega
      simpa [BitVec.lt_def, hf8n] using this)
  refine ⟨teer_hss_vacuous_of_ult_80 hoff h80, teer_hls_vacuous_of_ult_b8 hoff hb8,
    teer_hll_vacuous_of_ult_f8 hoff hf8⟩

#print axioms teer_room_vacuous_of_single_byte

/-- Single-byte RLP head + `hinb` ⇒ `hdec` free (`rlpItemDecode_single_byte`). -/
theorem teer_hdec_single_byte
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : (bs[srcOff]'hoff).toNat < 0x80)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff) endPtr = true) :
    ∃ next len0 : Word,
      rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 :=
  ⟨_, _, rlpItemDecode_single_byte bs srcOff
    (regionBase + BitVec.ofNat 64 srcOff) endPtr hoff hb hinb⟩

#print axioms teer_hdec_single_byte

/-- `listOff = 0`, `listLenW = ofNat L`, `srcOff < L`, no wrap ⇒ `hinb` free. -/
theorem teer_hinb_listOff0_of_srcOff_lt
    (regionBase : Word) (srcOff L : Nat) (listLenW : Word)
    (hlen : listLenW = BitVec.ofNat 64 L)
    (hsrc : srcOff < L)
    (hnoWrap : regionBase.toNat + L < 2 ^ 64) :
    BitVec.ult (regionBase + BitVec.ofNat 64 srcOff)
      ((regionBase + BitVec.ofNat 64 0) + listLenW) = true := by
  subst hlen
  have h0 : regionBase + BitVec.ofNat 64 0 = regionBase := by
    change regionBase + (0 : Word) = regionBase
    exact BitVec.add_zero regionBase
  rw [h0]
  have hcur : (regionBase + BitVec.ofNat 64 srcOff).toNat = regionBase.toNat + srcOff := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hs64 : srcOff < 2 ^ 64 := by omega
    have hsum : regionBase.toNat + srcOff < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hs64, Nat.mod_eq_of_lt hsum]
  have hend : (regionBase + BitVec.ofNat 64 L).toNat = regionBase.toNat + L := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hL64 : L < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hL64, Nat.mod_eq_of_lt hnoWrap]
  have hlt : regionBase.toNat + srcOff < regionBase.toNat + L := by omega
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq, hcur, hend]
  exact hlt

#print axioms teer_hinb_listOff0_of_srcOff_lt

/-- Domain hover + `listLenW = ofNat L` with `L ≤ bs.length` ⇒ no-wrap for hinb. -/
theorem teer_hinb_listOff0_of_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (srcOff L : Nat) (listLenW : Word)
    (hlen : listLenW = BitVec.ofNat 64 L)
    (hsrc : srcOff < L)
    (hLle : L ≤ bs.length) :
    BitVec.ult (regionBase + BitVec.ofNat 64 srcOff)
      ((regionBase + BitVec.ofNat 64 0) + listLenW) = true := by
  have hnoWrap : regionBase.toNat + L < 2 ^ 64 := by
    have h := dom.hover; omega
  exact teer_hinb_listOff0_of_srcOff_lt regionBase srcOff L listLenW hlen hsrc hnoWrap

#print axioms teer_hinb_listOff0_of_dom

/-- Single-byte decode ⇒ bridge `next = regionBase + ofNat (srcOff+1)`. -/
theorem teer_hbridge_single_byte
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr next len0 : Word)
    (hoff : srcOff < bs.length)
    (hb : (bs[srcOff]'hoff).toNat < 0x80)
    (hdec : rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0)
    (hnoWrap : regionBase.toNat + (srcOff + 1) < 2 ^ 64) :
    next = regionBase + BitVec.ofNat 64 (srcOff + 1) := by
  have ⟨hnext, _hlen⟩ :=
    rlpItemDecode_single_byte_next bs srcOff
      (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 hoff hb hdec
  have hse : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := teer_se12_one
  -- next = (regionBase + srcOff) + 1
  have hnext' : next = (regionBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 1 := by
    simpa [hse] using hnext
  apply Eq.trans hnext'
  apply BitVec.eq_of_toNat_eq
  have hs : srcOff < 2 ^ 64 := by omega
  have hs1 : srcOff + 1 < 2 ^ 64 := by omega
  have hsum0 : regionBase.toNat + srcOff < 2 ^ 64 := by omega
  have hsum1 : regionBase.toNat + (srcOff + 1) < 2 ^ 64 := hnoWrap
  have h1mod : (1 : Nat) % 2 ^ 64 = 1 := by decide
  calc
    ((regionBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 1).toNat
        = ((regionBase + BitVec.ofNat 64 srcOff).toNat + 1) % 2 ^ 64 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, h1mod]
    _ = (regionBase.toNat + srcOff + 1) % 2 ^ 64 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
            Nat.mod_eq_of_lt hsum0]
    _ = regionBase.toNat + srcOff + 1 := by
          rw [Nat.mod_eq_of_lt (by omega : regionBase.toNat + srcOff + 1 < 2 ^ 64)]
    _ = regionBase.toNat + (srcOff + 1) := by omega
    _ = (regionBase + BitVec.ofNat 64 (srcOff + 1)).toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs1,
            Nat.mod_eq_of_lt hsum1]

#print axioms teer_hbridge_single_byte

/-- Single-byte decode exists + bridge package for packaging fill. -/
theorem teer_hdec_hbridge_single_byte
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : (bs[srcOff]'hoff).toNat < 0x80)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hnoWrap : regionBase.toNat + (srcOff + 1) < 2 ^ 64) :
    (∃ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) ∧
      (∀ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 →
          next = regionBase + BitVec.ofNat 64 (srcOff + 1)) := by
  refine ⟨teer_hdec_single_byte bs srcOff regionBase endPtr hoff hb hinb, ?_⟩
  intro next len0 hdec
  exact teer_hbridge_single_byte bs srcOff regionBase endPtr next len0 hoff hb hdec hnoWrap

#print axioms teer_hdec_hbridge_single_byte

/-- Empty short-string `0x80` + fit ⇒ `hdec` free (`rlpItemDecode_empty_short`).
    Fit shape: `ult 0 (end - cursor)`. -/
theorem teer_hdec_empty_short_string
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x80 : BitVec 8))
    (hfit : BitVec.ult (0 : Word)
      (endPtr - (regionBase + BitVec.ofNat 64 srcOff)) = true) :
    ∃ next len0 : Word,
      rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 :=
  ⟨_, _, rlpItemDecode_empty_short bs srcOff
    (regionBase + BitVec.ofNat 64 srcOff) endPtr hoff hb hfit⟩

#print axioms teer_hdec_empty_short_string

/-- Empty short-string decode ⇒ bridge `next = regionBase + ofNat (srcOff+1)`. -/
theorem teer_hbridge_empty_short_string
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr next len0 : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x80 : BitVec 8))
    (hdec : rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0)
    (hnoWrap : regionBase.toNat + (srcOff + 1) < 2 ^ 64) :
    next = regionBase + BitVec.ofNat 64 (srcOff + 1) := by
  have hnext := rlpItemDecode_pfx80_imp_next bs srcOff
    (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 hoff hb hdec
  have hse : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := teer_se12_one
  have hnext' : next = (regionBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 1 := by
    simpa [hse] using hnext
  apply Eq.trans hnext'
  apply BitVec.eq_of_toNat_eq
  have hs : srcOff < 2 ^ 64 := by omega
  have hs1 : srcOff + 1 < 2 ^ 64 := by omega
  have hsum0 : regionBase.toNat + srcOff < 2 ^ 64 := by omega
  have hsum1 : regionBase.toNat + (srcOff + 1) < 2 ^ 64 := hnoWrap
  have h1mod : (1 : Nat) % 2 ^ 64 = 1 := by decide
  calc
    ((regionBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 1).toNat
        = ((regionBase + BitVec.ofNat 64 srcOff).toNat + 1) % 2 ^ 64 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, h1mod]
    _ = (regionBase.toNat + srcOff + 1) % 2 ^ 64 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
            Nat.mod_eq_of_lt hsum0]
    _ = regionBase.toNat + srcOff + 1 := by
          rw [Nat.mod_eq_of_lt (by omega : regionBase.toNat + srcOff + 1 < 2 ^ 64)]
    _ = regionBase.toNat + (srcOff + 1) := by omega
    _ = (regionBase + BitVec.ofNat 64 (srcOff + 1)).toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs1,
            Nat.mod_eq_of_lt hsum1]

#print axioms teer_hbridge_empty_short_string

/-- `0x80` head ⇒ short-string room needs `srcOff+1` in bounds (ante true).
    Vacuous long-string/long-list rooms still free via `ult 0xb8` / `ult 0xf8`. -/
theorem teer_room_hls_hll_vacuous_of_byte_80
    {bs : List (BitVec 8)} {srcOff : Nat} (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x80 : BitVec 8)) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) := by
  have hb8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    rw [hb]; decide
  have hf8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    rw [hb]; decide
  exact ⟨teer_hls_vacuous_of_ult_b8 hoff hb8, teer_hll_vacuous_of_ult_f8 hoff hf8⟩

#print axioms teer_room_hls_hll_vacuous_of_byte_80

/-- Short-string room for `0x80`: need `srcOff+1` valid (empty content peek). -/
theorem teer_hss_room_of_byte_80
    {regionBase : Word} {bs : List (BitVec 8)} {srcOff : Nat}
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x80 : BitVec 8))
    (hoff1 : srcOff + 1 < bs.length)
    (hover1 : regionBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true) :
    ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
      BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true := by
  intro _ _
  exact ⟨hoff1, hover1, hvalid1⟩

#print axioms teer_hss_room_of_byte_80

/-- Domain slack ≥ 2 from `srcOff` ⇒ short-string room for `0x80` free. -/
theorem teer_hss_room_of_byte_80_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (srcOff : Nat) (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x80 : BitVec 8))
    (hroom : srcOff + 1 < bs.length) :
    ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
      BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true :=
  teer_hss_room_of_byte_80 hoff hb hroom
    (by have h := dom.hover; omega)
    (dom.hvalid (srcOff + 1) hroom)

#print axioms teer_hss_room_of_byte_80_dom

/-- 20-byte address short-string `0x94` + fit ⇒ `hdec` free. -/
theorem teer_hdec_addr20_short
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x94 : BitVec 8))
    (hfit : BitVec.ult (20 : Word)
      (endPtr - (regionBase + BitVec.ofNat 64 srcOff)) = true) :
    ∃ next len0 : Word,
      rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 :=
  ⟨_, _, rlpItemDecode_addr20_short bs srcOff
    (regionBase + BitVec.ofNat 64 srcOff) endPtr hoff hb hfit⟩

#print axioms teer_hdec_addr20_short

/-- `0x94` decode ⇒ bridge `next = regionBase + ofNat (srcOff+21)`. -/
theorem teer_hbridge_addr20_short
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr next len0 : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x94 : BitVec 8))
    (hdec : rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0)
    (hnoWrap : regionBase.toNat + (srcOff + 21) < 2 ^ 64) :
    next = regionBase + BitVec.ofNat 64 (srcOff + 21) := by
  have hnext := rlpItemDecode_pfx94_imp_next bs srcOff
    (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 hoff hb hdec
  have h21 : (21 : Word) = BitVec.ofNat 64 21 := rfl
  have hnext' : next =
      (regionBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 21 := by
    simpa [h21] using hnext
  apply Eq.trans hnext'
  apply BitVec.eq_of_toNat_eq
  have hs : srcOff < 2 ^ 64 := by omega
  have hs21 : srcOff + 21 < 2 ^ 64 := by omega
  have hsum0 : regionBase.toNat + srcOff < 2 ^ 64 := by omega
  have hsum21 : regionBase.toNat + (srcOff + 21) < 2 ^ 64 := hnoWrap
  have h21mod : (21 : Nat) % 2 ^ 64 = 21 := by decide
  calc
    ((regionBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 21).toNat
        = ((regionBase + BitVec.ofNat 64 srcOff).toNat + 21) % 2 ^ 64 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, h21mod]
    _ = (regionBase.toNat + srcOff + 21) % 2 ^ 64 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
            Nat.mod_eq_of_lt hsum0]
    _ = regionBase.toNat + srcOff + 21 := by
          rw [Nat.mod_eq_of_lt (by omega : regionBase.toNat + srcOff + 21 < 2 ^ 64)]
    _ = regionBase.toNat + (srcOff + 21) := by omega
    _ = (regionBase + BitVec.ofNat 64 (srcOff + 21)).toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs21,
            Nat.mod_eq_of_lt hsum21]

#print axioms teer_hbridge_addr20_short

/-- `0x94` hdec exists + bridge package. -/
theorem teer_hdec_hbridge_addr20_short
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x94 : BitVec 8))
    (hfit : BitVec.ult (20 : Word)
      (endPtr - (regionBase + BitVec.ofNat 64 srcOff)) = true)
    (hnoWrap : regionBase.toNat + (srcOff + 21) < 2 ^ 64) :
    (∃ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) ∧
      (∀ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 →
          next = regionBase + BitVec.ofNat 64 (srcOff + 21)) := by
  refine ⟨teer_hdec_addr20_short bs srcOff regionBase endPtr hoff hb hfit, ?_⟩
  intro next len0 hdec
  exact teer_hbridge_addr20_short bs srcOff regionBase endPtr next len0 hoff hb hdec hnoWrap

#print axioms teer_hdec_hbridge_addr20_short

/-- `0x94` head ⇒ long-string/long-list rooms vacuous. -/
theorem teer_room_hls_hll_vacuous_of_byte_94
    {bs : List (BitVec 8)} {srcOff : Nat} (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x94 : BitVec 8)) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) := by
  have hb8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    rw [hb]; decide
  have hf8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    rw [hb]; decide
  exact ⟨teer_hls_vacuous_of_ult_b8 hoff hb8, teer_hll_vacuous_of_ult_f8 hoff hf8⟩

#print axioms teer_room_hls_hll_vacuous_of_byte_94

/-- Short-string room for `0x94`: need `srcOff+1` valid (content peek). -/
theorem teer_hss_room_of_byte_94
    {regionBase : Word} {bs : List (BitVec 8)} {srcOff : Nat}
    (hoff : srcOff < bs.length)
    (_hb : bs[srcOff]'hoff = (0x94 : BitVec 8))
    (hoff1 : srcOff + 1 < bs.length)
    (hover1 : regionBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true) :
    ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
      BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true := by
  intro _ _
  exact ⟨hoff1, hover1, hvalid1⟩

#print axioms teer_hss_room_of_byte_94

/-- Domain + `srcOff+1 < length` ⇒ short-string room for `0x94` free. -/
theorem teer_hss_room_of_byte_94_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (srcOff : Nat) (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x94 : BitVec 8))
    (hroom : srcOff + 1 < bs.length) :
    ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
      BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true :=
  teer_hss_room_of_byte_94 hoff hb hroom
    (by have h := dom.hover; omega)
    (dom.hvalid (srcOff + 1) hroom)

#print axioms teer_hss_room_of_byte_94_dom

/-- Decode-gated: `0x94` ⇒ every decode has `len = 20`. -/
theorem teer_hlen20_of_byte_94
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr next len0 : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x94 : BitVec 8))
    (hdec : rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) :
    len0 = (20 : Word) :=
  rlpItemDecode_pfx94_imp_len20 bs srcOff
    (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 hoff hb hdec

#print axioms teer_hlen20_of_byte_94

/-- Head in short-string range `[0x80, 0xb8)` ⇒ long-string/long-list rooms vacuous. -/
theorem teer_room_hls_hll_vacuous_of_short_string
    {bs : List (BitVec 8)} {srcOff : Nat} (hoff : srcOff < bs.length)
    (_hge : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hlt : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) := by
  have hf8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    have hb8n : (0xb8 : Word).toNat = 0xb8 := by decide
    have hf8n : (0xf8 : Word).toNat = 0xf8 := by decide
    have hlt' : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0xb8 := by
      have := (BitVec.ult_iff_lt).1 hlt
      simpa [BitVec.lt_def, hb8n] using this
    exact (BitVec.ult_iff_lt).2 (by
      have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0xf8 := by omega
      simpa [BitVec.lt_def, hf8n] using this)
  exact ⟨teer_hls_vacuous_of_ult_b8 hoff hlt, teer_hll_vacuous_of_ult_f8 hoff hf8⟩

#print axioms teer_room_hls_hll_vacuous_of_short_string

/-- Short-string room: need `srcOff+1` valid (content peek / canonicity). -/
theorem teer_hss_room_of_short_string
    {regionBase : Word} {bs : List (BitVec 8)} {srcOff : Nat}
    (hoff : srcOff < bs.length)
    (hoff1 : srcOff + 1 < bs.length)
    (hover1 : regionBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true) :
    ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
      BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true := by
  intro _ _
  exact ⟨hoff1, hover1, hvalid1⟩

#print axioms teer_hss_room_of_short_string

/-- Domain + `srcOff+1 < length` ⇒ short-string hss room free. -/
theorem teer_hss_room_of_short_string_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (srcOff : Nat) (hoff : srcOff < bs.length)
    (hroom : srcOff + 1 < bs.length) :
    ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
      BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true :=
  teer_hss_room_of_short_string hoff hroom
    (by have h := dom.hover; omega)
    (dom.hvalid (srcOff + 1) hroom)

#print axioms teer_hss_room_of_short_string_dom

/-- Successful short-string decode ⇒ bridge `next = regionBase + ofNat (srcOff+1+len)`. -/
theorem teer_hbridge_short_string
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr next len0 : Word)
    (hoff : srcOff < bs.length)
    (hge : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (hlt : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (hdec : rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0)
    (hspan : regionBase.toNat + srcOff + 1 + len0.toNat < 2 ^ 64) :
    next = regionBase + BitVec.ofNat 64 (srcOff + 1 + len0.toNat) := by
  have hover : regionBase.toNat + srcOff < 2 ^ 64 := by omega
  have hb : ∃ b : BitVec 8, bs[srcOff]? = some b ∧
      ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) = true ∧
      BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true := by
    refine ⟨bs[srcOff]'hoff, List.getElem?_eq_getElem hoff, ?_⟩
    constructor
    · intro h; apply hge; simpa using h
    · simpa using hlt
  exact hnext_short_string_of_decode bs regionBase srcOff endPtr next len0
    hover hdec hb hspan

#print axioms teer_hbridge_short_string

/-- Short-string head byte `b = ofNat 8 (0x80 + n)` with `n ≤ 55` ⇒ hls/hll vacuous. -/
theorem teer_room_hls_hll_vacuous_of_short_string_pfx
    {bs : List (BitVec 8)} {srcOff n : Nat} (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = BitVec.ofNat 8 (0x80 + n))
    (hn : n ≤ 55) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) := by
  have hze : ((bs[srcOff]'hoff).zeroExtend 64).toNat = 0x80 + n := by
    have hp : (BitVec.ofNat 8 (0x80 + n)).toNat = 0x80 + n := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [hb, toNat_zeroExtend_byte, hp]
  have hb8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    have hb8n : (0xb8 : Word).toNat = 0xb8 := by decide
    exact (BitVec.ult_iff_lt).2 (by
      have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0xb8 := by rw [hze]; omega
      simpa [BitVec.lt_def, hb8n] using this)
  have hf8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    have hf8n : (0xf8 : Word).toNat = 0xf8 := by decide
    exact (BitVec.ult_iff_lt).2 (by
      have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0xf8 := by rw [hze]; omega
      simpa [BitVec.lt_def, hf8n] using this)
  exact ⟨teer_hls_vacuous_of_ult_b8 hoff hb8, teer_hll_vacuous_of_ult_f8 hoff hf8⟩

#print axioms teer_room_hls_hll_vacuous_of_short_string_pfx

/-- Short-list head `0xC0+pay` (`pay ≤ 55`) ⇒ all three room hyps vacuous
    (not short-string, not long-string, not long-list). -/
theorem teer_room_vacuous_of_short_list_pfx
    {bs : List (BitVec 8)} {srcOff pay : Nat} (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = BitVec.ofNat 8 (0xC0 + pay))
    (hpay : pay ≤ 55) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) := by
  have hze : ((bs[srcOff]'hoff).zeroExtend 64).toNat = 0xC0 + pay := by
    have hp : (BitVec.ofNat 8 (0xC0 + pay)).toNat = 0xC0 + pay := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [hb, toNat_zeroExtend_byte, hp]
  have h80n : (0x80 : Word).toNat = 0x80 := by decide
  have hb8n : (0xb8 : Word).toNat = 0xb8 := by decide
  have hc0n : (0xc0 : Word).toNat = 0xc0 := by decide
  have hf8n : (0xf8 : Word).toNat = 0xf8 := by decide
  have hn80 : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    intro hult
    have := (BitVec.ult_iff_lt).1 hult
    simp only [BitVec.lt_def, hze, h80n] at this; omega
  have hnb8 : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    intro hult
    have := (BitVec.ult_iff_lt).1 hult
    simp only [BitVec.lt_def, hze, hb8n] at this; omega
  have hnc0 : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
    intro hult
    have := (BitVec.ult_iff_lt).1 hult
    simp only [BitVec.lt_def, hze, hc0n] at this; omega
  have hf8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true :=
    (BitVec.ult_iff_lt).2 (by
      have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0xf8 := by rw [hze]; omega
      simpa [BitVec.lt_def, hf8n] using this)
  refine ⟨?_, ?_, teer_hll_vacuous_of_ult_f8 hoff hf8⟩
  · intro hge hlt; exact absurd hlt hnb8
  · intro hgeB8 hltC0; exact absurd hltC0 hnc0

#print axioms teer_room_vacuous_of_short_list_pfx

/-- Short-list decode exists under fit (`rlpItemDecode_short_list`). -/
theorem teer_hdec_short_list
    (bs : List (BitVec 8)) (srcOff pay : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = BitVec.ofNat 8 (0xC0 + pay))
    (hpay : pay ≤ 55)
    (hfit : ¬ BitVec.ult (endPtr - (regionBase + BitVec.ofNat 64 srcOff))
      (BitVec.ofNat 64 pay + signExtend12 (1 : BitVec 12)) = true) :
    ∃ next len0 : Word,
      rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 :=
  ⟨_, _, rlpItemDecode_short_list bs srcOff
    (regionBase + BitVec.ofNat 64 srcOff) endPtr pay hoff hb hpay hfit⟩

#print axioms teer_hdec_short_list

private theorem teer_short_list_pfx_toNat
    {bs : List (BitVec 8)} {srcOff pay : Nat} (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = BitVec.ofNat 8 (0xC0 + pay))
    (hpay : pay ≤ 55) :
    ((bs[srcOff]'hoff).zeroExtend 64).toNat = 0xC0 + pay := by
  have hp : (BitVec.ofNat 8 (0xC0 + pay)).toNat = 0xC0 + pay := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hb, toNat_zeroExtend_byte, hp]

/-- Short-list decode ⇒ bridge `next = regionBase + ofNat (srcOff + 1 + pay)`. -/
theorem teer_hbridge_short_list
    (bs : List (BitVec 8)) (srcOff pay : Nat) (regionBase endPtr next len0 : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = BitVec.ofNat 8 (0xC0 + pay))
    (hpay : pay ≤ 55)
    (hdec : rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0)
    (hnoWrap : regionBase.toNat + (srcOff + 1 + pay) < 2 ^ 64) :
    next = regionBase + BitVec.ofNat 64 (srcOff + 1 + pay) := by
  obtain ⟨b, hb?, hforms⟩ := hdec
  have heq : b = bs[srcOff]'hoff := by
    have hget : bs[srcOff]? = some (bs[srcOff]'hoff) := List.getElem?_eq_getElem hoff
    rw [hget] at hb?
    exact Option.some.inj hb?.symm
  subst heq
  have hze := teer_short_list_pfx_toNat hoff hb hpay
  have h80n : (0x80 : Word).toNat = 0x80 := by decide
  have hc0n : (0xc0 : Word).toNat = 0xc0 := by decide
  have hf8n : (0xf8 : Word).toNat = 0xf8 := by decide
  have hb8n : (0xb8 : Word).toNat = 0xb8 := by decide
  rcases hforms with h1 | h2 | h3 | h4 | h5
  · -- single-byte: ult 0x80
    have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0x80 := by
      have := (BitVec.ult_iff_lt).1 h1.1
      simpa [BitVec.lt_def, h80n] using this
    omega
  · -- short-string: ult 0xb8
    have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0xb8 := by
      have := (BitVec.ult_iff_lt).1 h2.2.1
      simpa [BitVec.lt_def, hb8n] using this
    omega
  · -- long-string: ult 0xc0
    have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0xc0 := by
      have := (BitVec.ult_iff_lt).1 h3.2.1
      simpa [BitVec.lt_def, hc0n] using this
    omega
  · -- short-list arm
    have hnext : next =
        (regionBase + BitVec.ofNat 64 srcOff) +
          (((bs[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
            signExtend12 (1 : BitVec 12)) := h4.2.2.2.1
    have hsub : (bs[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word) =
        BitVec.ofNat 64 pay := by
      apply BitVec.eq_of_toNat_eq
      have hle : 0xc0 ≤ ((bs[srcOff]'hoff).zeroExtend 64).toNat := by rw [hze]; omega
      rw [BitVec.toNat_sub_of_le hle, hze, hc0n]
      change 0xc0 + pay - 0xc0 = (BitVec.ofNat 64 pay).toNat
      have hsimp : 0xc0 + pay - 0xc0 = pay := by omega
      rw [hsimp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pay < 2 ^ 64)]
    have hse : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := teer_se12_one
    have hspanW :
        ((bs[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
            signExtend12 (1 : BitVec 12) =
          BitVec.ofNat 64 (pay + 1) := by
      rw [hsub, hse]
      apply BitVec.eq_of_toNat_eq
      have hp : pay < 2 ^ 64 := by omega
      have hp1 : pay + 1 < 2 ^ 64 := by omega
      have h1mod : (1 : Nat) % 2 ^ 64 = 1 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hp, h1mod, Nat.mod_eq_of_lt hp1]
    have hnext' : next =
        (regionBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 (pay + 1) :=
      calc next
          = (regionBase + BitVec.ofNat 64 srcOff) +
              (((bs[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
                signExtend12 (1 : BitVec 12)) := hnext
        _ = (regionBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 (pay + 1) := by
              rw [hspanW]
    have hbase :
        (regionBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 (pay + 1) =
          regionBase + BitVec.ofNat 64 (srcOff + 1 + pay) := by
      apply BitVec.eq_of_toNat_eq
      have hs : srcOff < 2 ^ 64 := by omega
      have htot : srcOff + 1 + pay < 2 ^ 64 := by omega
      have hsum0 : regionBase.toNat + srcOff < 2 ^ 64 := by omega
      have hp1 : pay + 1 < 2 ^ 64 := by omega
      have hL :
          ((regionBase + BitVec.ofNat 64 srcOff) + BitVec.ofNat 64 (pay + 1)).toNat =
            regionBase.toNat + srcOff + (pay + 1) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp1]
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hsum0]
        rw [Nat.mod_eq_of_lt (by omega : regionBase.toNat + srcOff + (pay + 1) < 2 ^ 64)]
      have hR :
          (regionBase + BitVec.ofNat 64 (srcOff + 1 + pay)).toNat =
            regionBase.toNat + (srcOff + 1 + pay) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htot,
          Nat.mod_eq_of_lt hnoWrap]
      rw [hL, hR]; omega
    exact hnext'.trans hbase
  · -- long-list: ¬ult 0xf8 but head < 0xf8
    have hf8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true :=
      (BitVec.ult_iff_lt).2 (by
        have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0xf8 := by rw [hze]; omega
        simpa [BitVec.lt_def, hf8n] using this)
    exact absurd hf8 h5.1

#print axioms teer_hbridge_short_list

/-- Short-list hdec exists + bridge package. -/
theorem teer_hdec_hbridge_short_list
    (bs : List (BitVec 8)) (srcOff pay : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = BitVec.ofNat 8 (0xC0 + pay))
    (hpay : pay ≤ 55)
    (hfit : ¬ BitVec.ult (endPtr - (regionBase + BitVec.ofNat 64 srcOff))
      (BitVec.ofNat 64 pay + signExtend12 (1 : BitVec 12)) = true)
    (hnoWrap : regionBase.toNat + (srcOff + 1 + pay) < 2 ^ 64) :
    (∃ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) ∧
      (∀ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 →
          next = regionBase + BitVec.ofNat 64 (srcOff + 1 + pay)) := by
  refine ⟨teer_hdec_short_list bs srcOff pay regionBase endPtr hoff hb hpay hfit, ?_⟩
  intro next len0 hdec
  exact teer_hbridge_short_list bs srcOff pay regionBase endPtr next len0
    hoff hb hpay hdec hnoWrap

#print axioms teer_hdec_hbridge_short_list


/-- Empty-string field package (`0x80`): hls/hll vacuous + hss room + hdec + bridge.
    Residual thins to head byte + room/fit/hinb bounds. -/
theorem teer_field_package_empty_string
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x80 : BitVec 8))
    (hoff1 : srcOff + 1 < bs.length)
    (hover1 : regionBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hfit : BitVec.ult (0 : Word)
      (endPtr - (regionBase + BitVec.ofNat 64 srcOff)) = true) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
          srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
            isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) ∧
    (∃ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) ∧
    (∀ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 →
          next = regionBase + BitVec.ofNat 64 (srcOff + 1)) := by
  have hss := teer_hss_room_of_byte_80 hoff hb hoff1 hover1 hvalid1
  have ⟨hls, hll⟩ := teer_room_hls_hll_vacuous_of_byte_80 hoff hb
  refine ⟨hss, hls, hll, teer_hdec_empty_short_string bs srcOff regionBase endPtr hoff hb hfit, ?_⟩
  intro next len0 hdec
  exact teer_hbridge_empty_short_string bs srcOff regionBase endPtr next len0
    hoff hb hdec hover1

#print axioms teer_field_package_empty_string

/-- Addr20 field package (`0x94`): hls/hll vacuous + hss room + hdec + bridge next+21.
    Residual thins to head byte + room/fit bounds. -/
theorem teer_field_package_addr20
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x94 : BitVec 8))
    (hoff1 : srcOff + 1 < bs.length)
    (hover1 : regionBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hover21 : regionBase.toNat + (srcOff + 21) < 2 ^ 64)
    (hfit : BitVec.ult (20 : Word)
      (endPtr - (regionBase + BitVec.ofNat 64 srcOff)) = true) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
          srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
            isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) ∧
    (∃ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) ∧
    (∀ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 →
          next = regionBase + BitVec.ofNat 64 (srcOff + 21)) := by
  have hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
      BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true := by
    intro _ _
    exact ⟨hoff1, hover1, hvalid1⟩
  have hb8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    rw [hb]; decide
  have hf8 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    rw [hb]; decide
  refine ⟨hss, teer_hls_vacuous_of_ult_b8 hoff hb8, teer_hll_vacuous_of_ult_f8 hoff hf8,
    teer_hdec_addr20_short bs srcOff regionBase endPtr hoff hb hfit, ?_⟩
  intro next len0 hdec
  exact teer_hbridge_addr20_short bs srcOff regionBase endPtr next len0
    hoff hb hdec hover21

#print axioms teer_field_package_addr20

/-- Single-byte field package (`b < 0x80`): all rooms vacuous + hdec + bridge. -/
theorem teer_field_package_single_byte
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : (bs[srcOff]'hoff).toNat < 0x80)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hnoWrap : regionBase.toNat + (srcOff + 1) < 2 ^ 64) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
          srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
            isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) ∧
    (∃ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) ∧
    (∀ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 →
          next = regionBase + BitVec.ofNat 64 (srcOff + 1)) := by
  have ⟨hssV, hls, hll⟩ := teer_room_vacuous_of_single_byte hoff hb
  -- strengthen vacuous hss (→ True) to the packaging room shape via absurd ante
  have hze : ((bs[srcOff]'hoff).zeroExtend 64).toNat = (bs[srcOff]'hoff).toNat :=
    toNat_zeroExtend_byte _
  have h80 : BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    have h80n : (0x80 : Word).toNat = 0x80 := by decide
    exact (BitVec.ult_iff_lt).2 (by
      have : ((bs[srcOff]'hoff).zeroExtend 64).toNat < 0x80 := by rw [hze]; exact hb
      simpa [BitVec.lt_def, h80n] using this)
  have hss :
      ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
          srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
            isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true := by
    intro hne _
    exact (hne h80).elim
  refine ⟨hss, hls, hll, ?_⟩
  exact teer_hdec_hbridge_single_byte bs srcOff regionBase endPtr hoff hb hinb hnoWrap

#print axioms teer_field_package_single_byte


/-- `hinb` (`cursor < end`) ⇒ empty-string fit `ult 0 (end - cursor)`. -/
theorem teer_hfit_empty_of_hinb
    (cursor endPtr : Word)
    (hinb : BitVec.ult cursor endPtr = true) :
    BitVec.ult (0 : Word) (endPtr - cursor) = true := by
  have hlt : cursor.toNat < endPtr.toNat := (BitVec.ult_iff_lt).1 hinb
  have hle : cursor.toNat ≤ endPtr.toNat := Nat.le_of_lt hlt
  have h0n : (0 : Word).toNat = 0 := by decide
  exact (BitVec.ult_iff_lt).2 (by
    have hsub : (endPtr - cursor).toNat = endPtr.toNat - cursor.toNat :=
      BitVec.toNat_sub_of_le hle
    simp only [BitVec.lt_def, h0n, hsub]
    omega)

#print axioms teer_hfit_empty_of_hinb

/-- Empty-string package with `hfit` free from `hinb`. -/
theorem teer_field_package_empty_string_of_hinb
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x80 : BitVec 8))
    (hoff1 : srcOff + 1 < bs.length)
    (hover1 : regionBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hinb : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff) endPtr = true) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
          srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
            isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) ∧
    (∃ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) ∧
    (∀ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 →
          next = regionBase + BitVec.ofNat 64 (srcOff + 1)) :=
  teer_field_package_empty_string bs srcOff regionBase endPtr hoff hb
    hoff1 hover1 hvalid1
    (teer_hfit_empty_of_hinb (regionBase + BitVec.ofNat 64 srcOff) endPtr hinb)

#print axioms teer_field_package_empty_string_of_hinb

/-- Short-list field package (`0xC0+pay`): rooms vacuous + hdec + bridge.
    Residual: head/pay + fit + noWrap. -/
theorem teer_field_package_short_list
    (bs : List (BitVec 8)) (srcOff pay : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = BitVec.ofNat 8 (0xC0 + pay))
    (hpay : pay ≤ 55)
    (hfit : ¬ BitVec.ult (endPtr - (regionBase + BitVec.ofNat 64 srcOff))
      (BitVec.ofNat 64 pay + signExtend12 (1 : BitVec 12)) = true)
    (hnoWrap : regionBase.toNat + (srcOff + 1 + pay) < 2 ^ 64) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) ∧
    (∃ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) ∧
    (∀ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 →
          next = regionBase + BitVec.ofNat 64 (srcOff + 1 + pay)) := by
  have ⟨hss, hls, hll⟩ := teer_room_vacuous_of_short_list_pfx hoff hb hpay
  refine ⟨hss, hls, hll,
    teer_hdec_short_list bs srcOff pay regionBase endPtr hoff hb hpay hfit, ?_⟩
  intro next len0 hdec
  exact teer_hbridge_short_list bs srcOff pay regionBase endPtr next len0
    hoff hb hpay hdec hnoWrap

#print axioms teer_field_package_short_list


/-- General fit: `n < end - cursor` in `toNat` (no wrap). -/
theorem teer_hfit_of_toNat
    (cursor endPtr : Word) (n : Nat)
    (hle : cursor.toNat ≤ endPtr.toNat)
    (hn : n < endPtr.toNat - cursor.toNat)
    (hn64 : n < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 n) (endPtr - cursor) = true := by
  have hsub : (endPtr - cursor).toNat = endPtr.toNat - cursor.toNat :=
    BitVec.toNat_sub_of_le hle
  exact (BitVec.ult_iff_lt).2 (by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, hsub]
    exact hn)

#print axioms teer_hfit_of_toNat

/-- Addr20 fit free when `cursor.toNat + 21 ≤ endPtr.toNat`. -/
theorem teer_hfit_addr20_of_span
    (cursor endPtr : Word)
    (hle : cursor.toNat ≤ endPtr.toNat)
    (hspan : cursor.toNat + 21 ≤ endPtr.toNat) :
    BitVec.ult (20 : Word) (endPtr - cursor) = true := by
  have hn : (20 : Nat) < endPtr.toNat - cursor.toNat := by omega
  have h20 : (20 : Word) = BitVec.ofNat 64 20 := rfl
  simpa [h20] using teer_hfit_of_toNat cursor endPtr 20 hle hn (by decide)

#print axioms teer_hfit_addr20_of_span

/-- Addr20 field package with fit free from span. -/
theorem teer_field_package_addr20_of_span
    (bs : List (BitVec 8)) (srcOff : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = (0x94 : BitVec 8))
    (hoff1 : srcOff + 1 < bs.length)
    (hover1 : regionBase.toNat + (srcOff + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hover21 : regionBase.toNat + (srcOff + 21) < 2 ^ 64)
    (hle : (regionBase + BitVec.ofNat 64 srcOff).toNat ≤ endPtr.toNat)
    (hspan : (regionBase + BitVec.ofNat 64 srcOff).toNat + 21 ≤ endPtr.toNat) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
          srcOff + 1 < bs.length ∧ regionBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
            isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff + 1)) = true) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) ∧
    (∃ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) ∧
    (∀ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 →
          next = regionBase + BitVec.ofNat 64 (srcOff + 21)) :=
  teer_field_package_addr20 bs srcOff regionBase endPtr hoff hb
    hoff1 hover1 hvalid1 hover21
    (teer_hfit_addr20_of_span (regionBase + BitVec.ofNat 64 srcOff) endPtr hle hspan)

#print axioms teer_field_package_addr20_of_span

/-- Short-list fit free when `cursor.toNat + (pay+1) ≤ endPtr.toNat`.
    Fit shape: `¬ ult (end-cursor) (pay+1)`. -/
theorem teer_hfit_short_list_of_span
    (cursor endPtr : Word) (pay : Nat)
    (hle : cursor.toNat ≤ endPtr.toNat)
    (hspan : cursor.toNat + (pay + 1) ≤ endPtr.toNat)
    (hpay : pay ≤ 55) :
    ¬ BitVec.ult (endPtr - cursor)
      (BitVec.ofNat 64 pay + signExtend12 (1 : BitVec 12)) = true := by
  intro hult
  have hse : signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 := teer_se12_one
  have hsum : (BitVec.ofNat 64 pay + signExtend12 (1 : BitVec 12)).toNat = pay + 1 := by
    rw [hse, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hp : pay < 2 ^ 64 := by omega
    have h1 : (1 : Nat) % 2 ^ 64 = 1 := by decide
    rw [Nat.mod_eq_of_lt hp, h1, Nat.mod_eq_of_lt (by omega : pay + 1 < 2 ^ 64)]
  have hsub : (endPtr - cursor).toNat = endPtr.toNat - cursor.toNat :=
    BitVec.toNat_sub_of_le hle
  have hlt := (BitVec.ult_iff_lt).1 hult
  simp only [BitVec.lt_def, hsub, hsum] at hlt
  omega

#print axioms teer_hfit_short_list_of_span

/-- Short-list field package with fit free from span. -/
theorem teer_field_package_short_list_of_span
    (bs : List (BitVec 8)) (srcOff pay : Nat) (regionBase endPtr : Word)
    (hoff : srcOff < bs.length)
    (hb : bs[srcOff]'hoff = BitVec.ofNat 8 (0xC0 + pay))
    (hpay : pay ≤ 55)
    (hnoWrap : regionBase.toNat + (srcOff + 1 + pay) < 2 ^ 64)
    (hle : (regionBase + BitVec.ofNat 64 srcOff).toNat ≤ endPtr.toNat)
    (hspan : (regionBase + BitVec.ofNat 64 srcOff).toNat + (pay + 1) ≤ endPtr.toNat) :
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true → True) ∧
    (¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true → True) ∧
    (∃ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0) ∧
    (∀ next len0 : Word,
        rlpItemDecode bs srcOff (regionBase + BitVec.ofNat 64 srcOff) endPtr next len0 →
          next = regionBase + BitVec.ofNat 64 (srcOff + 1 + pay)) :=
  teer_field_package_short_list bs srcOff pay regionBase endPtr hoff hb hpay
    (teer_hfit_short_list_of_span (regionBase + BitVec.ofNat 64 srcOff) endPtr pay
      hle hspan hpay)
    hnoWrap

#print axioms teer_field_package_short_list_of_span



/-- Short-list empty `0xc0` ⇒ `rlpItemDecode` with `next = cursor+1`, `len = 1`.
    Fit: at least one byte remains to `endPtr`. -/
theorem teer_rlpItemDecode_empty_list_c0
    (bytes : List (BitVec 8)) (off : Nat) (cursor endPtr : Word)
    (hoff : off < bytes.length)
    (hb : bytes[off]'hoff = (0xc0 : BitVec 8))
    (hfit : ¬ BitVec.ult (endPtr - cursor) (1 : Word) = true) :
    rlpItemDecode bytes off cursor endPtr
      (cursor + (1 : Word)) (1 : Word) := by
  refine ⟨(0xc0 : BitVec 8), ?_, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
  · rw [List.getElem?_eq_getElem hoff, hb]
  · have hge : ¬ BitVec.ult ((0xc0 : BitVec 8).zeroExtend 64) (0xc0 : Word) = true := by
      decide
    have hlt : BitVec.ult ((0xc0 : BitVec 8).zeroExtend 64) (0xf8 : Word) = true := by
      decide
    have hsub : (0xc0 : BitVec 8).zeroExtend 64 - (0xc0 : Word) = (0 : Word) := by
      decide
    have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := teer_se12_one
    refine ⟨hge, hlt, ?_, ?_, ?_⟩
    · -- fit: ¬ult (end-cursor) (0+1) = ¬ult (end-cursor) 1
      simpa [hsub, hse, BitVec.zero_add] using hfit
    · -- next: cursor + (0+1) = cursor + 1
      rw [hsub, hse, show (0 : Word) + (1 : Word) = (1 : Word) from BitVec.zero_add _]
    · -- len: 0+1 = 1
      rw [hsub, hse, show (0 : Word) + (1 : Word) = (1 : Word) from BitVec.zero_add _]

#print axioms teer_rlpItemDecode_empty_list_c0

private theorem teer_add_zero_ofNat (w : Word) :
    w + BitVec.ofNat 64 0 = w := by
  change w + (0 : Word) = w
  exact BitVec.add_zero w

private theorem teer_base_add_one_toNat (regionBase : Word)
    (hnoWrap : regionBase.toNat + 1 < 2 ^ 64) :
    (regionBase + BitVec.ofNat 64 1).toNat = regionBase.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : 1 % 2 ^ 64 = 1 := by decide
  rw [this, Nat.mod_eq_of_lt hnoWrap]

private theorem teer_add_sub_cancel_right (a b : Word) :
    (a + b) - a = b := by
  rw [BitVec.add_comm a b, BitVec.add_sub_cancel]

/-- Domain `bs[0]=0xc0` + `srcOffA9=0` + outer listLenW=1 at listOff=0
    ⇒ `hdecA9` free (empty short-list decode). -/
theorem teer_hdecA9_empty_short_listOff0
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (listOff : Nat) (hL : listOff = 0)
    (listLenW : Word) (hlen1 : listLenW = BitVec.ofNat 64 1)
    (srcOffA9 : Nat) (hA9 : srcOffA9 = 0)
    (hoffA9 : srcOffA9 < bs.length)
    (hnoWrap : regionBase.toNat + 1 < 2 ^ 64) :
    ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) + listLenW) next lenA9 := by
  subst hL; subst hA9; subst hlen1
  -- Goal becomes: ∃ n l, rlpItemDecode bs 0 (regionBase+0) ((regionBase+0)+1) n l
  refine ⟨regionBase + BitVec.ofNat 64 1, BitVec.ofNat 64 1, ?_⟩
  have hfit : ¬ BitVec.ult
      ((regionBase + BitVec.ofNat 64 1) - regionBase) (1 : Word) = true := by
    rw [teer_add_sub_cancel_right regionBase (BitVec.ofNat 64 1)]
    decide
  have hdec := teer_rlpItemDecode_empty_list_c0 bs 0 regionBase
    (regionBase + BitVec.ofNat 64 1)
    (by simpa using hoffA9) (by simpa using dom.h0) hfit
  -- Align cursor/end with lemma: regionBase+0 = regionBase, (regionBase+0)+1 = regionBase+1
  simpa [teer_add_zero_ofNat, BitVec.add_zero] using hdec

#print axioms teer_hdecA9_empty_short_listOff0

/-- `listOff=0`, `listLenW=1`, `srcOffA9=0` ⇒ `hinbA9` free (`ult base (base+1)`). -/
theorem teer_hinbA9_empty_short_listOff0
    (regionBase : Word)
    (listOff : Nat) (hL : listOff = 0)
    (listLenW : Word) (hlen1 : listLenW = BitVec.ofNat 64 1)
    (srcOffA9 : Nat) (hA9 : srcOffA9 = 0)
    (hnoWrap : regionBase.toNat + 1 < 2 ^ 64) :
    BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) + listLenW) = true := by
  subst hL; subst hA9; subst hlen1
  -- Goal: ult (regionBase+0) ((regionBase+0)+1)
  have hto := teer_base_add_one_toNat regionBase hnoWrap
  have hlt : regionBase.toNat < (regionBase + BitVec.ofNat 64 1).toNat := by
    rw [hto]; exact Nat.lt_succ_self _
  have hcur : (regionBase + BitVec.ofNat 64 0).toNat = regionBase.toNat := by
    rw [teer_add_zero_ofNat]
  have hend : ((regionBase + BitVec.ofNat 64 0) + BitVec.ofNat 64 1).toNat =
      (regionBase + BitVec.ofNat 64 1).toNat := by
    rw [teer_add_zero_ofNat]
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq, hcur, hend]
  exact hlt

#print axioms teer_hinbA9_empty_short_listOff0

/-- Domain slack + `listOff=0` + `srcOff0 = listOff+1` ⇒ `hoff0` free (`1 < length`). -/
theorem teer_hoff0_srcOff_succ_listOff0_of_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (listOff : Nat) (hL : listOff = 0)
    (srcOff0 : Nat) (hsrc0 : srcOff0 = listOff + 1) :
    srcOff0 < bs.length := by
  subst hL; subst hsrc0
  have hs := dom.hslack
  omega

#print axioms teer_hoff0_srcOff_succ_listOff0_of_dom

/-- Domain slack + `srcOffA9=0` ⇒ `hoffA9` free (`0 < length`). -/
theorem teer_hoffA9_of_zero_dom
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (srcOffA9 : Nat) (hA9 : srcOffA9 = 0) :
    srcOffA9 < bs.length := by
  subst hA9
  exact teer_hoff0_of_empty_short_slack dom.hslack

#print axioms teer_hoffA9_of_zero_dom

/-- Packaging note: `hoff0`/`hoffA9` remain binders on applied packaging because
    field-guard hyps (`hss0`, …) are dependent on the named `hoff*`. Callers
    discharge them with `teer_hoff0_srcOff_succ_listOff0_of_dom` /
    `teer_hoffA9_of_zero_dom` rather than a separate signature dual. -/
theorem teer_hoff0_hoffA9_empty_short_discharge
    {regionBase : Word} {bs : List (BitVec 8)}
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (listOff : Nat) (hL : listOff = 0)
    (srcOff0 : Nat) (hsrc0 : srcOff0 = listOff + 1)
    (srcOffA9 : Nat) (hA9 : srcOffA9 = 0) :
    srcOff0 < bs.length ∧ srcOffA9 < bs.length :=
  ⟨teer_hoff0_srcOff_succ_listOff0_of_dom dom listOff hL srcOff0 hsrc0,
    teer_hoffA9_of_zero_dom dom srcOffA9 hA9⟩

#print axioms teer_hoff0_hoffA9_empty_short_discharge



/-- Minimal empty-short fixture bytes: `0xc0` + 9 padding zeros (slack ≥ 10). -/
def teerEmptyShortFixtureBytes : List (BitVec 8) :=
  (0xc0 : BitVec 8) :: List.replicate 9 (0 : BitVec 8)

theorem teerEmptyShortFixtureBytes_length :
    teerEmptyShortFixtureBytes.length = 10 := by
  decide

theorem teerEmptyShortFixtureBytes_get0 :
    teerEmptyShortFixtureBytes[0]'(by decide : (0 : Nat) < 10) =
      (0xc0 : BitVec 8) := by
  decide

/-- Concrete domain inhabit at RAM base `0xa0000000` for the fixture. -/
theorem teerEmptyShortFixture_domain_ram0 :
    TeerEmptyAuthDomainEmptyShortRun
      (BitVec.ofNat 64 0xa0000000) teerEmptyShortFixtureBytes := by
  refine ⟨?halign, ?hslack, ?hover, ?hvalid, ?h0⟩
  · decide
  · have hl : teerEmptyShortFixtureBytes.length = 10 := teerEmptyShortFixtureBytes_length
    omega
  · decide
  · intro k hk
    have hk10 : k < 10 := by
      have hl := teerEmptyShortFixtureBytes_length; omega
    have haddr :
        (BitVec.ofNat 64 0xa0000000 + BitVec.ofNat 64 k).toNat =
          0xa0000000 + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have hk64 : k < 2 ^ 64 := by omega
      have hsum : 0xa0000000 + k < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt (by decide : 0xa0000000 < 2 ^ 64),
        Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hsum]
    -- isValidByteAccess = isValidMemAddr; left-assoc or: (MEM∨INPUT)∨RAM
    simp only [isValidByteAccess_eq, isValidMemAddr_eq, haddr,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    refine Or.inr ⟨?_, ?_⟩
    · show 0xa0000000 ≤ 0xa0000000 + k; omega
    · show 0xa0000000 + k ≤ 0xc0000000; omega
  · -- h0 needs hoff from slack; head byte
    have hlen := teerEmptyShortFixtureBytes_length
    have hoff : (0 : Nat) < teerEmptyShortFixtureBytes.length := by omega
    -- use get0; cast length proof
    simpa [hlen] using teerEmptyShortFixtureBytes_get0

#print axioms teerEmptyShortFixture_domain_ram0

theorem teerEmptyAuth_free26_to_exitPack_of_applied_as_postEx_is_empty_short_abi_dom
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s5 s6 s7 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (hbound : off + len ≤ bs.length)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hssA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA9 + 1 < bs.length ∧ regionBase.toNat + (srcOffA9 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1)) = true)
    (hlsA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hllA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0) :
    let s0 := loadPtr
    let s1 := lenW
    let s2 := balPtr
    let s3 := balLenW
    let s4 := chainIdW
    let s8 := regionBase + BitVec.ofNat 64 srcOffV
    let s9 :=
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1)
      E AfterAuthLoopLi teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun h =>
        ∃ (refund t0Old t1Old baiW' : Word),
          teerAuthLoopEmptyExitPack spVal spC s
            (teerAuthLoopEmptyWalkCur regionBase)
            (teerAuthLoopEmptyWalkEnd regionBase (BitVec.ofNat 64 1))
            refund
            (teerAuthLoopEmptyWalkCur regionBase)
            (teerAuthLoopEmptyWalkEnd regionBase (BitVec.ofNat 64 1))
            t0Old t1Old baiW'
            regionBase bs balBytes balPtr h) := by
  intro s0 s1 s2 s3 s4 s8 s9 s
  exact teerEmptyAuth_free26_to_exitPack_of_applied_as_postEx_is_empty_short_abi
    ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW
    s5 s6 s7 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    dom.halign hbound dom.hover (teer_hvalid_of_dom dom (teer_hoffOff_of_success_bound hsuccess hbound)) listOff ha0 hoffL (teer_hover_of_dom dom hoffL) (teer_hvalid_of_dom dom hoffL) hlenL
    h_ge h_hi h_exact
    srcOff0 hcur0 hoff0 (teer_hover_of_dom dom hoff0) (teer_hvalid_of_dom dom hoff0) hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 (teer_hover_of_dom dom hoff1) (teer_hvalid_of_dom dom hoff1) hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 (teer_hover_of_dom dom hoff2) (teer_hvalid_of_dom dom hoff2) hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 (teer_hover_of_dom dom hoff3) (teer_hvalid_of_dom dom hoff3) hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 (teer_hover_of_dom dom hoff4) (teer_hvalid_of_dom dom hoff4) hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 (teer_hover_of_dom dom hoff5) (teer_hvalid_of_dom dom hoff5) hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV (teer_hover_of_dom dom hoffV) (teer_hvalid_of_dom dom hoffV) hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA (teer_hover_of_dom dom hoffA) (teer_hvalid_of_dom dom hoffA) hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 (teer_hover_of_dom dom hoffA1) (teer_hvalid_of_dom dom hoffA1) hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
    srcOffA2 hoffA2 (teer_hover_of_dom dom hoffA2) (teer_hvalid_of_dom dom hoffA2) hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1
    srcOffA3 hoffA3 (teer_hover_of_dom dom hoffA3) (teer_hvalid_of_dom dom hoffA3) hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2
    srcOffA4 hoffA4 (teer_hover_of_dom dom hoffA4) (teer_hvalid_of_dom dom hoffA4) hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3
    srcOffA5 hoffA5 (teer_hover_of_dom dom hoffA5) (teer_hvalid_of_dom dom hoffA5) hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
    srcOffA6 hoffA6 (teer_hover_of_dom dom hoffA6) (teer_hvalid_of_dom dom hoffA6) hssA6 hlsA6 hllA6 hdecA6 hinbA6 hbridgeA5
    srcOffA7 hoffA7 (teer_hover_of_dom dom hoffA7) (teer_hvalid_of_dom dom hoffA7) hssA7 hlsA7 hllA7 hdecA7 hinbA7 hbridgeA6
    srcOffA8 hoffA8 (teer_hover_of_dom dom hoffA8) (teer_hvalid_of_dom dom hoffA8) hssA8 hlsA8 hllA8 hdecA8 hinbA8 hbridgeA7
    srcOffA9 hoffA9 (teer_hover_of_dom dom hoffA9) (teer_hvalid_of_dom dom hoffA9) hssA9 hlsA9 hllA9 hdecA9 hinbA9 hbridgeA8
    hA9
    (teer_hoff0_of_empty_short_slack dom.hslack) dom.h0
      teerListCountAuthLoopAssumed_teerLinked
    dom.hslack dom.hvalid

#print axioms teerEmptyAuth_free26_to_exitPack_of_applied_as_postEx_is_empty_short_abi_dom

theorem teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short_abi_dom
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s5 s6 s7 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (hbound : off + len ≤ bs.length)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hssA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA9 + 1 < bs.length ∧ regionBase.toNat + (srcOffA9 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1)) = true)
    (hlsA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hllA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hret : (ret &&& ~~~(1 : Word)) = ret) :
    let s0 := loadPtr
    let s1 := lenW
    let s2 := balPtr
    let s3 := balLenW
    let s4 := chainIdW
    let s8 := regionBase + BitVec.ofNat 64 srcOffV
    let s9 :=
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1 + 30)
      E ret teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (refund _t0Old _t1Old baiW' : Word),
          ((((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) **
              (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) **
              (.x23 ↦ᵣ s.s7) ** (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) **
              (.x26 ↦ᵣ s.s10) ** (.x27 ↦ᵣ s.s11) **
              frameSlotsSaved teerEpiFrame spC (teerSavedVals s) **
              (.x11 ↦ᵣ refund) ** (.x5 ↦ᵣ RolledBackAddr) **
              (.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
              (RegularRefundAddr ↦ₘ refund) **
              memOwn WouldbeStateAddr ** memOwn WouldbeRegularAddr **
              (RolledBackAddr ↦ₘ (0 : Word))) **
              teerEmptyAuthExitFrame baiW' spVal spC regionBase bs balBytes balPtr) **
            stackFree spC 6) hp) := by
  intro s0 s1 s2 s3 s4 s8 s9 s
  exact teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short_abi
    ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW
    s5 s6 s7 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    dom.halign hbound dom.hover (teer_hvalid_of_dom dom (teer_hoffOff_of_success_bound hsuccess hbound)) listOff ha0 hoffL (teer_hover_of_dom dom hoffL) (teer_hvalid_of_dom dom hoffL) hlenL
    h_ge h_hi h_exact
    srcOff0 hcur0 hoff0 (teer_hover_of_dom dom hoff0) (teer_hvalid_of_dom dom hoff0) hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 (teer_hover_of_dom dom hoff1) (teer_hvalid_of_dom dom hoff1) hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 (teer_hover_of_dom dom hoff2) (teer_hvalid_of_dom dom hoff2) hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 (teer_hover_of_dom dom hoff3) (teer_hvalid_of_dom dom hoff3) hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 (teer_hover_of_dom dom hoff4) (teer_hvalid_of_dom dom hoff4) hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 (teer_hover_of_dom dom hoff5) (teer_hvalid_of_dom dom hoff5) hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV (teer_hover_of_dom dom hoffV) (teer_hvalid_of_dom dom hoffV) hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA (teer_hover_of_dom dom hoffA) (teer_hvalid_of_dom dom hoffA) hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 (teer_hover_of_dom dom hoffA1) (teer_hvalid_of_dom dom hoffA1) hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
    srcOffA2 hoffA2 (teer_hover_of_dom dom hoffA2) (teer_hvalid_of_dom dom hoffA2) hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1
    srcOffA3 hoffA3 (teer_hover_of_dom dom hoffA3) (teer_hvalid_of_dom dom hoffA3) hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2
    srcOffA4 hoffA4 (teer_hover_of_dom dom hoffA4) (teer_hvalid_of_dom dom hoffA4) hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3
    srcOffA5 hoffA5 (teer_hover_of_dom dom hoffA5) (teer_hvalid_of_dom dom hoffA5) hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
    srcOffA6 hoffA6 (teer_hover_of_dom dom hoffA6) (teer_hvalid_of_dom dom hoffA6) hssA6 hlsA6 hllA6 hdecA6 hinbA6 hbridgeA5
    srcOffA7 hoffA7 (teer_hover_of_dom dom hoffA7) (teer_hvalid_of_dom dom hoffA7) hssA7 hlsA7 hllA7 hdecA7 hinbA7 hbridgeA6
    srcOffA8 hoffA8 (teer_hover_of_dom dom hoffA8) (teer_hvalid_of_dom dom hoffA8) hssA8 hlsA8 hllA8 hdecA8 hinbA8 hbridgeA7
    srcOffA9 hoffA9 (teer_hover_of_dom dom hoffA9) (teer_hvalid_of_dom dom hoffA9) hssA9 hlsA9 hllA9 hdecA9 hinbA9 hbridgeA8
    hA9
    (teer_hoff0_of_empty_short_slack dom.hslack) dom.h0
      teerListCountAuthLoopAssumed_teerLinked
    dom.hslack dom.hvalid hret


theorem teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_dom_zero
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s5 s6 s7 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (hbound : off + len ≤ bs.length)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[listOff]'hoffL).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hssA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA9 + 1 < bs.length ∧ regionBase.toNat + (srcOffA9 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1)) = true)
    (hlsA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hllA9 : ¬ BitVec.ult ((bs[srcOffA9]'hoffA9).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA9 + 1 + ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA9 + 1 +
          ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA9]'hoffA9).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA9 + 1 + k)) = true)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hret : (ret &&& ~~~(1 : Word)) = ret) :
    let s0 := loadPtr
    let s1 := lenW
    let s2 := balPtr
    let s3 := balLenW
    let s4 := chainIdW
    let s8 := regionBase + BitVec.ofNat 64 srcOffV
    let s9 :=
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1 + 30)
      E ret teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (_refund _baiW' : Word),
          (((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              stackFree spVal nTeerStackDwords **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
              (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
              (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
              (.x27 ↦ᵣ s.s11) **
              (.x10 ↦ᵣ (0 : Word)) **
              regOwn .x11 **
              bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
              teerScratchOwn **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
              regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
              regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) **
            stackFree spC 6) hp) := by
  intro s0 s1 s2 s3 s4 s8 s9 s
  exact teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_zero
    ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW
    s5 s6 s7 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    dom.halign hbound dom.hover (teer_hvalid_of_dom dom (teer_hoffOff_of_success_bound hsuccess hbound)) listOff ha0 hoffL (teer_hover_of_dom dom hoffL) (teer_hvalid_of_dom dom hoffL) hlenL
    h_ge h_hi h_exact
    srcOff0 hcur0 hoff0 (teer_hover_of_dom dom hoff0) (teer_hvalid_of_dom dom hoff0) hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 (teer_hover_of_dom dom hoff1) (teer_hvalid_of_dom dom hoff1) hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 (teer_hover_of_dom dom hoff2) (teer_hvalid_of_dom dom hoff2) hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 (teer_hover_of_dom dom hoff3) (teer_hvalid_of_dom dom hoff3) hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 (teer_hover_of_dom dom hoff4) (teer_hvalid_of_dom dom hoff4) hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 (teer_hover_of_dom dom hoff5) (teer_hvalid_of_dom dom hoff5) hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV (teer_hover_of_dom dom hoffV) (teer_hvalid_of_dom dom hoffV) hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA (teer_hover_of_dom dom hoffA) (teer_hvalid_of_dom dom hoffA) hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 (teer_hover_of_dom dom hoffA1) (teer_hvalid_of_dom dom hoffA1) hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
    srcOffA2 hoffA2 (teer_hover_of_dom dom hoffA2) (teer_hvalid_of_dom dom hoffA2) hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1
    srcOffA3 hoffA3 (teer_hover_of_dom dom hoffA3) (teer_hvalid_of_dom dom hoffA3) hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2
    srcOffA4 hoffA4 (teer_hover_of_dom dom hoffA4) (teer_hvalid_of_dom dom hoffA4) hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3
    srcOffA5 hoffA5 (teer_hover_of_dom dom hoffA5) (teer_hvalid_of_dom dom hoffA5) hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
    srcOffA6 hoffA6 (teer_hover_of_dom dom hoffA6) (teer_hvalid_of_dom dom hoffA6) hssA6 hlsA6 hllA6 hdecA6 hinbA6 hbridgeA5
    srcOffA7 hoffA7 (teer_hover_of_dom dom hoffA7) (teer_hvalid_of_dom dom hoffA7) hssA7 hlsA7 hllA7 hdecA7 hinbA7 hbridgeA6
    srcOffA8 hoffA8 (teer_hover_of_dom dom hoffA8) (teer_hvalid_of_dom dom hoffA8) hssA8 hlsA8 hllA8 hdecA8 hinbA8 hbridgeA7
    srcOffA9 hoffA9 (teer_hover_of_dom dom hoffA9) (teer_hvalid_of_dom dom hoffA9) hssA9 hlsA9 hllA9 hdecA9 hinbA9 hbridgeA8
    hA9
    (teer_hoff0_of_empty_short_slack dom.hslack) dom.h0
      teerListCountAuthLoopAssumed_teerLinked
    dom.hslack dom.hvalid hret


#print axioms teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short_abi
#print axioms teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_dom_zero


/-- `listOff = 0` + domain: free walk_init `h_ge`/`h_hi` and A9 room hyps
    (`srcOffA9 = 0` via `hA9`). Dual of `abi_dom_zero`. -/
theorem teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_dom_listOff0_zero
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s5 s6 s7 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (hbound : off + len ≤ bs.length)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hL : listOff = 0)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (h_exact : (regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoffL).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
    (srcOff0 : Nat)
    (hcur0 : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOff0)
    (hoff0 : srcOff0 < bs.length)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hret : (ret &&& ~~~(1 : Word)) = ret) :
    let s0 := loadPtr
    let s1 := lenW
    let s2 := balPtr
    let s3 := balLenW
    let s4 := chainIdW
    let s8 := regionBase + BitVec.ofNat 64 srcOffV
    let s9 :=
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1 + 30)
      E ret teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (_refund _baiW' : Word),
          (((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              stackFree spVal nTeerStackDwords **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
              (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
              (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
              (.x27 ↦ᵣ s.s11) **
              (.x10 ↦ᵣ (0 : Word)) **
              regOwn .x11 **
              bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
              teerScratchOwn **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
              regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
              regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) **
            stackFree spC 6) hp) := by
  intro s0 s1 s2 s3 s4 s8 s9 s
  exact teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_zero
    ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW
    s5 s6 s7 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    dom.halign hbound dom.hover (teer_hvalid_of_dom dom (teer_hoffOff_of_success_bound hsuccess hbound)) listOff ha0 hoffL (teer_hover_of_dom dom hoffL) (teer_hvalid_of_dom dom hoffL) hlenL
    (teer_h_ge_listOff0_of_dom dom listOff hL hoffL)
    (teer_h_hi_listOff0_of_dom dom listOff hL hoffL)
    h_exact
    srcOff0 hcur0 hoff0 (teer_hover_of_dom dom hoff0) (teer_hvalid_of_dom dom hoff0) hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 (teer_hover_of_dom dom hoff1) (teer_hvalid_of_dom dom hoff1) hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 (teer_hover_of_dom dom hoff2) (teer_hvalid_of_dom dom hoff2) hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 (teer_hover_of_dom dom hoff3) (teer_hvalid_of_dom dom hoff3) hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 (teer_hover_of_dom dom hoff4) (teer_hvalid_of_dom dom hoff4) hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 (teer_hover_of_dom dom hoff5) (teer_hvalid_of_dom dom hoff5) hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV (teer_hover_of_dom dom hoffV) (teer_hvalid_of_dom dom hoffV) hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA (teer_hover_of_dom dom hoffA) (teer_hvalid_of_dom dom hoffA) hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 (teer_hover_of_dom dom hoffA1) (teer_hvalid_of_dom dom hoffA1) hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
    srcOffA2 hoffA2 (teer_hover_of_dom dom hoffA2) (teer_hvalid_of_dom dom hoffA2) hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1
    srcOffA3 hoffA3 (teer_hover_of_dom dom hoffA3) (teer_hvalid_of_dom dom hoffA3) hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2
    srcOffA4 hoffA4 (teer_hover_of_dom dom hoffA4) (teer_hvalid_of_dom dom hoffA4) hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3
    srcOffA5 hoffA5 (teer_hover_of_dom dom hoffA5) (teer_hvalid_of_dom dom hoffA5) hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
    srcOffA6 hoffA6 (teer_hover_of_dom dom hoffA6) (teer_hvalid_of_dom dom hoffA6) hssA6 hlsA6 hllA6 hdecA6 hinbA6 hbridgeA5
    srcOffA7 hoffA7 (teer_hover_of_dom dom hoffA7) (teer_hvalid_of_dom dom hoffA7) hssA7 hlsA7 hllA7 hdecA7 hinbA7 hbridgeA6
    srcOffA8 hoffA8 (teer_hover_of_dom dom hoffA8) (teer_hvalid_of_dom dom hoffA8) hssA8 hlsA8 hllA8 hdecA8 hinbA8 hbridgeA7
    srcOffA9 hoffA9 (teer_hover_of_dom dom hoffA9) (teer_hvalid_of_dom dom hoffA9)
    (teer_hss_vacuous_srcOff0_of_dom dom srcOffA9 hA9 hoffA9)
    (teer_hls_vacuous_srcOff0_of_dom dom srcOffA9 hA9 hoffA9)
    (teer_hll_vacuous_srcOff0_of_dom dom srcOffA9 hA9 hoffA9)
    hdecA9 hinbA9 hbridgeA8
    hA9
    (teer_hoff0_of_empty_short_slack dom.hslack) dom.h0
      teerListCountAuthLoopAssumed_teerLinked
    dom.hslack dom.hvalid hret


#print axioms teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short_abi
#print axioms teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_dom_listOff0_zero

/-- `listOff=0` + `listLenW=1` + `srcOff0=listOff+1`: free h_ge/h_hi/h_exact/hcur0. -/
theorem teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_dom_listOff0_exact_zero
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s5 s6 s7 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (hbound : off + len ≤ bs.length)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hL : listOff = 0)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (hlen1 : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 = BitVec.ofNat 64 1)
    (srcOff0 : Nat)
    (hsrc0 : srcOff0 = listOff + 1)
    (hoff0 : srcOff0 < bs.length)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hdecA9 : ∃ next lenA9 : Word,
      rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA9)
    (hinbA9 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA9)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hret : (ret &&& ~~~(1 : Word)) = ret) :
    let s0 := loadPtr
    let s1 := lenW
    let s2 := balPtr
    let s3 := balLenW
    let s4 := chainIdW
    let s8 := regionBase + BitVec.ofNat 64 srcOffV
    let s9 :=
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1 + 30)
      E ret teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (_refund _baiW' : Word),
          (((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              stackFree spVal nTeerStackDwords **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
              (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
              (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
              (.x27 ↦ᵣ s.s11) **
              (.x10 ↦ᵣ (0 : Word)) **
              regOwn .x11 **
              bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
              teerScratchOwn **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
              regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
              regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) **
            stackFree spC 6) hp) := by
  intro s0 s1 s2 s3 s4 s8 s9 s
  exact teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_zero
    ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW
    s5 s6 s7 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    dom.halign hbound dom.hover (teer_hvalid_of_dom dom (teer_hoffOff_of_success_bound hsuccess hbound)) listOff ha0 hoffL (teer_hover_of_dom dom hoffL) (teer_hvalid_of_dom dom hoffL) hlenL
    (teer_h_ge_listOff0_of_dom dom listOff hL hoffL)
    (teer_h_hi_listOff0_of_dom dom listOff hL hoffL)
    (teer_h_exact_listOff0_of_dom dom listOff hL hoffL
      (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) hlen1)
    srcOff0
    (teer_hcur_of_srcOff_succ regionBase listOff srcOff0 hsrc0
      (by
        have hsrc' : srcOff0 = listOff + 1 := hsrc0
        have hoff' : srcOff0 < bs.length := hoff0
        have hspan := teer_hover_of_dom dom hoff'
        -- regionBase + srcOff0 < 2^64 and srcOff0 = listOff+1
        omega))
    hoff0 (teer_hover_of_dom dom hoff0) (teer_hvalid_of_dom dom hoff0) hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 (teer_hover_of_dom dom hoff1) (teer_hvalid_of_dom dom hoff1) hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 (teer_hover_of_dom dom hoff2) (teer_hvalid_of_dom dom hoff2) hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 (teer_hover_of_dom dom hoff3) (teer_hvalid_of_dom dom hoff3) hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 (teer_hover_of_dom dom hoff4) (teer_hvalid_of_dom dom hoff4) hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 (teer_hover_of_dom dom hoff5) (teer_hvalid_of_dom dom hoff5) hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV (teer_hover_of_dom dom hoffV) (teer_hvalid_of_dom dom hoffV) hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA (teer_hover_of_dom dom hoffA) (teer_hvalid_of_dom dom hoffA) hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 (teer_hover_of_dom dom hoffA1) (teer_hvalid_of_dom dom hoffA1) hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
    srcOffA2 hoffA2 (teer_hover_of_dom dom hoffA2) (teer_hvalid_of_dom dom hoffA2) hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1
    srcOffA3 hoffA3 (teer_hover_of_dom dom hoffA3) (teer_hvalid_of_dom dom hoffA3) hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2
    srcOffA4 hoffA4 (teer_hover_of_dom dom hoffA4) (teer_hvalid_of_dom dom hoffA4) hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3
    srcOffA5 hoffA5 (teer_hover_of_dom dom hoffA5) (teer_hvalid_of_dom dom hoffA5) hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
    srcOffA6 hoffA6 (teer_hover_of_dom dom hoffA6) (teer_hvalid_of_dom dom hoffA6) hssA6 hlsA6 hllA6 hdecA6 hinbA6 hbridgeA5
    srcOffA7 hoffA7 (teer_hover_of_dom dom hoffA7) (teer_hvalid_of_dom dom hoffA7) hssA7 hlsA7 hllA7 hdecA7 hinbA7 hbridgeA6
    srcOffA8 hoffA8 (teer_hover_of_dom dom hoffA8) (teer_hvalid_of_dom dom hoffA8) hssA8 hlsA8 hllA8 hdecA8 hinbA8 hbridgeA7
    srcOffA9 hoffA9 (teer_hover_of_dom dom hoffA9) (teer_hvalid_of_dom dom hoffA9)
    (teer_hss_vacuous_srcOff0_of_dom dom srcOffA9 hA9 hoffA9)
    (teer_hls_vacuous_srcOff0_of_dom dom srcOffA9 hA9 hoffA9)
    (teer_hll_vacuous_srcOff0_of_dom dom srcOffA9 hA9 hoffA9)
    hdecA9 hinbA9 hbridgeA8
    hA9
    (teer_hoff0_of_empty_short_slack dom.hslack) dom.h0
      teerListCountAuthLoopAssumed_teerLinked
    dom.hslack dom.hvalid hret


#print axioms teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short_abi
#print axioms teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_dom_listOff0_exact_zero
theorem teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_dom_listOff0_exact_A9dec_zero
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s5 s6 s7 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) (off len : Nat)
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (hnez : balPtr ≠ (0 : Word))
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlenW : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (htype4 : (teerTxTypeDispatch (txSlice bs off len)).2.1 = (4 : Word))
    (dom : TeerEmptyAuthDomainEmptyShortRun regionBase bs)
    (hbound : off + len ≤ bs.length)
    (listOff : Nat)
    (ha0 : loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2 =
      regionBase + BitVec.ofNat 64 listOff)
    (hoffL : listOff < bs.length)
    (hL : listOff = 0)
    (hlenL : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 ≠ (0 : Word))
    (hlen1 : lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2 = BitVec.ofNat 64 1)
    (srcOff0 : Nat)
    (hsrc0 : srcOff0 = listOff + 1)
    (hoff0 : srcOff0 < bs.length)
    (hss0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        srcOff0 + 1 < bs.length ∧ regionBase.toNat + (srcOff0 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1)) = true)
    (hls0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xc0 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hll0 : ¬ BitVec.ult ((bs[srcOff0]'hoff0).zeroExtend 64) (0xf8 : Word) = true →
        srcOff0 + 1 + ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff0 + 1 +
          ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff0]'hoff0).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff0 + 1 + k)) = true)
    (hdec0 : ∃ next len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len0)
    (hinb0 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff0)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff1 : Nat)
    (hoff1 : srcOff1 < bs.length)
    (hss1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        srcOff1 + 1 < bs.length ∧ regionBase.toNat + (srcOff1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1)) = true)
    (hls1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xc0 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hll1 : ¬ BitVec.ult ((bs[srcOff1]'hoff1).zeroExtend 64) (0xf8 : Word) = true →
        srcOff1 + 1 + ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff1 + 1 +
          ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff1]'hoff1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff1 + 1 + k)) = true)
    (hdec1 : ∃ next len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len1)
    (hinb1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff2 : Nat)
    (hoff2 : srcOff2 < bs.length)
    (hss2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        srcOff2 + 1 < bs.length ∧ regionBase.toNat + (srcOff2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1)) = true)
    (hls2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xc0 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hll2 : ¬ BitVec.ult ((bs[srcOff2]'hoff2).zeroExtend 64) (0xf8 : Word) = true →
        srcOff2 + 1 + ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff2 + 1 +
          ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff2]'hoff2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff2 + 1 + k)) = true)
    (hdec2 : ∃ next len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len2)
    (hinb2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff3 : Nat)
    (hoff3 : srcOff3 < bs.length)
    (hss3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        srcOff3 + 1 < bs.length ∧ regionBase.toNat + (srcOff3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1)) = true)
    (hls3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xc0 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hll3 : ¬ BitVec.ult ((bs[srcOff3]'hoff3).zeroExtend 64) (0xf8 : Word) = true →
        srcOff3 + 1 + ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff3 + 1 +
          ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff3]'hoff3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff3 + 1 + k)) = true)
    (hdec3 : ∃ next len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len3)
    (hinb3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff4 : Nat)
    (hoff4 : srcOff4 < bs.length)
    (hss4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        srcOff4 + 1 < bs.length ∧ regionBase.toNat + (srcOff4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1)) = true)
    (hls4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xc0 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hll4 : ¬ BitVec.ult ((bs[srcOff4]'hoff4).zeroExtend 64) (0xf8 : Word) = true →
        srcOff4 + 1 + ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff4 + 1 +
          ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff4]'hoff4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff4 + 1 + k)) = true)
    (hdec4 : ∃ next len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len4)
    (hinb4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOff5 : Nat)
    (hoff5 : srcOff5 < bs.length)
    (hss5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        srcOff5 + 1 < bs.length ∧ regionBase.toNat + (srcOff5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1)) = true)
    (hls5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xc0 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hll5 : ¬ BitVec.ult ((bs[srcOff5]'hoff5).zeroExtend 64) (0xf8 : Word) = true →
        srcOff5 + 1 + ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOff5 + 1 +
          ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff5]'hoff5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOff5 + 1 + k)) = true)
    (hdec5 : ∃ next len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next len5)
    (hinb5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOff5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge : ∀ next0 len0 : Word,
      rlpItemDecode bs srcOff0 (regionBase + BitVec.ofNat 64 srcOff0)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next0 len0 →
      next0 = regionBase + BitVec.ofNat 64 srcOff1)
    (hbridge1 : ∀ next1 len1 : Word,
      rlpItemDecode bs srcOff1 (regionBase + BitVec.ofNat 64 srcOff1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next1 len1 →
      next1 = regionBase + BitVec.ofNat 64 srcOff2)
    (hbridge2 : ∀ next2 len2 : Word,
      rlpItemDecode bs srcOff2 (regionBase + BitVec.ofNat 64 srcOff2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next2 len2 →
      next2 = regionBase + BitVec.ofNat 64 srcOff3)
    (hbridge3 : ∀ next3 len3 : Word,
      rlpItemDecode bs srcOff3 (regionBase + BitVec.ofNat 64 srcOff3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next3 len3 →
      next3 = regionBase + BitVec.ofNat 64 srcOff4)
    (hbridge4 : ∀ next4 len4 : Word,
      rlpItemDecode bs srcOff4 (regionBase + BitVec.ofNat 64 srcOff4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next4 len4 →
      next4 = regionBase + BitVec.ofNat 64 srcOff5)
    (srcOffV : Nat)
    (hoffV : srcOffV < bs.length)
    (hssV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        srcOffV + 1 < bs.length ∧ regionBase.toNat + (srcOffV + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1)) = true)
    (hlsV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xc0 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hllV : ¬ BitVec.ult ((bs[srcOffV]'hoffV).zeroExtend 64) (0xf8 : Word) = true →
        srcOffV + 1 + ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffV + 1 +
          ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffV]'hoffV).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffV + 1 + k)) = true)
    (hdecV : ∃ next lenV : Word,
      rlpItemDecode bs srcOffV (regionBase + BitVec.ofNat 64 srcOffV)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenV)
    (hinbV : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffV)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridge5 : ∀ next5 len5 : Word,
      rlpItemDecode bs srcOff5 (regionBase + BitVec.ofNat 64 srcOff5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next5 len5 →
      next5 = regionBase + BitVec.ofNat 64 srcOffV) 
    -- auth walk_next0 item
    (srcOffA : Nat)
    (hcurA : (regionBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) =
      regionBase + BitVec.ofNat 64 srcOffA)
    (hoffA : srcOffA < bs.length)
    (hssA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA + 1 < bs.length ∧ regionBase.toNat + (srcOffA + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1)) = true)
    (hlsA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hllA : ¬ BitVec.ult ((bs[srcOffA]'hoffA).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA + 1 + ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA + 1 +
          ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA]'hoffA).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA + 1 + k)) = true)
    (hdecA : ∃ next lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA)
    (hinbA : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (srcOffA1 : Nat)
    (hoffA1 : srcOffA1 < bs.length)
    (hssA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA1 + 1 < bs.length ∧ regionBase.toNat + (srcOffA1 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1)) = true)
    (hlsA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hllA1 : ¬ BitVec.ult ((bs[srcOffA1]'hoffA1).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA1 + 1 + ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA1 + 1 +
          ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA1]'hoffA1).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA1 + 1 + k)) = true)
    (hdecA1 : ∃ next lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA1)
    (hinbA1 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA1)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA : ∀ nextA lenA : Word,
      rlpItemDecode bs srcOffA (regionBase + BitVec.ofNat 64 srcOffA)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA lenA →
      nextA = regionBase + BitVec.ofNat 64 srcOffA1)
    (srcOffA2 : Nat)
    (hoffA2 : srcOffA2 < bs.length)
    (hssA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA2 + 1 < bs.length ∧ regionBase.toNat + (srcOffA2 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1)) = true)
    (hlsA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hllA2 : ¬ BitVec.ult ((bs[srcOffA2]'hoffA2).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA2 + 1 + ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA2 + 1 +
          ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA2]'hoffA2).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA2 + 1 + k)) = true)
    (hdecA2 : ∃ next lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA2)
    (hinbA2 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA2)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA1 : ∀ nextA1 lenA1 : Word,
      rlpItemDecode bs srcOffA1 (regionBase + BitVec.ofNat 64 srcOffA1)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA1 lenA1 →
      nextA1 = regionBase + BitVec.ofNat 64 srcOffA2)
    (srcOffA3 : Nat)
    (hoffA3 : srcOffA3 < bs.length)
    (hssA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA3 + 1 < bs.length ∧ regionBase.toNat + (srcOffA3 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1)) = true)
    (hlsA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hllA3 : ¬ BitVec.ult ((bs[srcOffA3]'hoffA3).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA3 + 1 + ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA3 + 1 +
          ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA3]'hoffA3).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA3 + 1 + k)) = true)
    (hdecA3 : ∃ next lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA3)
    (hinbA3 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA3)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA2 : ∀ nextA2 lenA2 : Word,
      rlpItemDecode bs srcOffA2 (regionBase + BitVec.ofNat 64 srcOffA2)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA2 lenA2 →
      nextA2 = regionBase + BitVec.ofNat 64 srcOffA3)
    (srcOffA4 : Nat)
    (hoffA4 : srcOffA4 < bs.length)
    (hssA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA4 + 1 < bs.length ∧ regionBase.toNat + (srcOffA4 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1)) = true)
    (hlsA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hllA4 : ¬ BitVec.ult ((bs[srcOffA4]'hoffA4).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA4 + 1 + ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA4 + 1 +
          ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA4]'hoffA4).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA4 + 1 + k)) = true)
    (hdecA4 : ∃ next lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA4)
    (hinbA4 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA4)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA3 : ∀ nextA3 lenA3 : Word,
      rlpItemDecode bs srcOffA3 (regionBase + BitVec.ofNat 64 srcOffA3)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA3 lenA3 →
      nextA3 = regionBase + BitVec.ofNat 64 srcOffA4)
    (srcOffA5 : Nat)
    (hoffA5 : srcOffA5 < bs.length)
    (hssA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA5 + 1 < bs.length ∧ regionBase.toNat + (srcOffA5 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1)) = true)
    (hlsA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hllA5 : ¬ BitVec.ult ((bs[srcOffA5]'hoffA5).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA5 + 1 + ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA5 + 1 +
          ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA5]'hoffA5).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA5 + 1 + k)) = true)
    (hdecA5 : ∃ next lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA5)
    (hinbA5 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA5)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA4 : ∀ nextA4 lenA4 : Word,
      rlpItemDecode bs srcOffA4 (regionBase + BitVec.ofNat 64 srcOffA4)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA4 lenA4 →
      nextA4 = regionBase + BitVec.ofNat 64 srcOffA5)
    (srcOffA6 : Nat)
    (hoffA6 : srcOffA6 < bs.length)
    (hssA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA6 + 1 < bs.length ∧ regionBase.toNat + (srcOffA6 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1)) = true)
    (hlsA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hllA6 : ¬ BitVec.ult ((bs[srcOffA6]'hoffA6).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA6 + 1 + ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA6 + 1 +
          ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA6]'hoffA6).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA6 + 1 + k)) = true)
    (hdecA6 : ∃ next lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA6)
    (hinbA6 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA6)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA5 : ∀ nextA5 lenA5 : Word,
      rlpItemDecode bs srcOffA5 (regionBase + BitVec.ofNat 64 srcOffA5)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA5 lenA5 →
      nextA5 = regionBase + BitVec.ofNat 64 srcOffA6)
    (srcOffA7 : Nat)
    (hoffA7 : srcOffA7 < bs.length)
    (hssA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA7 + 1 < bs.length ∧ regionBase.toNat + (srcOffA7 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1)) = true)
    (hlsA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hllA7 : ¬ BitVec.ult ((bs[srcOffA7]'hoffA7).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA7 + 1 + ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA7 + 1 +
          ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA7]'hoffA7).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA7 + 1 + k)) = true)
    (hdecA7 : ∃ next lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA7)
    (hinbA7 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA7)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA6 : ∀ nextA6 lenA6 : Word,
      rlpItemDecode bs srcOffA6 (regionBase + BitVec.ofNat 64 srcOffA6)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA6 lenA6 →
      nextA6 = regionBase + BitVec.ofNat 64 srcOffA7)
    (srcOffA8 : Nat)
    (hoffA8 : srcOffA8 < bs.length)
    (hssA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        srcOffA8 + 1 < bs.length ∧ regionBase.toNat + (srcOffA8 + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1)) = true)
    (hlsA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xc0 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hllA8 : ¬ BitVec.ult ((bs[srcOffA8]'hoffA8).zeroExtend 64) (0xf8 : Word) = true →
        srcOffA8 + 1 + ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (srcOffA8 + 1 +
          ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOffA8]'hoffA8).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (srcOffA8 + 1 + k)) = true)
    (hdecA8 : ∃ next lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) next lenA8)
    (hinbA8 : BitVec.ult (regionBase + BitVec.ofNat 64 srcOffA8)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) = true)
    (hbridgeA7 : ∀ nextA7 lenA7 : Word,
      rlpItemDecode bs srcOffA7 (regionBase + BitVec.ofNat 64 srcOffA7)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA7 lenA7 →
      nextA7 = regionBase + BitVec.ofNat 64 srcOffA8)
    (srcOffA9 : Nat)
    (hoffA9 : srcOffA9 < bs.length)
    (hbridgeA8 : ∀ nextA8 lenA8 : Word,
      rlpItemDecode bs srcOffA8 (regionBase + BitVec.ofNat 64 srcOffA8)
        ((regionBase + BitVec.ofNat 64 listOff) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) nextA8 lenA8 →
      nextA8 = regionBase + BitVec.ofNat 64 srcOffA9)
    (hA9 : srcOffA9 = 0)
    (hret : (ret &&& ~~~(1 : Word)) = ret) :
    let s0 := loadPtr
    let s1 := lenW
    let s2 := balPtr
    let s3 := balLenW
    let s4 := chainIdW
    let s8 := regionBase + BitVec.ofNat 64 srcOffV
    let s9 :=
      (regionBase + BitVec.ofNat 64 listOff) +
        (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
    let s : TeerSaved :=
      { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4
        s5 := s5, s6 := s6, s7 := s7, s8 := s8, s9 := s9
        s10 := s10, s11 := s11, a5 := baiW }
    cpsTripleWithin (nFrontToAtListCount + nListCountAuthLoopStart 1 + 30)
      E ret teerLinkedField0
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRestIs ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun hp =>
        ∃ (_refund _baiW' : Word),
          (((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
              stackFree spVal nTeerStackDwords **
              (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
              (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
              (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
              (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
              (.x27 ↦ᵣ s.s11) **
              (.x10 ↦ᵣ (0 : Word)) **
              regOwn .x11 **
              bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
              teerScratchOwn **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
              regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
              regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) **
            stackFree spC 6) hp) := by
  intro s0 s1 s2 s3 s4 s8 s9 s
  exact teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_zero
    ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW
    s5 s6 s7 s10 s11
    regionBase bs balBytes off len hspC hnez hptr hlenW hsuccess htype4
    dom.halign hbound dom.hover (teer_hvalid_of_dom dom (teer_hoffOff_of_success_bound hsuccess hbound)) listOff ha0 hoffL (teer_hover_of_dom dom hoffL) (teer_hvalid_of_dom dom hoffL) hlenL
    (teer_h_ge_listOff0_of_dom dom listOff hL hoffL)
    (teer_h_hi_listOff0_of_dom dom listOff hL hoffL)
    (teer_h_exact_listOff0_of_dom dom listOff hL hoffL
      (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) hlen1)
    srcOff0
    (teer_hcur_of_srcOff_succ regionBase listOff srcOff0 hsrc0
      (by
        have hsrc' : srcOff0 = listOff + 1 := hsrc0
        have hoff' : srcOff0 < bs.length := hoff0
        have hspan := teer_hover_of_dom dom hoff'
        -- regionBase + srcOff0 < 2^64 and srcOff0 = listOff+1
        omega))
    hoff0 (teer_hover_of_dom dom hoff0) (teer_hvalid_of_dom dom hoff0) hss0 hls0 hll0 hdec0 hinb0
    srcOff1 hoff1 (teer_hover_of_dom dom hoff1) (teer_hvalid_of_dom dom hoff1) hss1 hls1 hll1 hdec1 hinb1
    srcOff2 hoff2 (teer_hover_of_dom dom hoff2) (teer_hvalid_of_dom dom hoff2) hss2 hls2 hll2 hdec2 hinb2
    srcOff3 hoff3 (teer_hover_of_dom dom hoff3) (teer_hvalid_of_dom dom hoff3) hss3 hls3 hll3 hdec3 hinb3
    srcOff4 hoff4 (teer_hover_of_dom dom hoff4) (teer_hvalid_of_dom dom hoff4) hss4 hls4 hll4 hdec4 hinb4
    srcOff5 hoff5 (teer_hover_of_dom dom hoff5) (teer_hvalid_of_dom dom hoff5) hss5 hls5 hll5 hdec5 hinb5
    hbridge hbridge1 hbridge2 hbridge3 hbridge4
    srcOffV hoffV (teer_hover_of_dom dom hoffV) (teer_hvalid_of_dom dom hoffV) hssV hlsV hllV hdecV hinbV hbridge5
    srcOffA hcurA hoffA (teer_hover_of_dom dom hoffA) (teer_hvalid_of_dom dom hoffA) hssA hlsA hllA hdecA hinbA
    srcOffA1 hoffA1 (teer_hover_of_dom dom hoffA1) (teer_hvalid_of_dom dom hoffA1) hssA1 hlsA1 hllA1 hdecA1 hinbA1 hbridgeA
    srcOffA2 hoffA2 (teer_hover_of_dom dom hoffA2) (teer_hvalid_of_dom dom hoffA2) hssA2 hlsA2 hllA2 hdecA2 hinbA2 hbridgeA1
    srcOffA3 hoffA3 (teer_hover_of_dom dom hoffA3) (teer_hvalid_of_dom dom hoffA3) hssA3 hlsA3 hllA3 hdecA3 hinbA3 hbridgeA2
    srcOffA4 hoffA4 (teer_hover_of_dom dom hoffA4) (teer_hvalid_of_dom dom hoffA4) hssA4 hlsA4 hllA4 hdecA4 hinbA4 hbridgeA3
    srcOffA5 hoffA5 (teer_hover_of_dom dom hoffA5) (teer_hvalid_of_dom dom hoffA5) hssA5 hlsA5 hllA5 hdecA5 hinbA5 hbridgeA4
    srcOffA6 hoffA6 (teer_hover_of_dom dom hoffA6) (teer_hvalid_of_dom dom hoffA6) hssA6 hlsA6 hllA6 hdecA6 hinbA6 hbridgeA5
    srcOffA7 hoffA7 (teer_hover_of_dom dom hoffA7) (teer_hvalid_of_dom dom hoffA7) hssA7 hlsA7 hllA7 hdecA7 hinbA7 hbridgeA6
    srcOffA8 hoffA8 (teer_hover_of_dom dom hoffA8) (teer_hvalid_of_dom dom hoffA8) hssA8 hlsA8 hllA8 hdecA8 hinbA8 hbridgeA7
    srcOffA9 hoffA9 (teer_hover_of_dom dom hoffA9) (teer_hvalid_of_dom dom hoffA9)
    (teer_hss_vacuous_srcOff0_of_dom dom srcOffA9 hA9 hoffA9)
    (teer_hls_vacuous_srcOff0_of_dom dom srcOffA9 hA9 hoffA9)
    (teer_hll_vacuous_srcOff0_of_dom dom srcOffA9 hA9 hoffA9)
    (teer_hdecA9_empty_short_listOff0 dom listOff hL
      (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) hlen1
      srcOffA9 hA9 hoffA9 (by
        have h := dom.hover; have hs := dom.hslack; omega)) (teer_hinbA9_empty_short_listOff0 regionBase listOff hL
      (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) hlen1
      srcOffA9 hA9 (by
        have h := dom.hover; have hs := dom.hslack; omega)) hbridgeA8
    hA9
    (teer_hoff0_of_empty_short_slack dom.hslack) dom.h0
      teerListCountAuthLoopAssumed_teerLinked
    dom.hslack dom.hvalid hret


#print axioms teerEmptyAuth_free26_toRet_of_applied_as_postEx_is_empty_short_abi
#print axioms teerEmptyAuth_free26_to_applied_flat_of_applied_as_postEx_is_empty_short_abi_dom_listOff0_exact_A9dec_zero

end EvmAsm.Codegen.TxEip7702TeerSpec
