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
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch txSlice)

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
    (hoffOff : off < bs.length)
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
    dom.halign hbound dom.hover (teer_hvalid_of_dom dom hoffOff) listOff ha0 hoffL (teer_hover_of_dom dom hoffL) (teer_hvalid_of_dom dom hoffL) hlenL
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
    (hoffOff : off < bs.length)
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
    dom.halign hbound dom.hover (teer_hvalid_of_dom dom hoffOff) listOff ha0 hoffL (teer_hover_of_dom dom hoffL) (teer_hvalid_of_dom dom hoffL) hlenL
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
    (hoffOff : off < bs.length)
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
    dom.halign hbound dom.hover (teer_hvalid_of_dom dom hoffOff) listOff ha0 hoffL (teer_hover_of_dom dom hoffL) (teer_hvalid_of_dom dom hoffL) hlenL
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


end EvmAsm.Codegen.TxEip7702TeerSpec
