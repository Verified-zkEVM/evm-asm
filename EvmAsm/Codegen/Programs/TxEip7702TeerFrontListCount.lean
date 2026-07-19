/-
  Teer front packaging: AtListCount → AfterAuthLoopLi under nested stackFree spC 6.

  * TeerListCountAuthLoopAssumed — named hyp combining ListCount Call+BNE+LD +
    AuthLoopStartShort (Prep+WI+LI). Body residual: TeerListCountAssumed Result→ok
    + frame compose (leaves classical-3).
  * Empty-auth: Success count=0 → s7=0; LI s8=0 at AfterAuthLoopLi.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerListCount
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthLoopStart
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmBase
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpListCountItemsSAsm

/-- Steps: list_count ok+load + AuthLoopStartShort. -/
def nListCountAuthLoopStart (listLen : Nat) : Nat :=
  nListCountOkToLoad listLen + nAuthLoopStartShort

/-- After list_count load + AuthLoopStart short: s7=countW, s8=0, cursors saved. -/
def teerListCountAuthLoopPost (spC listBase outPtr s0 s1 s2 s3 countW : Word)
    (bytes : List (BitVec 8)) (listOff : Nat) (listLenW t5Old t6Old : Word) :
    Assertion :=
  let cur := (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12)
  let endW := (listBase + BitVec.ofNat 64 listOff) + listLenW
  ((.x1 ↦ᵣ LinkWalkInitAuth) ** (.x10 ↦ᵣ cur) ** (.x11 ↦ᵣ endW) **
    (.x12 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ cur) ** (.x22 ↦ᵣ endW) **
    (.x23 ↦ᵣ countW) ** (.x24 ↦ᵣ (0 : Word)) **
    (.x5 ↦ᵣ AuthCountAddr) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) **
    (.x2 ↦ᵣ spC) **
    ((.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3)) **
    stackFree spC 6 **
    bytesRegion listBase bytes ** (outPtr ↦ₘ countW))

/-- Named hyp: AtListCount → AfterAuthLoopLi.
    Prest: list_count callee ABI + s5/s6 = listBase+listOff / listLenW + nested free.
    Requires Success + short-list WI guards. Leaves exist classical-3; body residual
    Result→ok specialize + frame compose. -/
structure TeerListCountAuthLoopAssumed (cr : CodeReq) where
  run :
    ∀ (spC listBase listLenW outPtr oldCount s0 s1 s2 s3 countW : Word)
      (bytes : List (BitVec 8)) (listLen count listOff : Nat)
      (old1 s7Old t0Old v10 v11 v24 : Word)
      (hoff : listOff < bytes.length),
      listLenW = BitVec.ofNat 64 listLen →
      listBase.toNat % 8 = 0 →
      listLen + 9 ≤ bytes.length →
      listBase.toNat + bytes.length < 2 ^ 64 →
      (∀ k, k < bytes.length →
        isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) →
      (LinkListCount &&& ~~~(1 : Word)) = LinkListCount →
      countW = BitVec.ofNat 64 count →
      count < 2 ^ 64 →
      Success bytes listBase listLen count →
      outPtr = AuthCountAddr →
      listLenW ≠ (0 : Word) →
      listBase.toNat + listOff < 2 ^ 64 →
      isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true →
      ¬ BitVec.ult ((bytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
      BitVec.ult ((bytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
      (listBase + BitVec.ofNat 64 listOff) +
          (((bytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
            signExtend12 (1 : BitVec 12)) =
        (listBase + BitVec.ofNat 64 listOff) + listLenW →
      cpsTripleWithin (nListCountAuthLoopStart listLen) AtListCount AfterAuthLoopLi cr
        ((.x1 ↦ᵣ old1) ** (.x5 ↦ᵣ t0Old) ** (.x23 ↦ᵣ s7Old) **
          (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x24 ↦ᵣ v24) **
          (.x21 ↦ᵣ listBase + BitVec.ofNat 64 listOff) **
          (.x22 ↦ᵣ listLenW) **
          teerListCountCalleeP spC listBase listLenW outPtr oldCount s0 s1 s2 s3
            bytes)
        (teerListCountAuthLoopPost spC listBase outPtr s0 s1 s2 s3 countW bytes
          listOff listLenW (0 : Word) (0 : Word))

end EvmAsm.Codegen.TxEip7702TeerSpec
