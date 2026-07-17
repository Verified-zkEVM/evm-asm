/-
  bal≠0 glue + one-iter + loop induction for block_verdict_tx_state_gas_array (a4gbr).
  Split for Codegen/Programs 1500-line file-size guard.
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayLoopClose
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayEpilogue

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec (wordArray)


/-! ## EndSpan → FromIntrinsic (bal≠0) + LoopInv post reshape -/

/-- EndSpan post (concrete x1, bal≠0) → FromIntrinsic bal≠0 pre. -/
private theorem endSpan_to_fromIntr_bal1
    (spC txBase outBase balBase chainIdW nW iW startW endW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8))
    (txPtr txLenW outPtr old1 : Word) (i : Nat) :
    ∀ h, (((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
            (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
            (.x1 ↦ᵣ old1) ** regOwn .x6 ** regOwn .x7 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            payload txBase outBase balBase txBlob outVals balBytes true **
            (.x0 ↦ᵣ (0 : Word))) h) →
      -- BalNezFromIntrinsic pre: s-regs outside loopIntrinsicFrame.
      (((.x1 ↦ᵣ old1) **
          (.x2 ↦ᵣ spC) ** stackFree spC nCalleeStackDwords **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
          (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) **
          (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
          bytesRegion txBase txBlob **
          wordArray outBase outVals **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
            startW endW (BitVec.ofNat 64 txBlob.length) csaved balBytes
            true) h) := by
  intro h hp
  have hp1 :
      (((.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
          ((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
            (.x1 ↦ᵣ old1) ** regOwn .x6 ** regOwn .x7 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            payload txBase outBase balBase txBlob outVals balBytes true **
            (.x0 ↦ᵣ (0 : Word)))) h) := by
    xperm_hyp hp
  have hp2 := sepConj_mono (regIs_to_regOwn .x5 (BitVec.ofNat 64 (8 * i)))
    (fun _ hh => hh) h hp1
  simp only [payload, loopIntrinsicFrame, ↓reduceIte] at hp2 ⊢
  xperm_hyp hp2

set_option maxRecDepth 8000 in
/-- bal≠0 FromIntrinsic post → LoopInv (i+1) with updated outVals'. -/
private theorem balNezPost_to_loopInv
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals' : List Nat)
    (balBytes : List (BitVec 8)) (i : Nat) (startW endW chargeW outPtr sumW : Word) :
    ∀ h, (((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
            (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x24 ↦ᵣ balBase) **
            (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
            (.x6 ↦ᵣ outPtr) **
            (.x7 ↦ᵣ sumW) **
            (.x1 ↦ᵣ LinkTeer) **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
            (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            bytesRegion txBase txBlob **
            wordArray outBase outVals' **
            bytesRegion balBase balBytes **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) h) →
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals'
        balBytes true (i + 1)) h := by
  intro h hp
  have step (r : Reg) (v : Word) (P : Assertion) :
      ∀ h', ((r ↦ᵣ v) ** P) h' → (regOwn r ** P) h' :=
    fun h' hp' => sepConj_mono (regIs_to_regOwn r v) (fun _ hh => hh) h' hp'
  -- Pull focus regs left, mono regIs→regOwn one at a time.
  have hp1 :
      (((.x1 ↦ᵣ LinkTeer) ** (.x10 ↦ᵣ chargeW) **
          (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) ** (.x6 ↦ᵣ outPtr) **
          (.x7 ↦ᵣ sumW) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
            (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ balBase) **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
            (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            bytesRegion txBase txBlob ** wordArray outBase outVals' **
            bytesRegion balBase balBytes **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)) h) := by
    xperm_hyp hp
  have hp2 := step .x1 LinkTeer _ h hp1
  have hp3 :
      (((.x10 ↦ᵣ chargeW) **
          (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) ** (.x6 ↦ᵣ outPtr) **
          (.x7 ↦ᵣ sumW) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (regOwn .x1 **
            ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
              (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ balBase) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
              (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
              (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
              (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
              savedFrame spC csaved **
              stackFree spC nCalleeStackDwords **
              bytesRegion txBase txBlob ** wordArray outBase outVals' **
              bytesRegion balBase balBytes **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31))) h) := by
    xperm_hyp hp2
  have hp4 := step .x10 chargeW _ h hp3
  have hp5 :
      (((.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) ** (.x6 ↦ᵣ outPtr) **
          (.x7 ↦ᵣ sumW) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (regOwn .x10 ** regOwn .x1 **
            ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
              (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ balBase) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
              (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
              (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
              (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
              savedFrame spC csaved **
              stackFree spC nCalleeStackDwords **
              bytesRegion txBase txBlob ** wordArray outBase outVals' **
              bytesRegion balBase balBytes **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31))) h) := by
    xperm_hyp hp4
  have hp6 := step .x5 (BitVec.ofNat 64 (8 * i)) _ h hp5
  have hp7 :
      (((.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) **
          (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (regOwn .x5 ** regOwn .x10 ** regOwn .x1 **
            ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
              (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ balBase) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
              (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
              (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
              (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
              savedFrame spC csaved **
              stackFree spC nCalleeStackDwords **
              bytesRegion txBase txBlob ** wordArray outBase outVals' **
              bytesRegion balBase balBytes **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31))) h) := by
    xperm_hyp hp6
  have hp8 := step .x6 outPtr _ h hp7
  have hp9 :
      (((.x7 ↦ᵣ sumW) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (regOwn .x6 ** regOwn .x5 ** regOwn .x10 ** regOwn .x1 **
            ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
              (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ balBase) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
              (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
              (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
              (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
              savedFrame spC csaved **
              stackFree spC nCalleeStackDwords **
              bytesRegion txBase txBlob ** wordArray outBase outVals' **
              bytesRegion balBase balBytes **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31))) h) := by
    xperm_hyp hp8
  have hp10 := step .x7 sumW _ h hp9
  have hp11 :
      (((.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (regOwn .x7 ** regOwn .x6 ** regOwn .x5 ** regOwn .x10 ** regOwn .x1 **
            ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
              (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ balBase) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
              (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
              (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
              (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
              savedFrame spC csaved **
              stackFree spC nCalleeStackDwords **
              bytesRegion txBase txBlob ** wordArray outBase outVals' **
              bytesRegion balBase balBytes **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31))) h) := by
    xperm_hyp hp10
  have hp12 := step .x22 startW _ h hp11
  have hp13 :
      (((.x23 ↦ᵣ endW) **
          (regOwn .x22 ** regOwn .x7 ** regOwn .x6 ** regOwn .x5 **
            regOwn .x10 ** regOwn .x1 **
            ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
              (.x0 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ balBase) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
              (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
              (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
              (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
              savedFrame spC csaved **
              stackFree spC nCalleeStackDwords **
              bytesRegion txBase txBlob ** wordArray outBase outVals' **
              bytesRegion balBase balBytes **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31))) h) := by
    xperm_hyp hp12
  have hp14 := step .x23 endW _ h hp13
  unfold LoopInv payload scratchRegs
  simp only [↓reduceIte]
  xperm_hyp hp14

/-- EndSpan post with regOwn x1 rightmost (bal≠0). -/
private def endSpanOwnRaBal (spC txBase outBase balBase chainIdW nW iW
    startW endW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (txPtr txLenW outPtr : Word) (i : Nat)
    : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
  (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
  regOwn .x6 ** regOwn .x7 **
  regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  savedFrame spC csaved **
  stackFree spC nCalleeStackDwords **
  payload txBase outBase balBase txBlob outVals balBytes true **
  (.x0 ↦ᵣ (0 : Word))

private theorem endSpan_to_ownRaBal
    (spC txBase outBase balBase chainIdW nW iW startW endW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (txPtr txLenW outPtr : Word) (i : Nat) :
    ∀ h, (((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
            (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
            regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            payload txBase outBase balBase txBlob outVals balBytes true **
            (.x0 ↦ᵣ (0 : Word))) h) →
      ((endSpanOwnRaBal spC txBase outBase balBase chainIdW nW iW startW endW
          csaved txBlob outVals balBytes txPtr txLenW outPtr i **
          regOwn .x1) h) := by
  intro h hp
  unfold endSpanOwnRaBal
  xperm_hyp hp

private theorem ownRaBal_vals_to_endSpan
    (spC txBase outBase balBase chainIdW nW iW startW endW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (txPtr txLenW outPtr old1 : Word) (i : Nat) :
    ∀ h, ((endSpanOwnRaBal spC txBase outBase balBase chainIdW nW iW startW endW
            csaved txBlob outVals balBytes txPtr txLenW outPtr i **
          (.x1 ↦ᵣ old1)) h) →
      (((.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
          (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
          (.x1 ↦ᵣ old1) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          payload txBase outBase balBase txBlob outVals balBytes true **
          (.x0 ↦ᵣ (0 : Word))) h) := by
  intro h hp
  unfold endSpanOwnRaBal at hp
  xperm_hyp hp

set_option maxRecDepth 8000 in
/-- AfterEndSpan → LoopGuard (i+1) on bal≠0 under Intrinsic+TeerAssumed.
    Updates outVals[i] := pure + teer charge. -/
theorem bvtIterBalNez_fromEndSpan
    (hintr : IntrinsicAssumed fullCode)
    (teer : TeerApplied) (hteer : TeerAssumed fullCode teer)
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob balBytes : List (BitVec 8))
    (outVals : List Nat) (chainId i off len : Nat)
    (startW endW : Word)
    (hentryI : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hentryT : hteer.entry =
      (GuestAddrs.tx_eip7702_existing_authority_refund : Word))
    (hretI : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hretT : (LinkTeer &&& ~~~(1 : Word)) = LinkTeer)
    (hbal : balBase ≠ 0)
    (hstart : startW = BitVec.ofNat 64 off)
    (hlen : off + len ≤ txBlob.length)
    (htxLen : endW - startW = BitVec.ofNat 64 len)
    (hchain : chainIdW = BitVec.ofNat 64 chainId)
    (hi : i < outVals.length)
    (hcell : outVals[i] = pureIntrinsicStateGasSuccess)
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let bodyLenW := BitVec.ofNat 64 txBlob.length
    let chargeNat := teer ((txBlob.drop off).take len) balBytes chainId (i + 1)
    let outVals' := outVals.set i (pureIntrinsicStateGasSuccess + chargeNat)
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    cpsTripleWithin
      ((1 + nIntrinsicSteps) + (1 + 1 + 6 + (1 + nTeerSteps) + 5 + 1 + 2))
      AfterEndSpan LoopGuard fullCode
      ((.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase balBase txBlob outVals balBytes true **
        (.x0 ↦ᵣ (0 : Word)))
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals'
        balBytes true (i + 1)) := by
  intro iW bodyLenW chargeNat outVals' txPtr txLenW outPtr
  refine cpsTripleWithin_weaken
    (fun h hp => endSpan_to_ownRaBal spC txBase outBase balBase chainIdW nW iW
      startW endW csaved txBlob outVals balBytes txPtr txLenW outPtr i h hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x1) (fun old1 => ?_)
  have hcore := bvtIterBalNezFromIntrinsic hintr teer hteer spC txBase outBase
    balBase chainIdW nW csaved txBlob balBytes outVals chainId i off len
    startW endW old1 hentryI hentryT hretI hretT hbal hstart hlen htxLen
    hchain hi hcell hi61
  refine cpsTripleWithin_weaken
    (fun h hp => by
      have hp1 := ownRaBal_vals_to_endSpan spC txBase outBase balBase chainIdW nW
        iW startW endW csaved txBlob outVals balBytes txPtr txLenW outPtr
        old1 i h hp
      exact endSpan_to_fromIntr_bal1 spC txBase outBase balBase chainIdW nW iW
        startW endW csaved txBlob outVals balBytes txPtr txLenW outPtr
        old1 i h hp1)
    (fun h hq => by
      let chargeW := BitVec.ofNat 64 chargeNat
      let sumW := BitVec.ofNat 64 pureIntrinsicStateGasSuccess + chargeW
      have hq' :
          (((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
              (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
              (.x24 ↦ᵣ balBase) **
              (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
              (.x6 ↦ᵣ outPtr) **
              (.x7 ↦ᵣ sumW) **
              (.x1 ↦ᵣ LinkTeer) **
              (.x2 ↦ᵣ spC) **
              (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
              (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
              (.x20 ↦ᵣ nW) **
              (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
              (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
              (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
              savedFrame spC csaved **
              stackFree spC nCalleeStackDwords **
              bytesRegion txBase txBlob **
              wordArray outBase outVals' **
              bytesRegion balBase balBytes **
              regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) h) := by
        xperm_hyp hq
      exact balNezPost_to_loopInv spC txBase outBase balBase chainIdW nW csaved
        txBlob outVals' balBytes i startW endW chargeW outPtr sumW h hq')
    hcore

/-! ## One full iteration: LoopGuard → LoopGuard (i+1)

    Guard ntaken ;; ThroughSpan ;; ThroughEnd ;; EndSpanSetup ;; Bal0|BalNez.
    Step bound is the max (bal≠0) path; bal=0 mono-lifts. -/

/-- Exact one-iter step budget (covers bal≠0 teer path). -/
def nOneIterSteps : Nat :=
  1 +
    ((2 + (1 + nBgvSteps) + 1) + 3) +
    nEndPathSteps +
    6 +
    ((1 + nIntrinsicSteps) + (1 + 1 + 6 + (1 + nTeerSteps) + 5 + 1 + 2))

/-- `ofNat i ≠ ofNat n` when `i < n < 2^62`. -/
private theorem ofNat_ne_of_lt (i n : Nat) (hi : i < n) (hn : n < 2 ^ 62) :
    (BitVec.ofNat 64 i : Word) ≠ BitVec.ofNat 64 n := by
  intro heq
  have hi64 : i < 2 ^ 64 := Nat.lt_trans hi (Nat.lt_trans hn (by decide))
  have hn64 : n < 2 ^ 64 := Nat.lt_trans hn (by decide)
  have : i = n := by
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hn64] at this
  omega

set_option maxRecDepth 8000 in
/-- One iteration bal=0: LoopGuard → LoopGuard (i+1), outVals unchanged. -/
theorem bvtIterOne_bal0
    (hintr : IntrinsicAssumed fullCode)
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (n i : Nat)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : IterOk txBlob n i)
    (htxAlign : txBase.toNat % 8 = 0)
    (hnW : nW = BitVec.ofNat 64 n)
    (hentry : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hret : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hiOut : i < outVals.length)
    (hcell : outVals[i] = pureIntrinsicStateGasSuccess)
    (hi61 : i < 2 ^ 61) :
    cpsTripleWithin nOneIterSteps LoopGuard LoopGuard fullCode
      (LoopInv spC txBase outBase (0 : Word) chainIdW nW csaved txBlob outVals
        balBytes false i)
      (LoopInv spC txBase outBase (0 : Word) chainIdW nW csaved txBlob outVals
        balBytes false (i + 1)) := by
  let startW := leU32 txBlob (4 * i)
  let endW := hok.endW
  let off := startW.toNat
  let len := endW.toNat - startW.toNat
  have hiW : BitVec.ofNat 64 i ≠ nW := by
    rw [hnW]; exact ofNat_ne_of_lt i n hok.hi hok.hNBound
  have hguard0 := bvtGuardNtaken spC txBase outBase (0 : Word) chainIdW nW
    csaved txBlob outVals balBytes false i hiW
  have hguard := cpsTripleWithin_extend_code bvt_mono hguard0
  have hspan := bvtIterThroughSpan spC txBase outBase (0 : Word) chainIdW nW
    csaved txBlob outVals balBytes false n i hbgv hok htxAlign hnW
  have hend := bvtIterThroughEnd spC txBase outBase (0 : Word) chainIdW nW
    csaved txBlob outVals balBytes false n i startW (BitVec.ofNat 64 (4 * n))
    hbgv hok hnW rfl rfl htxAlign
  have hStartEq : startW = hok.startW := hok.hStart.symm
  have hsetup0 := bvtIterEndSpanSetup_fromEnd spC txBase outBase (0 : Word)
    chainIdW nW csaved txBlob outVals balBytes false n i startW endW
    (if i + 1 = n then LinkLoopBgv1 else LinkLoopBgv2)
    (if i + 1 = n then startW else endW)
    hok hStartEq rfl hi61
  have hsetup := cpsTripleWithin_extend_code bvt_mono hsetup0
  have hstart : startW = BitVec.ofNat 64 off := word_eq_ofNat_toNat startW
  have hge : startW.toNat ≤ endW.toNat := by
    have h1 : startW = hok.startW := hok.hStart.symm
    simpa [h1] using hok.hEndGeStart
  have htxLen : endW - startW = BitVec.ofNat 64 len :=
    word_sub_toNat endW startW hge
  have hlen : off + len ≤ txBlob.length := by
    change startW.toNat + (endW.toNat - startW.toNat) ≤ txBlob.length
    rw [Nat.add_sub_cancel' hge]
    -- endW := hok.endW
    exact hok.hEndLeLen
  have hbal0 := bvtIterBal0_fromEndSpan hintr spC txBase outBase chainIdW nW
    csaved txBlob outVals balBytes i off len startW endW
    hentry hret hstart hlen htxLen hiOut hcell
  -- Compose: guard ;; span ;; end ;; setup ;; bal0, padding each to nOneIterSteps pieces.
  have hgs := cpsTripleWithin_seq_perm_same_cr (fun _ hq => hq) hguard hspan
  have hgse := cpsTripleWithin_seq_perm_same_cr (fun _ hq => hq) hgs hend
  have hgseS := cpsTripleWithin_seq_perm_same_cr (fun _ hq => hq) hgse hsetup
  have hfull := cpsTripleWithin_seq_perm_same_cr (fun _ hq => hq) hgseS hbal0
  exact cpsTripleWithin_mono_nSteps
    (nSteps :=
      1 + ((2 + (1 + nBgvSteps) + 1) + 3) + nEndPathSteps + 6 +
        ((1 + nIntrinsicSteps) + 4))
    (nSteps' := nOneIterSteps)
    (by simp only [nOneIterSteps, nEndPathSteps, nBgvSteps, nIntrinsicSteps,
          nTeerSteps]; omega)
    hfull

set_option maxRecDepth 8000 in
/-- One iteration bal≠0: LoopGuard → LoopGuard (i+1) with outVals.set charge. -/
theorem bvtIterOne_balNez
    (hintr : IntrinsicAssumed fullCode)
    (teer : TeerApplied) (hteer : TeerAssumed fullCode teer)
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob balBytes : List (BitVec 8))
    (outVals : List Nat) (chainId n i : Nat)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : IterOk txBlob n i)
    (htxAlign : txBase.toNat % 8 = 0)
    (hnW : nW = BitVec.ofNat 64 n)
    (hentryI : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hentryT : hteer.entry =
      (GuestAddrs.tx_eip7702_existing_authority_refund : Word))
    (hretI : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hretT : (LinkTeer &&& ~~~(1 : Word)) = LinkTeer)
    (hbal : balBase ≠ 0)
    (hchain : chainIdW = BitVec.ofNat 64 chainId)
    (hiOut : i < outVals.length)
    (hcell : outVals[i] = pureIntrinsicStateGasSuccess)
    (hi61 : i < 2 ^ 61) :
    let startW := leU32 txBlob (4 * i)
    let endW := hok.endW
    let off := startW.toNat
    let len := endW.toNat - startW.toNat
    let chargeNat := teer ((txBlob.drop off).take len) balBytes chainId (i + 1)
    let outVals' := outVals.set i (pureIntrinsicStateGasSuccess + chargeNat)
    cpsTripleWithin nOneIterSteps LoopGuard LoopGuard fullCode
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
        balBytes true i)
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals'
        balBytes true (i + 1)) := by
  intro startW endW off len chargeNat outVals'
  have hiW : BitVec.ofNat 64 i ≠ nW := by
    rw [hnW]; exact ofNat_ne_of_lt i n hok.hi hok.hNBound
  have hguard0 := bvtGuardNtaken spC txBase outBase balBase chainIdW nW
    csaved txBlob outVals balBytes true i hiW
  have hguard := cpsTripleWithin_extend_code bvt_mono hguard0
  have hspan := bvtIterThroughSpan spC txBase outBase balBase chainIdW nW
    csaved txBlob outVals balBytes true n i hbgv hok htxAlign hnW
  have hend := bvtIterThroughEnd spC txBase outBase balBase chainIdW nW
    csaved txBlob outVals balBytes true n i startW (BitVec.ofNat 64 (4 * n))
    hbgv hok hnW rfl rfl htxAlign
  have hStartEq : startW = hok.startW := hok.hStart.symm
  have hsetup0 := bvtIterEndSpanSetup_fromEnd spC txBase outBase balBase
    chainIdW nW csaved txBlob outVals balBytes true n i startW endW
    (if i + 1 = n then LinkLoopBgv1 else LinkLoopBgv2)
    (if i + 1 = n then startW else endW)
    hok hStartEq rfl hi61
  have hsetup := cpsTripleWithin_extend_code bvt_mono hsetup0
  have hstart : startW = BitVec.ofNat 64 off := word_eq_ofNat_toNat startW
  have hge : startW.toNat ≤ endW.toNat := by
    have h1 : startW = hok.startW := hok.hStart.symm
    simpa [h1] using hok.hEndGeStart
  have htxLen : endW - startW = BitVec.ofNat 64 len :=
    word_sub_toNat endW startW hge
  have hlen : off + len ≤ txBlob.length := by
    change startW.toNat + (endW.toNat - startW.toNat) ≤ txBlob.length
    rw [Nat.add_sub_cancel' hge]
    exact hok.hEndLeLen
  have hbal1 := bvtIterBalNez_fromEndSpan hintr teer hteer spC txBase outBase
    balBase chainIdW nW csaved txBlob balBytes outVals chainId i off len
    startW endW hentryI hentryT hretI hretT hbal hstart hlen htxLen hchain
    hiOut hcell hi61
  have hgs := cpsTripleWithin_seq_perm_same_cr (fun _ hq => hq) hguard hspan
  have hgse := cpsTripleWithin_seq_perm_same_cr (fun _ hq => hq) hgs hend
  have hgseS := cpsTripleWithin_seq_perm_same_cr (fun _ hq => hq) hgse hsetup
  have hfull := cpsTripleWithin_seq_perm_same_cr (fun _ hq => hq) hgseS hbal1
  -- nOneIterSteps is definitionally the composed sum.
  exact hfull

/-! ## Loop induction: LoopGuard@i=0 → postOk via exit at i=n -/

/-- Remaining-iteration fuel: exit (18) at 0, else one-iter + rest. -/
def nLoopFrom : Nat → Nat
  | 0     => 18
  | r + 1 => nOneIterSteps + nLoopFrom r

private theorem outVals_getElem_bang
    {outVals : List Nat} {i : Nat} (hi : i < outVals.length) :
    outVals[i]! = outVals[i] := getElem!_pos outVals i hi

set_option maxRecDepth 8000 in
/-- Full loop bal=0 from index `i` under remaining fuel. -/
theorem bvtLoopFrom_bal0
    (hintr : IntrinsicAssumed fullCode)
    (sp0 spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (teer : TeerApplied)
    (txs : List (List (BitVec 8))) (txBlob : List (BitVec 8))
    (outVals : List Nat) (balBytes : List (BitVec 8))
    (chainId n : Nat)
    (hbgv : BgvOffsetAssumed fullCode)
    (hAllOk : ∀ i, i < n → IterOk txBlob n i)
    (hAllLen : n ≤ outVals.length)
    (hAllCell : ∀ i, i < n →
      outVals[i]! = pureIntrinsicStateGasSuccess)
    (hnLe61 : n ≤ 2 ^ 61)
    (htxAlign : txBase.toNat % 8 = 0)
    (hnW : nW = BitVec.ofNat 64 n)
    (hentry : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hretI : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12))
    (hret : csaved.ra &&& ~~~(1 : Word) = csaved.ra)
    (hsucc : successCells teer txs balBytes chainId false outVals) :
    ∀ (f i : Nat), n - i ≤ f → i ≤ n →
      cpsTripleWithin (nLoopFrom (n - i)) LoopGuard csaved.ra fullCode
        (LoopInv spC txBase outBase (0 : Word) chainIdW nW csaved txBlob outVals
          balBytes false i)
        (postOk sp0 spC txBase outBase (0 : Word) csaved teer txs txBlob balBytes
          chainId false outVals) := by
  intro f
  induction f with
  | zero =>
    intro i hle hi
    have hi_eq : i = n := by omega
    rw [hi_eq, Nat.sub_self, nLoopFrom]
    have hexit0 := bvtExitOk sp0 spC txBase outBase (0 : Word) chainIdW nW
      csaved teer txs txBlob outVals balBytes chainId false n hnW hspC hret hsucc
    exact cpsTripleWithin_extend_code bvt_mono hexit0
  | succ f ih =>
    intro i hle hi
    by_cases hi_eq : i = n
    · rw [hi_eq, Nat.sub_self, nLoopFrom]
      have hexit0 := bvtExitOk sp0 spC txBase outBase (0 : Word) chainIdW nW
        csaved teer txs txBlob outVals balBytes chainId false n hnW hspC hret hsucc
      exact cpsTripleWithin_extend_code bvt_mono hexit0
    · have hi_lt : i < n := by omega
      have hrem : n - i = (n - (i + 1)) + 1 := by omega
      rw [hrem, nLoopFrom]
      have hok := hAllOk i hi_lt
      have hiOut : i < outVals.length := Nat.lt_of_lt_of_le hi_lt hAllLen
      have hcell : outVals[i] = pureIntrinsicStateGasSuccess := by
        have := hAllCell i hi_lt
        rwa [outVals_getElem_bang hiOut] at this
      have hi61 : i < 2 ^ 61 := Nat.lt_of_lt_of_le hi_lt hnLe61
      have hone := bvtIterOne_bal0 hintr spC txBase outBase chainIdW nW
        csaved txBlob outVals balBytes n i hbgv hok htxAlign hnW hentry hretI
        hiOut hcell hi61
      have htail := ih (i + 1) (by omega) (by omega)
      exact cpsTripleWithin_seq_perm_same_cr (fun _ hq => hq) hone htail

set_option maxRecDepth 8000 in
/-- Loop from i=0 bal=0 → postOk. -/
theorem bvtLoop_bal0
    (hintr : IntrinsicAssumed fullCode)
    (sp0 spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (teer : TeerApplied)
    (txs : List (List (BitVec 8))) (txBlob : List (BitVec 8))
    (outVals : List Nat) (balBytes : List (BitVec 8))
    (chainId n : Nat)
    (hbgv : BgvOffsetAssumed fullCode)
    (hAllOk : ∀ i, i < n → IterOk txBlob n i)
    (hAllLen : n ≤ outVals.length)
    (hAllCell : ∀ i, i < n →
      outVals[i]! = pureIntrinsicStateGasSuccess)
    (hnLe61 : n ≤ 2 ^ 61)
    (htxAlign : txBase.toNat % 8 = 0)
    (hnW : nW = BitVec.ofNat 64 n)
    (hentry : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hretI : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12))
    (hret : csaved.ra &&& ~~~(1 : Word) = csaved.ra)
    (hsucc : successCells teer txs balBytes chainId false outVals) :
    cpsTripleWithin (nLoopFrom n) LoopGuard csaved.ra fullCode
      (LoopInv spC txBase outBase (0 : Word) chainIdW nW csaved txBlob outVals
        balBytes false 0)
      (postOk sp0 spC txBase outBase (0 : Word) csaved teer txs txBlob balBytes
        chainId false outVals) := by
  have h := bvtLoopFrom_bal0 hintr sp0 spC txBase outBase chainIdW nW
    csaved teer txs txBlob outVals balBytes chainId n hbgv hAllOk hAllLen
    hAllCell hnLe61 htxAlign hnW hentry hretI hspC hret hsucc n 0
    (by omega) (by omega)
  simpa using h

/-! ## bal≠0 loop: outVals mutates; `finalOut` is the success model array -/

/-- Charge written at index `j` under SSZ table offsets (matches one-iter). -/
def iterCharge (teer : TeerApplied) (txBlob balBytes : List (BitVec 8))
    (chainId n j : Nat) : Nat :=
  let startW := leU32 txBlob (4 * j)
  let endW :=
    if j + 1 = n then BitVec.ofNat 64 txBlob.length
    else leU32 txBlob (4 * (j + 1))
  let off := startW.toNat
  let len := endW.toNat - startW.toNat
  teer ((txBlob.drop off).take len) balBytes chainId (j + 1)

/-- Pointwise list equality from bang-get. -/
private theorem list_eq_of_getElem!_eq {α : Type _} [Inhabited α]
    (l₁ l₂ : List α) (hlen : l₁.length = l₂.length)
    (h : ∀ j, j < l₁.length → l₁[j]! = l₂[j]!) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro j hj1 hj2
  have hbang := h j hj1
  have h1 : l₁[j]! = l₁[j] := getElem!_pos l₁ j hj1
  have h2 : l₂[j]! = l₂[j] := getElem!_pos l₂ j hj2
  exact h1.symm.trans (hbang.trans h2)

/-- `getElem!` after `List.set` at the same index. -/
private theorem getElem!_set_self (l : List Nat) (i : Nat) (a : Nat)
    (hi : i < l.length) : (l.set i a)[i]! = a := by
  have hlen : i < (l.set i a).length := by simpa [List.length_set] using hi
  have hpos : (l.set i a)[i]! = (l.set i a)[i] := getElem!_pos _ i hlen
  rw [hpos, List.getElem_set_self]

/-- `getElem!` after `List.set` at a different index. -/
private theorem getElem!_set_ne (l : List Nat) (i j : Nat) (a : Nat)
    (hne : i ≠ j) (hj : j < l.length) : (l.set i a)[j]! = l[j]! := by
  have hlen : j < (l.set i a).length := by simpa [List.length_set] using hj
  have hpos : (l.set i a)[j]! = (l.set i a)[j] := getElem!_pos _ j hlen
  have hpos0 : l[j]! = l[j] := getElem!_pos l j hj
  rw [hpos, hpos0, List.getElem_set_ne hne]

set_option maxRecDepth 8000 in
/-- bal≠0 loop from index `i` with current `outVals` evolving toward `finalOut`.
    Requires `finalOut.length = n` so exit equality is exactly the written prefix. -/
theorem bvtLoopFrom_balNez
    (hintr : IntrinsicAssumed fullCode)
    (teer : TeerApplied) (hteer : TeerAssumed fullCode teer)
    (sp0 spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved)
    (txs : List (List (BitVec 8))) (txBlob balBytes : List (BitVec 8))
    (finalOut : List Nat) (chainId n : Nat)
    (hbgv : BgvOffsetAssumed fullCode)
    (hAllOk : ∀ i, i < n → IterOk txBlob n i)
    (hFinalLen : finalOut.length = n)
    (hWrite : ∀ j, j < n →
      finalOut[j]! =
        pureIntrinsicStateGasSuccess + iterCharge teer txBlob balBytes chainId n j)
    (hnLe61 : n ≤ 2 ^ 61)
    (htxAlign : txBase.toNat % 8 = 0)
    (hnW : nW = BitVec.ofNat 64 n)
    (hentryI : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hentryT : hteer.entry =
      (GuestAddrs.tx_eip7702_existing_authority_refund : Word))
    (hretI : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hretT : (LinkTeer &&& ~~~(1 : Word)) = LinkTeer)
    (hbal : balBase ≠ 0)
    (hchain : chainIdW = BitVec.ofNat 64 chainId)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12))
    (hret : csaved.ra &&& ~~~(1 : Word) = csaved.ra)
    (hsucc : successCells teer txs balBytes chainId true finalOut) :
    ∀ (f idx : Nat) (outVals : List Nat),
      n - idx ≤ f → idx ≤ n →
      outVals.length = n →
      (∀ j, j < idx → outVals[j]! = finalOut[j]!) →
      (∀ j, idx ≤ j → j < n → outVals[j]! = pureIntrinsicStateGasSuccess) →
      cpsTripleWithin (nLoopFrom (n - idx)) LoopGuard csaved.ra fullCode
        (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes true idx)
        (postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
          chainId true finalOut) := by
  intro f
  induction f with
  | zero =>
    intro idx outVals hle hi hlen hpre _hrest
    have hi_eq : idx = n := by omega
    have heq : outVals = finalOut := by
      apply list_eq_of_getElem!_eq outVals finalOut (by rw [hlen, hFinalLen])
      intro j hj
      have hj' : j < n := by rwa [hlen] at hj
      have hbang := hpre j (by omega)
      simpa [hi_eq] using hbang
    rw [hi_eq, Nat.sub_self, nLoopFrom, heq]
    have hexit0 := bvtExitOk sp0 spC txBase outBase balBase chainIdW nW
      csaved teer txs txBlob finalOut balBytes chainId true n hnW hspC hret hsucc
    exact cpsTripleWithin_extend_code bvt_mono hexit0
  | succ f ih =>
    intro idx outVals hle hi hlen hpre hrest
    by_cases hi_eq : idx = n
    · have heq : outVals = finalOut := by
        apply list_eq_of_getElem!_eq outVals finalOut (by rw [hlen, hFinalLen])
        intro j hj
        have hj' : j < n := by rwa [hlen] at hj
        simpa [hi_eq] using hpre j (by omega)
      rw [hi_eq, Nat.sub_self, nLoopFrom, heq]
      have hexit0 := bvtExitOk sp0 spC txBase outBase balBase chainIdW nW
        csaved teer txs txBlob finalOut balBytes chainId true n hnW hspC hret hsucc
      exact cpsTripleWithin_extend_code bvt_mono hexit0
    · have hi_lt : idx < n := by omega
      have hrem : n - idx = (n - (idx + 1)) + 1 := by omega
      rw [hrem, nLoopFrom]
      have hok := hAllOk idx hi_lt
      have hiOut : idx < outVals.length := by rw [hlen]; exact hi_lt
      have hcell : outVals[idx] = pureIntrinsicStateGasSuccess := by
        have := hrest idx (Nat.le_refl _) hi_lt
        rwa [outVals_getElem_bang hiOut] at this
      have hi61 : idx < 2 ^ 61 := Nat.lt_of_lt_of_le hi_lt hnLe61
      have hone := bvtIterOne_balNez hintr teer hteer spC txBase outBase balBase
        chainIdW nW csaved txBlob balBytes outVals chainId n idx hbgv hok
        htxAlign hnW hentryI hentryT hretI hretT hbal hchain hiOut hcell hi61
      let startW := leU32 txBlob (4 * idx)
      let endW := hok.endW
      let off := startW.toNat
      let lenC := endW.toNat - startW.toNat
      let chargeNat := teer ((txBlob.drop off).take lenC) balBytes chainId (idx + 1)
      let outVals' := outVals.set idx (pureIntrinsicStateGasSuccess + chargeNat)
      have hone' :
          cpsTripleWithin nOneIterSteps LoopGuard LoopGuard fullCode
            (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals
              balBytes true idx)
            (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals'
              balBytes true (idx + 1)) := by
        simpa [startW, endW, off, lenC, chargeNat, outVals'] using hone
      have hlen' : outVals'.length = n := by
        simpa [outVals', List.length_set] using hlen
      have hpre' : ∀ j, j < idx + 1 → outVals'[j]! = finalOut[j]! := by
        intro j hj
        rcases (by omega : j < idx ∨ j = idx) with hlt | heq
        · have hjOut : j < outVals.length := by rw [hlen]; omega
          have hne : idx ≠ j := by omega
          have hset := getElem!_set_ne outVals idx j
            (pureIntrinsicStateGasSuccess + chargeNat) hne hjOut
          exact hset.trans (hpre j hlt)
        · -- j = idx: written cell equals finalOut[idx]
          have hbang := getElem!_set_self outVals idx
            (pureIntrinsicStateGasSuccess + chargeNat) hiOut
          have hw := hWrite idx hi_lt
          have hcharge :
              chargeNat = iterCharge teer txBlob balBytes chainId n idx := by
            simp only [iterCharge, chargeNat, startW, endW, off, lenC, hok.hEnd]
          have hcellF :
              finalOut[idx]! = pureIntrinsicStateGasSuccess + chargeNat := by
            rw [hw, hcharge]
          -- outVals'[idx]! = charge cell = finalOut[idx]!
          calc
            outVals'[j]! = outVals'[idx]! := by rw [heq]
            _ = pureIntrinsicStateGasSuccess + chargeNat := by
              simpa [outVals'] using hbang
            _ = finalOut[idx]! := hcellF.symm
            _ = finalOut[j]! := by rw [heq]
      have hrest' : ∀ j, idx + 1 ≤ j → j < n →
          outVals'[j]! = pureIntrinsicStateGasSuccess := by
        intro j hj1 hj2
        have hjOut : j < outVals.length := by rw [hlen]; exact hj2
        have hne : idx ≠ j := by omega
        have hset := getElem!_set_ne outVals idx j
          (pureIntrinsicStateGasSuccess + chargeNat) hne hjOut
        exact hset.trans (hrest j (by omega) hj2)
      have htail := ih (idx + 1) outVals' (by omega) (by omega) hlen' hpre' hrest'
      exact cpsTripleWithin_seq_perm_same_cr (fun _ hq => hq) hone' htail

set_option maxRecDepth 8000 in
/-- Loop from idx=0 bal≠0 with pure initial cells → postOk on finalOut. -/
theorem bvtLoop_balNez
    (hintr : IntrinsicAssumed fullCode)
    (teer : TeerApplied) (hteer : TeerAssumed fullCode teer)
    (sp0 spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved)
    (txs : List (List (BitVec 8))) (txBlob balBytes : List (BitVec 8))
    (finalOut outVals0 : List Nat) (chainId n : Nat)
    (hbgv : BgvOffsetAssumed fullCode)
    (hAllOk : ∀ i, i < n → IterOk txBlob n i)
    (hFinalLen : finalOut.length = n)
    (hWrite : ∀ j, j < n →
      finalOut[j]! =
        pureIntrinsicStateGasSuccess + iterCharge teer txBlob balBytes chainId n j)
    (hnLe61 : n ≤ 2 ^ 61)
    (htxAlign : txBase.toNat % 8 = 0)
    (hnW : nW = BitVec.ofNat 64 n)
    (hentryI : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hentryT : hteer.entry =
      (GuestAddrs.tx_eip7702_existing_authority_refund : Word))
    (hretI : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hretT : (LinkTeer &&& ~~~(1 : Word)) = LinkTeer)
    (hbal : balBase ≠ 0)
    (hchain : chainIdW = BitVec.ofNat 64 chainId)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12))
    (hret : csaved.ra &&& ~~~(1 : Word) = csaved.ra)
    (hsucc : successCells teer txs balBytes chainId true finalOut)
    (hlen0 : outVals0.length = n)
    (hrest0 : ∀ j, j < n → outVals0[j]! = pureIntrinsicStateGasSuccess) :
    cpsTripleWithin (nLoopFrom n) LoopGuard csaved.ra fullCode
      (LoopInv spC txBase outBase balBase chainIdW nW csaved txBlob outVals0
        balBytes true 0)
      (postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
        chainId true finalOut) := by
  have h := bvtLoopFrom_balNez hintr teer hteer sp0 spC txBase outBase balBase
    chainIdW nW csaved txs txBlob balBytes finalOut chainId n hbgv hAllOk
    hFinalLen hWrite hnLe61 htxAlign hnW hentryI hentryT hretI hretT hbal hchain
    hspC hret hsucc n 0 outVals0 (by omega) (by omega) hlen0
    (fun j hj => False.elim (Nat.not_lt_zero j hj))
    (fun j _hj hj2 => hrest0 j hj2)
  simpa using h

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
