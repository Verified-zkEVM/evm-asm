/-
  20B copy path with content owned inside `bytesRegion` (no separate contentDwords).
  Split three dwords from the region, reuse extractCopyPath, rejoin.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressHaveFieldBody
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen

/-- Content dwords packed from `txBytes` at dword index `q` (offset `8*q`). -/
def contentWordsAt (txBytes : List (BitVec 8)) (q : Nat) : Word × Word × Word :=
  (packBytes ((txBytes.drop (8 * q)).take 8),
    packBytes ((txBytes.drop (8 * q + 8)).take 8),
    packBytes ((txBytes.drop (8 * q + 16)).take 8))

/-- When `8*q` does not wrap the base, content pointer toNat is base+8q. -/
theorem contentPtr_toNat (txBase : Word) (q : Nat)
    (hover : txBase.toNat + 8 * q < 2 ^ 64) :
    (txBase + BitVec.ofNat 64 (8 * q)).toNat = txBase.toNat + 8 * q := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Content pointer is dword-aligned when base is. -/
theorem contentPtr_align (txBase : Word) (q : Nat)
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + 8 * q < 2 ^ 64) :
    (txBase + BitVec.ofNat 64 (8 * q)).toNat % 8 = 0 := by
  rw [contentPtr_toNat txBase q hover]
  omega

/-- Address of dword `q+1` relative to content at dword `q`. -/
theorem contentPtr_add8 (txBase : Word) (q : Nat)
    (hover : txBase.toNat + 8 * q + 8 < 2 ^ 64) :
    txBase + BitVec.ofNat 64 (8 * q + 8) =
      (txBase + BitVec.ofNat 64 (8 * q)) + (8 : Word) := by
  apply BitVec.eq_of_toNat_eq
  have h8 : (8 : Word).toNat = 8 := by decide
  have hL : (txBase + BitVec.ofNat 64 (8 * q + 8)).toNat =
      txBase.toNat + (8 * q + 8) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hR : ((txBase + BitVec.ofNat 64 (8 * q)) + (8 : Word)).toNat =
      txBase.toNat + 8 * q + 8 := by
    have hbase : txBase.toNat + 8 * q < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, contentPtr_toNat txBase q hbase, h8]
    omega
  omega

/-- Address of dword `q+2` relative to content at dword `q`. -/
theorem contentPtr_add16 (txBase : Word) (q : Nat)
    (hover : txBase.toNat + 8 * q + 16 < 2 ^ 64) :
    txBase + BitVec.ofNat 64 (8 * q + 16) =
      (txBase + BitVec.ofNat 64 (8 * q)) + (16 : Word) := by
  apply BitVec.eq_of_toNat_eq
  have h16 : (16 : Word).toNat = 16 := by decide
  have hL : (txBase + BitVec.ofNat 64 (8 * q + 16)).toNat =
      txBase.toNat + (8 * q + 16) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hR : ((txBase + BitVec.ofNat 64 (8 * q)) + (16 : Word)).toNat =
      txBase.toNat + 8 * q + 16 := by
    have hbase : txBase.toNat + 8 * q < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, contentPtr_toNat txBase q hbase, h16]
    omega
  omega

set_option maxRecDepth 8000 in
/-- Copy path AfterBne20Nt → EpiRestore reading 20B from `bytesRegion` at dword `q`.
    Content cells are a partition of the region (no double-own). classical-3. -/
theorem extractCopyPath_region
    (txBase toBuf isCreationPtr t0Old a0Old old16 : Word)
    (txBytes : List (BitVec 8)) (q : Nat)
    (hq : 8 * q + 16 < txBytes.length)
    (halign : txBase.toNat % 8 = 0)
    (hcover : txBase.toNat + 8 * q + 16 < 2 ^ 64)
    (hcvalid : isValidMemAccess
      (txBase + BitVec.ofNat 64 (8 * q) + (16 : Word)) = true)
    (htalign : toBuf.toNat % 8 = 0)
    (htover : toBuf.toNat + 16 < 2 ^ 64)
    (htvalid : isValidMemAccess (toBuf + (16 : Word)) = true) :
    let contentPtr := txBase + BitVec.ofNat 64 (8 * q)
    let w0 := (contentWordsAt txBytes q).1
    let w1 := (contentWordsAt txBytes q).2.1
    let w2 := (contentWordsAt txBytes q).2.2
    cpsTripleWithin
      (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))
      AfterBne20Nt EpiRestore extractLinkedCode
      ((.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ a0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        memOwn toBuf ** memOwn (toBuf + 8) ** ((toBuf + 16) ↦ₘ old16) **
        memOwn isCreationPtr)
      ((.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
        ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
          (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
        (isCreationPtr ↦ₘ (0 : Word))) := by
  intro contentPtr w0 w1 w2
  have hptr : contentPtr = txBase + BitVec.ofNat 64 (8 * q) := rfl
  have hw0 : w0 = packBytes ((txBytes.drop (8 * q)).take 8) := rfl
  have hw1 : w1 = packBytes ((txBytes.drop (8 * q + 8)).take 8) := rfl
  have hw2 : w2 = packBytes ((txBytes.drop (8 * q + 16)).take 8) := rfl
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegion_dword_triple_at txBase txBytes q hq
  have hbase_q : txBase.toNat + 8 * q < 2 ^ 64 := by omega
  have hcalign : contentPtr.toNat % 8 = 0 := by
    rw [hptr]
    exact contentPtr_align txBase q halign hbase_q
  have hcover' : contentPtr.toNat + 16 < 2 ^ 64 := by
    rw [hptr, contentPtr_toNat txBase q hbase_q]
    omega
  have hcvalid' : isValidMemAccess (contentPtr + (16 : Word)) = true := by
    simpa [hptr, BitVec.add_assoc] using hcvalid
  have ha8 : txBase + BitVec.ofNat 64 (8 * q + 8) = contentPtr + 8 := by
    rw [hptr, contentPtr_add8 txBase q (by omega)]
  have ha16 : txBase + BitVec.ofNat 64 (8 * q + 16) = contentPtr + 16 := by
    rw [hptr, contentPtr_add16 txBase q hcover]
  have hsplit :
      bytesRegion txBase txBytes =
        (front ** ((contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) **
          ((contentPtr + 16) ↦ₘ w2) ** rest)) := by
    rw [heq, hw0, hw1, hw2, ← hptr, ha8, ha16]
  have hleaf := extractCopyPath contentPtr toBuf isCreationPtr t0Old a0Old
    w0 w1 w2 old16 hcalign hcover' hcvalid' htalign htover htvalid
  have hF := cpsTripleWithin_frameR (front ** rest)
    (pcFree_sepConj hf hr) hleaf
  refine cpsTripleWithin_weaken (fun st hp => by
    rw [hsplit] at hp
    xperm_hyp hp) (fun st hq => by
    have hq' :
        (((.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
          (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) ** ((contentPtr + 16) ↦ₘ w2) **
          (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
          ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
            (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
          (isCreationPtr ↦ₘ (0 : Word))) **
          (front ** rest)) st := by
      xperm_hyp hq
    have hq2 :
        ((.x31 ↦ᵣ contentPtr) ** (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
          (.x5 ↦ᵣ (extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (toBuf ↦ₘ w0) ** ((toBuf + 8) ↦ₘ w1) **
          ((toBuf + 16) ↦ₘ replaceWord32 old16 ((byteOffset (toBuf + 16)) / 4)
            (((extractWord32 w2 (byteOffset (contentPtr + 16) / 4)).zeroExtend 64).truncate 32)) **
          (isCreationPtr ↦ₘ (0 : Word)) **
          (front ** ((contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) **
            ((contentPtr + 16) ↦ₘ w2) ** rest))) st := by
      xperm_hyp hq'
    have hbr :
        (front ** ((contentPtr ↦ₘ w0) ** ((contentPtr + 8) ↦ₘ w1) **
          ((contentPtr + 16) ↦ₘ w2) ** rest)) = bytesRegion txBase txBytes := hsplit.symm
    rw [hbr] at hq2
    xperm_hyp hq2) hF

#print axioms extractCopyPath_region

end EvmAsm.Codegen.TxExtractToAddressSpec
