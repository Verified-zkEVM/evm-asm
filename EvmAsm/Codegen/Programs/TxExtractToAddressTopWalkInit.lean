/-
  Extract mid: framed rlp_walk_init after type+load
  WalkInitJalPc (E+144) → LinkWalkInit (E+148), 9-way leaf post.

  Residual: select a2=0 success arm under extractSuccess + BNE + save cursor.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressLoadType
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

local macro "pcf" : tactic => `(tactic|
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_emp
    | exact pcFree_pure
    | exact bytesRegion_pcFree _ _)

/-- Ambient framed across walk_init (not in leaf prest). -/
def walkInitAmbient (txBase lenW typeW innerW : Word) : Assertion :=
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
    (.x20 ↦ᵣ typeW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16

private theorem walkInitAmbient_pcFree (txBase lenW typeW innerW : Word) :
    (walkInitAmbient txBase lenW typeW innerW).pcFree := by
  unfold walkInitAmbient; pcf

set_option maxRecDepth 8000 in
/-- Walk_init call matching typeThenLoad post shape (inner = teer.2.2).
    Peels regOwn temps; frames s0/s1/s4/tea/stable. 9-way post residual. -/
theorem extractWalkInitCall_fromTypeLoad
    (txBase lenW : Word) (txBytes : List (BitVec 8))
    (old1 : Word)
    (hsalign : txBase.toNat % 8 = 0)
    (hoff : (teerTxTypeDispatch txBytes).2.2.toNat < txBytes.length)
    (hover : txBase.toNat + (teerTxTypeDispatch txBytes).2.2.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess
      (txBase + BitVec.ofNat 64 (teerTxTypeDispatch txBytes).2.2.toNat) = true)
    (hll_len : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      (teerTxTypeDispatch txBytes).2.2.toNat + 1 +
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
          (0xf7 : Word)).toNat
        ≤ txBytes.length)
    (hll_over : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      txBase.toNat + ((teerTxTypeDispatch txBytes).2.2.toNat + 1 +
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
          (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hll_valid : ¬ BitVec.ult
        ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64)
        (0xf8 : Word) = true →
      ∀ k, k < ((txBytes[(teerTxTypeDispatch txBytes).2.2.toNat]'hoff).zeroExtend 64 -
          (0xf7 : Word)).toNat →
        isValidByteAccess (txBase + BitVec.ofNat 64
          ((teerTxTypeDispatch txBytes).2.2.toNat + 1 + k)) = true) :
    cpsTripleWithin (1 + 81) WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + (teerTxTypeDispatch txBytes).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch txBytes).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch txBytes).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch txBytes).2.2) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31)
      (walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
        extractWalkInitPost txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
          txBytes (teerTxTypeDispatch txBytes).2.2.toNat hoff) := by
  set inner := (teerTxTypeDispatch txBytes).2.2 with h_inner
  set typeW := (teerTxTypeDispatch txBytes).2.1 with h_type
  set listOff := inner.toNat with h_listOff
  set listLen := lenW - inner with h_listLen
  have h_off : BitVec.ofNat 64 listOff = inner := by
    simp only [listOff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h_a0 : txBase + inner = txBase + BitVec.ofNat 64 listOff := by rw [h_off]
  -- peels (rightmost first): x31, x29, x28, x12, x7, x6
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x31)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29)
      (fun t6Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** (.x31 ↦ᵣ t6Old))
      (fun t4Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old))
      (fun t3Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old))
      (fun a2Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old) **
        (.x12 ↦ᵣ a2Old))
      (fun t2Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old) **
        (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old))
      (fun t1Old => ?_))
  have hcall := extractWalkInitCall txBase listLen a2Old TeaInnerAddr t1Old t2Old
    t3Old t4Old inner t6Old txBytes listOff old1
    hsalign hoff hover hvalid hll_len hll_over hll_valid
  have hcallF := cpsTripleWithin_frameR
    (walkInitAmbient txBase lenW typeW inner) (by pcf) hcall
  -- Align x10 form via h_a0, then permute to prest ** ambient
  have hcallW : cpsTripleWithin (1 + 81) WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (txBase + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion txBase txBytes **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old) **
        (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old))
      (walkInitAmbient txBase lenW typeW inner **
        extractWalkInitPost txBase listLen txBytes listOff hoff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkInitPrest, walkInitAmbient, h_a0] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [walkInitAmbient] at hq ⊢
      xperm_hyp hq) hcallF
  exact cpsTripleWithin_weaken (fun _ hp => by
    simp only [inner, typeW, listLen] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [inner, typeW, listLen] at hq ⊢
    xperm_hyp hq) hcallW

#print axioms extractWalkInitCall_fromTypeLoad

end EvmAsm.Codegen.TxExtractToAddressSpec
