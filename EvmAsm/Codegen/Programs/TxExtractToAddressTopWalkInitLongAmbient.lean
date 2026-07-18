/-
  Ambient dual: long walk_init fromTypeLoad + s5s6 (regionBase/loadPtr split).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitNorm
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInitAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNextAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec
open EvmAsm.EL.RLP

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

/-- Ambient long cursor (base is regionBase; listOff is absolute). -/
def longWalkCursorAmbient (regionBase : Word) (bs : List (BitVec 8))
    (listOff : Nat) (hoff : listOff < bs.length) : Word :=
  (regionBase + BitVec.ofNat 64 listOff) +
    (((bs[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
      signExtend12 (1 : BitVec 12))

def longWalkEndAmbient (regionBase listLen : Word) (listOff : Nat) : Word :=
  (regionBase + BitVec.ofNat 64 listOff) + listLen

set_option maxRecDepth 8000 in
/-- WalkInitJalPc → LinkWalkInit long path; post ambient ** common ** LongOkRegs. -/
theorem extractWalkInitCall_long_fromTypeLoad_ambient
    (regionBase loadPtr lenW : Word) (bs : List (BitVec 8)) (off len : Nat)
    (old1 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hsalign : regionBase.toNat % 8 = 0)
    (_hbound : off + len ≤ bs.length)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < bs.length)
    (hover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hspan : regionBase.toNat +
        (off + (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) < 2 ^ 64)
    (hlen : (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xf8 : Word) = true)
    (hllen : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
      ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64 - (0xf7 : Word)).toNat ≤ bs.length)
    (hlover : regionBase.toNat +
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k <
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
            ).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 + k)) = true)
    (hoff1 : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 <
      bs.length)
    (h_fits : ¬ BitVec.ult
        ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
        ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1]'hoff1
        ).zeroExtend 64 ≠ (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
        ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
            ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
                ).zeroExtend 64 - (0xf7 : Word)).toNat))
      = (regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    cpsTripleWithin
      (1 + (7 * ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64 - (0xf7 : Word)).toNat + 25))
      WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31)
      (walkInitAmbient loadPtr lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1
          (teerTxTypeDispatch (txSlice bs off len)).2.2 **
        extractWalkInitCommon regionBase bs **
        extractWalkInitLongOkRegs regionBase
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          bs (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) hoff) := by
  set inner := (teerTxTypeDispatch (txSlice bs off len)).2.2 with h_inner
  set typeW := (teerTxTypeDispatch (txSlice bs off len)).2.1 with h_type
  set listOff := ambientAbsOff off inner.toNat with h_listOff
  set listLen := lenW - inner with h_listLen
  have h_a0 : loadPtr + inner = regionBase + BitVec.ofNat 64 listOff := by
    simp only [listOff, ambientAbsOff]
    exact loadPtr_add_inner_eq_abs regionBase loadPtr inner off hptr (by
      simpa only [inner, h_inner] using hspan)
  -- peels rightmost: x31, x29, x28, x12, x7, x6
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x31)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29)
      (fun t6Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** (.x31 ↦ᵣ t6Old))
      (fun t4Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x28)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old))
      (fun t3Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old))
      (fun a2Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x7)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x6 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old) **
        (.x12 ↦ᵣ a2Old))
      (fun t2Old => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old) **
        (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old))
      (fun t1Old => ?_))
  -- long pure under set aliases
  have hlen' : listLen ≠ (0 : Word) := by simpa only [listLen, h_listLen] using hlen
  have h_ge' : ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
    simpa only [listOff, h_listOff, h_inner] using h_ge
  have h_ge_f8' : ¬ BitVec.ult ((bs[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
    simpa only [listOff, h_listOff, h_inner] using h_ge_f8
  have hllen' : listOff + 1 + ((bs[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat ≤
      bs.length := by
    simpa only [listOff, h_listOff, h_inner] using hllen
  have hlover' : regionBase.toNat + (listOff + 1 +
      ((bs[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 := by
    simpa only [listOff, h_listOff, h_inner] using hlover
  have hlvalid' : ∀ k, k < ((bs[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (regionBase + BitVec.ofNat 64 (listOff + 1 + k)) = true := by
    simpa only [listOff, h_listOff, h_inner] using hlvalid
  have hoff1' : listOff + 1 < bs.length := by
    simpa only [listOff, h_listOff, h_inner] using hoff1
  have h_fits' : ¬ BitVec.ult ((regionBase + BitVec.ofNat 64 listOff) + listLen)
      ((regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) = true := by
    simpa only [listOff, listLen, h_listOff, h_listLen, h_inner] using h_fits
  have h_llz' : (bs[listOff + 1]'hoff1').zeroExtend 64 ≠ (0 : Word) := by
    simpa only [listOff, h_listOff, h_inner] using h_llz
  have h_min' : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
      ((bs.drop (listOff + 1)).take
        ((bs[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat)))
      (56 : Word) = true := by
    simpa only [listOff, h_listOff, h_inner] using h_min
  have h_match' : ((regionBase + BitVec.ofNat 64 listOff) +
        (((bs[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12))) +
      BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop (listOff + 1)).take
        ((bs[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
    = (regionBase + BitVec.ofNat 64 listOff) + listLen := by
    simpa only [listOff, listLen, h_listOff, h_listLen, h_inner] using h_match
  have hcall := extractWalkInitCall_long_ambient regionBase listLen a2Old TeaInnerAddr t1Old t2Old
    t3Old t4Old inner t6Old bs listOff old1
    hsalign hoff hover hvalid hlen' h_ge' h_ge_f8' hllen' hlover' hlvalid' hoff1'
    h_fits' h_llz' h_min' h_match'
  have hcallF := cpsTripleWithin_frameR
    (walkInitAmbient loadPtr lenW typeW inner) (by pcf) hcall
  have hcallW : cpsTripleWithin
      (1 + (7 * ((bs[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 25))
      WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old) **
        (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old))
      (walkInitAmbient loadPtr lenW typeW inner **
        extractWalkInitLongPost regionBase listLen bs listOff hoff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [extractWalkInitPrest, walkInitAmbient, h_a0] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [walkInitAmbient] at hq ⊢
      xperm_hyp hq) hcallF
  -- LongPost → common ** LongOkRegs; align nSteps aliases
  have hcallW' : cpsTripleWithin
      (1 + (7 * ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64 - (0xf7 : Word)).toNat + 25))
      WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + inner)) ** (.x11 ↦ᵣ listLen) **
        (.x20 ↦ᵣ typeW) ** (.x30 ↦ᵣ inner) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ inner) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        (.x31 ↦ᵣ t6Old) ** (.x29 ↦ᵣ t4Old) ** (.x28 ↦ᵣ t3Old) **
        (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x6 ↦ᵣ t1Old))
      (walkInitAmbient loadPtr lenW typeW inner **
        extractWalkInitLongPost regionBase listLen bs listOff hoff) := by
    simpa only [listOff, h_listOff, h_inner] using hcallW
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [inner, typeW, listLen] at hp ⊢
    xperm_hyp hp) (fun h hq => by
    simp only [inner, typeW, listLen] at hq
    have hq' :
        (walkInitAmbient loadPtr lenW typeW inner **
          extractWalkInitLongPost regionBase listLen bs listOff hoff) h := by
      xperm_hyp hq
    obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
    have hconc := extractWalkInitLongPost_to_okConcrete regionBase listLen bs
      listOff hoff _ hpost
    obtain ⟨hL, hR, hd2, hu2, htemps, hRegs⟩ := hconc
    have hmid :
        (extractWalkInitCommon regionBase bs **
          extractWalkInitLongOkRegs regionBase listLen bs listOff hoff) hP := by
      have htemps' : (extractWalkInitCommon regionBase bs) hL := by
        simp only [extractWalkInitCommon] at htemps ⊢
        xperm_hyp htemps
      exact ⟨hL, hR, hd2, hu2, htemps', hRegs⟩
    have hmid' :
        (extractWalkInitCommon regionBase bs **
          extractWalkInitLongOkRegs regionBase (lenW - inner) bs
            (ambientAbsOff off inner.toNat) hoff) hP := by
      simpa only [listLen, listOff, h_listLen, h_listOff, h_inner] using hmid
    exact ⟨hA, hP, hd, hu, hamb, hmid'⟩) hcallW'

set_option maxRecDepth 8000 in
/-- Frame s5/s6 through long call_fromTypeLoad ambient. -/
theorem extractWalkInitCall_long_ok_framed_s5s6_ambient
    (regionBase loadPtr lenW : Word) (bs : List (BitVec 8)) (off len : Nat)
    (old1 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hsalign : regionBase.toNat % 8 = 0)
    (_hbound : off + len ≤ bs.length)
    (hoff : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < bs.length)
    (hover : regionBase.toNat +
        ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) = true)
    (hspan : regionBase.toNat +
        (off + (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) < 2 ^ 64)
    (hlen : (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2) ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64)
        (0xf8 : Word) = true)
    (hllen : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
      ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64 - (0xf7 : Word)).toNat ≤ bs.length)
    (hlover : regionBase.toNat +
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 +
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k <
        ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
            ).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 + k)) = true)
    (hoff1 : ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1 <
      bs.length)
    (h_fits : ¬ BitVec.ult
        ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2))
        ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1]'hoff1
        ).zeroExtend 64 ≠ (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE
        ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
          ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
              ).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE
          ((bs.drop (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat + 1)).take
            ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
                ).zeroExtend 64 - (0xf7 : Word)).toNat))
      = (regionBase + BitVec.ofNat 64
            (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat)) +
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) :
    cpsTripleWithin
      (1 + (7 * ((bs[ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat]'hoff
          ).zeroExtend 64 - (0xf7 : Word)).toNat + 25))
      WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x5 ↦ᵣ TeaInnerAddr) **
        (.x10 ↦ᵣ (loadPtr + (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x11 ↦ᵣ (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)) **
        (.x20 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (.x30 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        bytesRegion regionBase bs **
        (TeaTypeAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (TeaInnerAddr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
        regOwn .x21 ** regOwn .x22)
      (walkInitAmbient loadPtr lenW
          (teerTxTypeDispatch (txSlice bs off len)).2.1
          (teerTxTypeDispatch (txSlice bs off len)).2.2 **
        extractWalkInitCommon regionBase bs **
        extractWalkInitLongOkRegs regionBase
          (lenW - (teerTxTypeDispatch (txSlice bs off len)).2.2)
          bs (ambientAbsOff off (teerTxTypeDispatch (txSlice bs off len)).2.2.toNat) hoff **
        regOwn .x21 ** regOwn .x22) := by
  have h0 := extractWalkInitCall_long_fromTypeLoad_ambient
    regionBase loadPtr lenW bs off len old1 hptr hsalign _hbound
    hoff hover hvalid hspan hlen h_ge h_ge_f8 hllen hlover hlvalid hoff1
    h_fits h_llz h_min h_match
  have hF := cpsTripleWithin_frameR (regOwn .x21 ** regOwn .x22) (by pcf) h0
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms extractWalkInitCall_long_fromTypeLoad_ambient
#print axioms extractWalkInitCall_long_ok_framed_s5s6_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
