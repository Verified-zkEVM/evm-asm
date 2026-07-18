/-
  Extract mid: reshape walk_init 9-way post → a2=0 OK ∨ a2≠0 fail
  (HeaderFields `initOutcome_to_normalized` style; no extractSuccess pure yet).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitOk

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

/-- Temps + ra + bytes shared by all walk_init outcomes. -/
def extractWalkInitCommon (txBase : Word) (txBytes : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkInit) **
    bytesRegion txBase txBytes

/-- Normalized outcome: a2=0 OK (cursor/end) or a2≠0 fail. -/
def extractWalkInitOkFail : Assertion := fun h =>
  (∃ cursor endPtr : Word,
    ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word))) h) ∨
  (∃ status cursor endPtr : Word,
    (((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
      ⌜status ≠ (0 : Word)⌝) h))

/-- Peel pure from right-assoc `A ** B ** C ** ⌜P⌝` (HeaderFields style). -/
private theorem threeRegs_pure {A B C : Assertion} {P : Prop} :
    ∀ h, (A ** B ** C ** ⌜P⌝) h → P := by
  intro h hp
  extract_pure_deep hp
  exact hp.1

private theorem threeRegs_drop_pure {A B C : Assertion} {P : Prop} :
    ∀ h, (A ** B ** C ** ⌜P⌝) h → (A ** B ** C) h := by
  intro h hp
  extract_pure_deep hp
  -- extract_pure_deep yields ((A ** B) ** C) h; goal is right-assoc A ** B ** C
  have hp' : ((A ** B) ** C) h := hp.2
  xperm_hyp hp'

private theorem threeRegs_pure_mono {A B C : Assertion} {P Q : Prop}
    (himp : P → Q) : ∀ h, (A ** B ** C ** ⌜P⌝) h →
      (A ** B ** C ** ⌜Q⌝) h := by
  intro h hp
  extract_pure_deep hp
  rw [show (A ** B ** C ** ⌜Q⌝) = (((A ** B) ** C) ** ⌜Q⌝) by ac_rfl]
  exact (sepConj_pure_right h).2 ⟨hp.2, himp hp.1⟩

private theorem threeRegs_fail_status {cursor endPtr status : Word} {P : Prop}
    (hne : status ≠ (0 : Word)) :
    ∀ s, ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) ** ⌜P⌝) s →
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
        ⌜status ≠ (0 : Word)⌝) s := by
  intro s hp
  exact threeRegs_pure_mono (fun _ => hne) s hp

/-- 9-way leaf post → common ** (OK a2=0 ∨ fail a2≠0). -/
theorem extractWalkInitPost_to_okFail
    (txBase listLen : Word) (txBytes : List (BitVec 8))
    (listOff : Nat) (hoff : listOff < txBytes.length) :
    ∀ h, extractWalkInitPost txBase listLen txBytes listOff hoff h →
      (extractWalkInitCommon txBase txBytes ** extractWalkInitOkFail) h := by
  intro h hp
  simp only [extractWalkInitPost] at hp
  -- post = common-as-nested ** 9-way disj
  obtain ⟨h1, h2, hd, hu, hcom, hdisj⟩ := hp
  have hcom' : extractWalkInitCommon txBase txBytes h1 := by
    simp only [extractWalkInitCommon]
    xperm_hyp hcom
  refine ⟨h1, h2, hd, hu, hcom', ?_⟩
  simp only [extractWalkInitOkFail]
  rcases hdisj with h0 | h1a | hs | h3 | h4 | h5 | h6 | h7 | hl
  · refine Or.inr ⟨(2 : Word), txBase + BitVec.ofNat 64 listOff, (0 : Word), ?_⟩
    exact threeRegs_fail_status (status := (2 : Word)) (by decide) _ h0
  · refine Or.inr ⟨(1 : Word), txBase + BitVec.ofNat 64 listOff,
      (txBase + BitVec.ofNat 64 listOff) + listLen, ?_⟩
    exact threeRegs_fail_status (status := (1 : Word)) (by decide) _ h1a
  · refine Or.inl ⟨(txBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12),
      (txBase + BitVec.ofNat 64 listOff) + listLen, ?_⟩
    exact threeRegs_drop_pure _ hs
  · refine Or.inr ⟨(3 : Word), txBase + BitVec.ofNat 64 listOff,
      (txBase + BitVec.ofNat 64 listOff) + listLen, ?_⟩
    exact threeRegs_fail_status (status := (3 : Word)) (by decide) _ h3
  · refine Or.inr ⟨(4 : Word), txBase + BitVec.ofNat 64 listOff,
      (txBase + BitVec.ofNat 64 listOff) + listLen, ?_⟩
    exact threeRegs_fail_status (status := (4 : Word)) (by decide) _ h4
  · refine Or.inr ⟨(5 : Word), txBase + BitVec.ofNat 64 listOff,
      (txBase + BitVec.ofNat 64 listOff) + listLen, ?_⟩
    exact threeRegs_fail_status (status := (5 : Word)) (by decide) _ h5
  · refine Or.inr ⟨(6 : Word), txBase + BitVec.ofNat 64 listOff,
      (txBase + BitVec.ofNat 64 listOff) + listLen, ?_⟩
    exact threeRegs_fail_status (status := (6 : Word)) (by decide) _ h6
  · refine Or.inr ⟨(7 : Word), txBase + BitVec.ofNat 64 listOff,
      (txBase + BitVec.ofNat 64 listOff) + listLen, ?_⟩
    exact threeRegs_fail_status (status := (7 : Word)) (by decide) _ h7
  · refine Or.inl ⟨
      (txBase + BitVec.ofNat 64 listOff) +
        (((txBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)),
      (txBase + BitVec.ofNat 64 listOff) + listLen, ?_⟩
    exact threeRegs_drop_pure _ hl

set_option maxRecDepth 8000 in
/-- Walk_init call post weakened to common ** OkFail under ambient. -/
theorem extractWalkInitCall_fromTypeLoad_okFail
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
        extractWalkInitCommon txBase txBytes ** extractWalkInitOkFail) := by
  have h0 := extractWalkInitCall_fromTypeLoad txBase lenW txBytes old1
    hsalign hoff hover hvalid hll_len hll_over hll_valid
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    have hq' :
        (walkInitAmbient txBase lenW
            (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
          extractWalkInitPost txBase (lenW - (teerTxTypeDispatch txBytes).2.2)
            txBytes (teerTxTypeDispatch txBytes).2.2.toNat hoff) h := by
      xperm_hyp hq
    obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
    have hnorm := extractWalkInitPost_to_okFail txBase
      (lenW - (teerTxTypeDispatch txBytes).2.2) txBytes
      (teerTxTypeDispatch txBytes).2.2.toNat hoff _ hpost
    exact ⟨hA, hP, hd, hu, hamb, hnorm⟩) h0

/-- OK arm concrete: a2=0 with cursor/end under ambient+common. -/
def extractWalkInitOkConcrete (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) : Assertion :=
  walkInitAmbient txBase lenW typeW innerW **
    extractWalkInitCommon txBase txBytes **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word))

set_option maxRecDepth 8000 in
/-- From OkFail OK arm, BNE+save under ambient (peels s5/s6 via BneSave). -/
theorem extractWalkInitOk_bneSave
    (txBase lenW typeW innerW cursor endPtr : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + 1)) LinkWalkInit AfterSaveCursor extractLinkedCode
      (extractWalkInitOkConcrete txBase lenW typeW innerW cursor endPtr txBytes **
        regOwn .x21 ** regOwn .x22)
      (extractAfterSavePost txBase lenW typeW innerW cursor endPtr txBytes) := by
  have h0 := extractWalkInitBneSave txBase lenW typeW innerW cursor endPtr txBytes
  refine cpsTripleWithin_weaken (fun _ hp => by
    simp only [extractWalkInitOkConcrete, extractWalkInitCommon,
      walkInitAmbient, walkInitRest] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    simp only [extractAfterSavePost] at hq ⊢
    xperm_hyp hq) h0

set_option maxRecDepth 8000 in
/-- OK-exists pre: outer ∃cursor,end → AfterSave with ∃ post. -/
theorem extractWalkInitOkExists_bneSave
    (txBase lenW typeW innerW : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + 1)) LinkWalkInit AfterSaveCursor extractLinkedCode
      (fun h => ∃ cursor endPtr : Word,
        (extractWalkInitOkConcrete txBase lenW typeW innerW cursor endPtr txBytes **
          regOwn .x21 ** regOwn .x22) h)
      (fun h => ∃ cursor endPtr : Word,
        extractAfterSavePost txBase lenW typeW innerW cursor endPtr txBytes h) := by
  refine cpsTripleWithin_exists_pre_gen (fun cursor => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun endPtr => ?_)
  have h0 := extractWalkInitOk_bneSave txBase lenW typeW innerW cursor endPtr txBytes
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => ⟨cursor, endPtr, hq⟩) h0

/-- Pull `∃ c e, A c e` out of the left of a sep. -/
private theorem exists2_sep_left
    {A : Word → Word → Assertion} {R : Assertion} :
    ∀ h, ((fun s => ∃ c e : Word, A c e s) ** R) h →
      ∃ c e : Word, (A c e ** R) h := by
  intro h ⟨h1, h2, hd, hu, ⟨c, e, hA⟩, hR⟩
  exact ⟨c, e, h1, h2, hd, hu, hA, hR⟩

set_option maxRecDepth 8000 in
/-- Nested OkFail-OK arm + s5/s6 → AfterSave ∃. -/
theorem extractWalkInitOkNested_bneSave
    (txBase lenW typeW innerW : Word)
    (txBytes : List (BitVec 8)) :
    cpsTripleWithin (1 + (1 + 1)) LinkWalkInit AfterSaveCursor extractLinkedCode
      (walkInitAmbient txBase lenW typeW innerW **
        extractWalkInitCommon txBase txBytes **
        (fun s => ∃ cursor endPtr : Word,
          ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word))) s) **
        regOwn .x21 ** regOwn .x22)
      (fun h => ∃ cursor endPtr : Word,
        extractAfterSavePost txBase lenW typeW innerW cursor endPtr txBytes h) := by
  have h0 := extractWalkInitOkExists_bneSave txBase lenW typeW innerW txBytes
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) h0
  have hp' :
      ((walkInitAmbient txBase lenW typeW innerW **
          extractWalkInitCommon txBase txBytes) **
        ((fun s => ∃ cursor endPtr : Word,
            ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
              (.x12 ↦ᵣ (0 : Word))) s) **
          (regOwn .x21 ** regOwn .x22))) h := by
    xperm_hyp hp
  obtain ⟨h1, h2, hd, hu, hAC, hEO⟩ := hp'
  obtain ⟨cursor, endPtr, hregsOwns⟩ := exists2_sep_left h2 hEO
  -- hregsOwns : (regs ** (x21 ** x22)) h2
  refine ⟨cursor, endPtr, ?_⟩
  simp only [extractWalkInitOkConcrete]
  have hgoal :
      ((walkInitAmbient txBase lenW typeW innerW **
          extractWalkInitCommon txBase txBytes) **
        (((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word))) **
          (regOwn .x21 ** regOwn .x22))) h :=
    ⟨h1, h2, hd, hu, hAC, hregsOwns⟩
  xperm_hyp hgoal

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

set_option maxRecDepth 8000 in
/-- walk_init call_okFail framed with s5/s6 (regOwn x21/x22). -/
theorem extractWalkInitCall_okFail_framed_s5s6
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
        regOwn .x28 ** regOwn .x29 ** regOwn .x31 **
        regOwn .x21 ** regOwn .x22)
      (walkInitAmbient txBase lenW
          (teerTxTypeDispatch txBytes).2.1 (teerTxTypeDispatch txBytes).2.2 **
        extractWalkInitCommon txBase txBytes ** extractWalkInitOkFail **
        regOwn .x21 ** regOwn .x22) := by
  have h0 := extractWalkInitCall_fromTypeLoad_okFail txBase lenW txBytes old1
    hsalign hoff hover hvalid hll_len hll_over hll_valid
  have hF := cpsTripleWithin_frameR (regOwn .x21 ** regOwn .x22) (by pcf) h0
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

#print axioms extractWalkInitPost_to_okFail
#print axioms extractWalkInitCall_fromTypeLoad_okFail
#print axioms extractWalkInitOk_bneSave
#print axioms extractWalkInitOkExists_bneSave
#print axioms extractWalkInitOkNested_bneSave
#print axioms extractWalkInitCall_okFail_framed_s5s6

end EvmAsm.Codegen.TxExtractToAddressSpec
