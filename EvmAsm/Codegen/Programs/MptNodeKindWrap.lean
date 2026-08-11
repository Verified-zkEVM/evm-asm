/-
  Count-outcome peel (file-size split from Top) + body compose + ABI-frame
  wrap for `mpt_node_kind` (#11799 dep).
-/

import EvmAsm.Codegen.Programs.MptNodeKindTop
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.MptNodeKindSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpListCountItemsSAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-! peel eq2 → nth call → bodyPostEx. Fuel countEq2Fuel. -/
set_option maxRecDepth 8000 in
theorem count_eq2_outcome
    (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved) (ks : KindSaved)
    (listBase listLenW : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen : Word)
    (v11 v12 v13 v14 v20 v21 : Word)
    (R : Assertion) (hRp : R.pcFree)
    (hR : stackFree newSp 8 = (R ** stackFree newSp 6))
    (hs0 : cSaved.s0 = listBase) (hs1 : cSaved.s1 = listLenW)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (halign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hc : RlpListCountItemsSAsm.Result bytes listBase listLen (0 : Word)
      (BitVec.ofNat 64 2))
    (hpath : PathByteOk bytes listBase listLen oldOff oldLen) :
    cpsTripleWithin (countEq2Fuel listLen) (pc 9) (pc 48) fullCode
      (countPeelAmb newSp cSaved ks (0 : Word) (2 : Word) v11 v12
        oldOff oldLen v13 v14 v20 v21 listBase bytes R)
      (bodyPostExAny newSp ks listBase bytes listLen oldCount oldOff oldLen
        cSaved.s2 cSaved.s3 v20 v21) := by
  have hsetup := count_eq2_nth_setup newSp cSaved ks listBase listLenW bytes
    oldOff oldLen v11 v12 v13 v14 v20 v21 R hRp hs0 hs1
  have hcall := kind_nth_call_spec_within newSp listBase listLenW (pc 9)
    oldOff oldLen
    (eq2NthSaved listBase listLenW cSaved.s2 cSaved.s3 v20 v21)
    bytes listLen
    (countEq2NthCallF newSp ks)
    (countEq2NthCallF_pcFree newSp ks)
    hlistLenW halign hslack hover hvalid
  have hsetupW := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => countEq2_setup_to_nth_call_pre newSp ks listBase listLenW
      bytes oldOff oldLen cSaved.s2 cSaved.s3 v20 v21 R hR h hq) hsetup
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [eq2NthSaved, countEq2NthCallF] at hp ⊢
      xperm_chunked hp)
    hsetupW hcall
  have hout := nth_outcome newSp ks
    (eq2NthSaved listBase listLenW cSaved.s2 cSaved.s3 v20 v21)
    listBase bytes listLen oldCount oldOff oldLen (2 : Word)
    halign hover hvalid hc rfl hpath
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [eq2NthSaved, countEq2NthCallF] at hp ⊢
      xperm_chunked hp)
    c01 hout
  unfold countEq2Fuel
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      obtain ⟨kind, offW, lenW, hq'⟩ := hq
      exact ⟨kind, (2 : Word), offW, lenW, hq'⟩) c012

/-! Count return (any Result) → bodyPostEx. Fuel = max path (eq2). -/
set_option maxRecDepth 8000 in
theorem count_outcome
    (newSp : Word) (cSaved : RlpListCountItemsSAsm.Saved) (ks : KindSaved)
    (listBase listLenW : Word) (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen : Word)
    (v13 v14 v20 v21 : Word)
    (R : Assertion) (hRp : R.pcFree)
    (hR : stackFree newSp 8 = (R ** stackFree newSp 6))
    (hs0 : cSaved.s0 = listBase) (hs1 : cSaved.s1 = listLenW)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (halign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hpath : PathByteOk bytes listBase listLen oldOff oldLen) :
    cpsTripleWithin (countEq2Fuel listLen) (pc 9) (pc 48) fullCode
      (((.x1 ↦ᵣ (pc 9)) **
        RlpListCountItemsSAsm.callReturnResult newSp listBase MnkCount cSaved
          bytes listLen) **
        countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R)
      (bodyPostExAny newSp ks listBase bytes listLen oldCount oldOff oldLen
        cSaved.s2 cSaved.s3 v20 v21) := by
  refine cpsTripleWithin_countReturn_pre (N := countEq2Fuel listLen)
    (ret := pc 48) (X := pc 9)
    (F := countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R)
    (Q := bodyPostExAny newSp ks listBase bytes listLen oldCount oldOff oldLen
      cSaved.s2 cSaved.s3 v20 v21)
    newSp listBase MnkCount cSaved bytes listLen
    (fun status result v11 v12 hres => by
      cases hres with
      | fail hf =>
        have hfail := count_fail_outcome newSp cSaved ks listBase bytes listLen
          oldCount oldOff oldLen v11 v12 v13 v14 v20 v21 R hR hRp (.fail hf)
        -- After `fail`, status=1 and result=0 by constructor indices.
        refine cpsTripleWithin_mono_nSteps (by unfold countEq2Fuel; omega)
          (cpsTripleWithin_weaken
            (fun h hp => by
              have hp' :
                  (countPeelAmb newSp cSaved ks (1 : Word) (0 : Word)
                    v11 v12 oldOff oldLen v13 v14 v20 v21 listBase bytes R) h := by
                -- status/result are 1/0 after cases; simpa bridges Word numerals.
                simpa using hp
              simp only [countPeelAmb] at hp' ⊢
              xperm_chunked hp')
            (fun _ hq => ⟨3, (0 : Word), oldOff, oldLen, hq⟩) hfail)
      | ok count hc64 hSucc =>
        have hc : RlpListCountItemsSAsm.Result bytes listBase listLen (0 : Word)
            (BitVec.ofNat 64 count) := .ok count hc64 hSucc
        by_cases h17 : count = 17
        · subst h17
          have hbr := count_branch_outcome newSp cSaved ks listBase bytes listLen
            oldCount oldOff oldLen v11 v12 v13 v14 v20 v21 R hR hRp hc
          refine cpsTripleWithin_mono_nSteps (by unfold countEq2Fuel; omega)
            (cpsTripleWithin_weaken
              (fun h hp => by
                have hp' :
                    (countPeelAmb newSp cSaved ks (0 : Word) (17 : Word)
                      v11 v12 oldOff oldLen v13 v14 v20 v21 listBase bytes R) h := by
                  simpa using hp
                simp only [countPeelAmb] at hp' ⊢
                xperm_chunked hp')
              (fun _ hq => ⟨0, (17 : Word), oldOff, oldLen, hq⟩) hbr)
        · by_cases h2 : count = 2
          · subst h2
            have heq2 := count_eq2_outcome newSp cSaved ks listBase listLenW
              bytes listLen oldCount oldOff oldLen v11 v12 v13 v14 v20 v21
              R hRp hR hs0 hs1 hlistLenW halign hslack hover hvalid hc hpath
            exact cpsTripleWithin_weaken
              (fun h hp => by
                have hp' :
                    (countPeelAmb newSp cSaved ks (0 : Word) (2 : Word)
                      v11 v12 oldOff oldLen v13 v14 v20 v21 listBase bytes R) h := by
                  simpa using hp
                simp only [countPeelAmb] at hp' ⊢
                xperm_chunked hp')
              (fun _ hq => hq) heq2
          · have hbad := count_badArity_outcome newSp cSaved ks listBase bytes
              listLen oldCount oldOff oldLen v11 v12 v13 v14 v20 v21
              count hc64 R hR hRp hc h17 h2
            refine cpsTripleWithin_mono_nSteps (by unfold countEq2Fuel; omega)
              (cpsTripleWithin_weaken
                (fun h hp => by
                  have hp' :
                      (countPeelAmb newSp cSaved ks (0 : Word)
                        (BitVec.ofNat 64 count) v11 v12
                        oldOff oldLen v13 v14 v20 v21 listBase bytes R) h := by
                    simpa using hp
                  simp only [countPeelAmb] at hp' ⊢
                  xperm_chunked hp')
                (fun _ hq =>
                  ⟨3, BitVec.ofNat 64 count, oldOff, oldLen, hq⟩) hbad))

/-! ## Body fuel: setup(4) + count call + count_outcome (eq2 max) -/

def bodyFuel (listLen : Nat) : Nat :=
  4 + (1 + (8 + (85 + (93 * (listLen + 1) + 3) + 7))) + countEq2Fuel listLen

def countCallFuel (listLen : Nat) : Nat :=
  1 + (8 + (85 + (93 * (listLen + 1) + 3) + 7))

/-- Count-call saved regs after setup: s0/s1 hold list ABI; s2/s3 ambient. -/
def bodyCountSaved (listBase listLenW v18 v19 : Word) : RlpListCountItemsSAsm.Saved :=
  { ra := pc 9, s0 := listBase, s1 := listLenW, s2 := v18, s3 := v19 }

/-! Reshape `afterSetup` → count-call pre under `stackFree_split`. -/
private theorem afterSetup_to_count_pre
    (newSp listBase listLenW : Word) (ks : KindSaved)
    (bytes : List (BitVec 8)) (oldCount oldOff oldLen : Word)
    (v13 v14 v18 v19 v20 v21 : Word)
    (R : Assertion)
    (hR : stackFree newSp 8 = (R ** stackFree newSp 6))
    (h : PartialState)
    (hp : (afterSetup newSp listBase listLenW ks bytes oldCount oldOff oldLen
        v13 v14 v18 v19 v20 v21) h) :
    (((.x1 ↦ᵣ ks.ra) **
      RlpListCountItemsSAsm.callEntryRest newSp listBase listLenW MnkCount
        oldCount (bodyCountSaved listBase listLenW v18 v19) bytes) **
      countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R) h := by
  simp only [afterSetup, countAmbient, countCallF, kindSavedFrame,
    RlpListCountItemsSAsm.callEntryRest, RlpListCountItemsSAsm.savedRegTail,
    RlpListCountItemsSAsm.entryRest, bodyCountSaved, hR] at hp ⊢
  xperm_chunked hp

/-! setup → count call → count_outcome. Body entry pc4 → epi join pc48. -/
set_option maxRecDepth 8000 in
theorem body_spec
    (newSp listBase listLenW : Word) (ks : KindSaved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word)
    (R : Assertion) (hRp : R.pcFree)
    (hR : stackFree newSp 8 = (R ** stackFree newSp 6))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (halign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hpath : PathByteOk bytes listBase listLen oldOff oldLen) :
    cpsTripleWithin (bodyFuel listLen) (pc 4) (pc 48) fullCode
      (bodyEntryPre newSp listBase listLenW ks bytes oldCount oldOff oldLen
        v12 v13 v14 v18 v19 v20 v21)
      (bodyPostExAny newSp ks listBase bytes listLen oldCount oldOff oldLen
        v18 v19 v20 v21) := by
  have hsetup := setup_spec newSp listBase listLenW ks bytes oldCount oldOff oldLen
    v12 v13 v14 v18 v19 v20 v21
  have hcall := kind_count_call_spec_within newSp listBase listLenW ks.ra oldCount
    (bodyCountSaved listBase listLenW v18 v19) bytes listLen
    (countCallF newSp ks oldOff oldLen v13 v14 v20 v21 R)
    (countCallF_pcFree newSp ks oldOff oldLen v13 v14 v20 v21 R hRp)
    hlistLenW halign hslack hover hvalid
  have hsetupW := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => afterSetup_to_count_pre newSp listBase listLenW ks bytes
      oldCount oldOff oldLen v13 v14 v18 v19 v20 v21 R hR h hq) hsetup
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [bodyCountSaved, countCallF] at hp ⊢
      xperm_chunked hp)
    hsetupW hcall
  have hout := count_outcome newSp
    (bodyCountSaved listBase listLenW v18 v19) ks listBase listLenW bytes listLen
    oldCount oldOff oldLen v13 v14 v20 v21 R hRp hR rfl rfl hlistLenW
    halign hslack hover hvalid hpath
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [bodyCountSaved, countCallF] at hp ⊢
      xperm_chunked hp)
    c01 hout
  unfold bodyFuel
  exact c012

/-! ## ABI-frame caller ambient (body footprint without frame regs/slots) -/

/-- Caller-owned body pre: ABI a0/a1 in x10/x11, temps, bytes, BSS, stack. -/
def kindCallerPre (newSp listBase listLenW : Word)
    (bytes : List (BitVec 8)) (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word) : Assertion :=
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ v12) **
  stackFree newSp 8 **
  countAmbient listBase bytes oldCount oldOff oldLen
    v13 v14 v18 v19 v20 v21

theorem kindCallerPre_pcFree (newSp listBase listLenW : Word)
    (bytes : List (BitVec 8)) (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word) :
    (kindCallerPre newSp listBase listLenW bytes oldCount oldOff oldLen
      v12 v13 v14 v18 v19 v20 v21).pcFree := by
  unfold kindCallerPre countAmbient
  repeat' first
    | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
    | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj

/-- Caller-owned body post: kind in a0 + BSS finals + pure Result.
    Path temps x18..x21 are PRESERVED (walk hop arms need path ptr/len). -/
def kindCallerPost (newSp listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen v18 v19 v20 v21 : Word) : Assertion :=
  fun h => ∃ (kind : Nat) (countW offW lenW : Word),
    (((.x10 ↦ᵣ BitVec.ofNat 64 kind) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase bytes **
      (MnkCount ↦ₘ countW) ** (MnkPathOff ↦ₘ offW) ** (MnkPathLen ↦ₘ lenW) **
      stackFree newSp 8) **
      ⌜MptNodeKindResult bytes listBase listLen oldCount oldOff oldLen kind⌝) h

theorem kindCallerPost_pcFree (newSp listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen v18 v19 v20 v21 : Word) :
    (kindCallerPost newSp listBase bytes listLen oldCount oldOff oldLen
      v18 v19 v20 v21).pcFree := by
  intro h hp
  obtain ⟨kind, countW, offW, lenW, hp'⟩ := hp
  have hpf :
      (((.x10 ↦ᵣ BitVec.ofNat 64 kind) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion listBase bytes **
        (MnkCount ↦ₘ countW) ** (MnkPathOff ↦ₘ offW) ** (MnkPathLen ↦ₘ lenW) **
        stackFree newSp 8) **
        ⌜MptNodeKindResult bytes listBase listLen oldCount oldOff oldLen kind⌝).pcFree := by
    repeat' first
      | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
      | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
      | exact pcFree_pure | apply pcFree_sepConj
  exact hpf h hp'

/-! Reshape bodyEntryPre ↔ abiFrame body-pre shape. -/
private theorem bodyEntryPre_of_abi
    (newSp listBase listLenW : Word) (ks : KindSaved)
    (bytes : List (BitVec 8)) (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word)
    (h : PartialState)
    (hp : (((.x2 ↦ᵣ newSp) ** regsAt kindFrame (kindSavedVals ks) **
        frameSlotsSaved kindFrame newSp (kindSavedVals ks) **
        kindCallerPre newSp listBase listLenW bytes oldCount oldOff oldLen
          v12 v13 v14 v18 v19 v20 v21) h)) :
    (bodyEntryPre newSp listBase listLenW ks bytes oldCount oldOff oldLen
      v12 v13 v14 v18 v19 v20 v21) h := by
  simp only [bodyEntryPre, kindCallerPre, countAmbient, regsAt_kindFrame,
    frameSlotsSaved_kindFrame, kindSavedFrame] at hp ⊢
  xperm_chunked hp

/-- Non-frame core of `bodyPost` (temps + BSS + pure) for a fixed kind. -/
private def kindCallerPostCore (newSp listBase : Word) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen v18 v19 v20 v21 : Word)
    (kind : Nat) (countW offW lenW : Word) : Assertion :=
  ((.x10 ↦ᵣ BitVec.ofNat 64 kind) ** (.x0 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
    (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    bytesRegion listBase bytes **
    (MnkCount ↦ₘ countW) ** (MnkPathOff ↦ₘ offW) ** (MnkPathLen ↦ₘ lenW) **
    stackFree newSp 8) **
  ⌜MptNodeKindResult bytes listBase listLen oldCount oldOff oldLen kind⌝

/-! Reshape bodyPostExAny → abiFrame body-post shape. -/
private theorem bodyPostExAny_to_abi
    (newSp listBase : Word) (ks : KindSaved) (bytes : List (BitVec 8))
    (listLen : Nat) (oldCount oldOff oldLen v18 v19 v20 v21 : Word)
    (h : PartialState)
    (hp : (bodyPostExAny newSp ks listBase bytes listLen oldCount oldOff oldLen
      v18 v19 v20 v21) h) :
    (((.x2 ↦ᵣ newSp) ** regsOwnAt kindFrame **
      frameSlotsSaved kindFrame newSp (kindSavedVals ks) **
      kindCallerPost newSp listBase bytes listLen oldCount oldOff oldLen
        v18 v19 v20 v21) h) := by
  obtain ⟨kind, countW, offW, lenW, hp0⟩ := hp
  -- Flatten bodyPost into x2 ** regsOwn ** kindSaved ** core.
  have hp1 :
      (((.x2 ↦ᵣ newSp) ** regsOwnAt kindFrame ** kindSavedFrame newSp ks **
        kindCallerPostCore newSp listBase bytes listLen oldCount oldOff oldLen
          v18 v19 v20 v21 kind countW offW lenW) h) := by
    simp only [bodyPost, bodyExitAmb, kindCallerPostCore, regsOwnAt_kindFrame,
      kindSavedFrame] at hp0 ⊢
    xperm_chunked hp0
  -- Lift core into kindCallerPost existential.
  have hp2 :
      (((.x2 ↦ᵣ newSp) ** regsOwnAt kindFrame ** kindSavedFrame newSp ks **
        kindCallerPost newSp listBase bytes listLen oldCount oldOff oldLen
          v18 v19 v20 v21) h) := by
    obtain ⟨a1, a2, hd1, hu1, hA, hRest⟩ := hp1
    obtain ⟨b1, b2, hd2, hu2, hB, hRest2⟩ := hRest
    obtain ⟨c1, c2, hd3, hu3, hC, hCore⟩ := hRest2
    refine ⟨a1, a2, hd1, hu1, hA,
      ⟨b1, b2, hd2, hu2, hB,
        ⟨c1, c2, hd3, hu3, hC, ?ex⟩⟩⟩
    exact ⟨kind, countW, offW, lenW, by
      simpa only [kindCallerPostCore] using hCore⟩
  simpa only [frameSlotsSaved_kindFrame] using hp2

/-! Body triple in `abiFrame_spec_own` pre/post shape. -/
set_option maxRecDepth 8000 in
theorem body_spec_abi
    (newSp listBase listLenW : Word) (ks : KindSaved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word)
    (R : Assertion) (hRp : R.pcFree)
    (hR : stackFree newSp 8 = (R ** stackFree newSp 6))
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (halign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hpath : PathByteOk bytes listBase listLen oldOff oldLen) :
    cpsTripleWithin (bodyFuel listLen) (pc 4) (pc 48) fullCode
      (((.x2 ↦ᵣ newSp) ** regsAt kindFrame (kindSavedVals ks) **
        frameSlotsSaved kindFrame newSp (kindSavedVals ks) **
        kindCallerPre newSp listBase listLenW bytes oldCount oldOff oldLen
          v12 v13 v14 v18 v19 v20 v21))
      (((.x2 ↦ᵣ newSp) ** regsOwnAt kindFrame **
        frameSlotsSaved kindFrame newSp (kindSavedVals ks) **
        kindCallerPost newSp listBase bytes listLen oldCount oldOff oldLen
          v18 v19 v20 v21)) := by
  have hb := body_spec newSp listBase listLenW ks bytes listLen
    oldCount oldOff oldLen v12 v13 v14 v18 v19 v20 v21 R hRp hR
    hlistLenW halign hslack hover hvalid hpath
  exact cpsTripleWithin_weaken
    (fun h hp => bodyEntryPre_of_abi newSp listBase listLenW ks bytes
      oldCount oldOff oldLen v12 v13 v14 v18 v19 v20 v21 h hp)
    (fun h hq => bodyPostExAny_to_abi newSp listBase ks bytes listLen
      oldCount oldOff oldLen v18 v19 v20 v21 h hq) hb

private theorem pc4_eq_bodyEntry :
    pc 4 = kindB + BitVec.ofNat 64 (4 * (1 + kindFrame.length)) := by
  unfold pc kindB kindFrame
  decide

private theorem pc48_eq_bodyExit :
    pc 48 = kindB + BitVec.ofNat 64 (4 * (1 + kindFrame.length + kindBody.length)) := by
  unfold pc kindB kindFrame kindBody
  decide

private theorem kind_frame_restore (sp0 : Word) :
    (sp0 + signExtend12 (-32 : BitVec 12)) + signExtend12 (32 : BitVec 12) = sp0 := by
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) by decide,
      show signExtend12 (32 : BitVec 12) = (32 : Word) by decide]
  bv_omega

private theorem kind_wrapper_sub :
    ∀ a i, CodeReq.ofProg kindB (abiFrameProg (-32 : BitVec 12) (32 : BitVec 12)
        kindFrame kindBody) a = some i → fullCode a = some i := by
  intro a i hi
  have hi' : CodeReq.ofProg kindB mptNodeKind_prog a = some i := by
    simpa [kind_abiFrame_byte_tie] using hi
  unfold fullCode wrapperCode
  exact CodeReq.union_mono_left a i hi'

/-! Whole-routine capstone: ABI frame + operational `MptNodeKindResult` post.
    No input-domain gate → registry `.proven`.
    Path temps x18..x21 PRESERVED for walk hop arms. -/
set_option maxRecDepth 8000 in
theorem mpt_node_kind_spec_within
    (sp0 ret listBase listLenW : Word) (ks : KindSaved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word)
    (hret : ks.ra = ret)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (halign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hpath : PathByteOk bytes listBase listLen oldOff oldLen) :
    cpsTripleWithin
      (1 + kindFrame.length + bodyFuel listLen + kindFrame.length + 1 + 1)
      kindB ret fullCode
      (((.x2 ↦ᵣ sp0) ** regsAt kindFrame (kindSavedVals ks) **
        frameSlotsOwn kindFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
        kindCallerPre (sp0 + signExtend12 (-32 : BitVec 12)) listBase listLenW
          bytes oldCount oldOff oldLen v12 v13 v14 v18 v19 v20 v21))
      (((.x2 ↦ᵣ sp0) ** regsAt kindFrame (kindSavedVals ks) **
        frameSlotsSaved kindFrame (sp0 + signExtend12 (-32 : BitVec 12))
          (kindSavedVals ks) **
        kindCallerPost (sp0 + signExtend12 (-32 : BitVec 12)) listBase bytes
          listLen oldCount oldOff oldLen v18 v19 v20 v21)) := by
  set newSp := sp0 + signExtend12 (-32 : BitVec 12) with hNS
  obtain ⟨R, hRp, hR⟩ := stackFree_split newSp (m := 6) (K := 8) (by decide)
  have hbody0 := body_spec_abi newSp listBase listLenW ks bytes listLen
    oldCount oldOff oldLen v12 v13 v14 v18 v19 v20 v21 R hRp hR
    hlistLenW halign hslack hover hvalid hpath
  have hbody : cpsTripleWithin (bodyFuel listLen)
      (kindB + BitVec.ofNat 64 (4 * (1 + kindFrame.length)))
      (kindB + BitVec.ofNat 64 (4 * (1 + kindFrame.length + kindBody.length)))
      fullCode
      (((.x2 ↦ᵣ newSp) ** regsAt kindFrame (kindSavedVals ks) **
        frameSlotsSaved kindFrame newSp (kindSavedVals ks) **
        kindCallerPre newSp listBase listLenW bytes oldCount oldOff oldLen
          v12 v13 v14 v18 v19 v20 v21))
      (((.x2 ↦ᵣ newSp) ** regsOwnAt kindFrame **
        frameSlotsSaved kindFrame newSp (kindSavedVals ks) **
        kindCallerPost newSp listBase bytes listLen oldCount oldOff oldLen
          v18 v19 v20 v21)) := by
    simpa only [← pc4_eq_bodyEntry, ← pc48_eq_bodyExit, ← hNS] using hbody0
  have hprogBound :
      4 * (abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) kindFrame kindBody).length
        < 2 ^ 64 := by
    have hlen : (abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) kindFrame kindBody).length
        = mptNodeKind_prog.length := by
      rw [kind_abiFrame_byte_tie]
    rw [hlen, program_length]
    decide
  apply abiFrame_spec_own kindB sp0 ret (-32 : BitVec 12) (32 : BitVec 12)
    kindFrame (0 : BitVec 12)
    [(.x8, 8), (.x9, 16)]
    (kindSavedVals ks) kindBody (bodyFuel listLen)
    (kindCallerPre newSp listBase listLenW bytes oldCount oldOff oldLen
      v12 v13 v14 v18 v19 v20 v21)
    (kindCallerPost newSp listBase bytes listLen oldCount oldOff oldLen
      v18 v19 v20 v21)
    fullCode
  · rfl
  · decide
  · decide
  · exact hprogBound
  · simpa [kindSavedVals] using hret
  · exact halignRet
  · exact kind_frame_restore sp0
  · exact kindCallerPre_pcFree newSp listBase listLenW bytes oldCount oldOff oldLen
      v12 v13 v14 v18 v19 v20 v21
  · exact kindCallerPost_pcFree newSp listBase bytes listLen oldCount oldOff oldLen
      v18 v19 v20 v21
  · exact kind_wrapper_sub
  · simpa only [hNS, kindFrame, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceMul] using hbody
