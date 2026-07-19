/-
  Teer AuthContent nested-free frame packaging under stackFree26 entry.

  * Entry free26 peels to nested6 ** free20 (Discharge stackFree26_peel).
  * frameL nested free through AtListCount triples (pcFree).
  * AuthContent_applied post (WithoutVnz) = AppliedFlatVnz (xperm).
  * nested ** Vnz-flat → ∃oldCount BridgePre (FrontListCount peel).
  * NestedPostEx→BridgePre + free26_to_bridgePre (hrun-parameterized) classical-3.
  * Residual: full-binder wire teerAuthContent_applied → free26_to_bridgePre;
    FrontToAuthLoopAssumed inhabit; general content-window.
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerFrontAuthCount
import EvmAsm.Codegen.Programs.TxEip7702TeerFrontListCount
import EvmAsm.Codegen.Programs.TxEip7702TeerDischarge
import EvmAsm.Codegen.Programs.TxEip7702TeerFrontValueNonzero
import EvmAsm.Codegen.Programs.TxEip7702TeerRecipient
import EvmAsm.Codegen.Programs.TxEip7702TeerType
import EvmAsm.Codegen.Programs.TxEip7702TeerAuthCount
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

/-- Frame nested list_count free on the left of any AtListCount triple. -/
theorem teerAtListCount_frameL_nested
    {n : Nat} {cr : CodeReq} {P Q : Assertion} (spC : Word)
    (hrun : cpsTripleWithin n E AtListCount cr P Q) :
    cpsTripleWithin n E AtListCount cr
      (stackFree spC 6 ** P) (stackFree spC 6 ** Q) :=
  cpsTripleWithin_frameL (stackFree spC 6) (pcFree_stackFree spC 6) hrun

/-- FrontValueNonzero WithoutVnz = local AuthContent WithoutVnz (AuthCountAddr). -/
theorem teerScratchWithoutVnzOwn_eq_authContentWithoutVnz :
    teerScratchWithoutVnzOwn = teerAuthContentWithoutVnzOwn := by
  unfold teerScratchWithoutVnzOwn teerAuthContentWithoutVnzOwn AuthCountAddr
  rfl

/-- AuthContent applied post atoms (no pure) match AppliedFlatVnz. -/
theorem teerAuthContentAppliedPost_to_VnzFlat
    (spVal spC old1 loadPtr lenW balPtr balLenW chainIdW : Word)
    (content listLenW s7Old cursorV endW s11 : Word)
    (s : TeerSaved) (innerVal : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) :
    ∀ h,
      ((.x2 ↦ᵣ spC) **
        (.x1 ↦ᵣ old1) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ content) ** (.x22 ↦ᵣ listLenW) **
        (.x23 ↦ᵣ s7Old) **
        (.x10 ↦ᵣ content) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ AuthCountAddr) **
        (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
        (.x26 ↦ᵣ (0 : Word)) **
        (.x27 ↦ᵣ s11) **
        frameSlotsSaved teerFrame spC (teerSavedVals s) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        stackFree spVal 6 **
        bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
        memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
        memOwn ValueNonzeroAddr **
        teerScratchWithoutVnzOwn) h →
      teerAuthContentAppliedFlatVnz spVal spC old1 loadPtr lenW balPtr balLenW
        chainIdW content listLenW s7Old cursorV endW s11 s innerVal
        regionBase bs balBytes h := by
  intro h hp
  dsimp only [teerAuthContentAppliedFlatVnz, TypeAddr, InnerOffAddr,
    RecipientPtrAddr, RecipientLenAddr, ValueNonzeroAddr] at *
  rw [teerScratchWithoutVnzOwn_eq_authContentWithoutVnz] at hp
  xperm_hyp hp

/-- Nested free ** applied post atoms → ∃ oldCount BridgePre. -/
theorem teerAuthContentAppliedPost_nested_to_bridgePre
    (spVal spC old1 loadPtr lenW balPtr balLenW chainIdW : Word)
    (content listLenW s7Old cursorV endW s11 : Word)
    (s : TeerSaved) (innerVal : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) :
    ∀ h,
      (stackFree spC 6 **
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ old1) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ content) ** (.x22 ↦ᵣ listLenW) **
          (.x23 ↦ᵣ s7Old) **
          (.x10 ↦ᵣ content) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ AuthCountAddr) **
          (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x0 ↦ᵣ (0 : Word)) **
          (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          memOwn ValueNonzeroAddr **
          teerScratchWithoutVnzOwn)) h →
      ∃ oldCount,
        teerAuthContentBridgePre spVal spC old1 loadPtr lenW balPtr balLenW chainIdW
          content listLenW s7Old cursorV endW s11 s innerVal oldCount
          regionBase bs balBytes h := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, hnest, hflat⟩ := hp
  have hV := teerAuthContentAppliedPost_to_VnzFlat
    spVal spC old1 loadPtr lenW balPtr balLenW chainIdW
    content listLenW s7Old cursorV endW s11 s innerVal
    regionBase bs balBytes h2 hflat
  exact teerAuthContentAppliedFlatVnz_nested_to_bridgePre
    spVal spC old1 loadPtr lenW balPtr balLenW chainIdW
    content listLenW s7Old cursorV endW s11 s innerVal
    regionBase bs balBytes h ⟨h1, h2, hd, hu, hnest, hV⟩

/-- Applied entry prest atoms without the free-20 slot. -/
def teerAuthContentAppliedEntryRest
    (ret spVal loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
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
    regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))

/-- Standard applied prest = free20 ** Rest (xperm). -/
theorem teerAuthContentAppliedEntry_split
    (ret spVal loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8)) :
    ∀ h,
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
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) h ↔
      (stackFree spVal nTeerStackDwords **
        teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes) h := by
  intro h
  constructor <;> intro hp <;>
    (dsimp only [teerAuthContentAppliedEntryRest] at *; xperm_hyp hp)

/-- Entry free26 ** Rest → nested ** applied prest. -/
theorem teerAuthContentEntry_free26_to_nested_applied
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12)) :
    ∀ h,
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes) h →
      (stackFree spC 6 **
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
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))) h := by
  intro h hp
  have hp' := teerAppliedEntry_stackFree26_peel spVal
    (teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
      chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      regionBase bs balBytes) h hp
  -- hp' : nested@spVal-160 ** (free20 ** Rest)
  subst hspC
  have hp2 :=
    (teerAuthContentAppliedEntry_split ret spVal loadPtr lenW balPtr balLenW
      chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      regionBase bs balBytes h).2
  -- Need: nested ** applied = nested ** (free20 ** Rest) after split inverse
  -- hp' already nested ** (free20 ** Rest)
  -- applied = free20 ** Rest via split.2 reverse... split says applied ↔ free20**Rest
  -- So nested ** applied ↔ nested ** (free20 ** Rest)
  obtain ⟨h1, h2, hd, hu, hnest, hmid⟩ := hp'
  have hApp :=
    (teerAuthContentAppliedEntry_split ret spVal loadPtr lenW balPtr balLenW
      chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      regionBase bs balBytes h2).2 hmid
  exact ⟨h1, h2, hd, hu, hnest, hApp⟩

/-- Float double-exists through left nested free (pair next×len). -/
theorem teerNested_sepConj_exists_pair
    {A : Word → Word → Assertion} (spC : Word) :
    ∀ h,
      (stackFree spC 6 ** (fun hp => ∃ next lenK : Word, A next lenK hp)) h →
      ∃ next lenK : Word, (stackFree spC 6 ** A next lenK) h := by
  intro h hp
  have hp' := sepConj_exists_right (A := stackFree spC 6)
    (B := fun p : Word × Word => A p.1 p.2) h (by
    -- reshape exists pair
    obtain ⟨h1, h2, hd, hu, hnest, hEx⟩ := hp
    refine ⟨h1, h2, hd, hu, hnest, ?_⟩
    obtain ⟨next, lenK, hA⟩ := hEx
    exact ⟨(next, lenK), hA⟩)
  obtain ⟨p, hpN⟩ := hp'
  exact ⟨p.1, p.2, hpN⟩

/-- Package: free26 entry + AuthContent_applied → nested post with exists. -/
theorem teerAuthContent_applied_nestedFree_of_run
    {n : Nat} {cr : CodeReq}
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (Q : Assertion)
    (hrun : cpsTripleWithin n E AtListCount cr
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
      Q) :
    cpsTripleWithin n E AtListCount cr
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (stackFree spC 6 ** Q) := by
  have hF := teerAtListCount_frameL_nested spC hrun
  exact cpsTripleWithin_weaken
    (teerAuthContentEntry_free26_to_nested_applied ret spVal spC loadPtr lenW
      balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      regionBase bs balBytes hspC)
    (fun _ hq => hq) hF

/-- AuthContent_applied post body (exists next/lenK + pure) nested under free6.
    Matches `teerAuthContent_applied` post atoms. -/
def teerAuthContentAppliedPostEx
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s7Old cursorV endW s11 : Word)
    (s : TeerSaved) (innerVal endL : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (srcOffA9 : Nat) : Assertion :=
  fun h =>
    ∃ next lenK : Word,
      (((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ LinkAuthWalkNext9) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ next - lenK) ** (.x22 ↦ᵣ lenK) **
          (.x23 ↦ᵣ s7Old) **
          (.x10 ↦ᵣ next - lenK) ** (.x11 ↦ᵣ lenK) ** (.x12 ↦ᵣ AuthCountAddr) **
          (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x0 ↦ᵣ (0 : Word)) **
          (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          memOwn ValueNonzeroAddr **
          teerScratchWithoutVnzOwn) **
        ⌜rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
          endL next lenK⌝) h

/-- Nested free ** AuthContent_applied post → ∃ next lenK oldCount, BridgePre.
    Drops trailing pure decode (ghost); peels AuthCount memOwn→memIs.
    content = next−lenK, listLenW = lenK, old1 = LinkAuthWalkNext9. -/
theorem teerAuthContentNestedPostEx_to_bridgePre
    (spVal spC loadPtr lenW balPtr balLenW chainIdW : Word)
    (s7Old cursorV endW s11 : Word)
    (s : TeerSaved) (innerVal endL : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (srcOffA9 : Nat) :
    ∀ h,
      (stackFree spC 6 **
        teerAuthContentAppliedPostEx spVal spC loadPtr lenW balPtr balLenW chainIdW
          s7Old cursorV endW s11 s innerVal endL regionBase bs balBytes srcOffA9) h →
      ∃ (next lenK oldCount : Word),
        teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
          balPtr balLenW chainIdW (next - lenK) lenK s7Old cursorV endW s11 s
          innerVal oldCount regionBase bs balBytes h := by
  intro h hp
  -- Unfold PostEx so nested_exists_pair sees fun h => ∃ next lenK, ...
  unfold teerAuthContentAppliedPostEx at hp
  -- Float ∃ next,lenK through nested free
  have hpEx :=
    teerNested_sepConj_exists_pair
      (A := fun next lenK =>
        (((.x2 ↦ᵣ spC) **
            (.x1 ↦ᵣ LinkAuthWalkNext9) **
            (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
            (.x21 ↦ᵣ next - lenK) ** (.x22 ↦ᵣ lenK) **
            (.x23 ↦ᵣ s7Old) **
            (.x10 ↦ᵣ next - lenK) ** (.x11 ↦ᵣ lenK) ** (.x12 ↦ᵣ AuthCountAddr) **
            (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
            (.x26 ↦ᵣ (0 : Word)) **
            (.x27 ↦ᵣ s11) **
            frameSlotsSaved teerFrame spC (teerSavedVals s) **
            (.x0 ↦ᵣ (0 : Word)) **
            (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            stackFree spVal 6 **
            bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
            memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
            memOwn ValueNonzeroAddr **
            teerScratchWithoutVnzOwn) **
          ⌜rlpItemDecode bs srcOffA9 (regionBase + BitVec.ofNat 64 srcOffA9)
            endL next lenK⌝))
      spC h hp
  obtain ⟨next, lenK, hpN⟩ := hpEx
  -- Drop pure via sepConj_pure_right on atoms**pure at h2
  obtain ⟨h1, h2, hd, hu, hnest, hAP⟩ := hpN
  have hAtoms2 := ((sepConj_pure_right _).1 hAP).1
  have hNestAtoms :
      (stackFree spC 6 **
        ((.x2 ↦ᵣ spC) **
          (.x1 ↦ᵣ LinkAuthWalkNext9) **
          (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ next - lenK) ** (.x22 ↦ᵣ lenK) **
          (.x23 ↦ᵣ s7Old) **
          (.x10 ↦ᵣ next - lenK) ** (.x11 ↦ᵣ lenK) ** (.x12 ↦ᵣ AuthCountAddr) **
          (.x24 ↦ᵣ cursorV) ** (.x25 ↦ᵣ endW) **
          (.x26 ↦ᵣ (0 : Word)) **
          (.x27 ↦ᵣ s11) **
          frameSlotsSaved teerFrame spC (teerSavedVals s) **
          (.x0 ↦ᵣ (0 : Word)) **
          (TypeAddr ↦ₘ (4 : Word)) ** (InnerOffAddr ↦ₘ innerVal) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          stackFree spVal 6 **
          bytesRegion regionBase bs ** bytesRegion balPtr balBytes **
          memOwn RecipientPtrAddr ** memOwn RecipientLenAddr **
          memOwn ValueNonzeroAddr **
          teerScratchWithoutVnzOwn)) h :=
    ⟨h1, h2, hd, hu, hnest, hAtoms2⟩
  obtain ⟨oldCount, hBr⟩ :=
    teerAuthContentAppliedPost_nested_to_bridgePre
      spVal spC LinkAuthWalkNext9 loadPtr lenW balPtr balLenW chainIdW
      (next - lenK) lenK s7Old cursorV endW s11 s innerVal
      regionBase bs balBytes h hNestAtoms
  exact ⟨next, lenK, oldCount, hBr⟩

/-- free26 entry + AuthContent_applied-shaped run → ∃ next lenK oldCount BridgePre.
    Package `teerAuthContent_applied` (or any free20 prest → PostEx) under nested free. -/
theorem teerAuthContent_free26_to_bridgePre
    {n : Nat} {cr : CodeReq}
    (ret spVal spC loadPtr lenW balPtr balLenW chainIdW baiW : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : Word)
    (regionBase : Word) (bs balBytes : List (BitVec 8))
    (hspC : spC = spVal + signExtend12 (-160 : BitVec 12))
    (s : TeerSaved) (innerVal endL endW cursorV : Word)
    (srcOffA9 : Nat)
    (hrun : cpsTripleWithin n E AtListCount cr
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
      (teerAuthContentAppliedPostEx spVal spC loadPtr lenW balPtr balLenW chainIdW
        s7 cursorV endW s11 s innerVal endL regionBase bs balBytes srcOffA9)) :
    cpsTripleWithin n E AtListCount cr
      (stackFree spVal nTeerStackWithListCount **
        teerAuthContentAppliedEntryRest ret spVal loadPtr lenW balPtr balLenW
          chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          regionBase bs balBytes)
      (fun h =>
        ∃ (next lenK oldCount : Word),
          teerAuthContentBridgePre spVal spC LinkAuthWalkNext9 loadPtr lenW
            balPtr balLenW chainIdW (next - lenK) lenK s7 cursorV endW s11 s
            innerVal oldCount regionBase bs balBytes h) := by
  have hNest :=
    teerAuthContent_applied_nestedFree_of_run ret spVal spC loadPtr lenW
      balPtr balLenW chainIdW baiW s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      regionBase bs balBytes hspC
      (teerAuthContentAppliedPostEx spVal spC loadPtr lenW balPtr balLenW chainIdW
        s7 cursorV endW s11 s innerVal endL regionBase bs balBytes srcOffA9)
      hrun
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (teerAuthContentNestedPostEx_to_bridgePre spVal spC loadPtr lenW balPtr balLenW
      chainIdW s7 cursorV endW s11 s innerVal endL regionBase bs balBytes srcOffA9)
    hNest

#print axioms teerAtListCount_frameL_nested
#print axioms teerScratchWithoutVnzOwn_eq_authContentWithoutVnz
#print axioms teerAuthContentAppliedPost_to_VnzFlat
#print axioms teerAuthContentAppliedPost_nested_to_bridgePre
#print axioms teerAuthContentAppliedEntry_split
#print axioms teerAuthContentEntry_free26_to_nested_applied
#print axioms teerNested_sepConj_exists_pair
#print axioms teerAuthContent_applied_nestedFree_of_run
#print axioms teerAuthContentNestedPostEx_to_bridgePre
#print axioms teerAuthContent_free26_to_bridgePre

end EvmAsm.Codegen.TxEip7702TeerSpec
