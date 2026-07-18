/-
  Ambient dual of type234 walk_next0 call under split bases.
  x8=loadPtr; bytesRegion/cursor use regionBase + absOff.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.StmtSoundCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNext
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkNextAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkNext0
import EvmAsm.Codegen.Programs.TxExtractToAddressTopType234Ambient

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

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

def wn0StableAmbient (loadPtr lenW typeW innerW endPtr cursor : Word) : Assertion :=
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
    (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    (.x20 ↦ᵣ typeW) **
    (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr)

theorem wn0StableAmbient_pcFree (loadPtr lenW typeW innerW endPtr cursor : Word) :
    (wn0StableAmbient loadPtr lenW typeW innerW endPtr cursor).pcFree := by
  unfold wn0StableAmbient; pcf

def wn0CommonAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNext0) **
    bytesRegion regionBase bs

private theorem of_forall_regOwn7_amb
    {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {r1 r2 r3 r4 r5 r6 r7 : Reg} {P Q : Assertion}
    (hspec : ∀ v1 v2 v3 v4 v5 v6 v7, cpsTripleWithin n entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) **
       (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7)) Q) :
    cpsTripleWithin n entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 **
       regOwn r5 ** regOwn r6 ** regOwn r7) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPOwn, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP, hO1⟩ := hPOwn
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact hspec v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP, g2, g3, d2, u2, hv1,
       g4, g5, d3, u3, hv2, g6, g7, d4, u4, hv3,
       g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
       g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc

theorem extractWalkNext0Post_to_commonOutcome_ambient
    (regionBase endPtr : Word) (bs : List (BitVec 8)) (absOff : Nat) :
    ∀ h, extractWalkNext0Post regionBase endPtr bs absOff h →
      (wn0CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) h := by
  intro h hp
  simp only [extractWalkNext0Post] at hp
  obtain ⟨h1, h2, hd, hu, hcom, hout⟩ := hp
  have hcom' : wn0CommonAmbient regionBase bs h1 := by
    simp only [wn0CommonAmbient]
    xperm_hyp hcom
  exact ⟨h1, h2, hd, hu, hcom', hout⟩

set_option maxRecDepth 8000 in
theorem extractWalkNext0Call_type234_outcome_ambient
    (loadPtr regionBase lenW typeW innerW endPtr : Word)
    (bs : List (BitVec 8)) (absOff : Nat)
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff : absOff < bs.length)
    (hover : regionBase.toNat + absOff < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff) = true)
    (hss : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        absOff + 1 < bs.length ∧ regionBase.toNat + (absOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        absOff + 1 + ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        regionBase.toNat + (absOff + 1 +
          ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[absOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (regionBase + BitVec.ofNat 64 (absOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNext0JalPc LinkWalkNext0 extractLinkedCode
      (type234StartFrameAmbient loadPtr regionBase lenW typeW innerW
        (regionBase + BitVec.ofNat 64 absOff) endPtr bs)
      (wn0StableAmbient loadPtr lenW typeW innerW endPtr
          (regionBase + BitVec.ofNat 64 absOff) **
        wn0CommonAmbient regionBase bs **
        wn0Outcome regionBase endPtr bs absOff) := by
  let cursor := regionBase + BitVec.ofNat 64 absOff
  let Pcore : Assertion :=
    (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (TeaTypeAddr ↦ₘ typeW) ** (TeaInnerAddr ↦ₘ innerW) **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      (.x20 ↦ᵣ typeW) **
      (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ endPtr) **
      (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkWalkInit) ** bytesRegion regionBase bs
  let Qassumed : Assertion :=
    wn0StableAmbient loadPtr lenW typeW innerW endPtr cursor **
      wn0CommonAmbient regionBase bs **
      wn0Outcome regionBase endPtr bs absOff
  have htemps :
      cpsTripleWithin (1 + 87) WalkNext0JalPc LinkWalkNext0 extractLinkedCode
        (Pcore ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        Qassumed := by
    refine of_forall_regOwn7_amb (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (r4 := .x28) (r5 := .x29) (r6 := .x30) (r7 := .x31)
      (fun t0 t1 t2 t3 t4 t5 t6 => ?_)
    have hleaf := extractWalkNext0Call_ambient regionBase endPtr (0 : Word)
      t0 t1 t2 t3 t4 t5 t6 bs absOff LinkWalkInit
      hsalign hoff hover hvalid hss hls hll
    have hF := cpsTripleWithin_frameR
      (wn0StableAmbient loadPtr lenW typeW innerW endPtr cursor)
      (wn0StableAmbient_pcFree _ _ _ _ _ _) hleaf
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, wn0StableAmbient, extractWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      dsimp only [Qassumed] at hq ⊢
      have hq' :
          (wn0StableAmbient loadPtr lenW typeW innerW endPtr cursor **
            extractWalkNext0Post regionBase endPtr bs absOff) h := by
        xperm_hyp hq
      obtain ⟨hA, hP, hd, hu, hamb, hpost⟩ := hq'
      have hnorm := extractWalkNext0Post_to_commonOutcome_ambient
        regionBase endPtr bs absOff _ hpost
      obtain ⟨hC, hO, hdc, huc, hcom, hout⟩ := hnorm
      exact ⟨hA, hP, hd, hu, hamb, hC, hO, hdc, huc, hcom, hout⟩) hF
  refine cpsTripleWithin_weaken (fun s hp => by
    dsimp only [Pcore, Qassumed, type234StartFrameAmbient, afterSaveFrameTyAmbient]
      at hp ⊢
    have hro : ∀ t, (.x5 ↦ᵣ (1 : Word)) t → regOwn .x5 t := fun _ hx => ⟨1, hx⟩
    have hp1 :
        (Pcore ** (.x5 ↦ᵣ (1 : Word)) ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) s := by
      dsimp only [Pcore] at hp ⊢
      xperm_hyp hp
    have hp2 :=
      sepConj_mono (fun _ x => x)
        (sepConj_mono hro (fun _ x => x)) s hp1
    dsimp only [Pcore] at hp2 ⊢
    xperm_hyp hp2) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) htemps

#print axioms extractWalkNext0Call_type234_outcome_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
