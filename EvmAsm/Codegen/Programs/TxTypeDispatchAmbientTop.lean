/-
  Ambient top merge + AssumedAmbient packaging for multi-tx Option A.
  Success-domain only (hsuccess); fail arms not needed for Assumed.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbientTyped
import EvmAsm.Codegen.Programs.TxTypeDispatchTisDischarge
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxTypeDispatchSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nTypeSteps TypeDispatchAssumed fullCode type_mono)

private theorem teer_legacy (b : BitVec 8) (rest : List (BitVec 8)) (h : 192 ≤ b.toNat) :
    teerTxTypeDispatch (b :: rest) = (0, 0, 0) := by
  simp only [teerTxTypeDispatch, h, ↓reduceIte]
private theorem teer_type1 (rest : List (BitVec 8)) :
    teerTxTypeDispatch ((1 : BitVec 8) :: rest) = (0, 1, 1) := by
  simp only [teerTxTypeDispatch]; decide
private theorem teer_type2 (rest : List (BitVec 8)) :
    teerTxTypeDispatch ((2 : BitVec 8) :: rest) = (0, 2, 1) := by
  simp only [teerTxTypeDispatch]; decide
private theorem teer_type3 (rest : List (BitVec 8)) :
    teerTxTypeDispatch ((3 : BitVec 8) :: rest) = (0, 3, 1) := by
  simp only [teerTxTypeDispatch]; decide
private theorem teer_type4 (rest : List (BitVec 8)) :
    teerTxTypeDispatch ((4 : BitVec 8) :: rest) = (0, 4, 1) := by
  simp only [teerTxTypeDispatch]; decide
private theorem teer_unknown (b : BitVec 8) (rest : List (BitVec 8))
    (hult : b.toNat < 192)
    (hne1 : b ≠ (1 : BitVec 8)) (hne2 : b ≠ (2 : BitVec 8))
    (hne3 : b ≠ (3 : BitVec 8)) (hne4 : b ≠ (4 : BitVec 8)) :
    teerTxTypeDispatch (b :: rest) = (1, 0, 0) := by
  simp only [teerTxTypeDispatch]
  have hnot : ¬ (192 ≤ b.toNat) := Nat.not_le_of_gt hult
  simp only [hnot, ↓reduceIte, hne1, hne2, hne3, hne4, ↓reduceIte]

private theorem arm_post_to_ambient
    (raIn regionBase typePtr innerPtr status typeW innerW v5 v6 txLen : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hstatus : status = (teerTxTypeDispatch (txSlice bs off len)).1)
    (htype : typeW = (teerTxTypeDispatch (txSlice bs off len)).2.1)
    (hinner : innerW = (teerTxTypeDispatch (txSlice bs off len)).2.2) :
    ∀ h,
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ status) ** (.x11 ↦ᵣ txLen) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ typeW) ** (innerPtr ↦ₘ innerW) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word))) h →
      typeAmbientPostOf raIn regionBase typePtr innerPtr bs off len h := by
  intro h hp
  simp only [typeAmbientPostOf]
  have hp' :
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        (.x10 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).1) **
        (typePtr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (innerPtr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        (.x11 ↦ᵣ txLen) ** (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr)) h := by
    have hp0 :
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs **
          (.x10 ↦ᵣ status) ** (typePtr ↦ₘ typeW) ** (innerPtr ↦ₘ innerW) **
          (.x11 ↦ᵣ txLen) ** (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr)) h := by
      xperm_hyp hp
    rwa [hstatus, htype, hinner] at hp0
  exact sepConj_mono (regIs_to_regOwn .x5 v5)
    (sepConj_mono (regIs_to_regOwn .x6 v6)
      (sepConj_mono (fun _ hq => hq)
        (sepConj_mono (fun _ hq => hq)
          (sepConj_mono (fun _ hq => hq)
            (sepConj_mono (fun _ hq => hq)
              (sepConj_mono (fun _ hq => hq)
                (sepConj_mono (fun _ hq => hq)
                  (sepConj_mono (regIs_to_regOwn .x11 txLen)
                    (sepConj_mono (regIs_to_regOwn .x12 typePtr)
                      (regIs_to_regOwn .x13 innerPtr)))))))))) h hp'

set_option maxRecDepth 8000 in
/-- Ambient success top under extractSuccess-style hsuccess on the slice. classical-3. -/
theorem txTypeDispatch_success_ambient
    (raIn regionBase loadPtr typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin nTxTypeDispatchSteps D raIn typeCode
      (typeAmbientPre raIn regionBase loadPtr (BitVec.ofNat 64 len)
        typePtr innerPtr t0Old t1Old typeOld innerOld bs)
      (typeAmbientPostOf raIn regionBase typePtr innerPtr bs off len) := by
  have hne := teer_success_implies_nonempty (txSlice bs off len) hsuccess
  have hlen_pos : 0 < len := by
    have hsl := txSlice_length bs off len hbound
    omega
  have hcons := teer_slice_cons bs off len hlen_pos hbound
  obtain ⟨b, rest, hslice, hb⟩ := hcons
  have hvalid' : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true := hvalid
  by_cases hleg : 192 ≤ b.toNat
  · have h0 :=
      txTypeDispatch_legacy_ambient raIn regionBase loadPtr typePtr innerPtr
        typeOld innerOld t0Old t1Old bs off len b rest hret hptr hslice hleg
        halign hbound hover hvalid'
    have h0' := cpsTripleWithin_mono_nSteps (nSteps := 8) (nSteps' := nTxTypeDispatchSteps)
      (by simp only [nTxTypeDispatchSteps]; omega) h0
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [typeAmbientPre] at hp ⊢; xperm_hyp hp)
      (arm_post_to_ambient raIn regionBase typePtr innerPtr 0 0 0
        (b.zeroExtend 64) (192 : Word)
        (BitVec.ofNat 64 len) bs off len
        (by rw [hslice, teer_legacy b rest hleg])
        (by rw [hslice, teer_legacy b rest hleg])
        (by rw [hslice, teer_legacy b rest hleg])) h0'
  · have hult : b.toNat < 192 := Nat.lt_of_not_ge hleg
    by_cases h1 : b = (1 : BitVec 8)
    · subst h1
      have h0 :=
        txTypeDispatch_type1_ambient raIn regionBase loadPtr typePtr innerPtr
          typeOld innerOld t0Old t1Old bs off len rest hret hptr hslice
          halign hbound hover hvalid'
      have h0' := cpsTripleWithin_mono_nSteps (nSteps := 12) (nSteps' := nTxTypeDispatchSteps)
        (by simp only [nTxTypeDispatchSteps]; omega) h0
      refine cpsTripleWithin_weaken (fun _ hp => by
        simp only [typeAmbientPre] at hp ⊢; xperm_hyp hp)
        (arm_post_to_ambient raIn regionBase typePtr innerPtr 0 1 1
          (1 : Word) (1 : Word)
          (BitVec.ofNat 64 len) bs off len
          (by rw [hslice, teer_type1])
          (by rw [hslice, teer_type1])
          (by rw [hslice, teer_type1])) h0'
    · by_cases h2 : b = (2 : BitVec 8)
      · subst h2
        have h0 :=
          txTypeDispatch_type2_ambient raIn regionBase loadPtr typePtr innerPtr
            typeOld innerOld t0Old t1Old bs off len rest hret hptr hslice
            halign hbound hover hvalid'
        have h0' := cpsTripleWithin_mono_nSteps (nSteps := 14) (nSteps' := nTxTypeDispatchSteps)
          (by simp only [nTxTypeDispatchSteps]; omega) h0
        refine cpsTripleWithin_weaken (fun _ hp => by
          simp only [typeAmbientPre] at hp ⊢; xperm_hyp hp)
          (arm_post_to_ambient raIn regionBase typePtr innerPtr 0 2 1
            (2 : Word) (1 : Word)
            (BitVec.ofNat 64 len) bs off len
            (by rw [hslice, teer_type2])
            (by rw [hslice, teer_type2])
            (by rw [hslice, teer_type2])) h0'
      · by_cases h3 : b = (3 : BitVec 8)
        · subst h3
          have h0 :=
            txTypeDispatch_type3_ambient raIn regionBase loadPtr typePtr innerPtr
              typeOld innerOld t0Old t1Old bs off len rest hret hptr hslice
              halign hbound hover hvalid'
          have h0' := cpsTripleWithin_mono_nSteps (nSteps := 16) (nSteps' := nTxTypeDispatchSteps)
            (by simp only [nTxTypeDispatchSteps]; omega) h0
          refine cpsTripleWithin_weaken (fun _ hp => by
            simp only [typeAmbientPre] at hp ⊢; xperm_hyp hp)
            (arm_post_to_ambient raIn regionBase typePtr innerPtr 0 3 1
              (3 : Word) (1 : Word)
              (BitVec.ofNat 64 len) bs off len
              (by rw [hslice, teer_type3])
              (by rw [hslice, teer_type3])
              (by rw [hslice, teer_type3])) h0'
        · by_cases h4 : b = (4 : BitVec 8)
          · subst h4
            have h0 :=
              txTypeDispatch_type4_ambient raIn regionBase loadPtr typePtr innerPtr
                typeOld innerOld t0Old t1Old bs off len rest hret hptr hslice
                halign hbound hover hvalid'
            have h0' := cpsTripleWithin_mono_nSteps (nSteps := 18) (nSteps' := nTxTypeDispatchSteps)
              (by simp only [nTxTypeDispatchSteps]; omega) h0
            refine cpsTripleWithin_weaken (fun _ hp => by
              simp only [typeAmbientPre] at hp ⊢; xperm_hyp hp)
              (arm_post_to_ambient raIn regionBase typePtr innerPtr 0 4 1
                (4 : Word) (1 : Word)
                (BitVec.ofNat 64 len) bs off len
                (by rw [hslice, teer_type4])
                (by rw [hslice, teer_type4])
                (by rw [hslice, teer_type4])) h0'
          · -- unknown → status 1, contradicts hsuccess
            have hteer := teer_unknown b rest hult h1 h2 h3 h4
            have : (teerTxTypeDispatch (txSlice bs off len)).1 = (1 : Word) := by
              rw [hslice, hteer]
            rw [this] at hsuccess
            exact absurd hsuccess (by decide)

private theorem amb_typeStableScratch_pcFree : typeStableScratch.pcFree := by
  unfold typeStableScratch
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regOwn
    | exact pcFree_emp

set_option maxRecDepth 8000 in
theorem txTypeDispatch_success_ambient_framed
    (raIn regionBase loadPtr typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin nTypeSteps D raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ loadPtr) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ typeOld) ** (innerPtr ↦ₘ innerOld) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        typeStableScratch)
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
        (innerPtr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        (.x0 ↦ᵣ (0 : Word)) ** typeStableScratch) := by
  have h0 := txTypeDispatch_success_ambient raIn regionBase loadPtr typePtr innerPtr
    t0Old t1Old typeOld innerOld bs off len hret hptr hsuccess
    halign hbound hover hvalid
  have h1 : cpsTripleWithin nTxTypeDispatchSteps D raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ loadPtr) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ typeOld) ** (innerPtr ↦ₘ innerOld) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)))
      (typeAmbientPostOf raIn regionBase typePtr innerPtr bs off len) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [typeAmbientPre] at hp ⊢; xperm_hyp hp) (fun _ hq => hq) h0
  have h2 := cpsTripleWithin_frameR typeStableScratch amb_typeStableScratch_pcFree h1
  have hle : nTxTypeDispatchSteps ≤ nTypeSteps := by
    change 256 ≤ 256; omega
  have h3 := cpsTripleWithin_mono_nSteps hle h2
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      -- Keep typeStableScratch folded (TisDischarge pattern); unfold only post core.
      simp only [typeAmbientPostOf, hsuccess] at hq
      xperm_hyp hq) h3

/-- Peel memOwn type/inner + regOwn x5/x6 (same as slice TisDischarge). -/
private theorem of_forall_type_dispatch_owns_amb
    {nSteps : Nat} {entry exit_ typePtr innerPtr : Word}
    {P Q : Assertion} {cr : CodeReq}
    (h : ∀ (typeOld innerOld t0Old t1Old : Word),
      cpsTripleWithin nSteps entry exit_ cr
        (P ** (typePtr ↦ₘ typeOld) ** (innerPtr ↦ₘ innerOld) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** memOwn typePtr ** memOwn innerPtr ** regOwn .x5 ** regOwn .x6) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨typeOld, htype⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨innerOld, hinner⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨t0Old, ht0⟩, ⟨t1Old, ht1⟩⟩ := hO3
  exact h typeOld innerOld t0Old t1Old R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0,
        g2, g3, d2, u2, htype,
        g4, g5, d3, u3, hinner,
        g6, g7, d4, u4, ht0, ht1⟩, hRb⟩ hpc

set_option maxRecDepth 8000 in
/-- Assumed-shaped ambient triple under typeCode. -/
theorem typeDispatch_assumed_ambient_flat_typeCode
    (ret regionBase loadPtr lenW typePtr innerPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin nTypeSteps D ret typeCode
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        memOwn typePtr ** memOwn innerPtr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        memOwn typePtr ** memOwn innerPtr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) := by
  let Pcore : Assertion :=
    (.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
      (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
      bytesRegion regionBase bs ** (.x0 ↦ᵣ (0 : Word)) ** typeStableScratch
  let Qassumed : Assertion :=
    (.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
      bytesRegion regionBase bs **
      memOwn typePtr ** memOwn innerPtr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))
  have hpeel :
      cpsTripleWithin nTypeSteps D ret typeCode
        (Pcore ** memOwn typePtr ** memOwn innerPtr ** regOwn .x5 ** regOwn .x6)
        Qassumed := by
    refine of_forall_type_dispatch_owns_amb (typePtr := typePtr) (innerPtr := innerPtr)
      (fun typeOld innerOld t0Old t1Old => ?_)
    have hf := txTypeDispatch_success_ambient_framed ret regionBase loadPtr typePtr
      innerPtr t0Old t1Old typeOld innerOld bs off len hret hptr hsuccess
      halign hbound hover hvalid
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, typeStableScratch] at hp ⊢
      simp only [hlen] at hp ⊢
      xperm_hyp hp) (fun s hq => by
      dsimp only [typeStableScratch] at hq
      let Rest : Assertion :=
        (.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs **
          regOwn .x5 ** regOwn .x6 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x7 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
      have hq1 : ((Rest **
          (typePtr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1)) **
          (innerPtr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2)) s := by
        dsimp only [Rest]
        xperm_hyp hq
      have hq2 :
          ((Rest ** memOwn typePtr) ** memOwn innerPtr) s :=
        sepConj_mono
          (sepConj_mono (fun _ x => x) memIs_implies_memOwn)
          memIs_implies_memOwn s hq1
      dsimp only [Qassumed, Rest] at hq2 ⊢
      xperm_hyp hq2) hf
  refine cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore, typeStableScratch] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qassumed] at hq ⊢
    exact hq) hpeel

/-- Full ambient Assumed under fullCode (general off/len). -/
structure TypeDispatchAssumedAmbientFull (cr : CodeReq) where
  entry : Word
  success_flat :
    ∀ (ret regionBase loadPtr lenW typePtr innerPtr : Word)
      (bs : List (BitVec 8)) (off len : Nat),
      (ret &&& ~~~(1 : Word)) = ret →
      loadPtr = regionBase + BitVec.ofNat 64 off →
      lenW = BitVec.ofNat 64 len →
      (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word) →
      regionBase.toNat % 8 = 0 →
      off + len ≤ bs.length →
      regionBase.toNat + bs.length < 2 ^ 64 →
      isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true →
      cpsTripleWithin nTypeSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
          (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
          bytesRegion regionBase bs **
          memOwn typePtr ** memOwn innerPtr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion regionBase bs **
          memOwn typePtr ** memOwn innerPtr **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)))

def typeDispatchAssumedAmbient_fullCode : TypeDispatchAssumedAmbientFull fullCode where
  entry := BitVec.ofNat 64 GuestAddrs.tx_type_dispatch
  success_flat := fun ret regionBase loadPtr lenW typePtr innerPtr bs off len
      hret hptr hlen hsuccess halign hbound hover hvalid =>
    cpsTripleWithin_extend_code type_mono
      (typeDispatch_assumed_ambient_flat_typeCode ret regionBase loadPtr lenW
        typePtr innerPtr bs off len hret hptr hlen hsuccess halign hbound
        hover hvalid)

#print axioms txTypeDispatch_success_ambient
#print axioms typeDispatch_assumed_ambient_flat_typeCode
#print axioms typeDispatchAssumedAmbient_fullCode

end EvmAsm.Codegen.TxTypeDispatchSpec

