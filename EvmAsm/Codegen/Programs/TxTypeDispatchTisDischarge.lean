/-
  Discharge intrinsic `TypeDispatchAssumed` from the proven type_dispatch leaf.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchTop
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxTypeDispatchSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nTypeSteps TypeDispatchAssumed fullCode type_mono)

/-- Pure: success status implies non-empty. -/
theorem teer_success_implies_nonempty (txBytes : List (BitVec 8))
    (h : (teerTxTypeDispatch txBytes).1 = (0 : Word)) :
    0 < txBytes.length := by
  match txBytes with
  | [] =>
    simp only [teerTxTypeDispatch] at h
    exact absurd h (by decide)
  | _ :: _ => simp

/-- Stable scratch framed across the leaf (not used by type_dispatch). -/
def typeStableScratch : Assertion :=
  regOwn .x7 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

private theorem typeStableScratch_pcFree : typeStableScratch.pcFree := by
  unfold typeStableScratch
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regOwn
    | exact pcFree_emp

set_option maxRecDepth 8000 in
/-- Leaf success top (domain-gated). -/
theorem typeDispatch_success_top
    (ret txBase typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
    (txBytes : List (BitVec 8))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin nTxTypeDispatchSteps D ret typeCode
      (typeFlatPre ret txBase (BitVec.ofNat 64 txBytes.length) typePtr innerPtr
        t0Old t1Old typeOld innerOld txBytes)
      (typeFlatPostOf ret txBase typePtr innerPtr txBytes) := by
  have _ := hsuccess
  exact txTypeDispatch_spec_within ret txBase typePtr innerPtr t0Old t1Old
    typeOld innerOld txBytes hret halign hover (Or.inr hvalid0)

set_option maxRecDepth 8000 in
/-- Leaf + frame stable scratch; mono to nTypeSteps; a0=0 under hsuccess. -/
theorem typeDispatch_success_framed
    (ret txBase typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
    (txBytes : List (BitVec 8))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin nTypeSteps D ret typeCode
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ typeOld) ** (innerPtr ↦ₘ innerOld) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        typeStableScratch)
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ (teerTxTypeDispatch txBytes).2.1) **
        (innerPtr ↦ₘ (teerTxTypeDispatch txBytes).2.2) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        (.x0 ↦ᵣ (0 : Word)) ** typeStableScratch) := by
  have h0 := typeDispatch_success_top ret txBase typePtr innerPtr t0Old t1Old
    typeOld innerOld txBytes hret hsuccess halign hover hvalid0
  have h1 : cpsTripleWithin nTxTypeDispatchSteps D ret typeCode
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txBase) **
        (.x11 ↦ᵣ BitVec.ofNat 64 txBytes.length) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        (typePtr ↦ₘ typeOld) ** (innerPtr ↦ₘ innerOld) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)))
      (typeFlatPostOf ret txBase typePtr innerPtr txBytes) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [typeFlatPre] at hp ⊢; xperm_hyp hp) (fun _ hq => hq) h0
  have h2 := cpsTripleWithin_frameR typeStableScratch typeStableScratch_pcFree h1
  have h3 := cpsTripleWithin_mono_nSteps
    (nSteps := nTxTypeDispatchSteps) (nSteps' := nTypeSteps)
    (by simp only [nTxTypeDispatchSteps, nTypeSteps]; omega) h2
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [typeFlatPostOf, hsuccess] at hq
      xperm_hyp hq) h3

/-- Peel memOwn type/inner + regOwn x5/x6 (BgvOffset-style nested destructure). -/
private theorem of_forall_type_dispatch_owns
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
/-- Assumed-shaped triple under `typeCode`. -/
theorem typeDispatch_assumed_flat_typeCode
    (ret txBase lenW typePtr innerPtr : Word)
    (txBytes : List (BitVec 8))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : lenW = BitVec.ofNat 64 txBytes.length)
    (hsuccess : (teerTxTypeDispatch txBytes).1 = (0 : Word))
    (halign : txBase.toNat % 8 = 0)
    (hover : txBase.toNat + txBytes.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (txBase + BitVec.ofNat 64 0) = true) :
    cpsTripleWithin nTypeSteps D ret typeCode
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion txBase txBytes **
        memOwn typePtr ** memOwn innerPtr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBytes **
        memOwn typePtr ** memOwn innerPtr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) := by
  let Pcore : Assertion :=
    (.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ lenW) **
      (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
      bytesRegion txBase txBytes ** (.x0 ↦ᵣ (0 : Word)) ** typeStableScratch
  let Qassumed : Assertion :=
    (.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
      bytesRegion txBase txBytes **
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
    refine of_forall_type_dispatch_owns (typePtr := typePtr) (innerPtr := innerPtr)
      (fun typeOld innerOld t0Old t1Old => ?_)
    have hf := typeDispatch_success_framed ret txBase typePtr innerPtr
      t0Old t1Old typeOld innerOld txBytes hret hsuccess halign hover hvalid0
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore, typeStableScratch] at hp ⊢
      simp only [hlen] at hp ⊢
      xperm_hyp hp) (fun s hq => by
      -- Put type/inner rightmost, convert memIs→memOwn, xperm to Qassumed
      dsimp only [typeStableScratch] at hq
      let Rest : Assertion :=
        (.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x7 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
      have hq1 : ((Rest ** (typePtr ↦ₘ (teerTxTypeDispatch txBytes).2.1)) **
          (innerPtr ↦ₘ (teerTxTypeDispatch txBytes).2.2)) s := by
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

/-- `TypeDispatchAssumed` under intrinsic `fullCode`. -/
def typeDispatchAssumed_fullCode : TypeDispatchAssumed fullCode where
  entry := BitVec.ofNat 64 GuestAddrs.tx_type_dispatch
  success_flat := fun ret txBase lenW typePtr innerPtr txBytes
      hret hlen hsuccess halign hover hvalid0 =>
    cpsTripleWithin_extend_code type_mono
      (typeDispatch_assumed_flat_typeCode ret txBase lenW typePtr innerPtr
        txBytes hret hlen hsuccess halign hover hvalid0)

theorem typeDispatchAssumed_entry :
    typeDispatchAssumed_fullCode.entry =
      BitVec.ofNat 64 GuestAddrs.tx_type_dispatch := rfl

#print axioms typeDispatch_success_top
#print axioms typeDispatch_success_framed
#print axioms typeDispatch_assumed_flat_typeCode
#print axioms typeDispatchAssumed_fullCode

end EvmAsm.Codegen.TxTypeDispatchSpec
