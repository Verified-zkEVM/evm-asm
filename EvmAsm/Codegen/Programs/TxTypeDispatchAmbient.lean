/-
  Multi-tx Option A substrate for `tx_type_dispatch`.

  Slice form owns `bytesRegion loadPtr slice` (requires loadPtr % 8 = 0).
  Array multi-tx has ambient `bytesRegion regionBase blob` with
  `loadPtr = regionBase + off` (SSZ offs are 4-align, not 8) — cannot peel
  via `bytesRegion_split`. Ambient LBU (BgvOffset-style) keeps the full
  region and indexes `bs[off + k]`.

  This file: ambient LBU first-byte + pure slice bridge + ambient pre/post
  + ambient Assumed structure (off=0 recovers slice discharge).
  Remaining: ambient leaf arms for off≠0 + ExtractAssumed ambient.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Codegen.Programs.TxTypeDispatchTisDischarge
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxTypeDispatchSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (nTypeSteps TypeDispatchAssumed fullCode)

/-- Tx slice viewed by type_dispatch / extract under multi-tx ambient. -/
def txSlice (bs : List (BitVec 8)) (off len : Nat) : List (BitVec 8) :=
  (bs.drop off).take len

theorem txSlice_length (bs : List (BitVec 8)) (off len : Nat)
    (h : off + len ≤ bs.length) :
    (txSlice bs off len).length = len := by
  simp only [txSlice, List.length_take, List.length_drop]
  omega

theorem txSlice_getElem_zero (bs : List (BitVec 8)) (off len : Nat)
    (hpos : 0 < len) (h : off + len ≤ bs.length) :
    (txSlice bs off len)[0]'(by rw [txSlice_length bs off len h]; omega) =
      bs[off]'(by omega) := by
  simp only [txSlice, List.getElem_take, List.getElem_drop, Nat.add_zero]

theorem txSlice_off0 (bs : List (BitVec 8)) :
    txSlice bs 0 bs.length = bs := by
  simp only [txSlice, List.drop_zero, List.take_length]

/-- Ambient flat pre: a0=loadPtr, a1=len, full ambient region. -/
def typeAmbientPre (raIn regionBase loadPtr lenW typePtr innerPtr
    t0Old t1Old typeOld innerOld : Word)
    (bs : List (BitVec 8)) : Assertion :=
  ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
    (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion regionBase bs **
    (typePtr ↦ₘ typeOld) ** (innerPtr ↦ₘ innerOld))

/-- Ambient flat post under teer of the tx slice. -/
def typeAmbientPostOf (raIn regionBase typePtr innerPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat) : Assertion :=
  (regOwn .x5 ** regOwn .x6 ** (.x1 ↦ᵣ raIn) ** (.x0 ↦ᵣ (0 : Word)) **
    bytesRegion regionBase bs **
    (.x10 ↦ᵣ (teerTxTypeDispatch (txSlice bs off len)).1) **
    (typePtr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.1) **
    (innerPtr ↦ₘ (teerTxTypeDispatch (txSlice bs off len)).2.2) **
    regOwn .x11 ** regOwn .x12 ** regOwn .x13)

theorem typeAmbientPre_off0
    (raIn regionBase typePtr innerPtr t0Old t1Old typeOld innerOld : Word)
    (bs : List (BitVec 8)) :
    typeAmbientPre raIn regionBase regionBase (BitVec.ofNat 64 bs.length)
        typePtr innerPtr t0Old t1Old typeOld innerOld bs =
      typeFlatPre raIn regionBase (BitVec.ofNat 64 bs.length) typePtr innerPtr
        t0Old t1Old typeOld innerOld bs := rfl

theorem typeAmbientPostOf_off0
    (raIn regionBase typePtr innerPtr : Word) (bs : List (BitVec 8)) :
    typeAmbientPostOf raIn regionBase typePtr innerPtr bs 0 bs.length =
      typeFlatPostOf raIn regionBase typePtr innerPtr bs := by
  simp only [typeAmbientPostOf, typeFlatPostOf, txSlice_off0]

set_option maxRecDepth 8000 in
/-- LBU a0+0 over ambient region at byte `off` (rs1 holds loadPtr). classical-3. -/
theorem type_dispatch_lbu_ambient
    (rd rs1 : Reg) (regionBase loadPtr vOld pc : Word)
    (bs : List (BitVec 8)) (off : Nat)
    (hrd : rd ≠ .x0)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (halign : regionBase.toNat % 8 = 0)
    (hi : off < bs.length)
    (hover : regionBase.toNat + off < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin 1 pc (pc + 4)
      (CodeReq.singleton pc (.LBU rd rs1 (0 : BitVec 12)))
      ((rs1 ↦ᵣ loadPtr) ** (rd ↦ᵣ vOld) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ loadPtr) **
        (rd ↦ᵣ ((bs[off]'hi).zeroExtend 64)) ** bytesRegion regionBase bs) := by
  have hlbu := bytesRegion_lbu_within rd rs1 regionBase vOld pc bs off
    hrd halign hi hover hvalid
  refine cpsTripleWithin_weaken
    (fun _ hp => by rw [hptr] at hp; exact hp)
    (fun _ hq => by rw [← hptr] at hq; exact hq) hlbu

/-- Ambient Assumed (off=0 full-len first). off≠0 residual needs ambient arms. -/
structure TypeDispatchAssumedAmbient (cr : CodeReq) where
  entry : Word
  success_flat_off0 :
    ∀ (ret regionBase lenW typePtr innerPtr : Word)
      (bs : List (BitVec 8)),
      (ret &&& ~~~(1 : Word)) = ret →
      lenW = BitVec.ofNat 64 bs.length →
      (teerTxTypeDispatch bs).1 = (0 : Word) →
      regionBase.toNat % 8 = 0 →
      regionBase.toNat + bs.length < 2 ^ 64 →
      isValidByteAccess (regionBase + BitVec.ofNat 64 0) = true →
      cpsTripleWithin nTypeSteps entry ret cr
        ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ regionBase) ** (.x11 ↦ᵣ lenW) **
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

/-- off=0 ambient Assumed from slice discharge. classical-3. -/
def typeDispatchAssumedAmbient_off0_pkg : TypeDispatchAssumedAmbient fullCode where
  entry := typeDispatchAssumed_fullCode.entry
  success_flat_off0 := fun ret regionBase lenW typePtr innerPtr bs
      hret hlen hsuccess halign hover hvalid =>
    typeDispatchAssumed_fullCode.success_flat ret regionBase lenW typePtr innerPtr
      bs hret hlen hsuccess halign hover hvalid

/-- Non-empty slice at off is cons with head bs[off]. -/
theorem teer_slice_cons (bs : List (BitVec 8)) (off len : Nat)
    (hpos : 0 < len) (hbound : off + len ≤ bs.length) :
    ∃ b rest, txSlice bs off len = b :: rest ∧ b = bs[off]'(by omega) := by
  have hlen := txSlice_length bs off len hbound
  have hne : txSlice bs off len ≠ [] := by
    intro he
    have := congrArg List.length he
    simp only [List.length_nil, hlen] at this
    omega
  match hs : txSlice bs off len with
  | [] => exact absurd hs hne
  | b :: rest =>
    refine ⟨b, rest, rfl, ?_⟩
    have h0 := txSlice_getElem_zero bs off len hpos hbound
    simpa [hs, List.getElem_cons_zero] using h0

#print axioms type_dispatch_lbu_ambient
#print axioms typeDispatchAssumedAmbient_off0_pkg
#print axioms txSlice_length
#print axioms txSlice_getElem_zero
#print axioms txSlice_off0
#print axioms teer_slice_cons

end EvmAsm.Codegen.TxTypeDispatchSpec
