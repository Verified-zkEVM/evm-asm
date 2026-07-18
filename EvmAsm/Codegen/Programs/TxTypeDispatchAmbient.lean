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
open EvmAsm.Rv64.SAsm (toNat_zeroExtend_byte)
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

/-- Local PC/helper facts (Spec counterparts are private). -/
private theorem amb_se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem amb_type_bound : 4 * typeProg.length < 2 ^ 64 := by
  rw [type_length]; decide
private theorem amb_ofNat_ne_zero {a : Nat} (h0 : a ≠ 0) (hlt : a < 2 ^ 64) :
    BitVec.ofNat 64 a ≠ (0 : Word) := by
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h2
  have hz : ((0 : Word).toNat) = 0 := by decide
  omega
private theorem amb_not_ult_zx_192 (b : BitVec 8) (h : 192 ≤ b.toNat) :
    ¬ BitVec.ult (b.zeroExtend 64 : Word) (192 : Word) := by
  intro hult
  have hlt : (b.zeroExtend 64 : Word).toNat < (192 : Word).toNat := by
    rwa [← BitVec.ult_iff_toNat_lt]
  have hz := toNat_zeroExtend_byte b
  have h192 : (192 : Word).toNat = 192 := by decide
  omega
private theorem amb_D4 : D + 4 = D + BitVec.ofNat 64 (4 * 1) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem amb_D8 : D + 8 = D + BitVec.ofNat 64 (4 * 2) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem amb_D12 : D + 12 = D + BitVec.ofNat 64 (4 * 3) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem amb_LegacyLi_eq : LegacyLi = D + BitVec.ofNat 64 (4 * 13) := by
  simp only [LegacyLi, D, GuestAddrs.tx_type_dispatch]; decide
private theorem amb_D56 : D + 56 = D + BitVec.ofNat 64 (4 * 14) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem amb_D60 : D + 60 = D + BitVec.ofNat 64 (4 * 15) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide
private theorem amb_D64 : D + 64 = D + BitVec.ofNat 64 (4 * 16) := by
  simp only [D, GuestAddrs.tx_type_dispatch]; decide

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact bytesRegion_pcFree _ _
      | exact pcFree_emp
      | exact pcFree_pure)

set_option maxRecDepth 8000 in
/-- Ambient legacy OkRet: region is framed only (no byte reads). classical-3. -/
theorem typeLegacyOkRet_ambient
    (raIn regionBase typePtr innerPtr oldT oldI a0v a1v v5 v6 : Word)
    (bs : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn) :
    cpsTripleWithin 4 LegacyLi raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ a0v) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ a1v) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word))) :=
  typeLegacyOkRet_spec raIn regionBase typePtr innerPtr oldT oldI a0v a1v v5 v6
    bs hret

set_option maxRecDepth 8000 in
/-- Ambient legacy path: LBU at `loadPtr = regionBase+off` over full region. classical-3. -/
theorem txTypeDispatch_legacy_ambient
    (raIn regionBase loadPtr typePtr innerPtr oldT oldI v5 v6 : Word)
    (bs : List (BitVec 8)) (off len : Nat) (b : BitVec 8) (rest : List (BitVec 8))
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hslice : txSlice bs off len = b :: rest)
    (hlegacy : 192 ≤ b.toNat)
    (halign : regionBase.toNat % 8 = 0)
    (hlen_bound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin 8 D raIn typeCode
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ loadPtr) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ (0 : Word)) ** (innerPtr ↦ₘ (0 : Word)) **
        (.x5 ↦ᵣ (b.zeroExtend 64)) ** (.x6 ↦ᵣ (192 : Word)) **
        (.x0 ↦ᵣ (0 : Word))) := by
  have hlen_pos : 0 < len := by
    have := congrArg List.length hslice
    simp only [List.length_cons] at this
    have hsl := txSlice_length bs off len hlen_bound
    omega
  have hlen_ne : BitVec.ofNat 64 len ≠ (0 : Word) := by
    have hpos : len ≠ 0 := Nat.ne_of_gt hlen_pos
    have hlt : len < 2 ^ 64 := by omega
    exact amb_ofNat_ne_zero hpos hlt
  have hoff : off < bs.length := by omega
  have hover_off : regionBase.toNat + off < 2 ^ 64 := by omega
  -- [0] BEQ a1,x0 +164 ntaken
  have hbr0 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D D typeProg 0
      (.BEQ .x11 .x0 (164 : BitVec 13))
      (by decide) (by rw [type_length]; decide) rfl amb_type_bound)
    (beq_spec_gen_within .x11 .x0 (164 : BitVec 13)
      (BitVec.ofNat 64 len) (0 : Word) D)
  have hnt0 := cpsBranchWithin_ntakenStripPure2 hbr0 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd ((sepConj_pure_right _).1 hrest).2 hlen_ne)
  have hnt0F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ loadPtr) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      (by pcf) hnt0
  -- [1] LBU x5, 0(x10) ambient
  have hlbu0 := type_dispatch_lbu_ambient .x5 .x10 regionBase loadPtr v5 (D + 4)
    bs off (by decide) hptr halign hoff hover_off hvalid
  have hpc_lbu : (D + 4) + 4 = D + 8 := by
    simp only [D, GuestAddrs.tx_type_dispatch]; decide
  have hbyte : bs[off]'hoff = b := by
    have h0 := txSlice_getElem_zero bs off len hlen_pos hlen_bound
    simpa [hslice, List.getElem_cons_zero] using h0.symm
  have hlbu0' : cpsTripleWithin 1 (D + 4) (D + 8)
      (CodeReq.singleton (D + 4) (.LBU .x5 .x10 (0 : BitVec 12)))
      ((.x10 ↦ᵣ loadPtr) ** (.x5 ↦ᵣ v5) ** bytesRegion regionBase bs)
      ((.x10 ↦ᵣ loadPtr) ** (.x5 ↦ᵣ (b.zeroExtend 64)) **
        bytesRegion regionBase bs) := by
    rw [← hpc_lbu]
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      rw [hbyte] at hq; exact hq) hlbu0
  have hlbuE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 4) typeProg 1
      (.LBU .x5 .x10 (0 : BitVec 12))
      amb_D4 (by rw [type_length]; decide) rfl amb_type_bound) hlbu0'
  have hlbuF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x6 ↦ᵣ v6) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hlbuE
  -- [2] LI x6, 192
  have hli := li_spec_gen_within .x6 v6 (192 : Word) (D + 8) (by decide)
  have hliE := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 8) typeProg 2
      (.LI .x6 (192 : Word))
      amb_D8 (by rw [type_length]; decide) rfl amb_type_bound) hli
  have hliF :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ loadPtr) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x5 ↦ᵣ (b.zeroExtend 64)) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcf) hliE
  -- [3] BGEU x5,x6 +40 TAKEN → LegacyLi
  have hbr3 := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 12) typeProg 3
      (.BGEU .x5 .x6 (40 : BitVec 13))
      amb_D12 (by rw [type_length]; decide) rfl amb_type_bound)
    (bgeu_spec_gen_within .x5 .x6 (40 : BitVec 13)
      (b.zeroExtend 64) (192 : Word) (D + 12))
  have hpc3 : (D + 12) + signExtend13 (40 : BitVec 13) = LegacyLi := by
    simp only [LegacyLi, D, GuestAddrs.tx_type_dispatch]; decide
  rw [hpc3] at hbr3
  have htk3 := cpsBranchWithin_takenStripPure2 hbr3 (fun _ hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact (amb_not_ult_zx_192 b hlegacy) ((sepConj_pure_right _).1 hrest).2)
  have htk3F :=
    cpsTripleWithin_frameR
      ((.x1 ↦ᵣ raIn) ** (.x10 ↦ᵣ loadPtr) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x12 ↦ᵣ typePtr) ** (.x13 ↦ᵣ innerPtr) **
        bytesRegion regionBase bs **
        (typePtr ↦ₘ oldT) ** (innerPtr ↦ₘ oldI) **
        (.x0 ↦ᵣ (0 : Word)))
      (by pcf) htk3
  have hleg :=
    typeLegacyOkRet_ambient raIn regionBase typePtr innerPtr oldT oldI
      loadPtr (BitVec.ofNat 64 len) (b.zeroExtend 64) (192 : Word)
      bs hret
  have c01 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hnt0F hlbuF
  have c02 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hliF
  have c03 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 htk3F
  have c04 :=
    cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 hleg
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c04

#print axioms type_dispatch_lbu_ambient
#print axioms typeDispatchAssumedAmbient_off0_pkg
#print axioms typeLegacyOkRet_ambient
#print axioms txTypeDispatch_legacy_ambient
#print axioms txSlice_length
#print axioms txSlice_getElem_zero
#print axioms txSlice_off0
#print axioms teer_slice_cons

end EvmAsm.Codegen.TxTypeDispatchSpec
