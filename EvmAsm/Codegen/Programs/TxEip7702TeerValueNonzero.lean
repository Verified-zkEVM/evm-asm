/-
  Teer: walk_next after recipient (value field) + store teer_value_nonzero.
  AfterRecipientSave (E+380): MV a0,s8; MV a1,s9; JAL walk_next; BNE a1=0;
  SLTU x30,x0,a2; la/sd teer_value_nonzero → AfterValueNonzero (E+412).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxEip7702TeerSpec
import EvmAsm.Codegen.Programs.TxEip7702TeerType
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNext0
import EvmAsm.Codegen.Programs.TxEip7702TeerWalkNextSkip
import EvmAsm.Codegen.Programs.TxEip7702TeerRecipient
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxEip7702TeerSpec

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

abbrev ValueNonzeroAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_value_nonzero

abbrev WalkNextValueJalPc : Word := E + 388
abbrev LinkWalkNextValue : Word := E + 392
abbrev AfterWalkNextValueBne : Word := E + 396
abbrev AfterValueSltu : Word := E + 400
abbrev AfterValueNonzero : Word := E + 412

def walkNextValueJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next
    (GuestAddrs.tx_eip7702_existing_authority_refund + 388)

theorem walkNextValueJalOff_resolves :
    (WalkNextValueJalPc + signExtend21 walkNextValueJalOff) &&& ~~~(1 : Word) = WN := by
  simp only [WalkNextValueJalPc, WN, walkNextValueJalOff, E]; decide

abbrev teerWalkNextValueBneOff : BitVec 13 := 2464

theorem teerWalkNextValueMvA0S8 (cursor a0Old : Word) :
    cpsTripleWithin 1 AfterRecipientSave (E + 384) teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ a0Old))
      ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) := by
  have h0 := mv_spec_gen_within .x10 .x24 cursor a0Old AfterRecipientSave (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterRecipientSave teerProg 95
        (.MV .x10 .x24) (by simp only [AfterRecipientSave]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterRecipientSave + 4 : Word) = E + 384 := by
    simp only [AfterRecipientSave]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNextValueMvA1S9 (endPtr a1Old : Word) :
    cpsTripleWithin 1 (E + 384) WalkNextValueJalPc teerLinkedEarly
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old))
      ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := mv_spec_gen_within .x11 .x25 endPtr a1Old (E + 384) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 384) teerProg 96
        (.MV .x11 .x25) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : ((E + 384 : Word) + 4) = WalkNextValueJalPc := by
    simp only [WalkNextValueJalPc]; bv_omega
  rw [hpc] at e0
  exact e0

theorem teerWalkNextValuePrep (cursor endPtr a0Old a1Old : Word) :
    cpsTripleWithin 2 AfterRecipientSave WalkNextValueJalPc teerLinkedEarly
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old))
      ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) := by
  have h0 := teerWalkNextValueMvA0S8 cursor a0Old
  have h0F := cpsTripleWithin_frameR
    ((.x25 ↦ᵣ endPtr) ** (.x11 ↦ᵣ a1Old)) (by pcf) h0
  have h1 := teerWalkNextValueMvA1S9 endPtr a1Old
  have h1F := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x10 ↦ᵣ cursor)) (by pcf) h1
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h0F h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
theorem teerWalkNextValueCall
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (1 + 87) WalkNextValueJalPc LinkWalkNextValue teerLinkedEarly
      ((.x1 ↦ᵣ old1) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNextValue listBase endPtr bs srcOff) := by
  have hret : (LinkWalkNextValue &&& ~~~(1 : Word)) = LinkWalkNextValue := by
    simp only [LinkWalkNextValue, E]; decide
  have hleaf := rlp_walk_next_spec_within WN listBase endPtr LinkWalkNextValue a2Old
    t0Old t1Old t2Old t3Old t4Old t5Old t6Old bs srcOff
    hsalign hoff hover hvalid hss hls hll
  rw [hret] at hleaf
  have hleafP : cpsTripleWithin 87 WN LinkWalkNextValue walkNextCode
      ((.x1 ↦ᵣ LinkWalkNextValue) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      (teerWalkNextPost LinkWalkNextValue listBase endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq ⊢
      xperm_hyp hq) hleaf
  have hcallee := cpsTripleWithin_extend_code teerEarly_mono_walkNext hleafP
  have hcallee' : cpsTripleWithin 87 WN LinkWalkNextValue teerLinkedEarly
      ((.x1 ↦ᵣ LinkWalkNextValue) **
        teerWalkNextPrest (listBase + BitVec.ofNat 64 srcOff) endPtr
          a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
      ((.x1 ↦ᵣ LinkWalkNextValue) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) **
         (fun h =>
           rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff h ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h) ∨
           (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜¬ ∃ next len, rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
                endPtr next len⌝) h)))) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
      simp only [teerWalkNextPost] at hq
      xperm_hyp hq) hcallee
  have hcall := callWithin_spec WalkNextValueJalPc WN old1 walkNextValueJalOff 87
    walkNextValueJalOff_resolves
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E WalkNextValueJalPc teerProg 97
        (.JAL .x1 walkNextValueJalOff) (by simp only [WalkNextValueJalPc]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerWalkNextPrest_pcFree (listBase + BitVec.ofNat 64 srcOff) endPtr
      a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
    hcallee'
  rw [show (WalkNextValueJalPc + 4 : Word) = LinkWalkNextValue from by
    simp only [WalkNextValueJalPc, LinkWalkNextValue]; bv_omega] at hcall
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => by
    simp only [teerWalkNextPost]
    xperm_hyp hq) hcall

theorem teerWalkNextValueBneOk :
    cpsTripleWithin 1 LinkWalkNextValue AfterWalkNextValueBne teerLinkedEarly
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x11 .x0 teerWalkNextValueBneOff
    (0 : Word) (0 : Word) LinkWalkNextValue
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkWalkNextValue teerProg 98
        (.BNE .x11 .x0 teerWalkNextValueBneOff)
        (by simp only [LinkWalkNextValue]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkWalkNextValue + 4 = AfterWalkNextValueBne := by
    simp only [LinkWalkNextValue, AfterWalkNextValueBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

/-- `sltu x30, x0, a2` — flag = (0 <u len). -/
theorem teerValueSltu (lenW t5Old : Word) :
    cpsTripleWithin 1 AfterWalkNextValueBne AfterValueSltu teerLinkedEarly
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x30 ↦ᵣ t5Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) **
        (.x30 ↦ᵣ (if BitVec.ult (0 : Word) lenW then (1 : Word) else 0))) := by
  have hs := sltu_spec_gen_within .x30 .x0 .x12 t5Old (0 : Word) lenW
    AfterWalkNextValueBne (by decide)
  have he := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterWalkNextValueBne teerProg 99
        (.SLTU .x30 .x0 .x12) (by simp only [AfterWalkNextValueBne]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hs
  have hpc : AfterWalkNextValueBne + 4 = AfterValueSltu := by
    simp only [AfterWalkNextValueBne, AfterValueSltu]; bv_omega
  rw [hpc] at he
  exact he

private theorem addr_add_off0 (a : Word) : a + signExtend12 (0 : BitVec 12) = a := by
  simp [signExtend12]

/-- `la x5, teer_value_nonzero` at E+400. -/
theorem teerLaValueNonzero (v : Word) :
    cpsTripleWithin 2 AfterValueSltu (E + 408) teerLinkedEarly
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ ValueNonzeroAddr) := by
  have hau : ∀ a i, CodeReq.singleton AfterValueSltu
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_value_nonzero
        (GuestAddrs.tx_eip7702_existing_authority_refund + 400)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterValueSltu teerProg 100
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.teer_value_nonzero
          (GuestAddrs.tx_eip7702_existing_authority_refund + 400)))
        (by simp only [AfterValueSltu]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AfterValueSltu + 4)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_value_nonzero
        (GuestAddrs.tx_eip7702_existing_authority_refund + 400)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (AfterValueSltu + 4) teerProg 101
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.teer_value_nonzero
          (GuestAddrs.tx_eip7702_existing_authority_refund + 400)))
        (by simp only [AfterValueSltu]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x5 v AfterValueSltu ValueNonzeroAddr
    (by decide) (by decide) hau had
  rw [show (AfterValueSltu : Word) + 8 = E + 408 from by
    simp only [AfterValueSltu, E]; bv_omega] at h
  exact h

private theorem teerSdCellVnz (rs2 : Reg) (addr data : Word) (pc : Word)
    (hmem : ∀ a i, CodeReq.singleton pc (.SD .x5 rs2 (0 : BitVec 12)) a = some i →
      teerLinkedEarly a = some i) :
    cpsTripleWithin 1 pc (pc + 4) teerLinkedEarly
      ((.x5 ↦ᵣ addr) ** (rs2 ↦ᵣ data) ** memOwn addr)
      ((.x5 ↦ᵣ addr) ** (rs2 ↦ᵣ data) ** memOwn addr) := by
  have heq := addr_add_off0 addr
  have h0 := sd_spec_gen_own_within .x5 rs2 addr data (0 : BitVec 12) pc
  have h1 := cpsTripleWithin_extend_code hmem h0
  have h2 : cpsTripleWithin 1 pc (pc + 4) teerLinkedEarly
      ((.x5 ↦ᵣ addr) ** (rs2 ↦ᵣ data) ** memOwn addr)
      ((.x5 ↦ᵣ addr) ** (rs2 ↦ᵣ data) ** (addr ↦ₘ data)) := by
    convert h1 using 1 <;> simp only [heq]
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq =>
      sepConj_mono_right
        (sepConj_mono_right (fun _ hh => memIs_implies_memOwn _ hh)) _ hq) h2

/-- `sd x30, 0(x5)` into teer_value_nonzero. -/
theorem teerSdValueNonzero (v5 flag : Word) (hv : v5 = ValueNonzeroAddr) :
    cpsTripleWithin 1 (E + 408) AfterValueNonzero teerLinkedEarly
      ((.x5 ↦ᵣ v5) ** (.x30 ↦ᵣ flag) ** memOwn ValueNonzeroAddr)
      ((.x5 ↦ᵣ v5) ** (.x30 ↦ᵣ flag) ** memOwn ValueNonzeroAddr) := by
  subst hv
  have h := teerSdCellVnz .x30 ValueNonzeroAddr flag (E + 408)
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 408) teerProg 102
        (.SD .x5 .x30 (0 : BitVec 12)) (by bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
  have hpc : (E + 408 : Word) + 4 = AfterValueNonzero := by
    simp only [AfterValueNonzero, E]; bv_omega
  rw [hpc] at h
  exact h

/-- Store value_nonzero flag after walk_next ok: SLTU + la/sd (4 steps). -/
theorem teerValueNonzeroStore (lenW t5Old v5 : Word) :
    cpsTripleWithin 4 AfterWalkNextValueBne AfterValueNonzero teerLinkedEarly
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) ** (.x30 ↦ᵣ t5Old) ** (.x5 ↦ᵣ v5) **
        memOwn ValueNonzeroAddr)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) **
        (.x30 ↦ᵣ (if BitVec.ult (0 : Word) lenW then (1 : Word) else 0)) **
        (.x5 ↦ᵣ ValueNonzeroAddr) ** memOwn ValueNonzeroAddr) := by
  have hs := teerValueSltu lenW t5Old
  have hsF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** memOwn ValueNonzeroAddr) (by pcf) hs
  have hla := teerLaValueNonzero v5
  have hlaF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW) **
      (.x30 ↦ᵣ (if BitVec.ult (0 : Word) lenW then (1 : Word) else 0)) **
      memOwn ValueNonzeroAddr) (by pcf) hla
  have hsd := teerSdValueNonzero ValueNonzeroAddr
    (if BitVec.ult (0 : Word) lenW then (1 : Word) else 0) rfl
  have hsdF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ lenW)) (by pcf) hsd
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsF hlaF
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 hsdF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c1

#print axioms teerWalkNextValuePrep
#print axioms teerWalkNextValueCall
#print axioms teerWalkNextValueBneOk
#print axioms teerValueSltu
#print axioms teerValueNonzeroStore

/-! ## Value walk_next CycleOk + store compose -/

def teerWalkNextValueCommon (listBase : Word) (bs : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNextValue) **
    bytesRegion listBase bs

theorem teerWalkNextValuePost_to_commonOutcome
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    ∀ h, teerWalkNextPost LinkWalkNextValue listBase endPtr bs srcOff h →
      (teerWalkNextValueCommon listBase bs **
        teerWalkNext0Outcome listBase endPtr bs srcOff) h := by
  intro h hp
  simp only [teerWalkNextPost, teerWalkNextValueCommon] at hp ⊢
  xperm_hyp hp

theorem teerWalkNextValueBneOk_framed
    (listBase next len : Word) (bs : List (BitVec 8)) :
    cpsTripleWithin 1 LinkWalkNextValue AfterWalkNextValueBne teerLinkedEarly
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
        bytesRegion listBase bs)
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
        bytesRegion listBase bs) := by
  have h0 := teerWalkNextValueBneOk
  have hF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
      bytesRegion listBase bs)
    (by pcf) h0
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

theorem teerWalkNextValueOkNested_bne
    (listBase endPtr : Word) (bs : List (BitVec 8)) (srcOff : Nat) :
    cpsTripleWithin 1 LinkWalkNextValue AfterWalkNextValueBne teerLinkedEarly
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNextValue) **
        bytesRegion listBase bs) **
        rlpWalkNextOk (listBase + BitVec.ofNat 64 srcOff) endPtr bs srcOff)
      (fun h => ∃ next len : Word,
        (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
          bytesRegion listBase bs) **
          ⌜rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
            endPtr next len⌝) h) := by
  let cursor := listBase + BitVec.ofNat 64 srcOff
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ next len : Word,
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ LinkWalkNextValue) **
        bytesRegion listBase bs) **
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝)) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hCom, hOk⟩ := hp
      obtain ⟨next, len, hw⟩ := hOk
      exact ⟨next, len, h1, h2, hd, hu, hCom, hw⟩)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
  refine cpsTripleWithin_weaken
    (P := ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝ **
      (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
          bytesRegion listBase bs)))
    (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hdec => ?_)
  have h0 := teerWalkNextValueBneOk_framed listBase next len bs
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
    refine ⟨next, len, ?_⟩
    exact (sepConj_pure_right h).mpr ⟨hq, hdec⟩) h0

private abbrev nWalkNextValueCycle : Nat := 2 + (1 + 87) + 1
private abbrev nValueNonzeroCycle : Nat := nWalkNextValueCycle + 4

set_option maxRecDepth 8000 in
/-- Value walk_next: Prep+Call+BNE ok (no Save). Post ∃ next len; s8 stays cursor. -/
theorem teerWalkNextValueCycleOk
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 v24 v25 a0Old a1Old : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next len : Word,
      rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
        endPtr next len)
    (hinb : BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hcur : v24 = listBase + BitVec.ofNat 64 srcOff)
    (hend : v25 = endPtr) :
    let cursor := listBase + BitVec.ofNat 64 srcOff
    cpsTripleWithin nWalkNextValueCycle AfterRecipientSave AfterWalkNextValueBne
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (fun h => ∃ next len : Word,
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
          bytesRegion listBase bs **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
  intro cursor
  have hprep := teerWalkNextValuePrep cursor endPtr a0Old a1Old
  have hprepF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) **
      (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hprep
  have hprep' :
      cpsTripleWithin 2 AfterRecipientSave WalkNextValueJalPc teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
    refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [hcur, hend] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hprepF
  have hcall := teerWalkNextValueCall listBase endPtr a2Old t0Old t1Old t2Old t3Old
    t4Old t5Old t6Old bs srcOff old1 hsalign hoff hover hvalid hss hls hll
  have hcallOk :
      cpsTripleWithin (1 + 87) WalkNextValueJalPc LinkWalkNextValue teerLinkedEarly
        ((.x1 ↦ᵣ old1) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (teerWalkNextValueCommon listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hcall
    have hq' := teerWalkNextValuePost_to_commonOutcome listBase endPtr bs srcOff h hq
    obtain ⟨hC, hO, hd, hu, hcom, hout⟩ := hq'
    exact ⟨hC, hO, hd, hu, hcom,
      teerWalkNext0Outcome_drop_fail_of_decode listBase endPtr bs srcOff
        hdec hinb hO hout⟩
  have hcallF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hcallOk
  have hcallF' :
      cpsTripleWithin (1 + 87) WalkNextValueJalPc LinkWalkNextValue teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          teerWalkNextPrest cursor endPtr
            a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBase bs)
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNextValueCommon listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff) := by
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [teerWalkNextPrest] at hp ⊢
      xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hcallF
  have hseq1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [teerWalkNextPrest] at hp ⊢
    xperm_hyp hp) hprep' hcallF'
  have hbne := teerWalkNextValueOkNested_bne listBase endPtr bs srcOff
  have hbneF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) (by pcf) hbne
  have hbneMid :
      cpsTripleWithin 1 LinkWalkNextValue AfterWalkNextValueBne teerLinkedEarly
        (((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr)) **
          teerWalkNextValueCommon listBase bs **
          rlpWalkNextOk cursor endPtr bs srcOff)
        (fun h => ∃ next len : Word,
          ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
            bytesRegion listBase bs **
            ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
    refine cpsTripleWithin_weaken (fun h hp => by
      simp only [teerWalkNextValueCommon] at hp ⊢
      xperm_hyp hp) (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hEx, hFr⟩ := hq
      obtain ⟨next, len, hOk⟩ := hEx
      refine ⟨next, len, ?_⟩
      have hnest :
          ((((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
            bytesRegion listBase bs) **
            ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) **
            ((.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr))) h :=
        ⟨h1, h2, hd, hu, hOk, hFr⟩
      xperm_hyp hnest) hbneF
  have hseq2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hseq1 hbneMid
  exact cpsTripleWithin_mono_nSteps
    (by decide : ((2 + (1 + 87)) + 1) ≤ nWalkNextValueCycle) hseq2

set_option maxRecDepth 8000 in
/-- Full value cycle: walk_next ok + SLTU/la/sd teer_value_nonzero. -/
theorem teerValueNonzeroCycleOk
    (listBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (srcOff : Nat) (old1 v24 v25 a0Old a1Old : Word)
    (hsalign : listBase.toNat % 8 = 0)
    (hoff : srcOff < bs.length)
    (hover : listBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < bs.length ∧ listBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((bs[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ bs.length ∧
        listBase.toNat + (srcOff + 1 +
          ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((bs[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hdec : ∃ next len : Word,
      rlpItemDecode bs srcOff (listBase + BitVec.ofNat 64 srcOff)
        endPtr next len)
    (hinb : BitVec.ult (listBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (hcur : v24 = listBase + BitVec.ofNat 64 srcOff)
    (hend : v25 = endPtr) :
    let cursor := listBase + BitVec.ofNat 64 srcOff
    cpsTripleWithin nValueNonzeroCycle AfterRecipientSave AfterValueNonzero
      teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
        (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
        memOwn ValueNonzeroAddr)
      (fun h => ∃ next len : Word,
        ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
          (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x30 ↦ᵣ (if BitVec.ult (0 : Word) len then (1 : Word) else 0)) **
          (.x5 ↦ᵣ ValueNonzeroAddr) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
          bytesRegion listBase bs ** memOwn ValueNonzeroAddr **
          ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) h) := by
  intro cursor
  have hwn := teerWalkNextValueCycleOk listBase endPtr a2Old t0Old t1Old t2Old t3Old
    t4Old t5Old t6Old bs srcOff old1 v24 v25 a0Old a1Old
    hsalign hoff hover hvalid hss hls hll hdec hinb hcur hend
  have hwnF := cpsTripleWithin_frameR (memOwn ValueNonzeroAddr) (by pcf) hwn
  have hwn' :
      cpsTripleWithin nWalkNextValueCycle AfterRecipientSave AfterWalkNextValueBne
        teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
          memOwn ValueNonzeroAddr)
        (fun h => ∃ next len : Word,
          (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
            (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
            bytesRegion listBase bs **
            ⌜rlpItemDecode bs srcOff cursor endPtr next len⌝) **
            memOwn ValueNonzeroAddr) h) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hwnF
    -- Reshape double-∃ to pair-∃ so sepConj_exists_left applies once
    have hqP :
        ((fun hp => ∃ p : Word × Word,
            ((.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
              (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
              (.x0 ↦ᵣ (0 : Word)) **
              regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
              bytesRegion listBase bs **
              ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝) hp) **
          memOwn ValueNonzeroAddr) h := by
      obtain ⟨h1, h2, hd, hu, hEx, hR⟩ := hq
      obtain ⟨nxt, ln, hB⟩ := hEx
      exact ⟨h1, h2, hd, hu, ⟨(nxt, ln), hB⟩, hR⟩
    have hq1 :=
      (sepConj_exists_left
        (F := fun (p : Word × Word) =>
          (.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
            (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
            (.x0 ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
            bytesRegion listBase bs **
            ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝)
        (R := memOwn ValueNonzeroAddr) h).mp hqP
    obtain ⟨⟨nxt, ln⟩, hq4⟩ := hq1
    exact ⟨nxt, ln, hq4⟩
  let Mid (p : Word × Word) : Assertion :=
    ((.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
      (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
      (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
      bytesRegion listBase bs **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝) **
      memOwn ValueNonzeroAddr
  have hwnE :
      cpsTripleWithin nWalkNextValueCycle AfterRecipientSave AfterWalkNextValueBne
        teerLinkedEarly
        ((.x1 ↦ᵣ old1) ** (.x24 ↦ᵣ v24) ** (.x25 ↦ᵣ v25) **
          (.x10 ↦ᵣ a0Old) ** (.x11 ↦ᵣ a1Old) ** (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
          (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
          (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
          memOwn ValueNonzeroAddr)
        (fun h => ∃ p : Word × Word, Mid p h) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hwn'
    obtain ⟨nxt, ln, hq'⟩ := hq
    exact ⟨(nxt, ln), by
      change Mid (nxt, ln) h
      dsimp only [Mid]
      exact hq'⟩
  let Fin (p : Word × Word) : Assertion :=
    (.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
      (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x30 ↦ᵣ (if BitVec.ult (0 : Word) p.2 then (1 : Word) else 0)) **
      (.x5 ↦ᵣ ValueNonzeroAddr) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
      bytesRegion listBase bs ** memOwn ValueNonzeroAddr **
      ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝
  have hstore (p : Word × Word) :
      cpsTripleWithin 4 AfterWalkNextValueBne AfterValueNonzero teerLinkedEarly
        (Mid p) (Fin p) := by
    -- Core store (regIs x30/x5) framed under ambient regs + pure
    have hcore (t5 v5 : Word) :
        cpsTripleWithin 4 AfterWalkNextValueBne AfterValueNonzero teerLinkedEarly
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) ** (.x30 ↦ᵣ t5) ** (.x5 ↦ᵣ v5) **
            memOwn ValueNonzeroAddr)
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
            (.x30 ↦ᵣ (if BitVec.ult (0 : Word) p.2 then (1 : Word) else 0)) **
            (.x5 ↦ᵣ ValueNonzeroAddr) ** memOwn ValueNonzeroAddr) :=
      teerValueNonzeroStore p.2 t5 v5
    let Amb : Assertion :=
      (.x10 ↦ᵣ p.1) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ cursor) ** (.x25 ↦ᵣ endPtr) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x31 ** (.x1 ↦ᵣ LinkWalkNextValue) **
        bytesRegion listBase bs **
        ⌜rlpItemDecode bs srcOff cursor endPtr p.1 p.2⌝
    have hstoreF (t5 v5 : Word) :
        cpsTripleWithin 4 AfterWalkNextValueBne AfterValueNonzero teerLinkedEarly
          (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) ** (.x30 ↦ᵣ t5) ** (.x5 ↦ᵣ v5) **
            memOwn ValueNonzeroAddr) ** Amb)
          (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
            (.x30 ↦ᵣ (if BitVec.ult (0 : Word) p.2 then (1 : Word) else 0)) **
            (.x5 ↦ᵣ ValueNonzeroAddr) ** memOwn ValueNonzeroAddr) ** Amb) :=
      cpsTripleWithin_frameR Amb (by pcf) (hcore t5 v5)
    -- Lift x5: of_forall prest is (P) ** regOwn (paren assoc)
    have h5 (t5 : Word) :
        cpsTripleWithin 4 AfterWalkNextValueBne AfterValueNonzero teerLinkedEarly
          (((( .x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) ** (.x30 ↦ᵣ t5) **
            memOwn ValueNonzeroAddr) ** Amb) ** regOwn .x5)
          (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
            (.x30 ↦ᵣ (if BitVec.ult (0 : Word) p.2 then (1 : Word) else 0)) **
            (.x5 ↦ᵣ ValueNonzeroAddr) ** memOwn ValueNonzeroAddr) ** Amb) := by
      exact cpsTripleWithin_of_forall_regIs_to_regOwn
        (r := .x5)
        (P := ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) ** (.x30 ↦ᵣ t5) **
          memOwn ValueNonzeroAddr) ** Amb)
        (fun v5 =>
          cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
            (fun _ hq => hq) (hstoreF t5 v5))
    -- Lift x30
    have h30 :
        cpsTripleWithin 4 AfterWalkNextValueBne AfterValueNonzero teerLinkedEarly
          (((((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) ** memOwn ValueNonzeroAddr) **
            Amb) ** regOwn .x5) ** regOwn .x30)
          (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) **
            (.x30 ↦ᵣ (if BitVec.ult (0 : Word) p.2 then (1 : Word) else 0)) **
            (.x5 ↦ᵣ ValueNonzeroAddr) ** memOwn ValueNonzeroAddr) ** Amb) := by
      exact cpsTripleWithin_of_forall_regIs_to_regOwn
        (r := .x30)
        (P := (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ p.2) ** memOwn ValueNonzeroAddr) **
          Amb) ** regOwn .x5)
        (fun t5 =>
          cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
            (fun _ hq => hq) (h5 t5))
    -- Mid → lifted prest; Fin ← lifted post
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        dsimp only [Mid] at hp
        xperm_hyp hp)
      (fun _ hq => by
        dsimp only [Fin]
        xperm_hyp hq) h30
  have hstoreE (p : Word × Word) :
      cpsTripleWithin 4 AfterWalkNextValueBne AfterValueNonzero teerLinkedEarly
        (Mid p) (fun h => ∃ q : Word × Word, Fin q h) :=
    cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hq => ⟨p, hq⟩) (hstore p)
  have hseq := cpsTripleWithin_seq_exists_same_cr hwnE hstoreE
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => by
    obtain ⟨⟨nxt, ln⟩, hq'⟩ := hq
    exact ⟨nxt, ln, by
      change Fin (nxt, ln) h at hq'
      dsimp only [Fin] at hq'
      exact hq'⟩)
    (cpsTripleWithin_mono_nSteps
      (by decide : nWalkNextValueCycle + 4 ≤ nValueNonzeroCycle) hseq)

#print axioms teerWalkNextValueCycleOk
#print axioms teerValueNonzeroCycleOk

end EvmAsm.Codegen.TxEip7702TeerSpec
