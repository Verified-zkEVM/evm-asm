/-
  Teer type-dispatch setup + call + success BNE (instr 34–41).
  Ambient under TypeDispatchAssumedAmbientFull teerLinkedEarly.
  PC AfterBalCheck → AfterTypeBne (E+168).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerBalCheck
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbientTop
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasSpec
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch txSlice TypeDispatchAssumedAmbientFull)
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (nTypeSteps)

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsSaved _ _ _)

abbrev TypeAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_type
abbrev InnerOffAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_inner_off
abbrev TypeEntry : Word := BitVec.ofNat 64 GuestAddrs.tx_type_dispatch

/-- PC after JAL link (instr 40 → E+164). -/
abbrev LinkType : Word := E + 164
/-- PC after success BNE not-taken (E+168). -/
abbrev AfterTypeBne : Word := E + 168

abbrev typeJalOff : BitVec 21 :=
  jalOff GuestAddrs.tx_type_dispatch
    (GuestAddrs.tx_eip7702_existing_authority_refund + 160)

abbrev teerTypeBneOff : BitVec 13 := (2692 : BitVec 13)

/-- teerCode ⊆ teerLinkedEarly (left-nested unions). -/
theorem teerEarly_mono_teer :
    ∀ a i, teerCode a = some i → teerLinkedEarly a = some i := by
  intro a i hi
  unfold teerLinkedEarly
  have h1 := CodeReq.union_mono_left (cr1 := teerCode) (cr2 := typeCode) a i hi
  have h2 := CodeReq.union_mono_left
    (cr1 := teerCode.union typeCode) (cr2 := walkInitCode) a i h1
  exact CodeReq.union_mono_left
    (cr1 := (teerCode.union typeCode).union walkInitCode) (cr2 := walkNextCode) a i h2

private theorem teer_type_disjoint : teerCode.Disjoint typeCode := by
  unfold teerCode typeCode E
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [teer_length]; decide
  · rw [type_length']; decide
  · rw [teer_length, type_length']; decide

private theorem teer_type_walkInit_disjoint :
    (teerCode.union typeCode).Disjoint walkInitCode := by
  apply CodeReq.Disjoint.union_left
  · unfold teerCode walkInitCode E
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [teer_length]; decide
    · rw [rlp_walk_init_prog_length]; decide
    · rw [teer_length, rlp_walk_init_prog_length]; decide
  · unfold typeCode walkInitCode
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [type_length']; decide
    · rw [rlp_walk_init_prog_length]; decide
    · rw [type_length', rlp_walk_init_prog_length]; decide

private theorem teer_type_walkInit_walkNext_disjoint :
    ((teerCode.union typeCode).union walkInitCode).Disjoint walkNextCode := by
  apply CodeReq.Disjoint.union_left
  · apply CodeReq.Disjoint.union_left
    · unfold teerCode walkNextCode E
      apply CodeReq.Disjoint.ofProg_ranges
      · rw [teer_length]; decide
      · rw [rlp_walk_next_prog_length]; decide
      · rw [teer_length, rlp_walk_next_prog_length]; decide
    · unfold typeCode walkNextCode
      apply CodeReq.Disjoint.ofProg_ranges
      · rw [type_length']; decide
      · rw [rlp_walk_next_prog_length]; decide
      · rw [type_length', rlp_walk_next_prog_length]; decide
  · unfold walkInitCode walkNextCode
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [rlp_walk_init_prog_length]; decide
    · rw [rlp_walk_next_prog_length]; decide
    · rw [rlp_walk_init_prog_length, rlp_walk_next_prog_length]; decide

/-- typeCode ⊆ teerLinkedEarly. -/
theorem teerEarly_mono_type :
    ∀ a i, typeCode a = some i → teerLinkedEarly a = some i := by
  intro a i hi
  unfold teerLinkedEarly
  have h1 := CodeReq.mono_union_right teer_type_disjoint (fun _ _ h => h) a i hi
  have h2 := CodeReq.union_mono_left
    (cr1 := teerCode.union typeCode) (cr2 := walkInitCode) a i h1
  exact CodeReq.union_mono_left
    (cr1 := (teerCode.union typeCode).union walkInitCode) (cr2 := walkNextCode) a i h2

/-- Restore a0/a1 from s0/s1 (instr 34–35). -/
theorem teerTypeAbiRestore (loadPtr lenW : Word) (v10 v11 : Word) :
    cpsTripleWithin 2 AfterBalCheck (E + 144) teerLinkedEarly
      ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11))
      ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW)) := by
  have h0 := mv_spec_gen_within .x10 .x8 loadPtr v10 AfterBalCheck (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterBalCheck teerProg 34
        (.MV .x10 .x8) (by simp only [AfterBalCheck]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have h1 := mv_spec_gen_within .x11 .x9 lenW v11 (E + 140) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 140) teerProg 35
        (.MV .x11 .x9) (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) h1
  have e0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ lenW) ** (.x11 ↦ᵣ v11)) (by pcf) e0
  have e1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x10 ↦ᵣ loadPtr)) (by pcf) e1
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h01

/-- `la x12, teer_type` at E+144 → E+152. -/
theorem teerLaType (v : Word) :
    cpsTripleWithin 2 (E + 144) (E + 152) teerLinkedEarly
      (.x12 ↦ᵣ v) (.x12 ↦ᵣ TypeAddr) := by
  have hau : ∀ a i, CodeReq.singleton (E + 144)
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_type
        (GuestAddrs.tx_eip7702_existing_authority_refund + 144)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 144) teerProg 36
        (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_type
          (GuestAddrs.tx_eip7702_existing_authority_refund + 144)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 148)
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_type
        (GuestAddrs.tx_eip7702_existing_authority_refund + 144)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 148) teerProg 37
        (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_type
          (GuestAddrs.tx_eip7702_existing_authority_refund + 144)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x12 v (E + 144) TypeAddr
    (by decide) (by decide) hau had
  rw [show (E + 144 : Word) + 8 = E + 152 from by bv_omega] at h
  exact h

/-- `la x13, teer_inner_off` at E+152 → E+160. -/
theorem teerLaInnerOff (v : Word) :
    cpsTripleWithin 2 (E + 152) (E + 160) teerLinkedEarly
      (.x13 ↦ᵣ v) (.x13 ↦ᵣ InnerOffAddr) := by
  have hau : ∀ a i, CodeReq.singleton (E + 152)
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.teer_inner_off
        (GuestAddrs.tx_eip7702_existing_authority_refund + 152)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 152) teerProg 38
        (.AUIPC .x13 (Codegen.laHi GuestAddrs.teer_inner_off
          (GuestAddrs.tx_eip7702_existing_authority_refund + 152)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 156)
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.teer_inner_off
        (GuestAddrs.tx_eip7702_existing_authority_refund + 152)))
        a = some i → teerLinkedEarly a = some i := fun a i hi =>
    teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 156) teerProg 39
        (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.teer_inner_off
          (GuestAddrs.tx_eip7702_existing_authority_refund + 152)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x13 v (E + 152) InnerOffAddr
    (by decide) (by decide) hau had
  rw [show (E + 152 : Word) + 8 = E + 160 from by bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Type setup: MV a0/a1 + two las (instr 34–39) → E+160. -/
theorem teerTypeSetup (loadPtr lenW : Word) (v10 v11 v12 v13 : Word) :
    cpsTripleWithin 6 AfterBalCheck (E + 160) teerLinkedEarly
      ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13))
      ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ TypeAddr) ** (.x13 ↦ᵣ InnerOffAddr)) := by
  have hmv := teerTypeAbiRestore loadPtr lenW v10 v11
  have hmvF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13)) (by pcf) hmv
  have h0 := teerLaType v12
  have h0F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) ** (.x13 ↦ᵣ v13)) (by pcf) h0
  have h1 := teerLaInnerOff v13
  have h1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ TypeAddr)) (by pcf) h1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF h0F
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 h1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c12

/-- Ambient type callee: loadPtr in a0; owns full regionBase/bs. -/
def teerTypeCalleePAmbient (regionBase loadPtr lenW : Word)
    (bs : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) **
  (.x12 ↦ᵣ TypeAddr) ** (.x13 ↦ᵣ InnerOffAddr) **
  bytesRegion regionBase bs **
  memOwn TypeAddr ** memOwn InnerOffAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

def teerTypeCalleeQAmbient (regionBase : Word) (bs : List (BitVec 8)) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) **
  bytesRegion regionBase bs **
  memOwn TypeAddr ** memOwn InnerOffAddr **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

theorem teerTypeCalleePAmbient_pcFree (regionBase loadPtr lenW : Word)
    (bs : List (BitVec 8)) :
    (teerTypeCalleePAmbient regionBase loadPtr lenW bs).pcFree := by
  unfold teerTypeCalleePAmbient; pcf

set_option maxRecDepth 8000 in
theorem teerTypeCallAmbient
    (asm : TypeDispatchAssumedAmbientFull teerLinkedEarly)
    (hentry : asm.entry = TypeEntry)
    (regionBase loadPtr lenW : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (old1 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin (1 + nTypeSteps) (E + 160) LinkType teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** teerTypeCalleePAmbient regionBase loadPtr lenW bs)
      ((.x1 ↦ᵣ LinkType) ** teerTypeCalleeQAmbient regionBase bs) := by
  have hret : (LinkType &&& ~~~(1 : Word)) = LinkType := by
    simp only [LinkType, E]; decide
  have hcallee0 := asm.success_flat LinkType regionBase loadPtr lenW
    TypeAddr InnerOffAddr bs off len
    hret hptr hlen hsuccess halign hbound hover hvalid0
  have hcallee0' : cpsTripleWithin nTypeSteps asm.entry LinkType teerLinkedEarly
      ((.x1 ↦ᵣ LinkType) ** teerTypeCalleePAmbient regionBase loadPtr lenW bs)
      ((.x1 ↦ᵣ LinkType) ** teerTypeCalleeQAmbient regionBase bs) := by
    unfold teerTypeCalleePAmbient teerTypeCalleeQAmbient
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcallee0
  have hcallee : cpsTripleWithin nTypeSteps TypeEntry LinkType teerLinkedEarly
      ((.x1 ↦ᵣ LinkType) ** teerTypeCalleePAmbient regionBase loadPtr lenW bs)
      ((.x1 ↦ᵣ LinkType) ** teerTypeCalleeQAmbient regionBase bs) := by
    rw [← hentry]; exact hcallee0'
  have hcall := callWithin_spec (E + 160) TypeEntry old1 typeJalOff nTypeSteps
    (by show (E + 160) + signExtend21 typeJalOff = TypeEntry; decide)
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 160) teerProg 40
        (.JAL .x1 typeJalOff) (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi))
    (teerTypeCalleePAmbient_pcFree regionBase loadPtr lenW bs)
    hcallee
  rw [show (E + 160 + 4 : Word) = LinkType from by
    simp only [LinkType]; bv_omega] at hcall
  exact hcall

set_option maxRecDepth 8000 in
theorem teerTypeBneOk :
    cpsTripleWithin 1 LinkType AfterTypeBne teerLinkedEarly
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 teerTypeBneOff
    (0 : Word) (0 : Word) LinkType
  have hbrC := cpsBranchWithin_extend_code
    (fun a i hi => teerEarly_mono_teer a i
      (CodeReq.ofProg_mem_at E LinkType teerProg 41
        (.BNE .x10 .x0 teerTypeBneOff)
        (by simp only [LinkType]; bv_omega)
        (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkType + 4 = AfterTypeBne := by
    simp only [LinkType, AfterTypeBne]; bv_omega
  rw [hpc] at hnt
  exact hnt

set_option maxRecDepth 8000 in
/-- Type path AfterBalCheck → AfterTypeBne under ambient TypeDispatchAssumed. -/
theorem teerTypeSuccessAmbient
    (asm : TypeDispatchAssumedAmbientFull teerLinkedEarly)
    (hentry : asm.entry = TypeEntry)
    (regionBase loadPtr lenW balPtr : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (old1 v10 v11 v12 v13 : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hlen : lenW = BitVec.ofNat 64 len)
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hbound : off + len ≤ bs.length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 off) = true) :
    cpsTripleWithin (6 + (1 + nTypeSteps) + 1) AfterBalCheck AfterTypeBne teerLinkedEarly
      ((.x1 ↦ᵣ old1) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
        (.x18 ↦ᵣ balPtr) **
        bytesRegion regionBase bs **
        memOwn TypeAddr ** memOwn InnerOffAddr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkType) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ balPtr) **
        bytesRegion regionBase bs **
        memOwn TypeAddr ** memOwn InnerOffAddr **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  have hsetup := teerTypeSetup loadPtr lenW v10 v11 v12 v13
  have hsetupF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ old1) ** (.x18 ↦ᵣ balPtr) **
      bytesRegion regionBase bs **
      memOwn TypeAddr ** memOwn InnerOffAddr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hsetup
  have hcall := teerTypeCallAmbient asm hentry regionBase loadPtr lenW
    bs off len old1 hptr hlen hsuccess halign hbound hover hvalid0
  have hcallF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ balPtr)) (by pcf) hcall
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold teerTypeCalleePAmbient at *
    xperm_hyp hp) hsetupF hcallF
  have hbne := teerTypeBneOk
  have hbneF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkType) ** (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ balPtr) **
      bytesRegion regionBase bs **
      memOwn TypeAddr ** memOwn InnerOffAddr **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by pcf) hbne
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    unfold teerTypeCalleeQAmbient at *
    xperm_hyp hp) h01 hbneF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h12

#print axioms teerTypeSetup
#print axioms teerTypeCallAmbient
#print axioms teerTypeBneOk
#print axioms teerTypeSuccessAmbient

end EvmAsm.Codegen.TxEip7702TeerSpec
