/-
  Teer after auth walk_next skips: content SUB + list_count_items call.
  PC AfterAuthWalkNext9Bne (E+652) → AfterListCountBne (E+684).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerAuthWalkNextSkip
import EvmAsm.Codegen.Programs.RlpListCountItemsFlatSAsm
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpListCountItemsSAsm
open EvmAsm.Rv64.RLP

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
      | exact bytesRegion_pcFree _ _)

abbrev AuthCountAddr : Word := BitVec.ofNat 64 GuestAddrs.teer_auth_count
abbrev LC : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_count_items
abbrev listCountCode : CodeReq := CodeReq.ofProg LC rlpListCountItems_prog

/-- Linked early ∪ list_count (for auth count call). -/
def teerLinkedCount : CodeReq := teerLinkedEarly.union listCountCode

private theorem teer_count_disjoint :
    teerLinkedEarly.Disjoint listCountCode := by
  unfold teerLinkedEarly listCountCode teerCode typeCode walkInitCode walkNextCode LC
  -- Disjoint pairwise via ofProg_ranges; discharge with decide on lengths.
  apply CodeReq.Disjoint.union_left
  · apply CodeReq.Disjoint.union_left
    · apply CodeReq.Disjoint.union_left
      · apply CodeReq.Disjoint.ofProg_ranges
        · rw [teer_length]; decide
        · rw [total_length]; decide
        · rw [teer_length, total_length]; decide
      · apply CodeReq.Disjoint.ofProg_ranges
        · rw [type_length']; decide
        · rw [total_length]; decide
        · rw [type_length', total_length]; decide
    · apply CodeReq.Disjoint.ofProg_ranges
      · rw [rlp_walk_init_prog_length]; decide
      · rw [total_length]; decide
      · rw [rlp_walk_init_prog_length, total_length]; decide
  · apply CodeReq.Disjoint.ofProg_ranges
    · rw [rlp_walk_next_prog_length]; decide
    · rw [total_length]; decide
    · rw [rlp_walk_next_prog_length, total_length]; decide

theorem teerCount_mono_early :
    ∀ a i, teerLinkedEarly a = some i → teerLinkedCount a = some i := by
  intro a i hi
  exact CodeReq.union_mono_left (cr1 := teerLinkedEarly) (cr2 := listCountCode) a i hi

theorem teerCount_mono_count :
    ∀ a i, listCountCode a = some i → teerLinkedCount a = some i :=
  CodeReq.mono_union_right teer_count_disjoint (fun _ _ h => h)

theorem teerCount_mono_teer :
    ∀ a i, teerCode a = some i → teerLinkedCount a = some i :=
  fun a i hi => teerCount_mono_early a i (teerEarly_mono_teer a i hi)

/-- PC after content SUB (E+656). -/
abbrev AfterAuthContentSub : Word := E + 656
/-- PC after MV s6,a2; MV a0/a1 setup (E+668). -/
abbrev AtLaAuthCount : Word := E + 668
/-- PC of list_count JAL (E+676). -/
abbrev AtListCount : Word := E + 676
abbrev LinkListCount : Word := E + 680
abbrev AfterListCountBne : Word := E + 684

abbrev listCountJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_list_count_items
    (GuestAddrs.tx_eip7702_existing_authority_refund + 676)

abbrev teerListCountBneOff : BitVec 13 := (2176 : BitVec 13)

theorem listCountJalOff_resolves :
    AtListCount + signExtend21 listCountJalOff = LC := by
  simp only [AtListCount, LC, listCountJalOff, E]; decide

/-- `sub s5, a0, a2` (instr 163): content = next - len. -/
theorem teerAuthContentSub (next lenW v21 : Word) :
    cpsTripleWithin 1 AfterAuthWalkNext9Bne AfterAuthContentSub teerLinkedCount
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x21 ↦ᵣ v21))
      ((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ lenW) ** (.x21 ↦ᵣ next - lenW)) := by
  have h0 := sub_spec_gen_within .x21 .x10 .x12 next lenW v21
    AfterAuthWalkNext9Bne (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthWalkNext9Bne teerProg 163
        (.SUB .x21 .x10 .x12) (by simp only [AfterAuthWalkNext9Bne]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthWalkNext9Bne + 4 : Word) = AfterAuthContentSub := by
    simp only [AfterAuthWalkNext9Bne, AfterAuthContentSub]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv s6, a2` (instr 164): x22 ← len. -/
theorem teerAuthMvS6A2 (lenW v22 : Word) :
    cpsTripleWithin 1 AfterAuthContentSub (E + 660) teerLinkedCount
      ((.x12 ↦ᵣ lenW) ** (.x22 ↦ᵣ v22))
      ((.x12 ↦ᵣ lenW) ** (.x22 ↦ᵣ lenW)) := by
  have h0 := mv_spec_gen_within .x22 .x12 lenW v22 AfterAuthContentSub (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AfterAuthContentSub teerProg 164
        (.MV .x22 .x12) (by simp only [AfterAuthContentSub]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (AfterAuthContentSub + 4 : Word) = E + 660 := by
    simp only [AfterAuthContentSub]; bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a0, s5` (instr 165). -/
theorem teerAuthMvA0S5 (content v10 : Word) :
    cpsTripleWithin 1 (E + 660) (E + 664) teerLinkedCount
      ((.x21 ↦ᵣ content) ** (.x10 ↦ᵣ v10))
      ((.x21 ↦ᵣ content) ** (.x10 ↦ᵣ content)) := by
  have h0 := mv_spec_gen_within .x10 .x21 content v10 (E + 660) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 660) teerProg 165
        (.MV .x10 .x21) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 660 : Word) + 4 = E + 664 := by bv_omega
  rw [hpc] at e0
  exact e0

/-- `mv a1, s6` (instr 166). -/
theorem teerAuthMvA1S6 (listLen v11 : Word) :
    cpsTripleWithin 1 (E + 664) AtLaAuthCount teerLinkedCount
      ((.x22 ↦ᵣ listLen) ** (.x11 ↦ᵣ v11))
      ((.x22 ↦ᵣ listLen) ** (.x11 ↦ᵣ listLen)) := by
  have h0 := mv_spec_gen_within .x11 .x22 listLen v11 (E + 664) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (fun a i hi => teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 664) teerProg 166
        (.MV .x11 .x22) (by bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)) h0
  have hpc : (E + 664 : Word) + 4 = AtLaAuthCount := by
    simp only [AtLaAuthCount]; bv_omega
  rw [hpc] at e0
  exact e0

set_option maxRecDepth 8000 in
/-- Content SUB + a0/a1 setup: AfterAuthWalkNext9Bne → AtLaAuthCount. -/
theorem teerAuthContentSetup
    (next lenW v11 v21 v22 : Word) :
    cpsTripleWithin 4 AfterAuthWalkNext9Bne AtLaAuthCount teerLinkedCount
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ lenW) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ next - lenW) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ lenW) **
        (.x21 ↦ᵣ next - lenW) ** (.x22 ↦ᵣ lenW)) := by
  have hsub := teerAuthContentSub next lenW v21
  have hsubF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x22 ↦ᵣ v22)) (by pcf) hsub
  have hm6 := teerAuthMvS6A2 lenW v22
  have hm6F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ v11) ** (.x21 ↦ᵣ next - lenW)) (by pcf) hm6
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hsubF hm6F
  -- a0 still holds `next` after SUB; move content into a0
  have hm0 := teerAuthMvA0S5 (next - lenW) next
  have hm0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ lenW) ** (.x22 ↦ᵣ lenW)) (by pcf) hm0
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 hm0F
  have hm1 := teerAuthMvA1S6 lenW v11
  have hm1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next - lenW) ** (.x12 ↦ᵣ lenW) ** (.x21 ↦ᵣ next - lenW)) (by pcf) hm1
  have c23 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c12 hm1F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c23

/-- `la a2, teer_auth_count` at AtLaAuthCount → AtListCount. -/
theorem teerLaAuthCount (v : Word) :
    cpsTripleWithin 2 AtLaAuthCount AtListCount teerLinkedCount
      (.x12 ↦ᵣ v) (.x12 ↦ᵣ AuthCountAddr) := by
  have hau : ∀ a i, CodeReq.singleton AtLaAuthCount
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_auth_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 668)))
        a = some i → teerLinkedCount a = some i := fun a i hi =>
    teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E AtLaAuthCount teerProg 167
        (.AUIPC .x12 (Codegen.laHi GuestAddrs.teer_auth_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 668)))
        (by simp only [AtLaAuthCount]; bv_omega)
        (by rw [teer_length]; decide) rfl (by rw [teer_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (E + 672)
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_auth_count
        (GuestAddrs.tx_eip7702_existing_authority_refund + 668)))
        a = some i → teerLinkedCount a = some i := fun a i hi =>
    teerCount_mono_teer a i
      (CodeReq.ofProg_mem_at E (E + 672) teerProg 168
        (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.teer_auth_count
          (GuestAddrs.tx_eip7702_existing_authority_refund + 668)))
        (by bv_omega) (by rw [teer_length]; decide) rfl
        (by rw [teer_length]; decide) a i hi)
  have h := la_materialize_within .x12 v AtLaAuthCount AuthCountAddr
    (by decide) (by decide) hau had
  rw [show (AtLaAuthCount : Word) + 8 = AtListCount from by
    simp only [AtLaAuthCount, AtListCount]; bv_omega] at h
  exact h

set_option maxRecDepth 8000 in
/-- Content setup + la outPtr: AfterAuthWalkNext9Bne → AtListCount.
    Pre requires `x12 ↦ lenW` (walk_next length in a2). -/
theorem teerAuthContentToListCount
    (next lenW v11 v21 v22 : Word) :
    cpsTripleWithin 6 AfterAuthWalkNext9Bne AtListCount teerLinkedCount
      ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ lenW) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22))
      ((.x10 ↦ᵣ next - lenW) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ AuthCountAddr) **
        (.x21 ↦ᵣ next - lenW) ** (.x22 ↦ᵣ lenW)) := by
  have hset := teerAuthContentSetup next lenW v11 v21 v22
  have hla := teerLaAuthCount lenW
  have hlaF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ next - lenW) ** (.x11 ↦ᵣ lenW) **
      (.x21 ↦ᵣ next - lenW) ** (.x22 ↦ᵣ lenW)) (by pcf) hla
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hset hlaF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

#print axioms teerAuthContentSub
#print axioms teerAuthContentSetup
#print axioms teerLaAuthCount
#print axioms teerAuthContentToListCount

end EvmAsm.Codegen.TxEip7702TeerSpec
