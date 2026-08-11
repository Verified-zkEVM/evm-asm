/-
  Machine body blocks for `mpt_node_kind` (#11799 dep).

  Geometry: bodyEntry = kindB+16 (idx 4) → bodyExit = kindB+192 (idx 48).
  Path: setup (MV/MV/la) → count call → arity branches → (nth + HP | branch | fail).
-/

import EvmAsm.Codegen.Programs.MptNodeKindMachine
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SAsm.GlobalData

namespace EvmAsm.Codegen.MptNodeKindSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.RlpListCountItemsSAsm
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-! ## Ambient / call pre helpers -/

/-- Temps + bytes + BSS cells owned through the count call. -/
def countAmbient (listBase : Word) (bytes : List (BitVec 8))
    (oldCount oldOff oldLen : Word)
    (v13 v14 v18 v19 v20 v21 : Word) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
  (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion listBase bytes **
  (MnkCount ↦ₘ oldCount) **
  (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen)

/-- Setup post / count-call pre (ra still entry ra until first call). -/
def afterSetup (newSp listBase listLenW : Word) (ks : KindSaved)
    (bytes : List (BitVec 8)) (oldCount oldOff oldLen : Word)
    (v13 v14 v18 v19 v20 v21 : Word) : Assertion :=
  (.x2 ↦ᵣ newSp) ** kindSavedFrame newSp ks **
  (.x1 ↦ᵣ ks.ra) **
  (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ MnkCount) **
  stackFree newSp 8 **
  countAmbient listBase bytes oldCount oldOff oldLen
    v13 v14 v18 v19 v20 v21

/-- Body entry ambient after frame. -/
def bodyEntryPre (newSp listBase listLenW : Word) (ks : KindSaved)
    (bytes : List (BitVec 8)) (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word) : Assertion :=
  (.x2 ↦ᵣ newSp) ** kindSavedFrame newSp ks **
  (.x1 ↦ᵣ ks.ra) **
  (.x8 ↦ᵣ ks.s0) ** (.x9 ↦ᵣ ks.s1) **
  (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ v12) **
  stackFree newSp 8 **
  countAmbient listBase bytes oldCount oldOff oldLen
    v13 v14 v18 v19 v20 v21

/-! ## Concrete PC / reloc facts (decide-closed) -/

private theorem count_jal_target :
    pc 8 + signExtend21
      (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.mpt_node_kind + 32)) =
      CountB := by
  change BitVec.ofNat 64 GuestAddrs.mpt_node_kind + BitVec.ofNat 64 32 +
      signExtend21 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.mpt_node_kind + 32)) =
    BitVec.ofNat 64 GuestAddrs.rlp_list_count_items
  exact jalOff_correct_add GuestAddrs.rlp_list_count_items GuestAddrs.mpt_node_kind 32
    (by decide) (by decide) (by decide) (by decide)

private theorem la_count_hi :
    laHi GuestAddrs.mnk_item_count (GuestAddrs.mpt_node_kind + 24) =
      EvmAsm.Rv64.laHi (pc 6) MnkCount := by
  unfold pc kindB MnkCount EvmAsm.Rv64.laHi laHi laDelta
  decide

private theorem la_count_lo :
    laLo GuestAddrs.mnk_item_count (GuestAddrs.mpt_node_kind + 24) =
      EvmAsm.Rv64.laLo (pc 6) MnkCount := by
  unfold pc kindB MnkCount EvmAsm.Rv64.laLo laLo laDelta
  decide

private theorem la_count_range : laInRange (pc 6) MnkCount := by
  unfold pc kindB MnkCount laInRange
  decide

private theorem count_ret_even :
    (pc 8 + 4) &&& ~~~(1 : Word) = pc 8 + 4 := by
  unfold pc kindB
  decide

/-! ## Count call at idx 8 (pc 8 → pc 9) -/

set_option maxRecDepth 8000 in
theorem kind_count_call_spec_within
    (newSp listBase listLenW vOld oldCount : Word)
    (cSaved : RlpListCountItemsSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (1 + (8 + (85 + (93 * (listLen + 1) + 3) + 7)))
      (pc 8) (pc 9) fullCode
      (((.x1 ↦ᵣ vOld) **
        callEntryRest newSp listBase listLenW MnkCount oldCount
          { cSaved with ra := pc 9 } bytes) ** F)
      (((.x1 ↦ᵣ (pc 9)) **
        callReturnResult newSp listBase MnkCount
          { cSaved with ra := pc 9 } bytes listLen) ** F) := by
  have hmem : ∀ a i,
      CodeReq.singleton (pc 8)
          (.JAL .x1 (jalOff GuestAddrs.rlp_list_count_items
            (GuestAddrs.mpt_node_kind + 32))) a = some i →
        fullCode a = some i :=
    kindMem (pc 8) 8
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_count_items
        (GuestAddrs.mpt_node_kind + 32)))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl
  have h := rlpListCountItems_call_spec_within (cr := fullCode)
    (callerPC := pc 8) (calleeEntry := CountB) vOld newSp listBase listLenW
    MnkCount oldCount
    (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.mpt_node_kind + 32))
    F hF cSaved bytes listLen
    hlistLenW hsalign hslack hover hvalid count_ret_even count_jal_target rfl hmem
    countCalleeMem
  have hpc : pc 8 + 4 = pc 9 := pc_succ 8
  simpa [hpc] using h

/-! ## Setup idx 4..7 (pc 4 → pc 8) -/

set_option maxRecDepth 8000 in
theorem setup_spec
    (newSp listBase listLenW : Word) (ks : KindSaved)
    (bytes : List (BitVec 8)) (oldCount oldOff oldLen : Word)
    (v12 v13 v14 v18 v19 v20 v21 : Word) :
    cpsTripleWithin 4 (pc 4) (pc 8) fullCode
      (bodyEntryPre newSp listBase listLenW ks bytes oldCount oldOff oldLen
        v12 v13 v14 v18 v19 v20 v21)
      (afterSetup newSp listBase listLenW ks bytes oldCount oldOff oldLen
        v13 v14 v18 v19 v20 v21) := by
  -- Shared frame: everything except x8/x9/x10/x11/x12 (those move across setup).
  let Frest : Assertion :=
    (.x2 ↦ᵣ newSp) ** kindSavedFrame newSp ks **
    (.x1 ↦ᵣ ks.ra) **
    stackFree newSp 8 **
    countAmbient listBase bytes oldCount oldOff oldLen
      v13 v14 v18 v19 v20 v21
  -- [4] MV x8, x10
  have hm0 := mv_spec_gen_within .x8 .x10 listBase ks.s0 (pc 4) (by decide)
  have hm0c := cpsTripleWithin_extend_code
    (kindMem (pc 4) 4 (.MV .x8 .x10)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hm0
  rw [pc_succ 4] at hm0c
  have hm0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ ks.s1) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ v12) ** Frest)
    (by unfold Frest countAmbient; pcf) hm0c
  -- [5] MV x9, x11
  have hm1 := mv_spec_gen_within .x9 .x11 listLenW ks.s1 (pc 5) (by decide)
  have hm1c := cpsTripleWithin_extend_code
    (kindMem (pc 5) 5 (.MV .x9 .x11)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hm1
  rw [pc_succ 5] at hm1c
  have hm1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) ** (.x12 ↦ᵣ v12) ** Frest)
    (by unfold Frest countAmbient; pcf) hm1c
  -- [6]-[7] la x12, mnk_item_count
  have hla := la_materialize_within (cr := fullCode) .x12 v12 (pc 6) MnkCount
    (by decide) la_count_range
    (kindMem (pc 6) 6 (.AUIPC .x12 (EvmAsm.Rv64.laHi (pc 6) MnkCount))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
      (by rw [← la_count_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 7)
          (.ADDI .x12 .x12 (EvmAsm.Rv64.laLo (pc 6) MnkCount)) a = some i := by
        simpa [pc_succ 6] using hs
      exact kindMem (pc 7) 7
        (.ADDI .x12 .x12 (EvmAsm.Rv64.laLo (pc 6) MnkCount))
        (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
        (by rw [← la_count_lo]; rfl) a i hs')
  rw [show pc 6 + 8 = pc 8 from by unfold pc; bv_omega] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** Frest)
    (by unfold Frest countAmbient; pcf) hla
  -- compose: MV x8 → MV x9 → la x12
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hm0F hm1F
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) c01 hlaF
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [bodyEntryPre, countAmbient, Frest] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      simp only [afterSetup, countAmbient, Frest] at hq ⊢
      xperm_chunked hq) c012

/-! ## Post-count helpers (peel + fail join) -/

/-- Caller frame around the count call (not part of `callEntryRest`). -/
def countCallF (newSp : Word) (ks : KindSaved)
    (oldOff oldLen : Word) (v13 v14 v20 v21 : Word)
    (Rstack : Assertion) : Assertion :=
  kindSavedFrame newSp ks ** Rstack **
  (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
  (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
  (MnkPathOff ↦ₘ oldOff) ** (MnkPathLen ↦ₘ oldLen)

theorem countCallF_pcFree (newSp : Word) (ks : KindSaved)
    (oldOff oldLen : Word) (v13 v14 v20 v21 : Word)
    (Rstack : Assertion) (hR : Rstack.pcFree) :
    (countCallF newSp ks oldOff oldLen v13 v14 v20 v21 Rstack).pcFree := by
  unfold countCallF kindSavedFrame
  repeat' first
    | exact hR | exact pcFree_regIs | exact pcFree_memIs
    | apply pcFree_sepConj

/-- Peel `callReturnResult` into a concrete status/result arm. -/
theorem cpsTripleWithin_countReturn_pre
    {N : Nat} {ret X : Word} {F Q : Assertion}
    (sp0 listBase outPtr : Word) (cSaved : RlpListCountItemsSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (h : ∀ status result v11 v12,
        RlpListCountItemsSAsm.Result bytes listBase listLen status result →
        cpsTripleWithin N (pc 9) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 6 **
              RlpListCountItemsSAsm.savedRegTail cSaved) **
             ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
              bytesRegion listBase bytes ** (outPtr ↦ₘ result)))) ** F) Q) :
    cpsTripleWithin N (pc 9) ret fullCode
      (((.x1 ↦ᵣ X) **
        RlpListCountItemsSAsm.callReturnResult sp0 listBase outPtr cSaved
          bytes listLen) ** F) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, s1, s2, hd12, hu12, hP, hRs⟩ := hPR
  obtain ⟨t1, t2, hdt, hut, hXcRR, hFt⟩ := hP
  obtain ⟨u1, u2, hdu, huu, hX, hcRR⟩ := hXcRR
  unfold RlpListCountItemsSAsm.callReturnResult at hcRR
  obtain ⟨status, result, v11, v12, hBig⟩ := hcRR
  have hspl := (sepConj_pure_right u2).1 hBig
  exact h status result v11 v12 hspl.2 R hR s hcr
    ⟨hp, hcompat, s1, s2, hd12, hu12,
      ⟨t1, t2, hdt, hut, ⟨u1, u2, hdu, huu, hX, hspl.1⟩, hFt⟩, hRs⟩ hpc

theorem bne_fail_off9 :
    pc 9 + signExtend13
      (brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 36)) =
      pc 47 := by
  unfold pc kindB brOff signExtend13
  decide

theorem bne_nt_off9 : pc 9 + 4 = pc 10 := pc_succ 9

/-- `li a0, 3` at fail label (idx 47 → 48). -/
theorem fail_li3 (v10 : Word) :
    cpsTripleWithin 1 (pc 47) (pc 48) fullCode
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ (3 : Word)) := by
  have h := li_spec_gen_within .x10 v10 (3 : Word) (pc 47) (by decide)
  have hc := cpsTripleWithin_extend_code
    (kindMem (pc 47) 47 (.LI .x10 (3 : Word))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) h
  rwa [pc_succ 47] at hc

/-- Count-status not zero: taken BNE to fail, then `li a0, 3`. -/
theorem count_fail_arm
    (newSp listBase result v11 v12 : Word)
    (cSaved : RlpListCountItemsSAsm.Saved)
    (bytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 9) (pc 48) fullCode
      (((.x1 ↦ᵣ (pc 9)) **
        (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
          RlpListCountItemsSAsm.savedRegTail cSaved) **
         ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase bytes ** (MnkCount ↦ₘ result)))) ** F)
      (((.x1 ↦ᵣ (pc 9)) **
        (((.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
          RlpListCountItemsSAsm.savedRegTail cSaved) **
         ((.x10 ↦ᵣ (3 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase bytes ** (MnkCount ↦ₘ result)))) ** F) := by
  let off : BitVec 13 :=
    brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 36)
  have hbne := bne_spec_gen_within .x10 .x0 off (1 : Word) (0 : Word) (pc 9)
  rw [bne_fail_off9, bne_nt_off9] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (kindMem (pc 9) 9 (.BNE .x10 .x0 off)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbne
  have htk := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (pc 9)) ** (.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
     RlpListCountItemsSAsm.savedRegTail cSaved **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 **
     bytesRegion listBase bytes ** (MnkCount ↦ₘ result) ** F)
    (by
      unfold RlpListCountItemsSAsm.savedRegTail
      repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) htk
  have hli := fail_li3 (1 : Word)
  have hliF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (pc 9)) ** (.x2 ↦ᵣ newSp) ** stackFree newSp 6 **
     RlpListCountItemsSAsm.savedRegTail cSaved **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** (MnkCount ↦ₘ result) ** F)
    (by
      unfold RlpListCountItemsSAsm.savedRegTail
      repeat' first
        | exact hF | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs
        | exact pcFree_stackFree _ _ | exact bytesRegion_pcFree _ _
        | apply pcFree_sepConj) hli
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) htkF hliF
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      unfold RlpListCountItemsSAsm.savedRegTail at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      unfold RlpListCountItemsSAsm.savedRegTail at hq ⊢
      xperm_chunked hq) s

/-! ## Count-success: load count word (idx 10..13) -/

private theorem la_count2_hi :
    laHi GuestAddrs.mnk_item_count (GuestAddrs.mpt_node_kind + 40) =
      EvmAsm.Rv64.laHi (pc 10) MnkCount := by
  unfold pc kindB MnkCount EvmAsm.Rv64.laHi laHi laDelta
  decide

private theorem la_count2_lo :
    laLo GuestAddrs.mnk_item_count (GuestAddrs.mpt_node_kind + 40) =
      EvmAsm.Rv64.laLo (pc 10) MnkCount := by
  unfold pc kindB MnkCount EvmAsm.Rv64.laLo laLo laDelta
  decide

private theorem la_count2_range : laInRange (pc 10) MnkCount := by
  unfold pc kindB MnkCount laInRange
  decide

/-- Peel three trailing `regOwn`s (right-assoc `**` chain). -/
private theorem of_forall3
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 r3 : Reg}
    {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2 v3, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, ⟨v3, hv3⟩⟩ := hO2
  exact h v1 v2 v3 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3, hv2, hv3⟩, hRb⟩ hpc

/-- After status check falls through: `la t0,count; ld t1,0(t0); li t2,17`. -/
theorem count_load_block (countW : Word) :
    cpsTripleWithin 4 (pc 10) (pc 14) fullCode
      ((MnkCount ↦ₘ countW) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7)
      ((MnkCount ↦ₘ countW) ** (.x5 ↦ᵣ MnkCount) ** (.x6 ↦ᵣ countW) **
        (.x7 ↦ᵣ (17 : Word))) := by
  refine of_forall3 (fun v5' v6' v7' => ?_)
  -- la x5
  have hla := la_materialize_within (cr := fullCode) .x5 v5' (pc 10) MnkCount
    (by decide) la_count2_range
    (kindMem (pc 10) 10 (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 10) MnkCount))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
      (by rw [← la_count2_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 11)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 10) MnkCount)) a = some i := by
        simpa [pc_succ 10] using hs
      exact kindMem (pc 11) 11
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 10) MnkCount))
        (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
        (by rw [← la_count2_lo]; rfl) a i hs')
  rw [show pc 10 + 8 = pc 12 from by unfold pc; bv_omega] at hla
  -- la focuses x5; frame mem+x6+x7
  have hlaF := cpsTripleWithin_frameR
    ((MnkCount ↦ₘ countW) ** (.x6 ↦ᵣ v6') ** (.x7 ↦ᵣ v7'))
    (by pcf) hla
  -- ld focuses x5+x6+mem; frame only x7
  have hld := ld_spec_gen_within .x6 .x5 MnkCount v6' countW (0 : BitVec 12)
    (pc 12) (by decide)
  rw [signExtend12_0, show (MnkCount + 0 : Word) = MnkCount from by bv_omega,
      pc_succ 12] at hld
  have hldc := cpsTripleWithin_extend_code
    (kindMem (pc 12) 12 (.LD .x6 .x5 (0 : BitVec 12))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hld
  have hldF := cpsTripleWithin_frameR ((.x7 ↦ᵣ v7')) (by pcf) hldc
  -- li focuses x7; frame mem+x5+x6
  have hli := li_spec_gen_within .x7 v7' (17 : Word) (pc 13) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (kindMem (pc 13) 13 (.LI .x7 (17 : Word))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hli
  rw [pc_succ 13] at hlic
  have hliF := cpsTripleWithin_frameR
    ((MnkCount ↦ₘ countW) ** (.x5 ↦ᵣ MnkCount) ** (.x6 ↦ᵣ countW))
    (by pcf) hlic
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlaF hldF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c01 hliF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c012

private theorem beq_branch_off :
    pc 14 + signExtend13
      (brOff (GuestAddrs.mpt_node_kind + 164) (GuestAddrs.mpt_node_kind + 56)) =
      pc 41 := by
  unfold pc kindB brOff signExtend13
  decide

private theorem jal_branch_to_epi :
    pc 42 + signExtend21 (24 : BitVec 21) = pc 48 := by
  unfold pc kindB signExtend21
  decide

/-- Branch arm: at BEQ idx 14 with count=17, take branch → li 0 → jal epi. -/
theorem branch_arm
    (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 14) (pc 48) fullCode
      ((.x6 ↦ᵣ (17 : Word)) ** (.x7 ↦ᵣ (17 : Word)) ** (.x10 ↦ᵣ v10) ** F)
      ((.x6 ↦ᵣ (17 : Word)) ** (.x7 ↦ᵣ (17 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 :=
    brOff (GuestAddrs.mpt_node_kind + 164) (GuestAddrs.mpt_node_kind + 56)
  have hbeq := beq_spec_gen_within .x6 .x7 off (17 : Word) (17 : Word) (pc 14)
  rw [beq_branch_off, show pc 14 + 4 = pc 15 from pc_succ 14] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (kindMem (pc 14) 14 (.BEQ .x6 .x7 off)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbeq
  have htk := cpsBranchWithin_takenStripPure2 hbeqe (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have htkF := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10) ** F)
    (by repeat' first | exact hF | exact pcFree_regIs | apply pcFree_sepConj) htk
  -- LI x10, 0 at pc 41
  have hli := li_spec_gen_within .x10 v10 (0 : Word) (pc 41) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (kindMem (pc 41) 41 (.LI .x10 (0 : Word))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hli
  rw [pc_succ 41] at hlic
  have hliF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (17 : Word)) ** (.x7 ↦ᵣ (17 : Word)) ** F)
    (by repeat' first | exact hF | exact pcFree_regIs | apply pcFree_sepConj) hlic
  -- JAL x0, +24 → epi (emp/emp). Match c01 post association: x10 ** (x6**x7**F).
  have hjal := jal_x0_spec_gen_within (24 : BitVec 21) (pc 42)
  rw [jal_branch_to_epi] at hjal
  have hjalc := cpsTripleWithin_extend_code
    (kindMem (pc 42) 42 (.JAL .x0 (24 : BitVec 21))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (17 : Word)) ** (.x7 ↦ᵣ (17 : Word)) ** F)
    (by repeat' first | exact hF | exact pcFree_regIs | apply pcFree_sepConj) hjalc
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) htkF hliF
  -- c01 post → emp ** post for hjalF pre
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => (sepConj_emp_left _).2 hp) c01 hjalF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      have hq' := (sepConj_emp_left _).1 hq
      xperm_chunked hq') c012

/-! ## Kind return arms (li k; jal epi) — same shape as branch_arm tail -/

private theorem jal_ext_to_epi :
    pc 44 + signExtend21 (16 : BitVec 21) = pc 48 := by
  unfold pc kindB signExtend21; decide

private theorem jal_leaf_to_epi :
    pc 46 + signExtend21 (8 : BitVec 21) = pc 48 := by
  unfold pc kindB signExtend21; decide

theorem ext_arm (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 43) (pc 48) fullCode
      ((.x10 ↦ᵣ v10) ** F) ((.x10 ↦ᵣ (1 : Word)) ** F) := by
  have hli := li_spec_gen_within .x10 v10 (1 : Word) (pc 43) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (kindMem (pc 43) 43 (.LI .x10 (1 : Word))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hli
  rw [pc_succ 43] at hlic
  have hliF := cpsTripleWithin_frameR F hF hlic
  have hjal0 := jal_x0_spec_gen_within (16 : BitVec 21) (pc 44)
  rw [jal_ext_to_epi] at hjal0
  have hjalc := cpsTripleWithin_extend_code
    (kindMem (pc 44) 44 (.JAL .x0 (16 : BitVec 21))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hjal0
  have hjalF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (1 : Word)) ** F)
    (by repeat' first | exact hF | exact pcFree_regIs | apply pcFree_sepConj) hjalc
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => (sepConj_emp_left _).2 hp) hliF hjalF
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) c01

theorem leaf_arm (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 45) (pc 48) fullCode
      ((.x10 ↦ᵣ v10) ** F) ((.x10 ↦ᵣ (2 : Word)) ** F) := by
  have hli := li_spec_gen_within .x10 v10 (2 : Word) (pc 45) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (kindMem (pc 45) 45 (.LI .x10 (2 : Word))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hli
  rw [pc_succ 45] at hlic
  have hliF := cpsTripleWithin_frameR F hF hlic
  have hjal0 := jal_x0_spec_gen_within (8 : BitVec 21) (pc 46)
  rw [jal_leaf_to_epi] at hjal0
  have hjalc := cpsTripleWithin_extend_code
    (kindMem (pc 46) 46 (.JAL .x0 (8 : BitVec 21))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hjal0
  have hjalF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (2 : Word)) ** F)
    (by repeat' first | exact hF | exact pcFree_regIs | apply pcFree_sepConj) hjalc
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => (sepConj_emp_left _).2 hp) hliF hjalF
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) c01

/-- Count status = 0 fall-through + load + BEQ taken → branch return 0.
    Fuel: 1 (BNE) + 4 (load) + 3 (branch_arm) = 8.
    Pre includes `x0 ↦ 0` for the BNE compare. -/
theorem count_ok_branch_arm
    (v11 v12 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 9) (pc 48) fullCode
      (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (17 : Word))) ** F)
      (((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ MnkCount) ** (.x6 ↦ᵣ (17 : Word)) ** (.x7 ↦ᵣ (17 : Word)) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (17 : Word))) ** F) := by
  let off9 : BitVec 13 :=
    brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 36)
  have hbne := bne_spec_gen_within .x10 .x0 off9 (0 : Word) (0 : Word) (pc 9)
  rw [bne_fail_off9, bne_nt_off9] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (kindMem (pc 9) 9 (.BNE .x10 .x0 off9)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have hntF := cpsTripleWithin_frameR
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (MnkCount ↦ₘ (17 : Word)) ** F)
    (by pcf; exact hF) hnt
  have hload := count_load_block (17 : Word)
  have hloadF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** F)
    (by pcf; exact hF) hload
  have hbr := branch_arm (0 : Word)
    ((.x5 ↦ᵣ MnkCount) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (MnkCount ↦ₘ (17 : Word)) ** F)
    (by pcf; exact hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hntF hloadF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hbr
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c012

/-! ## Count ≠ 17 path: BEQ fall-through → li 2 → BNE vs 2 -/

private theorem bne_fail_off16 :
    pc 16 + signExtend13
      (brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 64)) =
      pc 47 := by
  unfold pc kindB brOff signExtend13; decide

/-- After load at pc14 with `count ≠ 17`: BEQ ntaken, `li t2,2`. -/
theorem count_ne17_li2
    (countW : Word) (hne : countW ≠ (17 : Word))
    (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 14) (pc 16) fullCode
      ((.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ (17 : Word)) ** (.x10 ↦ᵣ v10) ** F)
      ((.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ v10) ** F) := by
  let off : BitVec 13 :=
    brOff (GuestAddrs.mpt_node_kind + 164) (GuestAddrs.mpt_node_kind + 56)
  have hbeq := beq_spec_gen_within .x6 .x7 off countW (17 : Word) (pc 14)
  rw [beq_branch_off, show pc 14 + 4 = pc 15 from pc_succ 14] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (kindMem (pc 14) 14 (.BEQ .x6 .x7 off)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbeq
  -- ntakenStrip: show TAKEN (countW=17) impossible via hne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hne ((sepConj_pure_right _).1 hQ).2)
  have hntF := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10) ** F)
    (by pcf; exact hF) hnt
  -- li overwrites x7 (still 17 after BEQ)
  have hli := li_spec_gen_within .x7 (17 : Word) (2 : Word) (pc 15) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (kindMem (pc 15) 15 (.LI .x7 (2 : Word))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hli
  rw [pc_succ 15] at hlic
  have hliF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ countW) ** (.x10 ↦ᵣ v10) ** F)
    (by pcf; exact hF) hlic
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hntF hliF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- At pc16 with `count ≠ 2`: BNE taken → fail li3. -/
theorem count_ne2_fail_arm
    (countW : Word) (hne : countW ≠ (2 : Word))
    (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 16) (pc 48) fullCode
      ((.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ v10) ** F)
      ((.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ (3 : Word)) ** F) := by
  let off : BitVec 13 :=
    brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 64)
  have hbne := bne_spec_gen_within .x6 .x7 off countW (2 : Word) (pc 16)
  rw [bne_fail_off16, show pc 16 + 4 = pc 17 from pc_succ 16] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (kindMem (pc 16) 16 (.BNE .x6 .x7 off)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbne
  -- takenStrip: show FALLTHROUGH (countW=2) impossible via hne
  have htk := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact hne ((sepConj_pure_right _).1 hQ).2)
  have htkF := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10) ** F)
    (by pcf; exact hF) htk
  have hli := fail_li3 v10
  have hliF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ (2 : Word)) ** F)
    (by pcf; exact hF) hli
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    htkF hliF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- At pc16 with `count = 2`: BNE ntaken → fall into nth setup at pc17. -/
theorem count_eq2_nth_entry
    (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 16) (pc 17) fullCode
      ((.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ v10) ** F)
      ((.x6 ↦ᵣ (2 : Word)) ** (.x7 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ v10) ** F) := by
  let off : BitVec 13 :=
    brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 64)
  have hbne := bne_spec_gen_within .x6 .x7 off (2 : Word) (2 : Word) (pc 16)
  rw [bne_fail_off16, show pc 16 + 4 = pc 17 from pc_succ 16] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (kindMem (pc 16) 16 (.BNE .x6 .x7 off)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbne
  -- ntakenStrip: show TAKEN (2≠2) impossible
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have hntF := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10) ** F) (by pcf; exact hF) hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-! ## Nth setup (idx 17..23) + call (idx 24) -/

private theorem nth_jal_target :
    pc 24 + signExtend21
      (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_node_kind + 96)) =
      NthB := by
  change BitVec.ofNat 64 GuestAddrs.mpt_node_kind + BitVec.ofNat 64 96 +
      signExtend21 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_node_kind + 96)) =
    BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
  exact jalOff_correct_add GuestAddrs.rlp_list_nth_item GuestAddrs.mpt_node_kind 96
    (by decide) (by decide) (by decide) (by decide)

private theorem nth_ret_even :
    (pc 24 + 4) &&& ~~~(1 : Word) = pc 24 + 4 := by
  unfold pc kindB
  decide

private theorem la_path_off_hi :
    laHi GuestAddrs.mnk_path_offset (GuestAddrs.mpt_node_kind + 80) =
      EvmAsm.Rv64.laHi (pc 20) MnkPathOff := by
  unfold pc kindB MnkPathOff EvmAsm.Rv64.laHi laHi laDelta
  decide

private theorem la_path_off_lo :
    laLo GuestAddrs.mnk_path_offset (GuestAddrs.mpt_node_kind + 80) =
      EvmAsm.Rv64.laLo (pc 20) MnkPathOff := by
  unfold pc kindB MnkPathOff EvmAsm.Rv64.laLo laLo laDelta
  decide

private theorem la_path_off_range : laInRange (pc 20) MnkPathOff := by
  unfold pc kindB MnkPathOff laInRange
  decide

private theorem la_path_len_hi :
    laHi GuestAddrs.mnk_path_length (GuestAddrs.mpt_node_kind + 88) =
      EvmAsm.Rv64.laHi (pc 22) MnkPathLen := by
  unfold pc kindB MnkPathLen EvmAsm.Rv64.laHi laHi laDelta
  decide

private theorem la_path_len_lo :
    laLo GuestAddrs.mnk_path_length (GuestAddrs.mpt_node_kind + 88) =
      EvmAsm.Rv64.laLo (pc 22) MnkPathLen := by
  unfold pc kindB MnkPathLen EvmAsm.Rv64.laLo laLo laDelta
  decide

private theorem la_path_len_range : laInRange (pc 22) MnkPathLen := by
  unfold pc kindB MnkPathLen laInRange
  decide

/-- Marshal nth ABI args: `MV/MV/LI0/la path_off/la path_len` (pc17→pc24). -/
theorem nth_setup_spec
    (listBase listLenW : Word)
    (v10 v11 v12 v13 v14 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc 17) (pc 24) fullCode
      ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** F)
      ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ MnkPathOff) ** (.x14 ↦ᵣ MnkPathLen) ** F) := by
  -- [17] MV x10, x8  (focus x10+x8)
  have hm0 := mv_spec_gen_within .x10 .x8 listBase v10 (pc 17) (by decide)
  have hm0c := cpsTripleWithin_extend_code
    (kindMem (pc 17) 17 (.MV .x10 .x8)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hm0
  rw [pc_succ 17] at hm0c
  have hm0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ listLenW) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** F)
    (by pcf; exact hF) hm0c
  -- [18] MV x11, x9  (focus x11+x9)
  have hm1 := mv_spec_gen_within .x11 .x9 listLenW v11 (pc 18) (by decide)
  have hm1c := cpsTripleWithin_extend_code
    (kindMem (pc 18) 18 (.MV .x11 .x9)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hm1
  rw [pc_succ 18] at hm1c
  have hm1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x10 ↦ᵣ listBase) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** F)
    (by pcf; exact hF) hm1c
  -- [19] LI x12, 0  (focus x12)
  have hli := li_spec_gen_within .x12 v12 (0 : Word) (pc 19) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (kindMem (pc 19) 19 (.LI .x12 (0 : Word))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hli
  rw [pc_succ 19] at hlic
  have hliF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** F)
    (by pcf; exact hF) hlic
  -- [20]-[21] la x13, mnk_path_offset  (focus x13)
  have hla0 := la_materialize_within (cr := fullCode) .x13 v13 (pc 20) MnkPathOff
    (by decide) la_path_off_range
    (kindMem (pc 20) 20 (.AUIPC .x13 (EvmAsm.Rv64.laHi (pc 20) MnkPathOff))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
      (by rw [← la_path_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 21)
          (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 20) MnkPathOff)) a = some i := by
        simpa [pc_succ 20] using hs
      exact kindMem (pc 21) 21
        (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 20) MnkPathOff))
        (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
        (by rw [← la_path_off_lo]; rfl) a i hs')
  rw [show pc 20 + 8 = pc 22 from by unfold pc; bv_omega] at hla0
  have hla0F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ (0 : Word)) **
     (.x14 ↦ᵣ v14) ** F)
    (by pcf; exact hF) hla0
  -- [22]-[23] la x14, mnk_path_length  (focus x14)
  have hla1 := la_materialize_within (cr := fullCode) .x14 v14 (pc 22) MnkPathLen
    (by decide) la_path_len_range
    (kindMem (pc 22) 22 (.AUIPC .x14 (EvmAsm.Rv64.laHi (pc 22) MnkPathLen))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
      (by rw [← la_path_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 23)
          (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 22) MnkPathLen)) a = some i := by
        simpa [pc_succ 22] using hs
      exact kindMem (pc 23) 23
        (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 22) MnkPathLen))
        (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
        (by rw [← la_path_len_lo]; rfl) a i hs')
  rw [show pc 22 + 8 = pc 24 from by unfold pc; bv_omega] at hla1
  have hla1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ listLenW) **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ (0 : Word)) **
     (.x13 ↦ᵣ MnkPathOff) ** F)
    (by pcf; exact hF) hla1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hm0F hm1F
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hliF
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hla0F
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 hla1F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01234

/-! `jal rlp_list_nth_item` at pc24 (index = 0, path item). -/
set_option maxRecDepth 8000 in
theorem kind_nth_call_spec_within
    (newSp listBase listLenW vOld oldOff oldLen : Word)
    (nSaved : RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9))
      (pc 24) (pc 25) fullCode
      (((.x1 ↦ᵣ vOld) **
        callEntryRest newSp listBase listLenW (0 : Word) MnkPathOff MnkPathLen
          oldOff oldLen { nSaved with ra := pc 25 } bytes) ** F)
      (((.x1 ↦ᵣ (pc 25)) **
        callReturnResult newSp listBase (0 : Word) MnkPathOff MnkPathLen
          oldOff oldLen { nSaved with ra := pc 25 } bytes listLen 0) ** F) := by
  have hmem : ∀ a i,
      CodeReq.singleton (pc 24)
          (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
            (GuestAddrs.mpt_node_kind + 96))) a = some i →
        fullCode a = some i :=
    kindMem (pc 24) 24
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.mpt_node_kind + 96)))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl
  have h := rlpListNthItem_call_spec_within (cr := fullCode)
    (callerPC := pc 24) (calleeEntry := NthB) vOld newSp listBase listLenW
    (0 : Word) MnkPathOff MnkPathLen oldOff oldLen
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_node_kind + 96))
    F hF nSaved bytes listLen 0
    hlistLenW rfl (by omega) hsalign hslack hover hvalid nth_ret_even
    nth_jal_target rfl hmem nthCalleeMem
  have hpc : pc 24 + 4 = pc 25 := pc_succ 24
  simpa [hpc] using h

private theorem bne_fail_off25 :
    pc 25 + signExtend13
      (brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 100)) =
      pc 47 := by
  unfold pc kindB brOff signExtend13; decide

/-- Nth-status not zero: taken BNE to fail, then `li a0, 3`. -/
theorem nth_fail_arm
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 25) (pc 48) fullCode
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (3 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 :=
    brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 100)
  have hbne := bne_spec_gen_within .x10 .x0 off (1 : Word) (0 : Word) (pc 25)
  rw [bne_fail_off25, show pc 25 + 4 = pc 26 from pc_succ 25] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (kindMem (pc 25) 25 (.BNE .x10 .x0 off)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbne
  have htk := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR F hF htk
  have hli := fail_li3 (1 : Word)
  have hliF := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hli
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    htkF hliF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- Nth-status zero: BNE ntaken → fall into HP path at pc26. -/
theorem nth_ok_entry
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 25) (pc 26) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 :=
    brOff (GuestAddrs.mpt_node_kind + 188) (GuestAddrs.mpt_node_kind + 100)
  have hbne := bne_spec_gen_within .x10 .x0 off (0 : Word) (0 : Word) (pc 25)
  rw [bne_fail_off25, show pc 25 + 4 = pc 26 from pc_succ 25] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (kindMem (pc 25) 25 (.BNE .x10 .x0 off)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 rfl)
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-! ## HP path: load path off/len (pc26→pc32) -/

private theorem la_hp_off_hi :
    laHi GuestAddrs.mnk_path_offset (GuestAddrs.mpt_node_kind + 104) =
      EvmAsm.Rv64.laHi (pc 26) MnkPathOff := by
  unfold pc kindB MnkPathOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_hp_off_lo :
    laLo GuestAddrs.mnk_path_offset (GuestAddrs.mpt_node_kind + 104) =
      EvmAsm.Rv64.laLo (pc 26) MnkPathOff := by
  unfold pc kindB MnkPathOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_hp_off_range : laInRange (pc 26) MnkPathOff := by
  unfold pc kindB MnkPathOff laInRange; decide

private theorem la_hp_len_hi :
    laHi GuestAddrs.mnk_path_length (GuestAddrs.mpt_node_kind + 116) =
      EvmAsm.Rv64.laHi (pc 29) MnkPathLen := by
  unfold pc kindB MnkPathLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_hp_len_lo :
    laLo GuestAddrs.mnk_path_length (GuestAddrs.mpt_node_kind + 116) =
      EvmAsm.Rv64.laLo (pc 29) MnkPathLen := by
  unfold pc kindB MnkPathLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_hp_len_range : laInRange (pc 29) MnkPathLen := by
  unfold pc kindB MnkPathLen laInRange; decide

/-- Load path offset+length from BSS into x6/x7 (pc26→pc32). -/
theorem hp_load_block (pathOff pathLen : Word) :
    cpsTripleWithin 6 (pc 26) (pc 32) fullCode
      (((MnkPathOff ↦ₘ pathOff) ** (MnkPathLen ↦ₘ pathLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7)
      (((MnkPathOff ↦ₘ pathOff) ** (MnkPathLen ↦ₘ pathLen)) **
        (.x5 ↦ᵣ MnkPathLen) ** (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen)) := by
  refine of_forall3 (fun v5 v6 v7 => ?_)
  -- la x5, path_off
  have hla0 := la_materialize_within (cr := fullCode) .x5 v5 (pc 26) MnkPathOff
    (by decide) la_hp_off_range
    (kindMem (pc 26) 26 (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 26) MnkPathOff))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
      (by rw [← la_hp_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 27)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 26) MnkPathOff)) a = some i := by
        simpa [pc_succ 26] using hs
      exact kindMem (pc 27) 27
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 26) MnkPathOff))
        (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
        (by rw [← la_hp_off_lo]; rfl) a i hs')
  rw [show pc 26 + 8 = pc 28 from by unfold pc; bv_omega] at hla0
  have hla0F := cpsTripleWithin_frameR
    ((MnkPathOff ↦ₘ pathOff) ** (MnkPathLen ↦ₘ pathLen) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7))
    (by pcf) hla0
  -- LD x6, 0(x5)  focus x5+x6+mem_off
  have hld0 := ld_spec_gen_within .x6 .x5 MnkPathOff v6 pathOff (0 : BitVec 12)
    (pc 28) (by decide)
  rw [signExtend12_0, show (MnkPathOff + 0 : Word) = MnkPathOff from by bv_omega,
      pc_succ 28] at hld0
  have hld0c := cpsTripleWithin_extend_code
    (kindMem (pc 28) 28 (.LD .x6 .x5 (0 : BitVec 12))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hld0
  have hld0F := cpsTripleWithin_frameR
    ((MnkPathLen ↦ₘ pathLen) ** (.x7 ↦ᵣ v7))
    (by pcf) hld0c
  -- la x5, path_len (overwrites x5)
  have hla1 := la_materialize_within (cr := fullCode) .x5 MnkPathOff (pc 29) MnkPathLen
    (by decide) la_hp_len_range
    (kindMem (pc 29) 29 (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 29) MnkPathLen))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
      (by rw [← la_hp_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 30)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 29) MnkPathLen)) a = some i := by
        simpa [pc_succ 29] using hs
      exact kindMem (pc 30) 30
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 29) MnkPathLen))
        (by rw [program_length]; norm_num) (by unfold pc; bv_omega)
        (by rw [← la_hp_len_lo]; rfl) a i hs')
  rw [show pc 29 + 8 = pc 31 from by unfold pc; bv_omega] at hla1
  have hla1F := cpsTripleWithin_frameR
    ((MnkPathOff ↦ₘ pathOff) ** (MnkPathLen ↦ₘ pathLen) **
      (.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ v7))
    (by pcf) hla1
  -- LD x7, 0(x5)  focus x5+x7+mem_len
  have hld1 := ld_spec_gen_within .x7 .x5 MnkPathLen v7 pathLen (0 : BitVec 12)
    (pc 31) (by decide)
  rw [signExtend12_0, show (MnkPathLen + 0 : Word) = MnkPathLen from by bv_omega,
      pc_succ 31] at hld1
  have hld1c := cpsTripleWithin_extend_code
    (kindMem (pc 31) 31 (.LD .x7 .x5 (0 : BitVec 12))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hld1
  have hld1F := cpsTripleWithin_frameR
    ((MnkPathOff ↦ₘ pathOff) ** (.x6 ↦ᵣ pathOff))
    (by pcf) hld1c
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hla0F hld0F
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hla1F
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hld1F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c0123

/-- Empty path: BEQ taken (len=0) → fail li3. -/
theorem hp_empty_fail
    (pathOff : Word) (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 32) (pc 48) fullCode
      ((.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** F)
      ((.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (3 : Word)) ** F) := by
  have hbeq := beq_spec_gen_within .x7 .x0 (60 : BitVec 13)
    (0 : Word) (0 : Word) (pc 32)
  rw [show pc 32 + signExtend13 (60 : BitVec 13) = pc 47 from by
        unfold pc kindB signExtend13; decide,
      show pc 32 + 4 = pc 33 from pc_succ 32] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (kindMem (pc 32) 32 (.BEQ .x7 .x0 (60 : BitVec 13))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbeq
  -- takenStrip: fallthrough pure is 0≠0 → absurd
  have htk := cpsBranchWithin_takenStripPure2 hbeqe (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  -- htk: (x7**x0) → (x7**x0) at pc47; frame x6+x10+F
  have htkF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ pathOff) ** (.x10 ↦ᵣ v10) ** F) (by pcf; exact hF) htk
  have hli := fail_li3 v10
  -- li focuses x10; frame x6+x7+x0+F
  have hliF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hli
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    htkF hliF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- Non-empty path: BEQ ntaken (len≠0) → continue at pc33. -/
theorem hp_nempty_entry
    (pathOff pathLen : Word) (hne : pathLen ≠ (0 : Word))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 32) (pc 33) fullCode
      ((.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x6 ↦ᵣ pathOff) ** (.x7 ↦ᵣ pathLen) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbeq := beq_spec_gen_within .x7 .x0 (60 : BitVec 13)
    pathLen (0 : Word) (pc 32)
  rw [show pc 32 + signExtend13 (60 : BitVec 13) = pc 47 from by
        unfold pc kindB signExtend13; decide,
      show pc 32 + 4 = pc 33 from pc_succ 32] at hbeq
  have hbeqe := cpsBranchWithin_extend_code
    (kindMem (pc 32) 32 (.BEQ .x7 .x0 (60 : BitVec 13))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbeq
  have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hne ((sepConj_pure_right _).1 hQ).2)
  -- hnt focuses x7+x0; frame x6+F
  have hntF := cpsTripleWithin_frameR ((.x6 ↦ᵣ pathOff) ** F) (by pcf; exact hF) hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-! ## HP nibble classify (idx 33..46 → kind at epi) -/

private theorem bltu_ext_off :
    pc 37 + signExtend13 (24 : BitVec 13) = pc 43 := by
  unfold pc kindB signExtend13; decide

private theorem bltu_leaf_off :
    pc 39 + signExtend13 (24 : BitVec 13) = pc 45 := by
  unfold pc kindB signExtend13; decide

private theorem jal_fail_from_hp :
    pc 40 + signExtend21 (28 : BitVec 21) = pc 47 := by
  unfold pc kindB signExtend21; decide

private theorem pathOff_eq_ofNat (pathOff : Word) :
    pathOff = BitVec.ofNat 64 pathOff.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem nibble_toNat (b : BitVec 8) :
    ((b.zeroExtend 64) >>> 4).toNat = b.toNat / 16 := by
  have hzx : (b.zeroExtend 64).toNat = b.toNat :=
    BitVec.toNat_setWidth_of_le (by decide : (8 : Nat) ≤ 64)
  simp [BitVec.toNat_ushiftRight, hzx, Nat.shiftRight_eq_div_pow]

private theorem nibble_ult2 (b : BitVec 8) (h : b.toNat / 16 < 2) :
    BitVec.ult ((b.zeroExtend 64) >>> 4) (2 : Word) := by
  simp only [BitVec.ult, decide_eq_true_eq, nibble_toNat]
  exact h

private theorem nibble_nult2 (b : BitVec 8) (h : 2 ≤ b.toNat / 16) :
    ¬ BitVec.ult ((b.zeroExtend 64) >>> 4) (2 : Word) := by
  simp only [BitVec.ult, decide_eq_true_eq, nibble_toNat]
  exact Nat.not_lt.mpr h

private theorem nibble_ult4 (b : BitVec 8) (h : b.toNat / 16 < 4) :
    BitVec.ult ((b.zeroExtend 64) >>> 4) (4 : Word) := by
  simp only [BitVec.ult, decide_eq_true_eq, nibble_toNat]
  exact h

private theorem nibble_nult4 (b : BitVec 8) (h : 4 ≤ b.toNat / 16) :
    ¬ BitVec.ult ((b.zeroExtend 64) >>> 4) (4 : Word) := by
  simp only [BitVec.ult, decide_eq_true_eq, nibble_toNat]
  exact Nat.not_lt.mpr h

/-- ADD+LBU: pc33→pc35. Path byte loaded into x29. -/
theorem hp_add_lbu
    (listBase pathOff : Word) (bytes : List (BitVec 8)) (b : BitVec 8)
    (v28 v29 v30 : Word)
    (halign : listBase.toNat % 8 = 0)
    (hi : pathOff.toNat < bytes.length)
    (hb : bytes[pathOff.toNat]'hi = b)
    (hover : listBase.toNat + pathOff.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 pathOff.toNat) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 33) (pc 35) fullCode
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        bytesRegion listBase bytes ** F)
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) **
        (.x28 ↦ᵣ (listBase + pathOff)) **
        (.x29 ↦ᵣ (b.zeroExtend 64)) ** (.x30 ↦ᵣ v30) **
        bytesRegion listBase bytes ** F) := by
  have hadd := add_spec_gen_within .x28 .x8 .x6 listBase pathOff v28 (pc 33) (by decide)
  have haddc := cpsTripleWithin_extend_code
    (kindMem (pc 33) 33 (.ADD .x28 .x8 .x6)
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hadd
  rw [pc_succ 33] at haddc
  have haddF := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** bytesRegion listBase bytes ** F)
    (by pcf; try exact hF; try exact bytesRegion_pcFree _ _) haddc
  have hptr : listBase + pathOff = listBase + BitVec.ofNat 64 pathOff.toNat := by
    rw [← pathOff_eq_ofNat pathOff]
  have hlbu0 := bytesRegion_lbu_within .x29 .x28 listBase v29 (pc 34) bytes
    pathOff.toNat (by decide) halign hi hover hvalid
  rw [← hptr, pc_succ 34, hb] at hlbu0
  have hlbuc := cpsTripleWithin_extend_code
    (kindMem (pc 34) 34 (.LBU .x29 .x28 (0 : BitVec 12))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hlbu0
  have hlbuF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x30 ↦ᵣ v30) ** F)
    (by pcf; try exact hF) hlbuc
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    haddF hlbuF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- SRLI+LI2: pc35→pc37. High nibble in x29, x30=2. -/
theorem hp_srli_li2
    (listBase pathOff : Word) (bytes : List (BitVec 8)) (b : BitVec 8)
    (v30 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 35) (pc 37) fullCode
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) **
        (.x28 ↦ᵣ (listBase + pathOff)) **
        (.x29 ↦ᵣ (b.zeroExtend 64)) ** (.x30 ↦ᵣ v30) **
        bytesRegion listBase bytes ** F)
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) **
        (.x28 ↦ᵣ (listBase + pathOff)) **
        (.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (2 : Word)) **
        bytesRegion listBase bytes ** F) := by
  -- SRLI posts `v >>> shamt.toNat`; pin that to `>>> 4`.
  have hsrli0 := srli_spec_gen_same_within .x29 (b.zeroExtend 64) (4 : BitVec 6)
    (pc 35) (by decide)
  have hsrli : cpsTripleWithin 1 (pc 35) (pc 36) fullCode
      (.x29 ↦ᵣ (b.zeroExtend 64))
      (.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) := by
    have h := cpsTripleWithin_extend_code
      (kindMem (pc 35) 35 (.SRLI .x29 .x29 (4 : BitVec 6))
        (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hsrli0
    rw [pc_succ 35] at h
    -- shamt.toNat = 4
    simpa using h
  have hsrliF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x28 ↦ᵣ (listBase + pathOff)) **
      (.x30 ↦ᵣ v30) ** bytesRegion listBase bytes ** F)
    (by pcf; try exact hF; try exact bytesRegion_pcFree _ _) hsrli
  have hli := li_spec_gen_within .x30 v30 (2 : Word) (pc 36) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (kindMem (pc 36) 36 (.LI .x30 (2 : Word))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hli
  rw [pc_succ 36] at hlic
  have hliF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) ** (.x28 ↦ᵣ (listBase + pathOff)) **
      (.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** bytesRegion listBase bytes ** F)
    (by pcf; try exact hF; try exact bytesRegion_pcFree _ _) hlic
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hsrliF hliF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- ADD+LBU+SRLI+LI2: pc33→pc37. -/
theorem hp_nibble_prep
    (listBase pathOff : Word) (bytes : List (BitVec 8)) (b : BitVec 8)
    (v28 v29 v30 : Word)
    (halign : listBase.toNat % 8 = 0)
    (hi : pathOff.toNat < bytes.length)
    (hb : bytes[pathOff.toNat]'hi = b)
    (hover : listBase.toNat + pathOff.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 pathOff.toNat) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 33) (pc 37) fullCode
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        bytesRegion listBase bytes ** F)
      ((.x8 ↦ᵣ listBase) ** (.x6 ↦ᵣ pathOff) **
        (.x28 ↦ᵣ (listBase + pathOff)) **
        (.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (2 : Word)) **
        bytesRegion listBase bytes ** F) := by
  have h0 := hp_add_lbu listBase pathOff bytes b v28 v29 v30
    halign hi hb hover hvalid F hF
  have h1 := hp_srli_li2 listBase pathOff bytes b v30 F hF
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) h0 h1
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- High nibble < 2 → extension (kind 1). -/
theorem hp_ext_from_nibble
    (b : BitVec 8) (v10 : Word) (h : b.toNat / 16 < 2)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 37) (pc 48) fullCode
      ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (2 : Word)) **
        (.x10 ↦ᵣ v10) ** F)
      ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (2 : Word)) **
        (.x10 ↦ᵣ (1 : Word)) ** F) := by
  have hbr := bltu_spec_gen_within .x29 .x30 (24 : BitVec 13)
    ((b.zeroExtend 64) >>> 4) (2 : Word) (pc 37)
  rw [bltu_ext_off, pc_succ 37] at hbr
  have hbre := cpsBranchWithin_extend_code
    (kindMem (pc 37) 37 (.BLTU .x29 .x30 (24 : BitVec 13))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbr
  have hult := nibble_ult2 b h
  have htk := cpsBranchWithin_takenStripPure2 hbre (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 hult)
  -- htk: (x29**x30) → (x29**x30) @ pc43; frame x10+F
  have htkF := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10) ** F)
    (by pcf; try exact hF) htk
  -- ext_arm: (x10**G) → (x10=1**G); G = x29**x30**F
  have hext := ext_arm v10
    ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (2 : Word)) ** F)
    (by pcf; try exact hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    htkF hext
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- High nibble ∈ [2,4) → leaf (kind 2). -/
theorem hp_leaf_from_nibble
    (b : BitVec 8) (v10 : Word)
    (hlo : 2 ≤ b.toNat / 16) (hhi : b.toNat / 16 < 4)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 5 (pc 37) (pc 48) fullCode
      ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (2 : Word)) **
        (.x10 ↦ᵣ v10) ** F)
      ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (4 : Word)) **
        (.x10 ↦ᵣ (2 : Word)) ** F) := by
  have hbr0 := bltu_spec_gen_within .x29 .x30 (24 : BitVec 13)
    ((b.zeroExtend 64) >>> 4) (2 : Word) (pc 37)
  rw [bltu_ext_off, pc_succ 37] at hbr0
  have hbr0e := cpsBranchWithin_extend_code
    (kindMem (pc 37) 37 (.BLTU .x29 .x30 (24 : BitVec 13))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbr0
  have hnult2 := nibble_nult2 b hlo
  have hnt0 := cpsBranchWithin_ntakenStripPure2 hbr0e (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult2 ((sepConj_pure_right _).1 hQ).2)
  have hnt0F := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10) ** F)
    (by pcf; try exact hF) hnt0
  have hli := li_spec_gen_within .x30 (2 : Word) (4 : Word) (pc 38) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (kindMem (pc 38) 38 (.LI .x30 (4 : Word))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hli
  rw [pc_succ 38] at hlic
  -- li focuses x30; frame x29+x10+F
  have hliF := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x10 ↦ᵣ v10) ** F)
    (by pcf; try exact hF) hlic
  have hbr1 := bltu_spec_gen_within .x29 .x30 (24 : BitVec 13)
    ((b.zeroExtend 64) >>> 4) (4 : Word) (pc 39)
  rw [bltu_leaf_off, pc_succ 39] at hbr1
  have hbr1e := cpsBranchWithin_extend_code
    (kindMem (pc 39) 39 (.BLTU .x29 .x30 (24 : BitVec 13))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbr1
  have hult4 := nibble_ult4 b hhi
  have htk1 := cpsBranchWithin_takenStripPure2 hbr1e (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 hult4)
  -- htk1: (x29**x30=4) → same @ pc45; frame x10+F
  have htk1F := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10) ** F)
    (by pcf; try exact hF) htk1
  have hleaf := leaf_arm v10
    ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (4 : Word)) ** F)
    (by pcf; try exact hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hnt0F hliF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 htk1F
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hleaf
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c0123

/-- High nibble ≥ 4 → fail (kind 3). -/
theorem hp_fail_from_nibble
    (b : BitVec 8) (v10 : Word) (h : 4 ≤ b.toNat / 16)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 5 (pc 37) (pc 48) fullCode
      ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (2 : Word)) **
        (.x10 ↦ᵣ v10) ** F)
      ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (4 : Word)) **
        (.x10 ↦ᵣ (3 : Word)) ** F) := by
  have hlo : 2 ≤ b.toNat / 16 := Nat.le_trans (by decide : (2 : Nat) ≤ 4) h
  have hbr0 := bltu_spec_gen_within .x29 .x30 (24 : BitVec 13)
    ((b.zeroExtend 64) >>> 4) (2 : Word) (pc 37)
  rw [bltu_ext_off, pc_succ 37] at hbr0
  have hbr0e := cpsBranchWithin_extend_code
    (kindMem (pc 37) 37 (.BLTU .x29 .x30 (24 : BitVec 13))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbr0
  have hnult2 := nibble_nult2 b hlo
  have hnt0 := cpsBranchWithin_ntakenStripPure2 hbr0e (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult2 ((sepConj_pure_right _).1 hQ).2)
  have hnt0F := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10) ** F)
    (by pcf; try exact hF) hnt0
  have hli := li_spec_gen_within .x30 (2 : Word) (4 : Word) (pc 38) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (kindMem (pc 38) 38 (.LI .x30 (4 : Word))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hli
  rw [pc_succ 38] at hlic
  have hliF := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x10 ↦ᵣ v10) ** F)
    (by pcf; try exact hF) hlic
  have hbr1 := bltu_spec_gen_within .x29 .x30 (24 : BitVec 13)
    ((b.zeroExtend 64) >>> 4) (4 : Word) (pc 39)
  rw [bltu_leaf_off, pc_succ 39] at hbr1
  have hbr1e := cpsBranchWithin_extend_code
    (kindMem (pc 39) 39 (.BLTU .x29 .x30 (24 : BitVec 13))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hbr1
  have hnult4 := nibble_nult4 b h
  have hnt1 := cpsBranchWithin_ntakenStripPure2 hbr1e (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult4 ((sepConj_pure_right _).1 hQ).2)
  -- hnt1: (x29**x30=4) @ pc40; frame x10+F
  have hnt1F := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10) ** F)
    (by pcf; try exact hF) hnt1
  -- JAL emp/emp then li3
  have hjal0 := jal_x0_spec_gen_within (28 : BitVec 21) (pc 40)
  rw [jal_fail_from_hp] at hjal0
  have hjalc := cpsTripleWithin_extend_code
    (kindMem (pc 40) 40 (.JAL .x0 (28 : BitVec 21))
      (by rw [program_length]; norm_num) (by unfold pc; bv_omega) rfl) hjal0
  have hjalF := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (4 : Word)) **
      (.x10 ↦ᵣ v10) ** F)
    (by pcf; try exact hF) hjalc
  have hli3 := fail_li3 v10
  have hli3F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ ((b.zeroExtend 64) >>> 4)) ** (.x30 ↦ᵣ (4 : Word)) ** F)
    (by pcf; try exact hF) hli3
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hnt0F hliF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hnt1F
  -- Match branch_arm: inject emp for JAL, strip emp before li3
  have c0123 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      refine (sepConj_emp_left _).2 ?_
      xperm_chunked hp) c012 hjalF
  have c01234 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      have hp' := (sepConj_emp_left _).1 hp
      xperm_chunked hp') c0123 hli3F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01234

end EvmAsm.Codegen.MptNodeKindSpec
