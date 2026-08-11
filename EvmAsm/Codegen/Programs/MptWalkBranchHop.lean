/-
  After successful branch hop `witness_lookup` (#11799 residual hyp): pc102→pc47.

  Assumes a0=0 from residual `witness_lookup_by_hash` at pc101 (SEPARATE).
  102 BNE ntaken status ok (fail→pc300)
  103-106 la+ld off; ADD x23 = witBase+off
  107-109 la+ld len → x24
  110 JAL x0 -260 → pc45 (kind ABI MVs; skips LI pos=0 — path already advanced)
  45-46 MV a0/a1 = node
  STOPS at kind JAL pc47 (`mpt_walk_kind_callWithin` takes over).

  Ext hop pc211 is the same shape (separate file when needed).
-/

import EvmAsm.Codegen.Programs.MptWalkWlCall
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec

set_option maxRecDepth 8000

private theorem bne_branch_hop_fail_off :
    pc 102 + signExtend13 (792 : BitVec 13) = pc 300 := by
  unfold pc walkB signExtend13; decide

private theorem la_bhop_off_hi :
    laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 412) =
      EvmAsm.Rv64.laHi (pc 103) MwLookupOff := by
  unfold pc walkB MwLookupOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_bhop_off_lo :
    laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 412) =
      EvmAsm.Rv64.laLo (pc 103) MwLookupOff := by
  unfold pc walkB MwLookupOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_bhop_off_range : laInRange (pc 103) MwLookupOff := by
  unfold pc walkB MwLookupOff laInRange; decide

private theorem la_bhop_len_hi :
    laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 428) =
      EvmAsm.Rv64.laHi (pc 107) MwLookupLen := by
  unfold pc walkB MwLookupLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_bhop_len_lo :
    laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 428) =
      EvmAsm.Rv64.laLo (pc 107) MwLookupLen := by
  unfold pc walkB MwLookupLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_bhop_len_range : laInRange (pc 107) MwLookupLen := by
  unfold pc walkB MwLookupLen laInRange; decide

private theorem jal_bhop_kind_target :
    pc 110 + signExtend21 (-260 : BitVec 21) = pc 45 := by
  unfold pc walkB signExtend21; decide

private theorem pc_add8_bh (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

private theorem signExtend12_0bh : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- Branch hop lookup status ≠ 0 → fail pc300. -/
theorem branch_hop_status_fail
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 102) (pc 300) fullCode
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 792
  have hbne := bne_spec_gen_within .x10 .x0 off (1 : Word) (0 : Word) (pc 102)
  rw [bne_branch_hop_fail_off, show pc 102 + 4 = pc 103 from pc_succ 102] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 102) 102 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have htk := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR F hF htk
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htkF

/-- Branch hop lookup status = 0: fall through. -/
theorem branch_hop_status_ok
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 102) (pc 103) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 792
  have hbne := bne_spec_gen_within .x10 .x0 off (0 : Word) (0 : Word) (pc 102)
  rw [bne_branch_hop_fail_off, show pc 102 + 4 = pc 103 from pc_succ 102] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 102) 102 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-- Load node ptr x23 = witBase + off (pc103→pc107). -/
theorem branch_hop_load_node_ptr
    (v5 v6 v23 nodeOff witBase : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 103) (pc 107) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x23 ↦ᵣ v23) **
       (.x8 ↦ᵣ witBase) ** (MwLookupOff ↦ₘ nodeOff) ** F)
      ((.x5 ↦ᵣ MwLookupOff) ** (.x6 ↦ᵣ nodeOff) **
       (.x23 ↦ᵣ (witBase + nodeOff)) **
       (.x8 ↦ᵣ witBase) ** (MwLookupOff ↦ₘ nodeOff) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 103) MwLookupOff
    (by decide) la_bhop_off_range
    (walkMem (pc 103) 103
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 103) MwLookupOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_bhop_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 104)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 103) MwLookupOff)) a = some i := by
        simpa [pc_succ 103] using hs
      exact walkMem (pc 104) 104
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 103) MwLookupOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_bhop_off_lo]; rfl) a i hs')
  rw [pc_add8_bh 103] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x23 ↦ᵣ v23) ** (.x8 ↦ᵣ witBase) **
     (MwLookupOff ↦ₘ nodeOff) ** F)
    (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x6 .x5 MwLookupOff v6 nodeOff
    (0 : BitVec 12) (pc 105) (by decide)
  rw [signExtend12_0bh, show (MwLookupOff + 0 : Word) = MwLookupOff from by bv_omega,
      pc_succ 105] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 105) 105 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x23 ↦ᵣ v23) ** (.x8 ↦ᵣ witBase) ** F)
    (by pcf; exact hF) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  have hadd0 := add_spec_gen_within .x23 .x8 .x6 witBase nodeOff v23
    (pc 106) (by decide)
  have hadd := cpsTripleWithin_extend_code
    (walkMem (pc 106) 106 (.ADD .x23 .x8 .x6)
      (by decide) (by unfold pc walkB; decide) rfl) hadd0
  rw [pc_succ 106] at hadd
  have haddF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwLookupOff) ** (MwLookupOff ↦ₘ nodeOff) ** F)
    (by pcf; exact hF) hadd
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 haddF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Load node len x24 (pc107→pc110). -/
theorem branch_hop_load_node_len
    (v5 v24 nodeLen : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 107) (pc 110) fullCode
      ((.x5 ↦ᵣ v5) ** (.x24 ↦ᵣ v24) ** (MwLookupLen ↦ₘ nodeLen) ** F)
      ((.x5 ↦ᵣ MwLookupLen) ** (.x24 ↦ᵣ nodeLen) **
       (MwLookupLen ↦ₘ nodeLen) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 107) MwLookupLen
    (by decide) la_bhop_len_range
    (walkMem (pc 107) 107
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 107) MwLookupLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_bhop_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 108)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 107) MwLookupLen)) a = some i := by
        simpa [pc_succ 107] using hs
      exact walkMem (pc 108) 108
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 107) MwLookupLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_bhop_len_lo]; rfl) a i hs')
  rw [pc_add8_bh 107] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ v24) ** (MwLookupLen ↦ₘ nodeLen) ** F)
    (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x24 .x5 MwLookupLen v24 nodeLen
    (0 : BitVec 12) (pc 109) (by decide)
  rw [signExtend12_0bh, show (MwLookupLen + 0 : Word) = MwLookupLen from by bv_omega,
      pc_succ 109] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 109) 109 (.LD .x24 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR F hF hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- JAL back to kind ABI MVs at pc45 (pc110→pc45). -/
theorem branch_hop_jal_kind_abi
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 110) (pc 45) fullCode F F := by
  have h0 := jal_x0_spec_gen_within (-260 : BitVec 21) (pc 110)
  rw [jal_bhop_kind_target] at h0
  have h := cpsTripleWithin_extend_code
    (walkMem (pc 110) 110 (.JAL .x0 (-260 : BitVec 21))
      (by decide) (by unfold pc walkB; decide) rfl) h0
  have hF' := cpsTripleWithin_frameR F hF h
  exact cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hF'

/-- MV kind ABI only (pc45→pc47). Shared hop landing — no LI pos=0. -/
theorem branch_hop_kind_abi
    (v10 v11 nodeBase nodeLenW : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 45) (pc 47) fullCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
      ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) **
       (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F) := by
  have h1 := mv_spec_gen_within .x10 .x23 nodeBase v10 (pc 45) (by decide)
  have h1c := cpsTripleWithin_extend_code
    (walkMem (pc 45) 45 (.MV .x10 .x23)
      (by decide) (by unfold pc walkB; decide) rfl) h1
  rw [pc_succ 45] at h1c
  have h1F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h1c
  have h2 := mv_spec_gen_within .x11 .x24 nodeLenW v11 (pc 46) (by decide)
  have h2c := cpsTripleWithin_extend_code
    (walkMem (pc 46) 46 (.MV .x11 .x24)
      (by decide) (by unfold pc walkB; decide) rfl) h2
  rw [pc_succ 46] at h2c
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x23 ↦ᵣ nodeBase) ** F)
    (by pcf; exact hF) h2c
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h1F h2F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Kind-call ABI after hop (path pos x22 preserved in F). -/
def branchHopKindEntry
    (witBase nodeOff nodeLen : Word) (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ (witBase + nodeOff)) ** (.x11 ↦ᵣ nodeLen) **
  (.x23 ↦ᵣ (witBase + nodeOff)) ** (.x24 ↦ᵣ nodeLen) **
  (.x8 ↦ᵣ witBase) **
  (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F

/-- Scratch owns matching residual `wlCallReturn` temps (x5/x6/x11).
    Node ptr/len x23/x24 also owned (unpinned by residual). -/
def hopScratchOwns : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x11 ** regOwn .x23 ** regOwn .x24

theorem hopScratchOwns_pcFree : hopScratchOwns.pcFree := by
  unfold hopScratchOwns
  repeat' first | exact pcFree_regOwn | apply pcFree_sepConj

/-- Peel five trailing owns into hopScratchOwns. -/
theorem of_forall_hopScratch
    {n : Nat} {entry exit : Word} {cr : CodeReq} {P Q : Assertion}
    (h : ∀ v5 v6 v11 v23 v24 : Word,
      cpsTripleWithin n entry exit cr
        (((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
          (.x23 ↦ᵣ v23)) ** (.x24 ↦ᵣ v24)) Q) :
    cpsTripleWithin n entry exit cr (P ** hopScratchOwns) Q := by
  unfold hopScratchOwns
  have h1 : ∀ v5 v6 v11 v23,
      cpsTripleWithin n entry exit cr
        (((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
          (.x23 ↦ᵣ v23)) ** regOwn .x24) Q :=
    fun v5 v6 v11 v23 =>
      cpsTripleWithin_of_forall_regIs_to_regOwn (fun v24 => h v5 v6 v11 v23 v24)
  have h2 : ∀ v5 v6 v11,
      cpsTripleWithin n entry exit cr
        ((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
          regOwn .x23 ** regOwn .x24) Q := by
    intro v5 v6 v11
    have hy : ∀ v23,
        cpsTripleWithin n entry exit cr
          (((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
            regOwn .x24) ** (.x23 ↦ᵣ v23)) Q :=
      fun v23 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
          (h1 v5 v6 v11 v23)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn hy)
  have h3 : ∀ v5 v6,
      cpsTripleWithin n entry exit cr
        (((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) **
          regOwn .x11 ** regOwn .x23 ** regOwn .x24) Q := by
    intro v5 v6
    have hy : ∀ v11,
        cpsTripleWithin n entry exit cr
          ((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) **
            regOwn .x23 ** regOwn .x24) ** (.x11 ↦ᵣ v11)) Q :=
      fun v11 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
          (h2 v5 v6 v11)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn hy)
  have h4 : ∀ v5,
      cpsTripleWithin n entry exit cr
        ((P ** (.x5 ↦ᵣ v5)) **
          regOwn .x6 ** regOwn .x11 ** regOwn .x23 ** regOwn .x24) Q := by
    intro v5
    have hy : ∀ v6,
        cpsTripleWithin n entry exit cr
          (((P ** (.x5 ↦ᵣ v5)) **
            regOwn .x11 ** regOwn .x23 ** regOwn .x24) ** (.x6 ↦ᵣ v6)) Q :=
      fun v6 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
          (h3 v5 v6)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn hy)
  have h5 :
      cpsTripleWithin n entry exit cr
        (P ** regOwn .x5 ** regOwn .x6 ** regOwn .x11 **
          regOwn .x23 ** regOwn .x24) Q := by
    have hy : ∀ v5,
        cpsTripleWithin n entry exit cr
          ((P ** regOwn .x6 ** regOwn .x11 ** regOwn .x23 ** regOwn .x24) **
            (.x5 ↦ᵣ v5)) Q :=
      fun v5 =>
        cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
          (h4 v5)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp) (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn hy)
  exact h5

/-- After residual branch hop lookup success: kind-call ABI at pc47.
    Fuel 1+4+3+1+2 = 11. Scratch temps owned (post-residual). -/
theorem branch_after_lookup_ok_to_kind
    (nodeOff nodeLen witBase : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 11 (pc 102) (pc 47) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       hopScratchOwns **
       (.x8 ↦ᵣ witBase) **
       (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       branchHopKindEntry witBase nodeOff nodeLen F) := by
  let P : Assertion :=
    (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x8 ↦ᵣ witBase) **
    (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F
  let Q : Assertion :=
    (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
    branchHopKindEntry witBase nodeOff nodeLen F
  have hconc : ∀ v5 v6 v11 v23 v24 : Word,
      cpsTripleWithin 11 (pc 102) (pc 47) fullCode
        (((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
          (.x23 ↦ᵣ v23)) ** (.x24 ↦ᵣ v24)) Q := by
    intro v5 v6 v11 v23 v24
    have h0 := branch_hop_status_ok
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x11 ↦ᵣ v11) **
       (.x23 ↦ᵣ v23) ** (.x24 ↦ᵣ v24) **
       (.x8 ↦ᵣ witBase) **
       (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F)
      (by pcf; exact hF)
    have h1 := branch_hop_load_node_ptr v5 v6 v23 nodeOff witBase
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
       (.x24 ↦ᵣ v24) **
       (MwLookupLen ↦ₘ nodeLen) ** F)
      (by pcf; exact hF)
    have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
      h0 h1
    have h2 := branch_hop_load_node_len MwLookupOff v24 nodeLen
      ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ nodeOff) ** (.x10 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ v11) **
       (.x23 ↦ᵣ (witBase + nodeOff)) ** (.x8 ↦ᵣ witBase) **
       (MwLookupOff ↦ₘ nodeOff) ** F)
      (by pcf; exact hF)
    have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
      c01 h2
    have h3 := branch_hop_jal_kind_abi
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
       (.x23 ↦ᵣ (witBase + nodeOff)) ** (.x24 ↦ᵣ nodeLen) **
       (.x8 ↦ᵣ witBase) **
       (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F)
      (by pcf; exact hF)
    have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
      c012 h3
    have h4 := branch_hop_kind_abi (0 : Word) v11 (witBase + nodeOff) nodeLen
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       (.x8 ↦ᵣ witBase) **
       (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F)
      (by pcf; exact hF)
    have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
      c0123 h4
    exact cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [P] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        simp only [Q, branchHopKindEntry] at hq ⊢
        xperm_chunked hq) c
  have hown := of_forall_hopScratch hconc
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [P, hopScratchOwns] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by simp only [Q] at hq ⊢; exact hq) hown

end EvmAsm.Codegen.MptWalkSpec
