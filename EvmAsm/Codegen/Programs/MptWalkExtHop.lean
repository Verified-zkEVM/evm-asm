/-
  After successful ext hop `witness_lookup` (#11799 residual hyp): pc211→pc47.

  Same shape as branch hop (MptWalkBranchHop): status ok, load node, JAL -696 → pc45,
  MV kind ABI. Path pos x22 preserved (no LI 0).
-/

import EvmAsm.Codegen.Programs.MptWalkBranchHop
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec

set_option maxRecDepth 8000

private theorem bne_ext_hop_fail_off :
    pc 211 + signExtend13 (368 : BitVec 13) = pc 303 := by
  unfold pc walkB signExtend13; decide

private theorem la_ehop_off_hi :
    laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 848) =
      EvmAsm.Rv64.laHi (pc 212) MwLookupOff := by
  unfold pc walkB MwLookupOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ehop_off_lo :
    laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 848) =
      EvmAsm.Rv64.laLo (pc 212) MwLookupOff := by
  unfold pc walkB MwLookupOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ehop_off_range : laInRange (pc 212) MwLookupOff := by
  unfold pc walkB MwLookupOff laInRange; decide

private theorem la_ehop_len_hi :
    laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 864) =
      EvmAsm.Rv64.laHi (pc 216) MwLookupLen := by
  unfold pc walkB MwLookupLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ehop_len_lo :
    laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 864) =
      EvmAsm.Rv64.laLo (pc 216) MwLookupLen := by
  unfold pc walkB MwLookupLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ehop_len_range : laInRange (pc 216) MwLookupLen := by
  unfold pc walkB MwLookupLen laInRange; decide

private theorem jal_ehop_kind_target :
    pc 219 + signExtend21 (-696 : BitVec 21) = pc 45 := by
  unfold pc walkB signExtend21; decide

private theorem pc_add8_eh (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

private theorem signExtend12_0eh : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

theorem ext_hop_status_fail
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 211) (pc 303) fullCode
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 368
  have hbne := bne_spec_gen_within .x10 .x0 off (1 : Word) (0 : Word) (pc 211)
  rw [bne_ext_hop_fail_off, show pc 211 + 4 = pc 212 from pc_succ 211] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 211) 211 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have htk := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR F hF htk
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htkF

theorem ext_hop_status_ok
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 211) (pc 212) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 368
  have hbne := bne_spec_gen_within .x10 .x0 off (0 : Word) (0 : Word) (pc 211)
  rw [bne_ext_hop_fail_off, show pc 211 + 4 = pc 212 from pc_succ 211] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 211) 211 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

theorem ext_hop_load_node_ptr
    (v5 v6 v23 nodeOff witBase : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 212) (pc 216) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x23 ↦ᵣ v23) **
       (.x8 ↦ᵣ witBase) ** (MwLookupOff ↦ₘ nodeOff) ** F)
      ((.x5 ↦ᵣ MwLookupOff) ** (.x6 ↦ᵣ nodeOff) **
       (.x23 ↦ᵣ (witBase + nodeOff)) **
       (.x8 ↦ᵣ witBase) ** (MwLookupOff ↦ₘ nodeOff) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 212) MwLookupOff
    (by decide) la_ehop_off_range
    (walkMem (pc 212) 212
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 212) MwLookupOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ehop_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 213)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 212) MwLookupOff)) a = some i := by
        simpa [pc_succ 212] using hs
      exact walkMem (pc 213) 213
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 212) MwLookupOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ehop_off_lo]; rfl) a i hs')
  rw [pc_add8_eh 212] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x23 ↦ᵣ v23) ** (.x8 ↦ᵣ witBase) **
     (MwLookupOff ↦ₘ nodeOff) ** F)
    (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x6 .x5 MwLookupOff v6 nodeOff
    (0 : BitVec 12) (pc 214) (by decide)
  rw [signExtend12_0eh, show (MwLookupOff + 0 : Word) = MwLookupOff from by bv_omega,
      pc_succ 214] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 214) 214 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x23 ↦ᵣ v23) ** (.x8 ↦ᵣ witBase) ** F)
    (by pcf; exact hF) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  have hadd0 := add_spec_gen_within .x23 .x8 .x6 witBase nodeOff v23
    (pc 215) (by decide)
  have hadd := cpsTripleWithin_extend_code
    (walkMem (pc 215) 215 (.ADD .x23 .x8 .x6)
      (by decide) (by unfold pc walkB; decide) rfl) hadd0
  rw [pc_succ 215] at hadd
  have haddF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwLookupOff) ** (MwLookupOff ↦ₘ nodeOff) ** F)
    (by pcf; exact hF) hadd
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 haddF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

theorem ext_hop_load_node_len
    (v5 v24 nodeLen : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 216) (pc 219) fullCode
      ((.x5 ↦ᵣ v5) ** (.x24 ↦ᵣ v24) ** (MwLookupLen ↦ₘ nodeLen) ** F)
      ((.x5 ↦ᵣ MwLookupLen) ** (.x24 ↦ᵣ nodeLen) **
       (MwLookupLen ↦ₘ nodeLen) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 216) MwLookupLen
    (by decide) la_ehop_len_range
    (walkMem (pc 216) 216
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 216) MwLookupLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ehop_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 217)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 216) MwLookupLen)) a = some i := by
        simpa [pc_succ 216] using hs
      exact walkMem (pc 217) 217
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 216) MwLookupLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ehop_len_lo]; rfl) a i hs')
  rw [pc_add8_eh 216] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ v24) ** (MwLookupLen ↦ₘ nodeLen) ** F)
    (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x24 .x5 MwLookupLen v24 nodeLen
    (0 : BitVec 12) (pc 218) (by decide)
  rw [signExtend12_0eh, show (MwLookupLen + 0 : Word) = MwLookupLen from by bv_omega,
      pc_succ 218] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 218) 218 (.LD .x24 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR F hF hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

theorem ext_hop_jal_kind_abi
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 219) (pc 45) fullCode F F := by
  have h0 := jal_x0_spec_gen_within (-696 : BitVec 21) (pc 219)
  rw [jal_ehop_kind_target] at h0
  have h := cpsTripleWithin_extend_code
    (walkMem (pc 219) 219 (.JAL .x0 (-696 : BitVec 21))
      (by decide) (by unfold pc walkB; decide) rfl) h0
  have hF' := cpsTripleWithin_frameR F hF h
  exact cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hF'

/-- After residual ext hop lookup success: kind-call ABI at pc47.
    Fuel 11. Scratch temps owned (post-residual). -/
theorem ext_after_lookup_ok_to_kind
    (nodeOff nodeLen witBase : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 11 (pc 211) (pc 47) fullCode
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
      cpsTripleWithin 11 (pc 211) (pc 47) fullCode
        (((((P ** (.x5 ↦ᵣ v5)) ** (.x6 ↦ᵣ v6)) ** (.x11 ↦ᵣ v11)) **
          (.x23 ↦ᵣ v23)) ** (.x24 ↦ᵣ v24)) Q := by
    intro v5 v6 v11 v23 v24
    have h0 := ext_hop_status_ok
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x11 ↦ᵣ v11) **
       (.x23 ↦ᵣ v23) ** (.x24 ↦ᵣ v24) **
       (.x8 ↦ᵣ witBase) **
       (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F)
      (by pcf; exact hF)
    have h1 := ext_hop_load_node_ptr v5 v6 v23 nodeOff witBase
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
       (.x24 ↦ᵣ v24) **
       (MwLookupLen ↦ₘ nodeLen) ** F)
      (by pcf; exact hF)
    have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
      h0 h1
    have h2 := ext_hop_load_node_len MwLookupOff v24 nodeLen
      ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ nodeOff) ** (.x10 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ v11) **
       (.x23 ↦ᵣ (witBase + nodeOff)) ** (.x8 ↦ᵣ witBase) **
       (MwLookupOff ↦ₘ nodeOff) ** F)
      (by pcf; exact hF)
    have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
      c01 h2
    have h3 := ext_hop_jal_kind_abi
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
