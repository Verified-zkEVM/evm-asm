/-
  After successful root witness_lookup (#11799 residual hyp): pc36→pc47.

  Assumes a0=0 from residual witness_lookup_by_hash machine (SEPARATE).
  36 BNE ntaken status ok
  37-40 la+ld off; ADD x23 = witBase+off
  41-43 la+ld len → x24
  44 LI x22, 0
  45-46 MV a0/a1 = node
  STOPS at kind JAL pc47 (mpt_walk_kind_callWithin takes over).
-/

import EvmAsm.Codegen.Programs.MptWalkSetupBody
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec

set_option maxRecDepth 8000

private theorem bne_root_fail_off :
    pc 36 + signExtend13 (1044 : BitVec 13) = pc 297 := by
  unfold pc walkB signExtend13; decide

private theorem la_root_off_hi :
    laHi GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 148) =
      EvmAsm.Rv64.laHi (pc 37) MwLookupOff := by
  unfold pc walkB MwLookupOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_root_off_lo :
    laLo GuestAddrs.mw_lookup_offset (GuestAddrs.mpt_walk + 148) =
      EvmAsm.Rv64.laLo (pc 37) MwLookupOff := by
  unfold pc walkB MwLookupOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_root_off_range : laInRange (pc 37) MwLookupOff := by
  unfold pc walkB MwLookupOff laInRange; decide

private theorem la_root_len_hi :
    laHi GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 164) =
      EvmAsm.Rv64.laHi (pc 41) MwLookupLen := by
  unfold pc walkB MwLookupLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_root_len_lo :
    laLo GuestAddrs.mw_lookup_length (GuestAddrs.mpt_walk + 164) =
      EvmAsm.Rv64.laLo (pc 41) MwLookupLen := by
  unfold pc walkB MwLookupLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_root_len_range : laInRange (pc 41) MwLookupLen := by
  unfold pc walkB MwLookupLen laInRange; decide

private theorem pc_add8_rr (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

private theorem signExtend12_0r : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

/-- Root lookup status ≠ 0 → empty entry pc297. -/
theorem root_lookup_status_fail
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 36) (pc 297) fullCode
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 1044
  have hbne := bne_spec_gen_within .x10 .x0 off (1 : Word) (0 : Word) (pc 36)
  rw [bne_root_fail_off, show pc 36 + 4 = pc 37 from pc_succ 36] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 36) 36 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have htk := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR F hF htk
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htkF

/-- Root lookup status = 0: fall through. -/
theorem root_lookup_status_ok
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 36) (pc 37) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 1044
  have hbne := bne_spec_gen_within .x10 .x0 off (0 : Word) (0 : Word) (pc 36)
  rw [bne_root_fail_off, show pc 36 + 4 = pc 37 from pc_succ 36] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 36) 36 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-- Load node ptr x23 = witBase + off (pc37→pc41). -/
theorem root_load_node_ptr
    (v5 v6 v23 nodeOff witBase : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 37) (pc 41) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x23 ↦ᵣ v23) **
       (.x8 ↦ᵣ witBase) ** (MwLookupOff ↦ₘ nodeOff) ** F)
      ((.x5 ↦ᵣ MwLookupOff) ** (.x6 ↦ᵣ nodeOff) **
       (.x23 ↦ᵣ (witBase + nodeOff)) **
       (.x8 ↦ᵣ witBase) ** (MwLookupOff ↦ₘ nodeOff) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 37) MwLookupOff
    (by decide) la_root_off_range
    (walkMem (pc 37) 37
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 37) MwLookupOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_root_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 38)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 37) MwLookupOff)) a = some i := by
        simpa [pc_succ 37] using hs
      exact walkMem (pc 38) 38
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 37) MwLookupOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_root_off_lo]; rfl) a i hs')
  rw [pc_add8_rr 37] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x23 ↦ᵣ v23) ** (.x8 ↦ᵣ witBase) **
     (MwLookupOff ↦ₘ nodeOff) ** F)
    (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x6 .x5 MwLookupOff v6 nodeOff
    (0 : BitVec 12) (pc 39) (by decide)
  rw [signExtend12_0r, show (MwLookupOff + 0 : Word) = MwLookupOff from by bv_omega,
      pc_succ 39] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 39) 39 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x23 ↦ᵣ v23) ** (.x8 ↦ᵣ witBase) ** F)
    (by pcf; exact hF) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  have hadd0 := add_spec_gen_within .x23 .x8 .x6 witBase nodeOff v23
    (pc 40) (by decide)
  have hadd := cpsTripleWithin_extend_code
    (walkMem (pc 40) 40 (.ADD .x23 .x8 .x6)
      (by decide) (by unfold pc walkB; decide) rfl) hadd0
  rw [pc_succ 40] at hadd
  have haddF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwLookupOff) ** (MwLookupOff ↦ₘ nodeOff) ** F)
    (by pcf; exact hF) hadd
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 haddF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Load node len x24 (pc41→pc44). -/
theorem root_load_node_len
    (v5 v24 nodeLen : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 41) (pc 44) fullCode
      ((.x5 ↦ᵣ v5) ** (.x24 ↦ᵣ v24) ** (MwLookupLen ↦ₘ nodeLen) ** F)
      ((.x5 ↦ᵣ MwLookupLen) ** (.x24 ↦ᵣ nodeLen) **
       (MwLookupLen ↦ₘ nodeLen) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 41) MwLookupLen
    (by decide) la_root_len_range
    (walkMem (pc 41) 41
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 41) MwLookupLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_root_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 42)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 41) MwLookupLen)) a = some i := by
        simpa [pc_succ 41] using hs
      exact walkMem (pc 42) 42
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 41) MwLookupLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_root_len_lo]; rfl) a i hs')
  rw [pc_add8_rr 41] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ v24) ** (MwLookupLen ↦ₘ nodeLen) ** F)
    (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x24 .x5 MwLookupLen v24 nodeLen
    (0 : BitVec 12) (pc 43) (by decide)
  rw [signExtend12_0r, show (MwLookupLen + 0 : Word) = MwLookupLen from by bv_omega,
      pc_succ 43] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 43) 43 (.LD .x24 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR F hF hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- LI pos=0 + MV kind ABI (pc44→pc47). -/
theorem root_kind_abi
    (v10 v11 v22 nodeBase nodeLenW : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 44) (pc 47) fullCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x22 ↦ᵣ v22) **
       (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
      ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x22 ↦ᵣ (0 : Word)) **
       (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F) := by
  have h0 := li_spec_gen_within .x22 v22 (0 : Word) (pc 44) (by decide)
  have h0c := cpsTripleWithin_extend_code
    (walkMem (pc 44) 44 (.LI .x22 (0 : Word))
      (by decide) (by unfold pc walkB; decide) rfl) h0
  rw [pc_succ 44] at h0c
  have h0F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
     (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h0c
  have h1 := mv_spec_gen_within .x10 .x23 nodeBase v10 (pc 45) (by decide)
  have h1c := cpsTripleWithin_extend_code
    (walkMem (pc 45) 45 (.MV .x10 .x23)
      (by decide) (by unfold pc walkB; decide) rfl) h1
  rw [pc_succ 45] at h1c
  have h1F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x22 ↦ᵣ (0 : Word)) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h1c
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0F h1F
  have h2 := mv_spec_gen_within .x11 .x24 nodeLenW v11 (pc 46) (by decide)
  have h2c := cpsTripleWithin_extend_code
    (walkMem (pc 46) 46 (.MV .x11 .x24)
      (by decide) (by unfold pc walkB; decide) rfl) h2
  rw [pc_succ 46] at h2c
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x22 ↦ᵣ (0 : Word)) ** (.x23 ↦ᵣ nodeBase) ** F)
    (by pcf; exact hF) h2c
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- After residual lookup success: build kind-call ABI at pc47. Fuel 1+4+3+3=11. -/
def rootKindEntry
    (witBase nodeOff nodeLen : Word) (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ (witBase + nodeOff)) ** (.x11 ↦ᵣ nodeLen) **
  (.x22 ↦ᵣ (0 : Word)) **
  (.x23 ↦ᵣ (witBase + nodeOff)) ** (.x24 ↦ᵣ nodeLen) **
  (.x8 ↦ᵣ witBase) **
  (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F

theorem root_after_lookup_ok_to_kind
    (v5 v6 v11 v22 v23 v24 nodeOff nodeLen witBase : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 11 (pc 36) (pc 47) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x11 ↦ᵣ v11) **
       (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x24 ↦ᵣ v24) **
       (.x8 ↦ᵣ witBase) **
       (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
       rootKindEntry witBase nodeOff nodeLen F) := by
  have h0 := root_lookup_status_ok
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x11 ↦ᵣ v11) **
     (.x22 ↦ᵣ v22) ** (.x23 ↦ᵣ v23) ** (.x24 ↦ᵣ v24) **
     (.x8 ↦ᵣ witBase) **
     (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F)
    (by pcf; exact hF)
  have h1 := root_load_node_ptr v5 v6 v23 nodeOff witBase
    ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
     (.x22 ↦ᵣ v22) ** (.x24 ↦ᵣ v24) **
     (MwLookupLen ↦ₘ nodeLen) ** F)
    (by pcf; exact hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0 h1
  have h2 := root_load_node_len MwLookupOff v24 nodeLen
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ nodeOff) ** (.x10 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ v11) ** (.x22 ↦ᵣ v22) **
     (.x23 ↦ᵣ (witBase + nodeOff)) ** (.x8 ↦ᵣ witBase) **
     (MwLookupOff ↦ₘ nodeOff) ** F)
    (by pcf; exact hF)
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2
  have h3 := root_kind_abi (0 : Word) v11 v22 (witBase + nodeOff) nodeLen
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwLookupLen) ** (.x6 ↦ᵣ nodeOff) **
     (.x8 ↦ᵣ witBase) **
     (MwLookupOff ↦ₘ nodeOff) ** (MwLookupLen ↦ₘ nodeLen) ** F)
    (by pcf; exact hF)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp only [rootKindEntry]
      xperm_chunked hq) c

end EvmAsm.Codegen.MptWalkSpec
