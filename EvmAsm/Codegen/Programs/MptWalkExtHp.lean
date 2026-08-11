/-
  Extension arm post-nth → hp_decode ABI setup (#11799).

  After rlp_list_nth_item returns (pc 133):
    BNE status fail;
    la+ld path_offset; ADD a0 = node+off;
    la+ld path_length → a1;
    la nibble_buf/count/is_leaf → a2/a3/a4;
    STOPS before JAL hp_decode_nibbles at pc147 (SEPARATE residual).
-/

import EvmAsm.Codegen.Programs.MptWalkExtNth
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

private theorem bne_ext_nth_fail_off :
    pc 133 + signExtend13 (668 : BitVec 13) = pc 300 := by
  unfold pc walkB signExtend13; decide

private theorem la_ext_path_off_post_hi :
    laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 536) =
      EvmAsm.Rv64.laHi (pc 134) MwPathOff := by
  unfold pc walkB MwPathOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_path_off_post_lo :
    laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 536) =
      EvmAsm.Rv64.laLo (pc 134) MwPathOff := by
  unfold pc walkB MwPathOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_path_off_post_range : laInRange (pc 134) MwPathOff := by
  unfold pc walkB MwPathOff laInRange; decide

private theorem la_ext_path_len_post_hi :
    laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 552) =
      EvmAsm.Rv64.laHi (pc 138) MwPathLen := by
  unfold pc walkB MwPathLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_path_len_post_lo :
    laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 552) =
      EvmAsm.Rv64.laLo (pc 138) MwPathLen := by
  unfold pc walkB MwPathLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_path_len_post_range : laInRange (pc 138) MwPathLen := by
  unfold pc walkB MwPathLen laInRange; decide

private theorem la_ext_nibble_buf_hi :
    laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 564) =
      EvmAsm.Rv64.laHi (pc 141) MwNibbleBuf := by
  unfold pc walkB MwNibbleBuf EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_nibble_buf_lo :
    laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 564) =
      EvmAsm.Rv64.laLo (pc 141) MwNibbleBuf := by
  unfold pc walkB MwNibbleBuf EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_nibble_buf_range : laInRange (pc 141) MwNibbleBuf := by
  unfold pc walkB MwNibbleBuf laInRange; decide

private theorem la_ext_nibble_count_hi :
    laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 572) =
      EvmAsm.Rv64.laHi (pc 143) MwNibbleCount := by
  unfold pc walkB MwNibbleCount EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_nibble_count_lo :
    laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 572) =
      EvmAsm.Rv64.laLo (pc 143) MwNibbleCount := by
  unfold pc walkB MwNibbleCount EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_nibble_count_range : laInRange (pc 143) MwNibbleCount := by
  unfold pc walkB MwNibbleCount laInRange; decide

private theorem la_ext_is_leaf_hi :
    laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 580) =
      EvmAsm.Rv64.laHi (pc 145) MwIsLeaf := by
  unfold pc walkB MwIsLeaf EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_is_leaf_lo :
    laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 580) =
      EvmAsm.Rv64.laLo (pc 145) MwIsLeaf := by
  unfold pc walkB MwIsLeaf EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_is_leaf_range : laInRange (pc 145) MwIsLeaf := by
  unfold pc walkB MwIsLeaf laInRange; decide

private theorem pc_add8_eh (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

private theorem pc_add12_eh (n : Nat) : pc n + 12 = pc (n + 3) := by
  unfold pc; bv_omega

/-- Nth status ≠ 0: taken BNE → fail entry pc300. -/
theorem ext_nth_status_fail
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 133) (pc 300) fullCode
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 668
  have hbne := bne_spec_gen_within .x10 .x0 off (1 : Word) (0 : Word) (pc 133)
  rw [bne_ext_nth_fail_off, show pc 133 + 4 = pc 134 from pc_succ 133] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 133) 133 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have htk := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR F hF htk
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htkF

/-- Nth status = 0: fall through. -/
theorem ext_nth_status_ok
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 133) (pc 134) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 668
  have hbne := bne_spec_gen_within .x10 .x0 off (0 : Word) (0 : Word) (pc 133)
  rw [bne_ext_nth_fail_off, show pc 133 + 4 = pc 134 from pc_succ 133] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 133) 133 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-- Load path offset and form a0 = nodeBase + off (pc134→pc138). -/
theorem ext_path_ptr
    (v5 v6 v10 pathOff nodeBase : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 134) (pc 138) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) **
       (.x23 ↦ᵣ nodeBase) ** (MwPathOff ↦ₘ pathOff) ** F)
      ((.x5 ↦ᵣ MwPathOff) ** (.x6 ↦ᵣ pathOff) **
       (.x10 ↦ᵣ (nodeBase + pathOff)) **
       (.x23 ↦ᵣ nodeBase) ** (MwPathOff ↦ₘ pathOff) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 134) MwPathOff
    (by decide) la_ext_path_off_post_range
    (walkMem (pc 134) 134
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 134) MwPathOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_path_off_post_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 135)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 134) MwPathOff)) a = some i := by
        simpa [pc_succ 134] using hs
      exact walkMem (pc 135) 135
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 134) MwPathOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_path_off_post_lo]; rfl) a i hs')
  rw [pc_add8_eh 134] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) ** (.x23 ↦ᵣ nodeBase) **
     (MwPathOff ↦ₘ pathOff) ** F)
    (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x6 .x5 MwPathOff v6 pathOff
    (0 : BitVec 12) (pc 136) (by decide)
  rw [signExtend12_0, show (MwPathOff + 0 : Word) = MwPathOff from by bv_omega,
      pc_succ 136] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 136) 136 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ v10) ** (.x23 ↦ᵣ nodeBase) ** F)
    (by pcf; exact hF) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  -- ADD x10 = x23 + x6
  have hadd0 := add_spec_gen_within .x10 .x23 .x6 nodeBase pathOff v10
    (pc 137) (by decide)
  have hadd := cpsTripleWithin_extend_code
    (walkMem (pc 137) 137 (.ADD .x10 .x23 .x6)
      (by decide) (by unfold pc walkB; decide) rfl) hadd0
  rw [pc_succ 137] at hadd
  -- ADD focuses x10+x23+x6; frame only x5+mem+F
  have haddF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwPathOff) ** (MwPathOff ↦ₘ pathOff) ** F)
    (by pcf; exact hF) hadd
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 haddF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Load path length into a1 (pc138→pc141). -/
theorem ext_path_len
    (v5 v11 pathLen : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 138) (pc 141) fullCode
      ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) ** (MwPathLen ↦ₘ pathLen) ** F)
      ((.x5 ↦ᵣ MwPathLen) ** (.x11 ↦ᵣ pathLen) **
       (MwPathLen ↦ₘ pathLen) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 138) MwPathLen
    (by decide) la_ext_path_len_post_range
    (walkMem (pc 138) 138
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 138) MwPathLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_path_len_post_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 139)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 138) MwPathLen)) a = some i := by
        simpa [pc_succ 138] using hs
      exact walkMem (pc 139) 139
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 138) MwPathLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_path_len_post_lo]; rfl) a i hs')
  rw [pc_add8_eh 138] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (MwPathLen ↦ₘ pathLen) ** F)
    (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x11 .x5 MwPathLen v11 pathLen
    (0 : BitVec 12) (pc 140) (by decide)
  rw [signExtend12_0, show (MwPathLen + 0 : Word) = MwPathLen from by bv_omega,
      pc_succ 140] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 140) 140 (.LD .x11 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR F hF hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-- Materialize hp_decode out pointers a2/a3/a4 (pc141→pc147). -/
theorem ext_hp_la_outs
    (v12 v13 v14 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 6 (pc 141) (pc 147) fullCode
      ((.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** F)
      ((.x12 ↦ᵣ MwNibbleBuf) ** (.x13 ↦ᵣ MwNibbleCount) **
       (.x14 ↦ᵣ MwIsLeaf) ** F) := by
  have h1 := la_materialize_within (cr := fullCode) .x12 v12 (pc 141) MwNibbleBuf
    (by decide) la_ext_nibble_buf_range
    (walkMem (pc 141) 141
      (.AUIPC .x12 (EvmAsm.Rv64.laHi (pc 141) MwNibbleBuf))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_nibble_buf_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 142)
          (.ADDI .x12 .x12 (EvmAsm.Rv64.laLo (pc 141) MwNibbleBuf)) a = some i := by
        simpa [pc_succ 141] using hs
      exact walkMem (pc 142) 142
        (.ADDI .x12 .x12 (EvmAsm.Rv64.laLo (pc 141) MwNibbleBuf))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_nibble_buf_lo]; rfl) a i hs')
  rw [pc_add8_eh 141] at h1
  have h1F := cpsTripleWithin_frameR
    ((.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** F) (by pcf; exact hF) h1
  have h2 := la_materialize_within (cr := fullCode) .x13 v13 (pc 143) MwNibbleCount
    (by decide) la_ext_nibble_count_range
    (walkMem (pc 143) 143
      (.AUIPC .x13 (EvmAsm.Rv64.laHi (pc 143) MwNibbleCount))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_nibble_count_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 144)
          (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 143) MwNibbleCount)) a = some i := by
        simpa [pc_succ 143] using hs
      exact walkMem (pc 144) 144
        (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 143) MwNibbleCount))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_nibble_count_lo]; rfl) a i hs')
  rw [pc_add8_eh 143] at h2
  have h2F := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ MwNibbleBuf) ** (.x14 ↦ᵣ v14) ** F) (by pcf; exact hF) h2
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h1F h2F
  have h3 := la_materialize_within (cr := fullCode) .x14 v14 (pc 145) MwIsLeaf
    (by decide) la_ext_is_leaf_range
    (walkMem (pc 145) 145
      (.AUIPC .x14 (EvmAsm.Rv64.laHi (pc 145) MwIsLeaf))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_is_leaf_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 146)
          (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 145) MwIsLeaf)) a = some i := by
        simpa [pc_succ 145] using hs
      exact walkMem (pc 146) 146
        (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 145) MwIsLeaf))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_is_leaf_lo]; rfl) a i hs')
  rw [pc_add8_eh 145] at h3
  have h3F := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ MwNibbleBuf) ** (.x13 ↦ᵣ MwNibbleCount) ** F)
    (by pcf; exact hF) h3
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c12 h3F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- After successful nth: build hp_decode ABI at pc147 (no call). Fuel 1+4+3+6=14. -/
def extHpAbi
    (nodeBase pathOff pathLen : Word) (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ (nodeBase + pathOff)) ** (.x11 ↦ᵣ pathLen) **
  (.x12 ↦ᵣ MwNibbleBuf) ** (.x13 ↦ᵣ MwNibbleCount) ** (.x14 ↦ᵣ MwIsLeaf) **
  (.x23 ↦ᵣ nodeBase) **
  (MwPathOff ↦ₘ pathOff) ** (MwPathLen ↦ₘ pathLen) ** F

theorem ext_after_nth_ok_to_hp_abi
    (v5 v6 v11 v12 v13 v14 pathOff pathLen nodeBase : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 14 (pc 133) (pc 147) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x11 ↦ᵣ v11) **
       (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x23 ↦ᵣ nodeBase) **
       (MwPathOff ↦ₘ pathOff) ** (MwPathLen ↦ₘ pathLen) ** F)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwPathLen) ** (.x6 ↦ᵣ pathOff) **
       extHpAbi nodeBase pathOff pathLen F) := by
  have h0 := ext_nth_status_ok
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x11 ↦ᵣ v11) **
     (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) **
     (MwPathOff ↦ₘ pathOff) ** (MwPathLen ↦ₘ pathLen) ** F)
    (by pcf; exact hF)
  have h1 := ext_path_ptr v5 v6 (0 : Word) pathOff nodeBase
    ((.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
     (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (MwPathLen ↦ₘ pathLen) ** F)
    (by pcf; exact hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0 h1
  have h2 := ext_path_len MwPathOff v11 pathLen
    ((.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ pathOff) **
     (.x10 ↦ᵣ (nodeBase + pathOff)) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** (MwPathOff ↦ₘ pathOff) ** F)
    (by pcf; exact hF)
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2
  have h3 := ext_hp_la_outs v12 v13 v14
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ MwPathLen) ** (.x6 ↦ᵣ pathOff) **
     (.x10 ↦ᵣ (nodeBase + pathOff)) ** (.x11 ↦ᵣ pathLen) **
     (.x23 ↦ᵣ nodeBase) **
     (MwPathOff ↦ₘ pathOff) ** (MwPathLen ↦ₘ pathLen) ** F)
    (by pcf; exact hF)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp only [extHpAbi]
      xperm_chunked hq) c

end EvmAsm.Codegen.MptWalkSpec
