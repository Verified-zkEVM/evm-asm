/-
  Extension arm post-hp gates (#11799): pc148→pc162.

  After `hp_decode_nibbles` returns success (a0=0):
    BNE status fail;
    la+ld is_leaf; BNE if leaf→fail (ext expects is_leaf=0);
    la+ld nibble_count;
    ADD end = pos + count; BLTU pathLen,end → fail;
    la nibble_buf; ADD path cursor; MV count;
    STOPS at compare-loop header BEQ count,0 (pc162).

  Path-compare loop body and child nth/hop are separate.
-/

import EvmAsm.Codegen.Programs.MptWalkExtHpCall
import EvmAsm.Codegen.Programs.HpDecodeNibblesSAsmPaths
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.HpDecodeNibblesSAsm

set_option maxRecDepth 8000

private theorem pc_add8_ep (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

private theorem signExtend12_0e : signExtend12 (0 : BitVec 12) = (0 : Word) := by
  decide

private theorem bne_ext_hp_fail_off :
    pc 148 + signExtend13 (608 : BitVec 13) = pc 300 := by
  unfold pc walkB signExtend13; decide

private theorem bne_ext_leaf_fail_off :
    pc 152 + signExtend13 (592 : BitVec 13) = pc 300 := by
  unfold pc walkB signExtend13; decide

private theorem bltu_ext_bounds_fail_off :
    pc 157 + signExtend13 (560 : BitVec 13) = pc 297 := by
  unfold pc walkB signExtend13; decide

private theorem la_ext_is_leaf_post_hi :
    laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 596) =
      EvmAsm.Rv64.laHi (pc 149) MwIsLeaf := by
  unfold pc walkB MwIsLeaf EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_is_leaf_post_lo :
    laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 596) =
      EvmAsm.Rv64.laLo (pc 149) MwIsLeaf := by
  unfold pc walkB MwIsLeaf EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_is_leaf_post_range : laInRange (pc 149) MwIsLeaf := by
  unfold pc walkB MwIsLeaf laInRange; decide

private theorem la_ext_nibble_count_post_hi :
    laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 612) =
      EvmAsm.Rv64.laHi (pc 153) MwNibbleCount := by
  unfold pc walkB MwNibbleCount EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_nibble_count_post_lo :
    laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 612) =
      EvmAsm.Rv64.laLo (pc 153) MwNibbleCount := by
  unfold pc walkB MwNibbleCount EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_nibble_count_post_range : laInRange (pc 153) MwNibbleCount := by
  unfold pc walkB MwNibbleCount laInRange; decide

private theorem la_ext_nibble_buf_post_hi :
    laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 632) =
      EvmAsm.Rv64.laHi (pc 158) MwNibbleBuf := by
  unfold pc walkB MwNibbleBuf EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_nibble_buf_post_lo :
    laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 632) =
      EvmAsm.Rv64.laLo (pc 158) MwNibbleBuf := by
  unfold pc walkB MwNibbleBuf EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_nibble_buf_post_range : laInRange (pc 158) MwNibbleBuf := by
  unfold pc walkB MwNibbleBuf laInRange; decide

/-! ## Status gate (pc148) -/

theorem ext_hp_status_ok (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 148) (pc 149) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbr0 := bne_spec_gen_within .x10 .x0 (608 : BitVec 13)
    (0 : Word) (0 : Word) (pc 148)
  rw [bne_ext_hp_fail_off, show pc 148 + 4 = pc 149 from pc_succ 148] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 148) 148 (.BNE .x10 .x0 (608 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-! ## is_leaf load + non-leaf gate (pc149→pc153) -/

theorem ext_hp_load_is_leaf
    (v5 v6 oldIsl : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 149) (pc 152) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (MwIsLeaf ↦ₘ oldIsl) ** F)
      ((.x5 ↦ᵣ MwIsLeaf) ** (.x6 ↦ᵣ oldIsl) ** (MwIsLeaf ↦ₘ oldIsl) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 149) MwIsLeaf
    (by decide) la_ext_is_leaf_post_range
    (walkMem (pc 149) 149
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 149) MwIsLeaf))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_is_leaf_post_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 150)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 149) MwIsLeaf)) a = some i := by
        simpa [pc_succ 149] using hs
      exact walkMem (pc 150) 150
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 149) MwIsLeaf))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_is_leaf_post_lo]; rfl) a i hs')
  rw [pc_add8_ep 149] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (MwIsLeaf ↦ₘ oldIsl) ** F) (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x6 .x5 MwIsLeaf v6 oldIsl
    (0 : BitVec 12) (pc 151) (by decide)
  rw [signExtend12_0e, show (MwIsLeaf + 0 : Word) = MwIsLeaf from by bv_omega,
      pc_succ 151] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 151) 151 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR F hF hld
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Extension requires is_leaf = 0 (BNE ntaken). -/
theorem ext_hp_is_ext (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 152) (pc 153) fullCode
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x6 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbr0 := bne_spec_gen_within .x6 .x0 (592 : BitVec 13)
    (0 : Word) (0 : Word) (pc 152)
  rw [bne_ext_leaf_fail_off, show pc 152 + 4 = pc 153 from pc_succ 152] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 152) 152 (.BNE .x6 .x0 (592 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-! ## nibble_count load (pc153→pc156) -/

theorem ext_hp_load_count
    (v5 v6 countW : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 153) (pc 156) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (MwNibbleCount ↦ₘ countW) ** F)
      ((.x5 ↦ᵣ MwNibbleCount) ** (.x6 ↦ᵣ countW) **
       (MwNibbleCount ↦ₘ countW) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 153) MwNibbleCount
    (by decide) la_ext_nibble_count_post_range
    (walkMem (pc 153) 153
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 153) MwNibbleCount))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_nibble_count_post_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 154)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 153) MwNibbleCount)) a = some i := by
        simpa [pc_succ 153] using hs
      exact walkMem (pc 154) 154
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 153) MwNibbleCount))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_nibble_count_post_lo]; rfl) a i hs')
  rw [pc_add8_ep 153] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (MwNibbleCount ↦ₘ countW) ** F) (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x6 .x5 MwNibbleCount v6 countW
    (0 : BitVec 12) (pc 155) (by decide)
  rw [signExtend12_0e, show (MwNibbleCount + 0 : Word) = MwNibbleCount from by bv_omega,
      pc_succ 155] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 155) 155 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR F hF hld
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-! ## Bounds: end = pos+count; BLTU pathLen,end ntaken (pc156→pc158) -/

theorem ext_hp_bounds_ok
    (pos countW pathLenW endW v7 : Word)
    (h_end : endW = pos + countW)
    (h_ge : ¬ BitVec.ult pathLenW endW)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 156) (pc 158) fullCode
      ((.x22 ↦ᵣ pos) ** (.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ v7) **
       (.x19 ↦ᵣ pathLenW) ** F)
      ((.x22 ↦ᵣ pos) ** (.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ endW) **
       (.x19 ↦ᵣ pathLenW) ** F) := by
  have hadd0 := add_spec_gen_within .x7 .x22 .x6 pos countW v7 (pc 156)
    (by decide)
  have hadd := cpsTripleWithin_extend_code
    (walkMem (pc 156) 156 (.ADD .x7 .x22 .x6)
      (by decide) (by unfold pc walkB; decide) rfl) hadd0
  rw [pc_succ 156] at hadd
  have haddF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ pathLenW) ** F) (by pcf; exact hF) hadd
  have haddW : cpsTripleWithin 1 (pc 156) (pc 157) fullCode
      ((.x22 ↦ᵣ pos) ** (.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ v7) **
       (.x19 ↦ᵣ pathLenW) ** F)
      ((.x22 ↦ᵣ pos) ** (.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ endW) **
       (.x19 ↦ᵣ pathLenW) ** F) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) ?_ haddF
    intro h hq
    -- hq: ((x22 ** x6 ** x7↦pos+count) ** x19 ** F)
    simp only [h_end] at hq ⊢
    xperm_chunked hq
  have hbr0 := bltu_spec_gen_within .x19 .x7 (560 : BitVec 13)
    pathLenW endW (pc 157)
  rw [bltu_ext_bounds_fail_off, show pc 157 + 4 = pc 158 from pc_succ 157] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 157) 157 (.BLTU .x19 .x7 (560 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hQ).2 h_ge)
  have hntF := cpsTripleWithin_frameR
    ((.x22 ↦ᵣ pos) ** (.x6 ↦ᵣ countW) ** F) (by pcf; exact hF) hnt
  have hntW : cpsTripleWithin 1 (pc 157) (pc 158) fullCode
      ((.x22 ↦ᵣ pos) ** (.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ endW) **
       (.x19 ↦ᵣ pathLenW) ** F)
      ((.x22 ↦ᵣ pos) ** (.x6 ↦ᵣ countW) ** (.x7 ↦ᵣ endW) **
       (.x19 ↦ᵣ pathLenW) ** F) := by
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    haddW hntW

/-! ## Compare-loop setup: la buf, ADD path cursor, MV count (pc158→pc162) -/

theorem ext_hp_cmp_setup
    (v7 v28 v29 pos countW pathPtr : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 158) (pc 162) fullCode
      ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x6 ↦ᵣ countW) ** (.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ pos) ** F)
      ((.x7 ↦ᵣ MwNibbleBuf) ** (.x28 ↦ᵣ (pathPtr + pos)) **
       (.x29 ↦ᵣ countW) ** (.x6 ↦ᵣ countW) **
       (.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ pos) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x7 v7 (pc 158) MwNibbleBuf
    (by decide) la_ext_nibble_buf_post_range
    (walkMem (pc 158) 158
      (.AUIPC .x7 (EvmAsm.Rv64.laHi (pc 158) MwNibbleBuf))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_nibble_buf_post_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 159)
          (.ADDI .x7 .x7 (EvmAsm.Rv64.laLo (pc 158) MwNibbleBuf)) a = some i := by
        simpa [pc_succ 158] using hs
      exact walkMem (pc 159) 159
        (.ADDI .x7 .x7 (EvmAsm.Rv64.laLo (pc 158) MwNibbleBuf))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_nibble_buf_post_lo]; rfl) a i hs')
  rw [pc_add8_ep 158] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x6 ↦ᵣ countW) **
     (.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ pos) ** F)
    (by pcf; exact hF) hla
  have hadd0 := add_spec_gen_within .x28 .x18 .x22 pathPtr pos v28 (pc 160)
    (by decide)
  have hadd := cpsTripleWithin_extend_code
    (walkMem (pc 160) 160 (.ADD .x28 .x18 .x22)
      (by decide) (by unfold pc walkB; decide) rfl) hadd0
  rw [pc_succ 160] at hadd
  have haddF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ MwNibbleBuf) ** (.x29 ↦ᵣ v29) ** (.x6 ↦ᵣ countW) ** F)
    (by pcf; exact hF) hadd
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF haddF
  have hmv0 := mv_spec_gen_within .x29 .x6 countW v29 (pc 161) (by decide)
  have hmv := cpsTripleWithin_extend_code
    (walkMem (pc 161) 161 (.MV .x29 .x6)
      (by decide) (by unfold pc walkB; decide) rfl) hmv0
  rw [pc_succ 161] at hmv
  have hmvF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ MwNibbleBuf) ** (.x28 ↦ᵣ (pathPtr + pos)) **
     (.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ pos) ** F)
    (by pcf; exact hF) hmv
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hmvF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Compose post-hp gates to compare-loop header (fuel 1+3+1+3+2+4 = 14).
    Domain: hp status 0, is_leaf cell = 0, pathLen ≥ pos+count. -/
theorem ext_after_hp_ok_to_cmp
    (v5 v6 v7 v28 v29 pos countW pathLenW pathPtr endW : Word)
    (h_end : endW = pos + countW)
    (h_ge : ¬ BitVec.ult pathLenW endW)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 14 (pc 148) (pc 162) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
       (MwIsLeaf ↦ₘ (0 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ MwNibbleCount) ** (.x6 ↦ᵣ countW) **
       (.x7 ↦ᵣ MwNibbleBuf) ** (.x28 ↦ᵣ (pathPtr + pos)) **
       (.x29 ↦ᵣ countW) **
       (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
       (MwIsLeaf ↦ₘ (0 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F) := by
  have h0 := ext_hp_status_ok
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
     (MwIsLeaf ↦ₘ (0 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F)
    (by pcf; exact hF)
  have h1 := ext_hp_load_is_leaf v5 v6 (0 : Word)
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
     (MwNibbleCount ↦ₘ countW) ** F)
    (by pcf; exact hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0 h1
  have h2 := ext_hp_is_ext
    ((.x10 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwIsLeaf) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
     (MwIsLeaf ↦ₘ (0 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F)
    (by pcf; exact hF)
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2
  have h3 := ext_hp_load_count MwIsLeaf (0 : Word) countW
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
     (MwIsLeaf ↦ₘ (0 : Word)) ** F)
    (by pcf; exact hF)
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3
  have h4 := ext_hp_bounds_ok pos countW pathLenW endW v7 h_end h_ge
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwNibbleCount) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x18 ↦ᵣ pathPtr) **
     (MwIsLeaf ↦ₘ (0 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F)
    (by pcf; exact hF)
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 h4
  have h5 := ext_hp_cmp_setup endW v28 v29 pos countW pathPtr
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwNibbleCount) ** (.x19 ↦ᵣ pathLenW) **
     (MwIsLeaf ↦ₘ (0 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F)
    (by pcf; exact hF)
  -- After bounds, x7 holds endW; cmp_setup overwrites x7 with MwNibbleBuf.
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01234 h5
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

end EvmAsm.Codegen.MptWalkSpec
