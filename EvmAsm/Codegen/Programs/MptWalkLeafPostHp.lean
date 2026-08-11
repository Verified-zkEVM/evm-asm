/-
  Leaf arm post-hp gates (#11799): pc243→pc258.

  After `hp_decode_nibbles` returns success (a0=0):
    BNE status fail;
    la+ld is_leaf; LI 1; BNE if not leaf→fail (leaf expects is_leaf=1);
    la+ld nibble_count;
    SUB remaining = pathLen - pos; BNE if count ≠ remaining → fail;
    la nibble_buf; ADD path cursor; MV count;
    STOPS at compare-loop header BEQ count,0 (pc258).

  Path-compare loop + value extract are separate.
-/
import EvmAsm.Codegen.Programs.MptWalkLeafHpCall
import EvmAsm.Codegen.Programs.HpDecodeNibblesSAsmPaths
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.HpDecodeNibblesSAsm

set_option maxRecDepth 8000

private theorem pc_add8_lp (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

private theorem signExtend12_0lp : signExtend12 (0 : BitVec 12) = (0 : Word) := by
  decide

private theorem bne_leaf_hp_fail_off :
    pc 243 + signExtend13 (228 : BitVec 13) = pc 300 := by
  unfold pc walkB signExtend13; decide

private theorem bne_leaf_not_leaf_fail_off :
    pc 248 + signExtend13 (208 : BitVec 13) = pc 300 := by
  unfold pc walkB signExtend13; decide

private theorem bne_leaf_len_fail_off :
    pc 253 + signExtend13 (176 : BitVec 13) = pc 297 := by
  unfold pc walkB signExtend13; decide

private theorem la_leaf_is_leaf_post_hi :
    laHi GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 976) =
      EvmAsm.Rv64.laHi (pc 244) MwIsLeaf := by
  unfold pc walkB MwIsLeaf EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_leaf_is_leaf_post_lo :
    laLo GuestAddrs.mw_is_leaf (GuestAddrs.mpt_walk + 976) =
      EvmAsm.Rv64.laLo (pc 244) MwIsLeaf := by
  unfold pc walkB MwIsLeaf EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_leaf_is_leaf_post_range : laInRange (pc 244) MwIsLeaf := by
  unfold pc walkB MwIsLeaf laInRange; decide

private theorem la_leaf_nibble_count_post_hi :
    laHi GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 996) =
      EvmAsm.Rv64.laHi (pc 249) MwNibbleCount := by
  unfold pc walkB MwNibbleCount EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_leaf_nibble_count_post_lo :
    laLo GuestAddrs.mw_nibble_count (GuestAddrs.mpt_walk + 996) =
      EvmAsm.Rv64.laLo (pc 249) MwNibbleCount := by
  unfold pc walkB MwNibbleCount EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_leaf_nibble_count_post_range : laInRange (pc 249) MwNibbleCount := by
  unfold pc walkB MwNibbleCount laInRange; decide

private theorem la_leaf_nibble_buf_post_hi :
    laHi GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 1016) =
      EvmAsm.Rv64.laHi (pc 254) MwNibbleBuf := by
  unfold pc walkB MwNibbleBuf EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_leaf_nibble_buf_post_lo :
    laLo GuestAddrs.mw_nibble_buf (GuestAddrs.mpt_walk + 1016) =
      EvmAsm.Rv64.laLo (pc 254) MwNibbleBuf := by
  unfold pc walkB MwNibbleBuf EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_leaf_nibble_buf_post_range : laInRange (pc 254) MwNibbleBuf := by
  unfold pc walkB MwNibbleBuf laInRange; decide

/-! ## Status gate (pc243) -/

theorem leaf_hp_status_ok (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 243) (pc 244) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hbr0 := bne_spec_gen_within .x10 .x0 (228 : BitVec 13)
    (0 : Word) (0 : Word) (pc 243)
  rw [bne_leaf_hp_fail_off, show pc 243 + 4 = pc 244 from pc_succ 243] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 243) 243 (.BNE .x10 .x0 (228 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-! ## is_leaf load + leaf gate (pc244→pc249) -/

theorem leaf_hp_load_is_leaf
    (v5 v6 oldIsl : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 244) (pc 247) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (MwIsLeaf ↦ₘ oldIsl) ** F)
      ((.x5 ↦ᵣ MwIsLeaf) ** (.x6 ↦ᵣ oldIsl) ** (MwIsLeaf ↦ₘ oldIsl) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 244) MwIsLeaf
    (by decide) la_leaf_is_leaf_post_range
    (walkMem (pc 244) 244
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 244) MwIsLeaf))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_leaf_is_leaf_post_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 245)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 244) MwIsLeaf)) a = some i := by
        simpa [pc_succ 244] using hs
      exact walkMem (pc 245) 245
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 244) MwIsLeaf))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_leaf_is_leaf_post_lo]; rfl) a i hs')
  rw [pc_add8_lp 244] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (MwIsLeaf ↦ₘ oldIsl) ** F) (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x6 .x5 MwIsLeaf v6 oldIsl
    (0 : BitVec 12) (pc 246) (by decide)
  rw [signExtend12_0lp, show (MwIsLeaf + 0 : Word) = MwIsLeaf from by bv_omega,
      pc_succ 246] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 246) 246 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR F hF hld
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Leaf requires is_leaf = 1: LI x7,1 then BNE ntaken (equal). Fuel 2. -/
theorem leaf_hp_is_leaf
    (v7 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 247) (pc 249) fullCode
      ((.x6 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x6 ↦ᵣ (1 : Word)) ** (.x7 ↦ᵣ (1 : Word)) **
       (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hli := li_spec_gen_within .x7 v7 (1 : Word) (pc 247) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (walkMem (pc 247) 247 (.LI .x7 (1 : Word))
      (by decide) (by unfold pc walkB; decide) rfl) hli
  rw [pc_succ 247] at hlic
  have hliF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hlic
  have hbr0 := bne_spec_gen_within .x6 .x7 (208 : BitVec 13)
    (1 : Word) (1 : Word) (pc 248)
  rw [bne_leaf_not_leaf_fail_off, show pc 248 + 4 = pc 249 from pc_succ 248] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 248) 248 (.BNE .x6 .x7 (208 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** F) (by pcf; exact hF) hnt
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hliF hntF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-! ## nibble_count load (pc249→pc252) -/

theorem leaf_hp_load_count
    (v5 v6 countW : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 3 (pc 249) (pc 252) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (MwNibbleCount ↦ₘ countW) ** F)
      ((.x5 ↦ᵣ MwNibbleCount) ** (.x6 ↦ᵣ countW) **
       (MwNibbleCount ↦ₘ countW) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 249) MwNibbleCount
    (by decide) la_leaf_nibble_count_post_range
    (walkMem (pc 249) 249
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 249) MwNibbleCount))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_leaf_nibble_count_post_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 250)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 249) MwNibbleCount)) a = some i := by
        simpa [pc_succ 249] using hs
      exact walkMem (pc 250) 250
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 249) MwNibbleCount))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_leaf_nibble_count_post_lo]; rfl) a i hs')
  rw [pc_add8_lp 249] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (MwNibbleCount ↦ₘ countW) ** F) (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x6 .x5 MwNibbleCount v6 countW
    (0 : BitVec 12) (pc 251) (by decide)
  rw [signExtend12_0lp, show (MwNibbleCount + 0 : Word) = MwNibbleCount from by bv_omega,
      pc_succ 251] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 251) 251 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  have hldF := cpsTripleWithin_frameR F hF hld
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-! ## Exact residual length: SUB remaining; BNE count≠remaining → fail -/

/-- SUB x7 = pathLen - pos; BNE ntaken when count = remaining. Fuel 2. -/
theorem leaf_hp_len_exact
    (pathLenW pos countW v7 : Word)
    (h_eq : countW = pathLenW - pos)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 252) (pc 254) fullCode
      ((.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) ** (.x6 ↦ᵣ countW) **
       (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) ** (.x6 ↦ᵣ countW) **
       (.x7 ↦ᵣ (pathLenW - pos)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hsub := sub_spec_gen_within .x7 .x19 .x22 pathLenW pos v7 (pc 252) (by decide)
  have hsubc := cpsTripleWithin_extend_code
    (walkMem (pc 252) 252 (.SUB .x7 .x19 .x22)
      (by decide) (by unfold pc walkB; decide) rfl) hsub
  rw [pc_succ 252] at hsubc
  have hsubF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ countW) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hsubc
  -- BNE ntaken: taken pure is countW ≠ (pathLenW-pos); contradicted by h_eq
  have hbr0 := bne_spec_gen_within .x6 .x7 (176 : BitVec 13)
    countW (pathLenW - pos) (pc 253)
  rw [bne_leaf_len_fail_off, show pc 253 + 4 = pc 254 from pc_succ 253] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 253) 253 (.BNE .x6 .x7 (176 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact ((sepConj_pure_right _).1 hQ).2 h_eq)
  have hntF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hnt
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hsubF hntF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-! ## Compare-loop setup (pc254→pc258) -/

theorem leaf_hp_cmp_setup
    (v7 v28 v29 pos countW pathPtr : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 254) (pc 258) fullCode
      ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x6 ↦ᵣ countW) ** (.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ pos) ** F)
      ((.x7 ↦ᵣ MwNibbleBuf) ** (.x28 ↦ᵣ (pathPtr + pos)) **
       (.x29 ↦ᵣ countW) ** (.x6 ↦ᵣ countW) **
       (.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ pos) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x7 v7 (pc 254) MwNibbleBuf
    (by decide) la_leaf_nibble_buf_post_range
    (walkMem (pc 254) 254
      (.AUIPC .x7 (EvmAsm.Rv64.laHi (pc 254) MwNibbleBuf))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_leaf_nibble_buf_post_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 255)
          (.ADDI .x7 .x7 (EvmAsm.Rv64.laLo (pc 254) MwNibbleBuf)) a = some i := by
        simpa [pc_succ 254] using hs
      exact walkMem (pc 255) 255
        (.ADDI .x7 .x7 (EvmAsm.Rv64.laLo (pc 254) MwNibbleBuf))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_leaf_nibble_buf_post_lo]; rfl) a i hs')
  rw [pc_add8_lp 254] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x6 ↦ᵣ countW) **
     (.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ pos) ** F)
    (by pcf; exact hF) hla
  have hadd0 := add_spec_gen_within .x28 .x18 .x22 pathPtr pos v28 (pc 256)
    (by decide)
  have hadd := cpsTripleWithin_extend_code
    (walkMem (pc 256) 256 (.ADD .x28 .x18 .x22)
      (by decide) (by unfold pc walkB; decide) rfl) hadd0
  rw [pc_succ 256] at hadd
  -- ADD focuses x28+x18+x22; frame keeps x7/x29/x6/F (x18/x22 restored in post)
  have haddF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ MwNibbleBuf) ** (.x29 ↦ᵣ v29) ** (.x6 ↦ᵣ countW) ** F)
    (by pcf; exact hF) hadd
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF haddF
  -- After ADD post: x28/x18/x22 ** (x7**x29**x6**F); need x18/x22 concrete for MV frame
  -- MV focuses rd+rs = x29+x6; frame omits both
  have hmv0 := mv_spec_gen_within .x29 .x6 countW v29 (pc 257) (by decide)
  have hmv := cpsTripleWithin_extend_code
    (walkMem (pc 257) 257 (.MV .x29 .x6)
      (by decide) (by unfold pc walkB; decide) rfl) hmv0
  rw [pc_succ 257] at hmv
  have hmvF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ MwNibbleBuf) ** (.x28 ↦ᵣ (pathPtr + pos)) **
     (.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ pos) ** F)
    (by pcf; exact hF) hmv
  -- Mid after ADD: reassoc to flat for MV pre
  have c01' :
      cpsTripleWithin 3 (pc 254) (pc 257) fullCode
        ((.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x6 ↦ᵣ countW) ** (.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ pos) ** F)
        ((.x7 ↦ᵣ MwNibbleBuf) ** (.x28 ↦ᵣ (pathPtr + pos)) **
         (.x29 ↦ᵣ v29) ** (.x6 ↦ᵣ countW) **
         (.x18 ↦ᵣ pathPtr) ** (.x22 ↦ᵣ pos) ** F) := by
    refine cpsTripleWithin_weaken ?_ ?_ c01
    · intro h hp; xperm_chunked hp
    · intro h hq; xperm_chunked hq
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01' hmvF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Compose post-hp gates to compare-loop header (fuel 1+3+2+3+2+4 = 15).
    Domain: hp status 0, is_leaf cell = 1, count = pathLen - pos. -/
theorem leaf_after_hp_ok_to_cmp
    (v5 v6 v7 v28 v29 pos countW pathLenW pathPtr : Word)
    (h_eq : countW = pathLenW - pos)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 15 (pc 243) (pc 258) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
       (MwIsLeaf ↦ₘ (1 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ MwNibbleCount) ** (.x6 ↦ᵣ countW) **
       (.x7 ↦ᵣ MwNibbleBuf) ** (.x28 ↦ᵣ (pathPtr + pos)) **
       (.x29 ↦ᵣ countW) **
       (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
       (MwIsLeaf ↦ₘ (1 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F) := by
  have h0 := leaf_hp_status_ok
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
     (MwIsLeaf ↦ₘ (1 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F)
    (by pcf; exact hF)
  have h1 := leaf_hp_load_is_leaf v5 v6 (1 : Word)
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
     (MwNibbleCount ↦ₘ countW) ** F)
    (by pcf; exact hF)
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0 h1
  have h2 := leaf_hp_is_leaf v7
    ((.x10 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwIsLeaf) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
     (MwIsLeaf ↦ₘ (1 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F)
    (by pcf; exact hF)
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2
  have h3 := leaf_hp_load_count MwIsLeaf (1 : Word) countW
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x7 ↦ᵣ (1 : Word)) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x18 ↦ᵣ pathPtr) ** (.x19 ↦ᵣ pathLenW) ** (.x22 ↦ᵣ pos) **
     (MwIsLeaf ↦ₘ (1 : Word)) ** F)
    (by pcf; exact hF)
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3
  have h4 := leaf_hp_len_exact pathLenW pos countW (1 : Word) h_eq
    ((.x10 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwNibbleCount) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (.x18 ↦ᵣ pathPtr) **
     (MwIsLeaf ↦ₘ (1 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F)
    (by pcf; exact hF)
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 h4
  have h5 := leaf_hp_cmp_setup (pathLenW - pos) v28 v29 pos countW pathPtr
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwNibbleCount) ** (.x19 ↦ᵣ pathLenW) **
     (MwIsLeaf ↦ₘ (1 : Word)) ** (MwNibbleCount ↦ₘ countW) ** F)
    (by pcf; exact hF)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01234 h5
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

end EvmAsm.Codegen.MptWalkSpec
