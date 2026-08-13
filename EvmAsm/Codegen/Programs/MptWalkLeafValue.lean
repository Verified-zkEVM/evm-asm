/-
  Leaf arm after path-match (#11799): pc266→success.

  266-272 nth setup: a0/a1=node, a2=1 (value field), la value BSS
  273 JAL rlp_list_nth_item
  274 BNE status fail → pc300
  275-278 store value_len to *outLen (x21)
  279-282 load value_off; ADD ptr = node+off
  283-287 clamp copy len ≤ 256
  288-294 byte-copy loop out←value
  295 LI a0,0; JAL epi success

  Domain: nth status 0; value fits out buffer under clamp.
-/
import EvmAsm.Codegen.Programs.MptWalkLeafCmp
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.SAsm.MultiDword

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

private theorem pc_add8_lv (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

private theorem signExtend12_0lv : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem signExtend12_1lv : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem signExtend12_m1lv : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
private theorem ofNat_zero_lv : BitVec.ofNat 64 0 = (0 : Word) := by decide
private theorem one_plus_neg1_lv : (1 : Word) + (-1 : Word) = 0 := by decide

private theorem bne_leaf_nth_fail_off :
    pc 274 + signExtend13 (104 : BitVec 13) = pc 300 := by
  unfold pc walkB signExtend13; decide

private theorem beq_leaf_copy_done_off :
    pc 288 + signExtend13 (28 : BitVec 13) = pc 295 := by
  unfold pc walkB signExtend13; decide

private theorem jal_leaf_copy_back_off :
    pc 294 + signExtend21 (-24 : BitVec 21) = pc 288 := by
  unfold pc walkB
  rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]
  bv_omega

private theorem jal_leaf_succ_epi_off :
    pc 296 + signExtend21 (36 : BitVec 21) = pc 305 := by
  unfold pc walkB
  rw [show signExtend21 (36 : BitVec 21) = (36 : Word) from by decide]
  bv_omega

private theorem bltu_leaf_clamp_off :
    pc 285 + signExtend13 (8 : BitVec 13) = pc 287 := by
  unfold pc walkB signExtend13; decide

private theorem jal_leaf_noclamp_off :
    pc 286 + signExtend21 (8 : BitVec 21) = pc 288 := by
  unfold pc walkB
  rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
  bv_omega

private theorem la_leaf_val_off_hi :
    laHi GuestAddrs.mw_value_offset (GuestAddrs.mpt_walk + 1076) =
      EvmAsm.Rv64.laHi (pc 269) MwValueOff := by
  unfold pc walkB MwValueOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_leaf_val_off_lo :
    laLo GuestAddrs.mw_value_offset (GuestAddrs.mpt_walk + 1076) =
      EvmAsm.Rv64.laLo (pc 269) MwValueOff := by
  unfold pc walkB MwValueOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_leaf_val_off_range : laInRange (pc 269) MwValueOff := by
  unfold pc walkB MwValueOff laInRange; decide

private theorem la_leaf_val_len_hi :
    laHi GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 1084) =
      EvmAsm.Rv64.laHi (pc 271) MwValueLen := by
  unfold pc walkB MwValueLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_leaf_val_len_lo :
    laLo GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 1084) =
      EvmAsm.Rv64.laLo (pc 271) MwValueLen := by
  unfold pc walkB MwValueLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_leaf_val_len_range : laInRange (pc 271) MwValueLen := by
  unfold pc walkB MwValueLen laInRange; decide

private theorem leaf_val_nth_jal_target :
    pc 273 + signExtend21
      (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 1092)) =
      NthB := by
  change BitVec.ofNat 64 GuestAddrs.mpt_walk + BitVec.ofNat 64 1092 +
      signExtend21 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 1092)) =
    BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
  exact jalOff_correct_add GuestAddrs.rlp_list_nth_item GuestAddrs.mpt_walk 1092
    (by decide) (by decide) (by decide) (by decide)

private theorem leaf_val_nth_ret_even :
    (pc 273 + 4) &&& ~~~(1 : Word) = pc 273 + 4 := by
  unfold pc walkB; decide

private theorem la_leaf_load_len_hi :
    laHi GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 1100) =
      EvmAsm.Rv64.laHi (pc 275) MwValueLen := by
  unfold pc walkB MwValueLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_leaf_load_len_lo :
    laLo GuestAddrs.mw_value_length (GuestAddrs.mpt_walk + 1100) =
      EvmAsm.Rv64.laLo (pc 275) MwValueLen := by
  unfold pc walkB MwValueLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_leaf_load_len_range : laInRange (pc 275) MwValueLen := by
  unfold pc walkB MwValueLen laInRange; decide

private theorem la_leaf_load_off_hi :
    laHi GuestAddrs.mw_value_offset (GuestAddrs.mpt_walk + 1116) =
      EvmAsm.Rv64.laHi (pc 279) MwValueOff := by
  unfold pc walkB MwValueOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_leaf_load_off_lo :
    laLo GuestAddrs.mw_value_offset (GuestAddrs.mpt_walk + 1116) =
      EvmAsm.Rv64.laLo (pc 279) MwValueOff := by
  unfold pc walkB MwValueOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_leaf_load_off_range : laInRange (pc 279) MwValueOff := by
  unfold pc walkB MwValueOff laInRange; decide

private theorem cursor_succ_lv (base : Word) (p : Nat) :
    base + BitVec.ofNat 64 p + (1 : Word) = base + BitVec.ofNat 64 (p + 1) := by
  rw [BitVec.add_assoc, ofNat_succ p]

private theorem cnt_step_down_lv (n : Nat) :
    BitVec.ofNat 64 (n + 1) + (-1 : Word) = BitVec.ofNat 64 n := by
  have e1 : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + (1 : Word) := (ofNat_succ n).symm
  calc
    BitVec.ofNat 64 (n + 1) + (-1 : Word)
        = (BitVec.ofNat 64 n + (1 : Word)) + (-1 : Word) := by rw [e1]
    _ = BitVec.ofNat 64 n + ((1 : Word) + (-1 : Word)) := by rw [BitVec.add_assoc]
    _ = BitVec.ofNat 64 n + (0 : Word) := by rw [one_plus_neg1_lv]
    _ = BitVec.ofNat 64 n := BitVec.add_zero _

private theorem word_ofNat_succ_ne_zero_lv (n : Nat) (h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  intro heq
  have htn := congrArg BitVec.toNat heq
  have hmod : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
    simp only [BitVec.toNat_ofNat]; omega
  have hz : (0 : Word).toNat = 0 := rfl
  omega

/-! ## Nth setup for value field (index 1) -/

def leafValNthSetup (nodeBase nodeLenW : Word) (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (1 : Word)) **
  (.x13 ↦ᵣ MwValueOff) ** (.x14 ↦ᵣ MwValueLen) **
  (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F

/-- MV/MV/LI1 + la value BSS (pc266→pc273). Fuel 7. -/
theorem leaf_val_nth_setup_spec
    (v10 v11 v12 v13 v14 nodeBase nodeLenW : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc 266) (pc 273) fullCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
      (leafValNthSetup nodeBase nodeLenW F) := by
  have h0 := mv_spec_gen_within .x10 .x23 nodeBase v10 (pc 266) (by decide)
  have h0c := cpsTripleWithin_extend_code
    (walkMem (pc 266) 266 (.MV .x10 .x23)
      (by decide) (by unfold pc walkB; decide) rfl) h0
  rw [pc_succ 266] at h0c
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h0c
  have h1 := mv_spec_gen_within .x11 .x24 nodeLenW v11 (pc 267) (by decide)
  have h1c := cpsTripleWithin_extend_code
    (walkMem (pc 267) 267 (.MV .x11 .x24)
      (by decide) (by unfold pc walkB; decide) rfl) h1
  rw [pc_succ 267] at h1c
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** F)
    (by pcf; exact hF) h1c
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0F h1F
  have h2 := li_spec_gen_within .x12 v12 (1 : Word) (pc 268) (by decide)
  have h2c := cpsTripleWithin_extend_code
    (walkMem (pc 268) 268 (.LI .x12 (1 : Word))
      (by decide) (by unfold pc walkB; decide) rfl) h2
  rw [pc_succ 268] at h2c
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h2c
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2F
  have h3 := la_materialize_within (cr := fullCode) .x13 v13 (pc 269) MwValueOff
    (by decide) la_leaf_val_off_range
    (walkMem (pc 269) 269
      (.AUIPC .x13 (EvmAsm.Rv64.laHi (pc 269) MwValueOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_leaf_val_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 270)
          (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 269) MwValueOff)) a = some i := by
        simpa [pc_succ 269] using hs
      exact walkMem (pc 270) 270
        (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 269) MwValueOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_leaf_val_off_lo]; rfl) a i hs')
  rw [pc_add8_lv 269] at h3
  have h3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (1 : Word)) **
     (.x14 ↦ᵣ v14) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h3
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3F
  have h4 := la_materialize_within (cr := fullCode) .x14 v14 (pc 271) MwValueLen
    (by decide) la_leaf_val_len_range
    (walkMem (pc 271) 271
      (.AUIPC .x14 (EvmAsm.Rv64.laHi (pc 271) MwValueLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_leaf_val_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 272)
          (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 271) MwValueLen)) a = some i := by
        simpa [pc_succ 271] using hs
      exact walkMem (pc 272) 272
        (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 271) MwValueLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_leaf_val_len_lo]; rfl) a i hs')
  rw [pc_add8_lv 271] at h4
  have h4F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (1 : Word)) **
     (.x13 ↦ᵣ MwValueOff) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h4
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 h4F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp only [leafValNthSetup]
      xperm_chunked hq) c

/-! ## Nth call at pc273 (value field index 1) -/

set_option maxRecDepth 8000 in
theorem leaf_val_nth_call_spec_within
    (newSp nodeBase nodeLenW valOldOff valOldLen : Word)
    (nSaved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlistLenW : nodeLenW = BitVec.ofNat 64 listLen)
    (hsalign : nodeBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : nodeBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (nodeBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9))
      (pc 273) (pc 274) fullCode
      (((.x1 ↦ᵣ nSaved.ra) **
        callEntryRest newSp nodeBase nodeLenW (1 : Word) MwValueOff MwValueLen
          valOldOff valOldLen
          { nSaved with ra := pc 273 + 4 } bytes) ** F)
      (((.x1 ↦ᵣ (pc 273 + 4)) **
        callReturnResult newSp nodeBase (1 : Word) MwValueOff MwValueLen
          valOldOff valOldLen
          { nSaved with ra := pc 273 + 4 } bytes listLen 1) ** F) := by
  have hcall := rlpListNthItem_call_spec_within (cr := fullCode)
    (pc 273) NthB nSaved.ra newSp nodeBase nodeLenW (1 : Word)
    MwValueOff MwValueLen valOldOff valOldLen
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 1092))
    F hF nSaved bytes listLen 1
    hlistLenW rfl (by omega) hsalign hslack hover hvalid
    leaf_val_nth_ret_even leaf_val_nth_jal_target rfl
    (fun a i hs => walkMem (pc 273) 273
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 1092)))
      (by decide) (by unfold pc walkB; decide) rfl a i hs)
    (fun a i hc => nthCalleeMem a i hc)
  simpa using hcall

/-! ## Post-nth status -/

theorem leaf_val_nth_status_ok
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 274) (pc 275) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 104
  have hbne := bne_spec_gen_within .x10 .x0 off (0 : Word) (0 : Word) (pc 274)
  rw [bne_leaf_nth_fail_off, show pc 274 + 4 = pc 275 from pc_succ 274] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 274) 274 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

theorem leaf_val_nth_status_fail
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 274) (pc 300) fullCode
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 104
  have hbne := bne_spec_gen_within .x10 .x0 off (1 : Word) (0 : Word) (pc 274)
  rw [bne_leaf_nth_fail_off, show pc 274 + 4 = pc 275 from pc_succ 274] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 274) 274 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have htk := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR F hF htk
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htkF

/-! ## Publish value length to *outLen (x21) -/

/-- la+ld value_len; SD to *x21 (pc275→pc279). Fuel 4. -/
theorem leaf_val_store_len
    (v5 v6 valLen outLenPtr oldOutLen : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 275) (pc 279) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x21 ↦ᵣ outLenPtr) **
       (MwValueLen ↦ₘ valLen) ** (outLenPtr ↦ₘ oldOutLen) ** F)
      ((.x5 ↦ᵣ MwValueLen) ** (.x6 ↦ᵣ valLen) ** (.x21 ↦ᵣ outLenPtr) **
       (MwValueLen ↦ₘ valLen) ** (outLenPtr ↦ₘ valLen) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 275) MwValueLen
    (by decide) la_leaf_load_len_range
    (walkMem (pc 275) 275
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 275) MwValueLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_leaf_load_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 276)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 275) MwValueLen)) a = some i := by
        simpa [pc_succ 275] using hs
      exact walkMem (pc 276) 276
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 275) MwValueLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_leaf_load_len_lo]; rfl) a i hs')
  rw [pc_add8_lv 275] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x21 ↦ᵣ outLenPtr) ** (MwValueLen ↦ₘ valLen) **
     (outLenPtr ↦ₘ oldOutLen) ** F)
    (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x6 .x5 MwValueLen v6 valLen
    (0 : BitVec 12) (pc 277) (by decide)
  rw [signExtend12_0lv, show (MwValueLen + 0 : Word) = MwValueLen from by bv_omega,
      pc_succ 277] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 277) 277 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  -- LD focuses rs1+rd+mem; frame = x21 + outLen cell + F
  have hldF := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ outLenPtr) ** (outLenPtr ↦ₘ oldOutLen) ** F)
    (by pcf; exact hF) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  have hsd0 := sd_spec_gen_within .x21 .x6 outLenPtr valLen oldOutLen
    (0 : BitVec 12) (pc 278)
  rw [signExtend12_0lv, show (outLenPtr + 0 : Word) = outLenPtr from by bv_omega,
      pc_succ 278] at hsd0
  have hsd := cpsTripleWithin_extend_code
    (walkMem (pc 278) 278 (.SD .x21 .x6 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hsd0
  -- SD focuses rs1+rs2+mem; frame = x5 + MwValueLen + F
  have hsdF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwValueLen) ** (MwValueLen ↦ₘ valLen) ** F)
    (by pcf; exact hF) hsd
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hsdF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-! ## Load value offset + form value pointer -/

/-- la+ld value_off; ADD x7 = node+off (pc279→pc283). Fuel 4. -/
theorem leaf_val_load_ptr
    (v5 v7 nodeBase valOff : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 279) (pc 283) fullCode
      ((.x5 ↦ᵣ v5) ** (.x7 ↦ᵣ v7) ** (.x23 ↦ᵣ nodeBase) **
       (MwValueOff ↦ₘ valOff) ** F)
      ((.x5 ↦ᵣ MwValueOff) ** (.x7 ↦ᵣ (nodeBase + valOff)) **
       (.x23 ↦ᵣ nodeBase) ** (MwValueOff ↦ₘ valOff) ** F) := by
  have hla := la_materialize_within (cr := fullCode) .x5 v5 (pc 279) MwValueOff
    (by decide) la_leaf_load_off_range
    (walkMem (pc 279) 279
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 279) MwValueOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_leaf_load_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 280)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 279) MwValueOff)) a = some i := by
        simpa [pc_succ 279] using hs
      exact walkMem (pc 280) 280
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 279) MwValueOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_leaf_load_off_lo]; rfl) a i hs')
  rw [pc_add8_lv 279] at hla
  have hlaF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** (.x23 ↦ᵣ nodeBase) ** (MwValueOff ↦ₘ valOff) ** F)
    (by pcf; exact hF) hla
  have hld0 := ld_spec_gen_within .x7 .x5 MwValueOff v7 valOff
    (0 : BitVec 12) (pc 281) (by decide)
  rw [signExtend12_0lv, show (MwValueOff + 0 : Word) = MwValueOff from by bv_omega,
      pc_succ 281] at hld0
  have hld := cpsTripleWithin_extend_code
    (walkMem (pc 281) 281 (.LD .x7 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  -- LD focuses rs1+rd+mem; frame = x23 + F
  have hldF := cpsTripleWithin_frameR
    ((.x23 ↦ᵣ nodeBase) ** F) (by pcf; exact hF) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hlaF hldF
  -- ADD x7, x23, x7 — rd = rs2 = x7
  have hadd0 := add_spec_gen_rd_eq_rs2_within .x7 .x23 nodeBase valOff (pc 282)
    (by decide)
  have hadd := cpsTripleWithin_extend_code
    (walkMem (pc 282) 282 (.ADD .x7 .x23 .x7)
      (by decide) (by unfold pc walkB; decide) rfl) hadd0
  rw [pc_succ 282] at hadd
  -- focuses rs1+rd (=x23+x7); frame = x5 + mem + F
  have haddF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ MwValueOff) ** (MwValueOff ↦ₘ valOff) ** F)
    (by pcf; exact hF) hadd
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 haddF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-! ## Setup out cursor + clamp len ≤ 256 (no-clamp path) -/

/-- MV x28,x20; LI x29,256; BLTU ntaken (len≤256); JAL skip clamp → pc288.
    Fuel 4. Domain: valLen ≤ 256. -/
theorem leaf_val_clamp_noleq
    (v28 v29 outBase valLen : Word)
    (hle : ¬ BitVec.ult (256 : Word) valLen)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 4 (pc 283) (pc 288) fullCode
      ((.x20 ↦ᵣ outBase) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (.x6 ↦ᵣ valLen) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x20 ↦ᵣ outBase) ** (.x28 ↦ᵣ outBase) ** (.x29 ↦ᵣ (256 : Word)) **
       (.x6 ↦ᵣ valLen) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  -- MV focuses x28+x20
  have hmv := mv_spec_gen_within .x28 .x20 outBase v28 (pc 283) (by decide)
  have hmvc := cpsTripleWithin_extend_code
    (walkMem (pc 283) 283 (.MV .x28 .x20)
      (by decide) (by unfold pc walkB; decide) rfl) hmv
  rw [pc_succ 283] at hmvc
  have hmvF := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ v29) ** (.x6 ↦ᵣ valLen) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hmvc
  -- LI focuses x29
  have hli := li_spec_gen_within .x29 v29 (256 : Word) (pc 284) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (walkMem (pc 284) 284 (.LI .x29 (256 : Word))
      (by decide) (by unfold pc walkB; decide) rfl) hli
  rw [pc_succ 284] at hlic
  have hliF := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ outBase) ** (.x28 ↦ᵣ outBase) ** (.x6 ↦ᵣ valLen) **
     (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hlic
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hmvF hliF
  -- BLTU focuses x29+x6; ntaken when ¬(256 < valLen)
  have hbr0 := bltu_spec_gen_within .x29 .x6 (8 : BitVec 13)
    (256 : Word) valLen (pc 285)
  rw [bltu_leaf_clamp_off, show pc 285 + 4 = pc 286 from pc_succ 285] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 285) 285 (.BLTU .x29 .x6 (8 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hle ((sepConj_pure_right _).1 hQ).2)
  have hntF := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ outBase) ** (.x28 ↦ᵣ outBase) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hnt
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hntF
  -- JAL emp/emp
  have hjal0 := jal_x0_spec_gen_within (8 : BitVec 21) (pc 286)
  have hjal := cpsTripleWithin_extend_code
    (walkMem (pc 286) 286 (.JAL .x0 (8 : BitVec 21))
      (by decide) (by unfold pc walkB; decide) rfl) hjal0
  rw [jal_leaf_noclamp_off] at hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ outBase) ** (.x28 ↦ᵣ outBase) ** (.x29 ↦ᵣ (256 : Word)) **
     (.x6 ↦ᵣ valLen) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hjal
  have hjalW := cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hjalF
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hjalW
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-! ## Byte-copy loop out ← value (pc288→pc295) -/

def leafCopyInv (srcBase dstBase : Word) (k done : Nat)
    (srcBytes : List (BitVec 8)) (dstBytes : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 done)) **
  (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 done)) **
  (.x6 ↦ᵣ BitVec.ofNat 64 k) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion srcBase srcBytes **
  bytesRegion dstBase dstBytes **
  regOwn .x5 ** F

def leafCopyDone (srcBase dstBase : Word) (n : Nat)
    (srcBytes dstBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 n)) **
  (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 n)) **
  (.x6 ↦ᵣ (0 : Word)) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion srcBase srcBytes **
  bytesRegion dstBase dstBytes **
  regOwn .x5 ** F

theorem leaf_copy_exit_zero
    (srcBase dstBase : Word) (n : Nat)
    (srcBytes dstBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 288) (pc 295) fullCode
      (leafCopyInv srcBase dstBase 0 n srcBytes dstBytes F)
      (leafCopyDone srcBase dstBase n srcBytes dstBytes F) := by
  have hbr0 := beq_spec_gen_within .x6 .x0 (28 : BitVec 13)
    (0 : Word) (0 : Word) (pc 288)
  rw [beq_leaf_copy_done_off, show pc 288 + 4 = pc 289 from pc_succ 288] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 288) 288 (.BEQ .x6 .x0 (28 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have ht := cpsBranchWithin_takenStripPure2 hbr
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  let G : Assertion :=
    (.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 n)) **
    (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 n)) **
    bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes **
    regOwn .x5 ** F
  have hG : G.pcFree := by pcf; exact hF
  have htF := cpsTripleWithin_frameR G hG ht
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [leafCopyInv, ofNat_zero_lv, G] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => by
      simp only [leafCopyDone, G] at hq ⊢
      xperm_chunked hq)
    htF

set_option maxRecDepth 8000 in
theorem leaf_copy_step
    (srcBase dstBase : Word) (k done : Nat)
    (srcBytes dstOrig : List (BitVec 8))
    (hsrc : done < srcBytes.length)
    (hdst : done < dstOrig.length)
    (hsrcAlign : srcBase.toNat % 8 = 0)
    (hdstAlign : dstBase.toNat % 8 = 0)
    (hsrcOver : srcBase.toNat + done < 2 ^ 64)
    (hdstOver : dstBase.toNat + done < 2 ^ 64)
    (hkbound : k + 1 < 2 ^ 64)
    (hvalidS : isValidByteAccess (srcBase + BitVec.ofNat 64 done) = true)
    (hvalidD : isValidByteAccess (dstBase + BitVec.ofNat 64 done) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc 288) (pc 288) fullCode
      (leafCopyInv srcBase dstBase (k + 1) done srcBytes dstOrig F)
      (leafCopyInv srcBase dstBase k (done + 1) srcBytes
        (dstOrig.set done (srcBytes[done]'hsrc)) F) := by
  have hne := word_ofNat_succ_ne_zero_lv k hkbound
  have hbr0 := beq_spec_gen_within .x6 .x0 (28 : BitVec 13)
    (BitVec.ofNat 64 (k + 1)) (0 : Word) (pc 288)
  rw [beq_leaf_copy_done_off, show pc 288 + 4 = pc 289 from pc_succ 288] at hbr0
  have hbr := cpsBranchWithin_extend_code
    (walkMem (pc 288) 288 (.BEQ .x6 .x0 (28 : BitVec 13))
      (by decide) (by unfold pc walkB; decide) rfl) hbr0
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hQ).2)
  have hbeq := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 done)) **
     (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 done)) **
     bytesRegion srcBase srcBytes ** bytesRegion dstBase dstOrig **
     regOwn .x5 ** F)
    (by pcf; exact hF) hnt
  -- LBU x5 from src (peel own x5)
  have hlbu : ∀ v5,
      cpsTripleWithin 1 (pc 289) (pc 290) fullCode
        (((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 done)) **
          bytesRegion srcBase srcBytes **
          (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 done)) **
          (.x6 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion dstBase dstOrig ** F) **
         (.x5 ↦ᵣ v5))
        (((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 done)) **
          (.x5 ↦ᵣ ((srcBytes[done]'hsrc).zeroExtend 64)) **
          bytesRegion srcBase srcBytes **
          (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 done)) **
          (.x6 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion dstBase dstOrig ** F)) := by
    intro v5
    have hl := bytesRegion_lbu_within .x5 .x7 srcBase v5 (pc 289)
      srcBytes done (by decide) hsrcAlign hsrc hsrcOver hvalidS
    have hlE := cpsTripleWithin_extend_code
      (walkMem (pc 289) 289 (.LBU .x5 .x7 (0 : BitVec 12))
        (by decide) (by unfold pc walkB; decide) rfl) hl
    rw [pc_succ 289] at hlE
    have hFr := cpsTripleWithin_frameR
      ((.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 done)) **
       (.x6 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion dstBase dstOrig ** F)
      (by pcf; exact hF) hlE
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hFr
  have hlbuOwn := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5) hlbu
  -- SB x5 to dst
  have hsb0 := bytesRegion_sb_within .x28 .x5 dstBase
    ((srcBytes[done]'hsrc).zeroExtend 64) (pc 290) dstOrig done
    hdstAlign hdst hdstOver hvalidD
  have hsb := cpsTripleWithin_extend_code
    (walkMem (pc 290) 290 (.SB .x28 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hsb0
  rw [pc_succ 290] at hsb
  -- sb post uses truncate 8 of zeroExtend = identity on byte
  have hbyte :
      ((srcBytes[done]'hsrc).zeroExtend 64).truncate 8 = srcBytes[done]'hsrc := by
    exact truncate_zeroExtend_byte _
  simp only [hbyte] at hsb
  have hsbF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 done)) **
     (.x6 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     bytesRegion srcBase srcBytes ** F)
    (by pcf; exact hF) hsb
  -- ADDIs
  have hadd70 := addi_spec_gen_same_within .x7 (srcBase + BitVec.ofNat 64 done)
    (1 : BitVec 12) (pc 291) (by decide)
  have hadd7 := cpsTripleWithin_extend_code
    (walkMem (pc 291) 291 (.ADDI .x7 .x7 (1 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hadd70
  rw [pc_succ 291, signExtend12_1lv] at hadd7
  have hadd7F := cpsTripleWithin_frameR
    ((.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 done)) **
     (.x6 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ ((srcBytes[done]'hsrc).zeroExtend 64)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (dstOrig.set done (srcBytes[done]'hsrc)) ** F)
    (by pcf; exact hF) hadd7
  have hadd280 := addi_spec_gen_same_within .x28 (dstBase + BitVec.ofNat 64 done)
    (1 : BitVec 12) (pc 292) (by decide)
  have hadd28 := cpsTripleWithin_extend_code
    (walkMem (pc 292) 292 (.ADDI .x28 .x28 (1 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hadd280
  rw [pc_succ 292, signExtend12_1lv] at hadd28
  have hadd28F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x6 ↦ᵣ BitVec.ofNat 64 (k + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ ((srcBytes[done]'hsrc).zeroExtend 64)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (dstOrig.set done (srcBytes[done]'hsrc)) ** F)
    (by pcf; exact hF) hadd28
  have hadd60 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (k + 1))
    (-1 : BitVec 12) (pc 293) (by decide)
  have hadd6 := cpsTripleWithin_extend_code
    (walkMem (pc 293) 293 (.ADDI .x6 .x6 (-1 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hadd60
  rw [pc_succ 293, signExtend12_m1lv] at hadd6
  have hadd6F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ ((srcBytes[done]'hsrc).zeroExtend 64)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (dstOrig.set done (srcBytes[done]'hsrc)) ** F)
    (by pcf; exact hF) hadd6
  have hjal0 := jal_x0_spec_gen_within (-24 : BitVec 21) (pc 294)
  have hjal := cpsTripleWithin_extend_code
    (walkMem (pc 294) 294 (.JAL .x0 (-24 : BitVec 21))
      (by decide) (by unfold pc walkB; decide) rfl) hjal0
  rw [jal_leaf_copy_back_off] at hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 done + (1 : Word))) **
     (.x6 ↦ᵣ (BitVec.ofNat 64 (k + 1) + (-1 : Word))) **
     (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ ((srcBytes[done]'hsrc).zeroExtend 64)) **
     bytesRegion srcBase srcBytes **
     bytesRegion dstBase (dstOrig.set done (srcBytes[done]'hsrc)) ** F)
    (by pcf; exact hF) hjal
  have hjalW := cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hjalF
  have c0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hbeq hlbuOwn
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0 hsbF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hadd7F
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hadd28F
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 hadd6F
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01234 hjalW
  have hcur7 := cursor_succ_lv srcBase done
  have hcur28 := cursor_succ_lv dstBase done
  have hrem := cnt_step_down_lv k
  refine cpsTripleWithin_weaken ?_ ?_ c
  · intro h hp; simp only [leafCopyInv] at hp ⊢; xperm_chunked hp
  · intro h hq
    -- rewrite cursors/rem, front x5, drop to own
    have hq1 :
        ((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (done + 1))) **
         (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 (done + 1))) **
         (.x6 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes **
         bytesRegion dstBase (dstOrig.set done (srcBytes[done]'hsrc)) **
         (.x5 ↦ᵣ ((srcBytes[done]'hsrc).zeroExtend 64)) ** F) h := by
      simp only [hcur7, hcur28, hrem] at hq
      xperm_chunked hq
    have hq2 :
        ((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (done + 1))) **
         (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 (done + 1))) **
         (.x6 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes **
         bytesRegion dstBase (dstOrig.set done (srcBytes[done]'hsrc)) **
         regOwn .x5 ** F) h := by
      -- right-assoc: (... ** (x5 ** F)); mono on x5
      have hx :
          (((.x7 ↦ᵣ (srcBase + BitVec.ofNat 64 (done + 1))) **
            (.x28 ↦ᵣ (dstBase + BitVec.ofNat 64 (done + 1))) **
            (.x6 ↦ᵣ BitVec.ofNat 64 k) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes **
            bytesRegion dstBase (dstOrig.set done (srcBytes[done]'hsrc)) ** F) **
           (.x5 ↦ᵣ ((srcBytes[done]'hsrc).zeroExtend 64))) h := by
        xperm_chunked hq1
      have hx' := sepConj_mono_right (regIs_implies_regOwn (r := .x5)) h hx
      xperm_chunked hx'
    simpa only [leafCopyInv] using hq2

/-- Success: LI a0,0; JAL epi (pc295→pc305). Fuel 2. -/
theorem leaf_val_success_exit
    (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 295) (pc 305) fullCode
      ((.x10 ↦ᵣ v10) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** F) := by
  have hli := li_spec_gen_within .x10 v10 (0 : Word) (pc 295) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (walkMem (pc 295) 295 (.LI .x10 (0 : Word))
      (by decide) (by unfold pc walkB; decide) rfl) hli
  rw [pc_succ 295] at hlic
  have hliF := cpsTripleWithin_frameR F hF hlic
  have hjal0 := jal_x0_spec_gen_within (36 : BitVec 21) (pc 296)
  have hjal := cpsTripleWithin_extend_code
    (walkMem (pc 296) 296 (.JAL .x0 (36 : BitVec 21))
      (by decide) (by unfold pc walkB; decide) rfl) hjal0
  rw [jal_leaf_succ_epi_off] at hjal
  have hjalF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** F) (by pcf; exact hF) hjal
  have hjalW := cpsTripleWithin_weaken
    (fun _ hp => (sepConj_emp_left _).2 hp)
    (fun _ hq => (sepConj_emp_left _).1 hq) hjalF
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hliF hjalW
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

end EvmAsm.Codegen.MptWalkSpec
