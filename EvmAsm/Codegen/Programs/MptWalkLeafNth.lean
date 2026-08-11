/-
  Leaf arm entry (#11799): pc220→nth call for path field.

  Idx:
  220-221 MV a0/a1 = node ptr/len
  222 LI a2, 0  (path field index)
  223-226 la a3/a4 = mw_path_offset/length
  227 JAL rlp_list_nth_item

  hp_decode at pc242 is SEPARATE residual.
-/

import EvmAsm.Codegen.Programs.MptWalkExtHp
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.LaResolve

namespace EvmAsm.Codegen.MptWalkSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.MptNodeKindSpec
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

private theorem la_leaf_path_off_hi :
    laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 892) =
      EvmAsm.Rv64.laHi (pc 223) MwPathOff := by
  unfold pc walkB MwPathOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_leaf_path_off_lo :
    laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 892) =
      EvmAsm.Rv64.laLo (pc 223) MwPathOff := by
  unfold pc walkB MwPathOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_leaf_path_off_range : laInRange (pc 223) MwPathOff := by
  unfold pc walkB MwPathOff laInRange; decide

private theorem la_leaf_path_len_hi :
    laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 900) =
      EvmAsm.Rv64.laHi (pc 225) MwPathLen := by
  unfold pc walkB MwPathLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_leaf_path_len_lo :
    laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 900) =
      EvmAsm.Rv64.laLo (pc 225) MwPathLen := by
  unfold pc walkB MwPathLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_leaf_path_len_range : laInRange (pc 225) MwPathLen := by
  unfold pc walkB MwPathLen laInRange; decide

private theorem leaf_nth_jal_target :
    pc 227 + signExtend21
      (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 908)) =
      NthB := by
  change BitVec.ofNat 64 GuestAddrs.mpt_walk + BitVec.ofNat 64 908 +
      signExtend21 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 908)) =
    BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
  exact jalOff_correct_add GuestAddrs.rlp_list_nth_item GuestAddrs.mpt_walk 908
    (by decide) (by decide) (by decide) (by decide)

private theorem leaf_nth_ret_even :
    (pc 227 + 4) &&& ~~~(1 : Word) = pc 227 + 4 := by
  unfold pc walkB; decide

private theorem pc_add8_lf (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

def leafNthSetup (nodeBase nodeLenW : Word) (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (0 : Word)) **
  (.x13 ↦ᵣ MwPathOff) ** (.x14 ↦ᵣ MwPathLen) **
  (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F

/-! MV/MV/LI + la path BSS (pc220→pc227). -/
theorem leaf_nth_setup_spec
    (v10 v11 v12 v13 v14 nodeBase nodeLenW : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc 220) (pc 227) fullCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
      (leafNthSetup nodeBase nodeLenW F) := by
  have h0 := mv_spec_gen_within .x10 .x23 nodeBase v10 (pc 220) (by decide)
  have h0c := cpsTripleWithin_extend_code
    (walkMem (pc 220) 220 (.MV .x10 .x23)
      (by decide) (by unfold pc walkB; decide) rfl) h0
  rw [pc_succ 220] at h0c
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h0c
  have h1 := mv_spec_gen_within .x11 .x24 nodeLenW v11 (pc 221) (by decide)
  have h1c := cpsTripleWithin_extend_code
    (walkMem (pc 221) 221 (.MV .x11 .x24)
      (by decide) (by unfold pc walkB; decide) rfl) h1
  rw [pc_succ 221] at h1c
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** F)
    (by pcf; exact hF) h1c
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0F h1F
  have h2 := li_spec_gen_within .x12 v12 (0 : Word) (pc 222) (by decide)
  have h2c := cpsTripleWithin_extend_code
    (walkMem (pc 222) 222 (.LI .x12 (0 : Word))
      (by decide) (by unfold pc walkB; decide) rfl) h2
  rw [pc_succ 222] at h2c
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x13 ↦ᵣ v13) **
     (.x14 ↦ᵣ v14) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h2c
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2F
  have h3 := la_materialize_within (cr := fullCode) .x13 v13 (pc 223) MwPathOff
    (by decide) la_leaf_path_off_range
    (walkMem (pc 223) 223
      (.AUIPC .x13 (EvmAsm.Rv64.laHi (pc 223) MwPathOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_leaf_path_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 224)
          (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 223) MwPathOff)) a = some i := by
        simpa [pc_succ 223] using hs
      exact walkMem (pc 224) 224
        (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 223) MwPathOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_leaf_path_off_lo]; rfl) a i hs')
  rw [pc_add8_lf 223] at h3
  have h3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (0 : Word)) **
     (.x14 ↦ᵣ v14) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h3
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3F
  have h4 := la_materialize_within (cr := fullCode) .x14 v14 (pc 225) MwPathLen
    (by decide) la_leaf_path_len_range
    (walkMem (pc 225) 225
      (.AUIPC .x14 (EvmAsm.Rv64.laHi (pc 225) MwPathLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_leaf_path_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 226)
          (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 225) MwPathLen)) a = some i := by
        simpa [pc_succ 225] using hs
      exact walkMem (pc 226) 226
        (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 225) MwPathLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_leaf_path_len_lo]; rfl) a i hs')
  rw [pc_add8_lf 225] at h4
  have h4F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (0 : Word)) **
     (.x13 ↦ᵣ MwPathOff) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h4
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 h4F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp only [leafNthSetup]
      xperm_chunked hq) c

/-! Nth call at walk pc227 (path field index 0). -/
theorem leaf_nth_call_spec_within
    (newSp nodeBase nodeLenW pathOldOff pathOldLen raVal : Word)
    (nSaved : Saved) (bytes : List (BitVec 8)) (listLen : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlistLenW : nodeLenW = BitVec.ofNat 64 listLen)
    (hsalign : nodeBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : nodeBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (nodeBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9))
      (pc 227) (pc 228) fullCode
      (((.x1 ↦ᵣ raVal) **
        callEntryRest newSp nodeBase nodeLenW (0 : Word) MwPathOff MwPathLen
          pathOldOff pathOldLen { nSaved with ra := pc 228 } bytes) ** F)
      (((.x1 ↦ᵣ (pc 228)) **
        callReturnResult newSp nodeBase (0 : Word) MwPathOff MwPathLen
          pathOldOff pathOldLen { nSaved with ra := pc 228 } bytes
          listLen 0) ** F) := by
  have hmem : ∀ a i,
      CodeReq.singleton (pc 227)
          (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
            (GuestAddrs.mpt_walk + 908))) a = some i →
        fullCode a = some i :=
    walkMem (pc 227) 227
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.mpt_walk + 908)))
      (by decide) (by unfold pc walkB; decide) rfl
  have h := rlpListNthItem_call_spec_within (cr := fullCode)
    (callerPC := pc 227) (calleeEntry := NthB) raVal
    newSp nodeBase nodeLenW (0 : Word) MwPathOff MwPathLen
    pathOldOff pathOldLen
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 908))
    F hF nSaved bytes listLen 0
    hlistLenW (rfl : (0 : Word) = BitVec.ofNat 64 0) (by decide)
    hsalign hslack hover hvalid
    leaf_nth_ret_even leaf_nth_jal_target rfl hmem nthCalleeMem
  have hpc : pc 227 + 4 = pc 228 := pc_succ 227
  simpa [hpc] using h

end EvmAsm.Codegen.MptWalkSpec
