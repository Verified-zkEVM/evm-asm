/-
  Extension arm entry (#11799): pc125→nth call.

  Idx:
  125-126 MV a0/a1 = node ptr/len
  127 LI a2, 0  (path field index)
  128-131 la a3/a4 = mw_path_offset/length
  132 JAL rlp_list_nth_item

  hp_decode_nibbles at pc147 is SEPARATE residual (no machine triple yet).
-/

import EvmAsm.Codegen.Programs.MptWalkBranchHash
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

private theorem la_ext_path_off_hi :
    laHi GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 512) =
      EvmAsm.Rv64.laHi (pc 128) MwPathOff := by
  unfold pc walkB MwPathOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_path_off_lo :
    laLo GuestAddrs.mw_path_offset (GuestAddrs.mpt_walk + 512) =
      EvmAsm.Rv64.laLo (pc 128) MwPathOff := by
  unfold pc walkB MwPathOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_path_off_range : laInRange (pc 128) MwPathOff := by
  unfold pc walkB MwPathOff laInRange; decide

private theorem la_ext_path_len_hi :
    laHi GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 520) =
      EvmAsm.Rv64.laHi (pc 130) MwPathLen := by
  unfold pc walkB MwPathLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_path_len_lo :
    laLo GuestAddrs.mw_path_length (GuestAddrs.mpt_walk + 520) =
      EvmAsm.Rv64.laLo (pc 130) MwPathLen := by
  unfold pc walkB MwPathLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_path_len_range : laInRange (pc 130) MwPathLen := by
  unfold pc walkB MwPathLen laInRange; decide

private theorem ext_nth_jal_target :
    pc 132 + signExtend21
      (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 528)) =
      NthB := by
  change BitVec.ofNat 64 GuestAddrs.mpt_walk + BitVec.ofNat 64 528 +
      signExtend21 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 528)) =
    BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
  exact jalOff_correct_add GuestAddrs.rlp_list_nth_item GuestAddrs.mpt_walk 528
    (by decide) (by decide) (by decide) (by decide)

private theorem ext_nth_ret_even :
    (pc 132 + 4) &&& ~~~(1 : Word) = pc 132 + 4 := by
  unfold pc walkB; decide

private theorem pc_add8_ext (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

/-- After dispatch into ext: setup nth ABI for path field (index 0). -/
def extNthSetup (nodeBase nodeLenW : Word) (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (0 : Word)) **
  (.x13 ↦ᵣ MwPathOff) ** (.x14 ↦ᵣ MwPathLen) **
  (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F

/-! MV/MV/LI + la path BSS (pc125→pc132). -/
theorem ext_nth_setup_spec
    (v10 v11 v12 v13 v14 nodeBase nodeLenW : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc 125) (pc 132) fullCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
      (extNthSetup nodeBase nodeLenW F) := by
  -- MV x10,x23
  have h0 := mv_spec_gen_within .x10 .x23 nodeBase v10 (pc 125) (by decide)
  have h0c := cpsTripleWithin_extend_code
    (walkMem (pc 125) 125 (.MV .x10 .x23)
      (by decide) (by unfold pc walkB; decide) rfl) h0
  rw [pc_succ 125] at h0c
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h0c
  -- MV x11,x24
  have h1 := mv_spec_gen_within .x11 .x24 nodeLenW v11 (pc 126) (by decide)
  have h1c := cpsTripleWithin_extend_code
    (walkMem (pc 126) 126 (.MV .x11 .x24)
      (by decide) (by unfold pc walkB; decide) rfl) h1
  rw [pc_succ 126] at h1c
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** F)
    (by pcf; exact hF) h1c
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0F h1F
  -- LI x12, 0
  have h2 := li_spec_gen_within .x12 v12 (0 : Word) (pc 127) (by decide)
  have h2c := cpsTripleWithin_extend_code
    (walkMem (pc 127) 127 (.LI .x12 (0 : Word))
      (by decide) (by unfold pc walkB; decide) rfl) h2
  rw [pc_succ 127] at h2c
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h2c
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2F
  -- la x13 path_off
  have h3 := la_materialize_within (cr := fullCode) .x13 v13 (pc 128) MwPathOff
    (by decide) la_ext_path_off_range
    (walkMem (pc 128) 128
      (.AUIPC .x13 (EvmAsm.Rv64.laHi (pc 128) MwPathOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_path_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 129)
          (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 128) MwPathOff)) a = some i := by
        simpa [pc_succ 128] using hs
      exact walkMem (pc 129) 129
        (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 128) MwPathOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_path_off_lo]; rfl) a i hs')
  rw [pc_add8_ext 128] at h3
  have h3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (0 : Word)) **
     (.x14 ↦ᵣ v14) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h3
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3F
  -- la x14 path_len
  have h4 := la_materialize_within (cr := fullCode) .x14 v14 (pc 130) MwPathLen
    (by decide) la_ext_path_len_range
    (walkMem (pc 130) 130
      (.AUIPC .x14 (EvmAsm.Rv64.laHi (pc 130) MwPathLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_path_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 131)
          (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 130) MwPathLen)) a = some i := by
        simpa [pc_succ 130] using hs
      exact walkMem (pc 131) 131
        (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 130) MwPathLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_path_len_lo]; rfl) a i hs')
  rw [pc_add8_ext 130] at h4
  have h4F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (0 : Word)) **
     (.x13 ↦ᵣ MwPathOff) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h4
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 h4F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp only [extNthSetup]
      xperm_chunked hq) c

/-! Nth call at walk pc132 (path field index 0). Frame through call is caller F. -/
theorem ext_nth_call_spec_within
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
      (pc 132) (pc 133) fullCode
      (((.x1 ↦ᵣ raVal) **
        callEntryRest newSp nodeBase nodeLenW (0 : Word) MwPathOff MwPathLen
          pathOldOff pathOldLen { nSaved with ra := pc 133 } bytes) ** F)
      (((.x1 ↦ᵣ (pc 133)) **
        callReturnResult newSp nodeBase (0 : Word) MwPathOff MwPathLen
          pathOldOff pathOldLen { nSaved with ra := pc 133 } bytes
          listLen 0) ** F) := by
  have hmem : ∀ a i,
      CodeReq.singleton (pc 132)
          (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
            (GuestAddrs.mpt_walk + 528))) a = some i →
        fullCode a = some i :=
    walkMem (pc 132) 132
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
        (GuestAddrs.mpt_walk + 528)))
      (by decide) (by unfold pc walkB; decide) rfl
  have h := rlpListNthItem_call_spec_within (cr := fullCode)
    (callerPC := pc 132) (calleeEntry := NthB) raVal
    newSp nodeBase nodeLenW (0 : Word) MwPathOff MwPathLen
    pathOldOff pathOldLen
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 528))
    F hF nSaved bytes listLen 0
    hlistLenW (rfl : (0 : Word) = BitVec.ofNat 64 0) (by decide)
    hsalign hslack hover hvalid
    ext_nth_ret_even ext_nth_jal_target rfl hmem nthCalleeMem
  have hpc : pc 132 + 4 = pc 133 := pc_succ 132
  simpa [hpc] using h

end EvmAsm.Codegen.MptWalkSpec
