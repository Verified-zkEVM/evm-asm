/-
  Extension arm after path-match (#11799): pc170→hash hop entry.

  170 ADD x22 += count (path position advance)
  171-177 nth setup: a0/a1=node, a2=1 (child field), la child BSS
  178 JAL rlp_list_nth_item
  179 BNE status fail → pc300
  180-185 load child_len / child_off
  186 ADD child ptr
  187-188 LI 32; BEQ → hash hop pc192
  189-191 inlined (len≠32) EXCLUDED BY GATE

  Stops before witness_lookup residual at pc210.
-/
import EvmAsm.Codegen.Programs.MptWalkExtCmp
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

private theorem pc_add8_ec (n : Nat) : pc n + 8 = pc (n + 2) := by
  unfold pc; bv_omega

private theorem signExtend12_0c : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide

private theorem bne_ext_nth_fail_off :
    pc 179 + signExtend13 (484 : BitVec 13) = pc 300 := by
  unfold pc walkB signExtend13; decide

private theorem beq_ext_hash_off :
    pc 188 + signExtend13 (16 : BitVec 13) = pc 192 := by
  unfold pc walkB signExtend13; decide

private theorem la_ext_child_off_hi :
    laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 696) =
      EvmAsm.Rv64.laHi (pc 174) MwChildOff := by
  unfold pc walkB MwChildOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_child_off_lo :
    laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 696) =
      EvmAsm.Rv64.laLo (pc 174) MwChildOff := by
  unfold pc walkB MwChildOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_child_off_range : laInRange (pc 174) MwChildOff := by
  unfold pc walkB MwChildOff laInRange; decide

private theorem la_ext_child_len_hi :
    laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 704) =
      EvmAsm.Rv64.laHi (pc 176) MwChildLen := by
  unfold pc walkB MwChildLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_child_len_lo :
    laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 704) =
      EvmAsm.Rv64.laLo (pc 176) MwChildLen := by
  unfold pc walkB MwChildLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_child_len_range : laInRange (pc 176) MwChildLen := by
  unfold pc walkB MwChildLen laInRange; decide

private theorem ext_child_nth_jal_target :
    pc 178 + signExtend21
      (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 712)) =
      NthB := by
  change BitVec.ofNat 64 GuestAddrs.mpt_walk + BitVec.ofNat 64 712 +
      signExtend21 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 712)) =
    BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
  exact jalOff_correct_add GuestAddrs.rlp_list_nth_item GuestAddrs.mpt_walk 712
    (by decide) (by decide) (by decide) (by decide)

private theorem ext_child_nth_ret_even :
    (pc 178 + 4) &&& ~~~(1 : Word) = pc 178 + 4 := by
  unfold pc walkB; decide

private theorem la_ext_load_len_hi :
    laHi GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 720) =
      EvmAsm.Rv64.laHi (pc 180) MwChildLen := by
  unfold pc walkB MwChildLen EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_load_len_lo :
    laLo GuestAddrs.mw_child_length (GuestAddrs.mpt_walk + 720) =
      EvmAsm.Rv64.laLo (pc 180) MwChildLen := by
  unfold pc walkB MwChildLen EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_load_len_range : laInRange (pc 180) MwChildLen := by
  unfold pc walkB MwChildLen laInRange; decide

private theorem la_ext_load_off_hi :
    laHi GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 732) =
      EvmAsm.Rv64.laHi (pc 183) MwChildOff := by
  unfold pc walkB MwChildOff EvmAsm.Rv64.laHi laHi laDelta; decide

private theorem la_ext_load_off_lo :
    laLo GuestAddrs.mw_child_offset (GuestAddrs.mpt_walk + 732) =
      EvmAsm.Rv64.laLo (pc 183) MwChildOff := by
  unfold pc walkB MwChildOff EvmAsm.Rv64.laLo laLo laDelta; decide

private theorem la_ext_load_off_range : laInRange (pc 183) MwChildOff := by
  unfold pc walkB MwChildOff laInRange; decide

/-! ## Pos advance after path match -/

/-- ADD x22, x22, x6 — advance path position by matched segment length. -/
theorem ext_pos_advance
    (posW countW : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 170) (pc 171) fullCode
      ((.x22 ↦ᵣ posW) ** (.x6 ↦ᵣ countW) ** F)
      ((.x22 ↦ᵣ (posW + countW)) ** (.x6 ↦ᵣ countW) ** F) := by
  have h := add_spec_gen_rd_eq_rs1_within .x22 .x6 posW countW (pc 170) (by decide)
  have hc := cpsTripleWithin_extend_code
    (walkMem (pc 170) 170 (.ADD .x22 .x22 .x6)
      (by decide) (by unfold pc walkB; decide) rfl) h
  rw [pc_succ 170] at hc
  have hF' := cpsTripleWithin_frameR F hF hc
  -- frameR yields left-pair ((x22**x6)**F); goal is right-assoc
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hF'

/-! ## Nth setup for child field (index 1) -/

/-- After setup: ABI ready for nth child field. -/
def extChildNthSetup (nodeBase nodeLenW : Word) (F : Assertion) : Assertion :=
  (.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (1 : Word)) **
  (.x13 ↦ᵣ MwChildOff) ** (.x14 ↦ᵣ MwChildLen) **
  (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F

/-- MV/MV/LI1 + la child BSS (pc171→pc178). Fuel 7. -/
theorem ext_child_nth_setup_spec
    (v10 v11 v12 v13 v14 nodeBase nodeLenW : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 7 (pc 171) (pc 178) fullCode
      ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
      (extChildNthSetup nodeBase nodeLenW F) := by
  -- MV x10,x23
  have h0 := mv_spec_gen_within .x10 .x23 nodeBase v10 (pc 171) (by decide)
  have h0c := cpsTripleWithin_extend_code
    (walkMem (pc 171) 171 (.MV .x10 .x23)
      (by decide) (by unfold pc walkB; decide) rfl) h0
  rw [pc_succ 171] at h0c
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h0c
  -- MV x11,x24
  have h1 := mv_spec_gen_within .x11 .x24 nodeLenW v11 (pc 172) (by decide)
  have h1c := cpsTripleWithin_extend_code
    (walkMem (pc 172) 172 (.MV .x11 .x24)
      (by decide) (by unfold pc walkB; decide) rfl) h1
  rw [pc_succ 172] at h1c
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** F)
    (by pcf; exact hF) h1c
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h0F h1F
  -- LI x12, 1
  have h2 := li_spec_gen_within .x12 v12 (1 : Word) (pc 173) (by decide)
  have h2c := cpsTripleWithin_extend_code
    (walkMem (pc 173) 173 (.LI .x12 (1 : Word))
      (by decide) (by unfold pc walkB; decide) rfl) h2
  rw [pc_succ 173] at h2c
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h2c
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 h2F
  -- la x13 child_off
  have h3 := la_materialize_within (cr := fullCode) .x13 v13 (pc 174) MwChildOff
    (by decide) la_ext_child_off_range
    (walkMem (pc 174) 174
      (.AUIPC .x13 (EvmAsm.Rv64.laHi (pc 174) MwChildOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_child_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 175)
          (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 174) MwChildOff)) a = some i := by
        simpa [pc_succ 174] using hs
      exact walkMem (pc 175) 175
        (.ADDI .x13 .x13 (EvmAsm.Rv64.laLo (pc 174) MwChildOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_child_off_lo]; rfl) a i hs')
  rw [pc_add8_ec 174] at h3
  have h3F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (1 : Word)) **
     (.x14 ↦ᵣ v14) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h3
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 h3F
  -- la x14 child_len
  have h4 := la_materialize_within (cr := fullCode) .x14 v14 (pc 176) MwChildLen
    (by decide) la_ext_child_len_range
    (walkMem (pc 176) 176
      (.AUIPC .x14 (EvmAsm.Rv64.laHi (pc 176) MwChildLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_child_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 177)
          (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 176) MwChildLen)) a = some i := by
        simpa [pc_succ 176] using hs
      exact walkMem (pc 177) 177
        (.ADDI .x14 .x14 (EvmAsm.Rv64.laLo (pc 176) MwChildLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_child_len_lo]; rfl) a i hs')
  rw [pc_add8_ec 176] at h4
  have h4F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ nodeBase) ** (.x11 ↦ᵣ nodeLenW) ** (.x12 ↦ᵣ (1 : Word)) **
     (.x13 ↦ᵣ MwChildOff) ** (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF) h4
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c0123 h4F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp only [extChildNthSetup]
      xperm_chunked hq) c

/-! ## Nth call at pc178 (child field index 1) -/

set_option maxRecDepth 8000 in
theorem ext_child_nth_call_spec_within
    (newSp nodeBase nodeLenW childOldOff childOldLen : Word)
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
      (pc 178) (pc 179) fullCode
      (((.x1 ↦ᵣ nSaved.ra) **
        callEntryRest newSp nodeBase nodeLenW (1 : Word) MwChildOff MwChildLen
          childOldOff childOldLen
          { nSaved with ra := pc 178 + 4 } bytes) ** F)
      (((.x1 ↦ᵣ (pc 178 + 4)) **
        callReturnResult newSp nodeBase (1 : Word) MwChildOff MwChildLen
          childOldOff childOldLen
          { nSaved with ra := pc 178 + 4 } bytes listLen 1) ** F) := by
  have hcall := rlpListNthItem_call_spec_within (cr := fullCode)
    (pc 178) NthB nSaved.ra newSp nodeBase nodeLenW (1 : Word)
    MwChildOff MwChildLen childOldOff childOldLen
    (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 712))
    F hF nSaved bytes listLen 1
    hlistLenW rfl (by omega) hsalign (by omega) (by omega) hover hvalid (by omega)
    ext_child_nth_ret_even ext_child_nth_jal_target rfl
    (fun a i hs => walkMem (pc 178) 178
      (.JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.mpt_walk + 712)))
      (by decide) (by unfold pc walkB; decide) rfl a i hs)
    (fun a i hc => nthCalleeMem a i hc)
  simpa using hcall

/-! ## Post-nth: status + load len/off + hash32 entry -/

/-- Nth status = 0: fall through. -/
theorem ext_child_nth_status_ok
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 179) (pc 180) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 484
  have hbne := bne_spec_gen_within .x10 .x0 off (0 : Word) (0 : Word) (pc 179)
  rw [bne_ext_nth_fail_off, show pc 179 + 4 = pc 180 from pc_succ 179] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 179) 179 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have hnt := cpsBranchWithin_ntakenStripPure2 hbnee (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hntF := cpsTripleWithin_frameR F hF hnt
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hntF

/-- Nth status ≠ 0: taken BNE to fail. -/
theorem ext_child_nth_status_fail
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 179) (pc 300) fullCode
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F) := by
  let off : BitVec 13 := 484
  have hbne := bne_spec_gen_within .x10 .x0 off (1 : Word) (0 : Word) (pc 179)
  rw [bne_ext_nth_fail_off, show pc 179 + 4 = pc 180 from pc_succ 179] at hbne
  have hbnee := cpsBranchWithin_extend_code
    (walkMem (pc 179) 179 (.BNE .x10 .x0 off)
      (by decide) (by unfold pc walkB; decide) rfl) hbne
  have htk := cpsBranchWithin_takenStripPure2 hbnee (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR F hF htk
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) htkF

/-- Load child_len into x6 and child_off into x7 (pc180→pc186). Fuel 6. -/
theorem ext_child_load_len_off
    (v5 v6 v7 childLen childOff : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 6 (pc 180) (pc 186) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (MwChildLen ↦ₘ childLen) ** (MwChildOff ↦ₘ childOff) ** F)
      ((.x5 ↦ᵣ MwChildOff) ** (.x6 ↦ᵣ childLen) ** (.x7 ↦ᵣ childOff) **
       (MwChildLen ↦ₘ childLen) ** (MwChildOff ↦ₘ childOff) ** F) := by
  -- la x5 child_len
  have hla0 := la_materialize_within (cr := fullCode) .x5 v5 (pc 180) MwChildLen
    (by decide) la_ext_load_len_range
    (walkMem (pc 180) 180
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 180) MwChildLen))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_load_len_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 181)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 180) MwChildLen)) a = some i := by
        simpa [pc_succ 180] using hs
      exact walkMem (pc 181) 181
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 180) MwChildLen))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_load_len_lo]; rfl) a i hs')
  rw [pc_add8_ec 180] at hla0
  have hla0F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (MwChildLen ↦ₘ childLen) ** (MwChildOff ↦ₘ childOff) ** F)
    (by pcf; exact hF) hla0
  -- LD x6, 0(x5)
  have hld0 := ld_spec_gen_within .x6 .x5 MwChildLen v6 childLen
    (0 : BitVec 12) (pc 182) (by decide)
  rw [signExtend12_0c, show (MwChildLen + 0 : Word) = MwChildLen from by bv_omega,
      pc_succ 182] at hld0
  have hld0e := cpsTripleWithin_extend_code
    (walkMem (pc 182) 182 (.LD .x6 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld0
  -- LD focuses rs1+rd+mem; frame = x7 + both mem cells + F
  have hld0F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** (MwChildOff ↦ₘ childOff) ** F)
    (by pcf; exact hF) hld0e
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hla0F hld0F
  -- la x5 child_off (x5 currently MwChildLen)
  have hla1 := la_materialize_within (cr := fullCode) .x5 MwChildLen (pc 183) MwChildOff
    (by decide) la_ext_load_off_range
    (walkMem (pc 183) 183
      (.AUIPC .x5 (EvmAsm.Rv64.laHi (pc 183) MwChildOff))
      (by decide) (by unfold pc walkB; decide)
      (by rw [← la_ext_load_off_hi]; rfl))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 184)
          (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 183) MwChildOff)) a = some i := by
        simpa [pc_succ 183] using hs
      exact walkMem (pc 184) 184
        (.ADDI .x5 .x5 (EvmAsm.Rv64.laLo (pc 183) MwChildOff))
        (by decide) (by unfold pc walkB; decide)
        (by rw [← la_ext_load_off_lo]; rfl) a i hs')
  rw [pc_add8_ec 183] at hla1
  have hla1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ childLen) ** (.x7 ↦ᵣ v7) **
     (MwChildLen ↦ₘ childLen) ** (MwChildOff ↦ₘ childOff) ** F)
    (by pcf; exact hF) hla1
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c01 hla1F
  -- LD x7, 0(x5); focuses x5+x7+mem; frame keeps x6 + both cells + F
  have hld1 := ld_spec_gen_within .x7 .x5 MwChildOff v7 childOff
    (0 : BitVec 12) (pc 185) (by decide)
  rw [signExtend12_0c, show (MwChildOff + 0 : Word) = MwChildOff from by bv_omega,
      pc_succ 185] at hld1
  have hld1e := cpsTripleWithin_extend_code
    (walkMem (pc 185) 185 (.LD .x7 .x5 (0 : BitVec 12))
      (by decide) (by unfold pc walkB; decide) rfl) hld1
  have hld1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ childLen) ** (MwChildLen ↦ₘ childLen) ** F)
    (by pcf; exact hF) hld1e
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c012 hld1F
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- ADD x28 = node + off (child pointer). -/
theorem ext_child_ptr
    (nodeBase childOff v28 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (pc 186) (pc 187) fullCode
      ((.x23 ↦ᵣ nodeBase) ** (.x7 ↦ᵣ childOff) ** (.x28 ↦ᵣ v28) ** F)
      ((.x23 ↦ᵣ nodeBase) ** (.x7 ↦ᵣ childOff) **
       (.x28 ↦ᵣ (nodeBase + childOff)) ** F) := by
  have h := add_spec_gen_within .x28 .x23 .x7 nodeBase childOff v28 (pc 186) (by decide)
  have hc := cpsTripleWithin_extend_code
    (walkMem (pc 186) 186 (.ADD .x28 .x23 .x7)
      (by decide) (by unfold pc walkB; decide) rfl) h
  rw [pc_succ 186] at hc
  have hF' := cpsTripleWithin_frameR F hF hc
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) hF'

/-- LI 32; BEQ taken → hash hop entry pc192. -/
theorem ext_child_hash32
    (v29 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (pc 187) (pc 192) fullCode
      ((.x6 ↦ᵣ (32 : Word)) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word)) ** F)
      ((.x6 ↦ᵣ (32 : Word)) ** (.x29 ↦ᵣ (32 : Word)) **
       (.x0 ↦ᵣ (0 : Word)) ** F) := by
  have hli := li_spec_gen_within .x29 v29 (32 : Word) (pc 187) (by decide)
  have hlic := cpsTripleWithin_extend_code
    (walkMem (pc 187) 187 (.LI .x29 (32 : Word))
      (by decide) (by unfold pc walkB; decide) rfl) hli
  rw [pc_succ 187] at hlic
  have hliF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (32 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** F)
    (by pcf; exact hF) hlic
  let off : BitVec 13 := 16
  have hb := beq_spec_gen_within .x6 .x29 off (32 : Word) (32 : Word) (pc 188)
  rw [beq_ext_hash_off, show pc 188 + 4 = pc 189 from pc_succ 188] at hb
  have hbe := cpsBranchWithin_extend_code
    (walkMem (pc 188) 188 (.BEQ .x6 .x29 off)
      (by decide) (by unfold pc walkB; decide) rfl) hb
  have htk := cpsBranchWithin_takenStripPure2 hbe (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have htkF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** F) (by pcf; exact hF) htk
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hliF htkF
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c01

/-!
  Domain: inlined child (len ≠ 32) is BEQ-ntaken at pc188 → MV/MV/JAL kind.
  EXCLUDED BY GATE (inlined sub-32). Hash hop body from pc192 calls
  witness_lookup_by_hash — SEPARATE residual (h_wl).
-/

/-! After nth success: status ok, load len=32/off, child ptr, take hash arm → pc192.
    Fuel: 1+6+1+2 = 10. -/
set_option maxRecDepth 8000 in
theorem ext_after_nth_ok_to_hash32
    (v5 v6 v7 v28 v29 nodeBase childOff : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 10 (pc 179) (pc 192) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x23 ↦ᵣ nodeBase) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
       (MwChildLen ↦ₘ (32 : Word)) ** (MwChildOff ↦ₘ childOff) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ MwChildOff) ** (.x6 ↦ᵣ (32 : Word)) ** (.x7 ↦ᵣ childOff) **
       (.x23 ↦ᵣ nodeBase) ** (.x28 ↦ᵣ (nodeBase + childOff)) **
       (.x29 ↦ᵣ (32 : Word)) **
       (MwChildLen ↦ₘ (32 : Word)) ** (MwChildOff ↦ₘ childOff) ** F) := by
  have h1 := ext_child_nth_status_ok
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x23 ↦ᵣ nodeBase) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
     (MwChildLen ↦ₘ (32 : Word)) ** (MwChildOff ↦ₘ childOff) ** F)
    (by pcf; exact hF)
  have h2 := ext_child_load_len_off v5 v6 v7 (32 : Word) childOff
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x23 ↦ᵣ nodeBase) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** F)
    (by pcf; exact hF)
  have c12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h1 h2
  have h3 := ext_child_ptr nodeBase childOff v28
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwChildOff) ** (.x6 ↦ᵣ (32 : Word)) ** (.x29 ↦ᵣ v29) **
     (MwChildLen ↦ₘ (32 : Word)) ** (MwChildOff ↦ₘ childOff) ** F)
    (by pcf; exact hF)
  have c123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c12 h3
  have h4 := ext_child_hash32 v29
    ((.x10 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ MwChildOff) ** (.x7 ↦ᵣ childOff) **
     (.x23 ↦ᵣ nodeBase) ** (.x28 ↦ᵣ (nodeBase + childOff)) **
     (MwChildLen ↦ₘ (32 : Word)) ** (MwChildOff ↦ₘ childOff) ** F)
    (by pcf; exact hF)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    c123 h4
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => by xperm_chunked hq) c

/-- Pos advance + nth setup (pc170→pc178). Fuel 1+7 = 8. -/
theorem ext_match_to_nth_setup
    (v10 v11 v12 v13 v14 posW countW nodeBase nodeLenW : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (pc 170) (pc 178) fullCode
      ((.x22 ↦ᵣ posW) ** (.x6 ↦ᵣ countW) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
      ((.x22 ↦ᵣ (posW + countW)) ** (.x6 ↦ᵣ countW) **
       extChildNthSetup nodeBase nodeLenW F) := by
  have h1 := ext_pos_advance posW countW
    ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x23 ↦ᵣ nodeBase) ** (.x24 ↦ᵣ nodeLenW) ** F)
    (by pcf; exact hF)
  have h2 := ext_child_nth_setup_spec v10 v11 v12 v13 v14 nodeBase nodeLenW
    ((.x22 ↦ᵣ (posW + countW)) ** (.x6 ↦ᵣ countW) ** F)
    (by pcf; exact hF)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    h1 h2
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by
      simp only [extChildNthSetup] at hq ⊢
      xperm_chunked hq) c

end EvmAsm.Codegen.MptWalkSpec
