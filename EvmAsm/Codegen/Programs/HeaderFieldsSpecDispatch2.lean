import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Codegen.Programs.RlpWalkInitFlatSAsm
import EvmAsm.Codegen.Programs.RlpWalkNextFlatSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase
import EvmAsm.Codegen.Programs.AccountBalanceHelperSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Codegen.Programs.HeaderFieldsSpecDispatch

namespace EvmAsm.Codegen.HeaderFieldsSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells (local re-declaration of the `mset_memcpy` helper macro). -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

/-- Init marshalling [12]-[15]: `SD x10; SD x11; LD x10; LD x11` — seed `sp+32 :=
    cursor`, `sp+40 := endPtr` (the spill slots start owned/`memOwn`). -/
private theorem hesrMarshalInit (cursor endPtr newSp : Word) :
    cpsTripleWithin 4 (hesrBase + 48) (hesrBase + 64) hesrCode
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x2 ↦ᵣ newSp) **
       memOwn (newSp + 32) ** memOwn (newSp + 40))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x2 ↦ᵣ newSp) **
       ((newSp + 32) ↦ₘ cursor) ** ((newSp + 40) ↦ₘ endPtr)) := by
  -- [12] SD x2 x10 32 : (newSp+32) := cursor  (into owned slot)
  have h12 := sd_spec_gen_own_within .x2 .x10 newSp cursor (32 : BitVec 12) (hesrBase + 48)
  rw [show newSp + signExtend12 (32 : BitVec 12) = newSp + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide],
      show (hesrBase + 48 : Word) + 4 = hesrBase + 52 from by bv_omega] at h12
  have e12 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 48) Codegen.headerExtractStateRoot_prog 12
      (.SD .x2 .x10 (32 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h12
  have f12 := cpsTripleWithin_frameR ((.x11 ↦ᵣ endPtr) ** memOwn (newSp + 40)) (by pcFreeR) e12
  -- [13] SD x2 x11 40 : (newSp+40) := endPtr  (into owned slot)
  have h13 := sd_spec_gen_own_within .x2 .x11 newSp endPtr (40 : BitVec 12) (hesrBase + 52)
  rw [show newSp + signExtend12 (40 : BitVec 12) = newSp + 40 from by
        rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide],
      show (hesrBase + 52 : Word) + 4 = hesrBase + 56 from by bv_omega] at h13
  have e13 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 52) Codegen.headerExtractStateRoot_prog 13
      (.SD .x2 .x11 (40 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h13
  have f13 := cpsTripleWithin_frameR ((.x10 ↦ᵣ cursor) ** ((newSp + 32) ↦ₘ cursor)) (by pcFreeR) e13
  -- [14] LD x10 x2 32 : x10 := cursor
  have h14 := ld_spec_gen_within .x10 .x2 newSp cursor cursor (32 : BitVec 12) (hesrBase + 56) (by decide)
  rw [show newSp + signExtend12 (32 : BitVec 12) = newSp + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide],
      show (hesrBase + 56 : Word) + 4 = hesrBase + 60 from by bv_omega] at h14
  have e14 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 56) Codegen.headerExtractStateRoot_prog 14
      (.LD .x10 .x2 (32 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h14
  have f14 := cpsTripleWithin_frameR ((.x11 ↦ᵣ endPtr) ** ((newSp + 40) ↦ₘ endPtr)) (by pcFreeR) e14
  -- [15] LD x11 x2 40 : x11 := endPtr
  have h15 := ld_spec_gen_within .x11 .x2 newSp endPtr endPtr (40 : BitVec 12) (hesrBase + 60) (by decide)
  rw [show newSp + signExtend12 (40 : BitVec 12) = newSp + 40 from by
        rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide],
      show (hesrBase + 60 : Word) + 4 = hesrBase + 64 from by bv_omega] at h15
  have e15 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at hesrBase (hesrBase + 60) Codegen.headerExtractStateRoot_prog 15
      (.LD .x11 .x2 (40 : BitVec 12)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num)) h15
  have f15 := cpsTripleWithin_frameR ((.x10 ↦ᵣ cursor) ** ((newSp + 32) ↦ₘ cursor)) (by pcFreeR) e15
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f12 f13
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f14
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f15
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s3

set_option maxRecDepth 8000 in
private theorem hesrStage2
    (listBase endPtr outPtr newSp : Word) (offPrev listLen cursorOff : Nat)
    (oldRa v12 v5 v6 v7 v28 v29 v30 v31 v9 : Word)
    (saved : Saved) (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    {cr : CodeReq}
    (hcr_prog : ∀ a i, hesrCode a = some i → cr a = some i)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ headerBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLen cursorOff endPtr)
    (hprefixPrev : RlpListNthItemSAsm.StrictPrefix headerBytes listBase endPtr cursorOff 1 offPrev)
    (hoffPrev : offPrev ≤ listLen)
    (hbound : ∀ o next len, o ≤ listLen →
      rlpItemDecode headerBytes o (listBase + BitVec.ofNat 64 o) endPtr next len →
      (next - len - listBase).toNat + 32 ≤ headerBytes.length) :
    cpsTripleWithin
      (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204))))))))))
      (hesrBase + 84) (saved.ra &&& ~~~(1 : Word)) cr
      ((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ v12) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr)))
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
  have hFpc : (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
      hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr).pcFree :=
    pcFree_sepConj (pcFree_hesrWalkAmbient _ _ _ _ _ _)
      (pcFree_sepConj (pcFree_hesrSpill _ _ _) hFr)
  -- the walk call [+84 → +88]
  have hwalk := hesrNextStep (hesrBase + 84)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_state_root + 84))
    listBase endPtr offPrev listLen
    oldRa v12 v5 v6 v7 v28 v29 v30 v31 headerBytes
    (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
     hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr) hFpc
    h_src_align h_slack h_src_over h_src_valid hoffPrev
    (by simp only [wnBase, hesrBase]; decide)
    (by simp only [hesrBase]; decide)
    (by simp only [wnBase, hesrBase]
        exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by
      refine CodeReq.union_sub (CodeReq.singleton_mono (hcr_prog _ _ ?_)) hcr_wn
      exact CodeReq.ofProg_mem_at hesrBase (hesrBase + 84) Codegen.headerExtractStateRoot_prog 21
        (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next
          (Codegen.GuestAddrs.header_extract_state_root + 84))) (by bv_omega)
        (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) _ _
        (by simp [CodeReq.singleton]))
  have hwalk' := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      exact sepConj_mono_left
        (sepConj_mono_right (hesrNextOutcome_to_norm listBase endPtr headerBytes offPrev)) h hq) hwalk
  -- the BNE dispatch [+88 → ret]
  have hdisp : cpsTripleWithin
      (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204))))))))) (hesrBase + 88)
      (saved.ra &&& ~~~(1 : Word)) cr
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 84 + 4)) **
         bytesRegion listBase headerBytes) ** hesrNextNorm listBase endPtr headerBytes offPrev) **
        (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
         hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
    have ha_t : (hesrBase + 88 : Word) + signExtend13 (148 : BitVec 13) = hesrBase + 236 := by
      rw [show signExtend13 (148 : BitVec 13) = (148 : Word) from by decide]; bv_omega
    have ha_f : (hesrBase + 88 : Word) + 4 = hesrBase + 92 := by bv_omega
    have hbnemono : ∀ a i, CodeReq.singleton (hesrBase + 88) (.BNE .x11 .x0 (148 : BitVec 13)) a = some i
        → cr a = some i := by
      intro a i hs
      exact hcr_prog _ _ (CodeReq.ofProg_mem_at hesrBase (hesrBase + 88)
        Codegen.headerExtractStateRoot_prog 22 (.BNE .x11 .x0 (148 : BitVec 13)) (by bv_omega)
        (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) _ _ hs)
    -- FAIL arm: x11 = status ≠ 0 → taken → status1 (a0 = 1, Failure.walk).
    have hFAIL : cpsTripleWithin
        (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204))))))))) (hesrBase + 88)
        (saved.ra &&& ~~~(1 : Word)) cr
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 84 + 4)) **
           bytesRegion listBase headerBytes) **
          (fun h => ∃ status : Word,
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x11 ↦ᵣ status) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜status ≠ (0 : Word) ∧
                RlpListNthItemSAsm.WalkFailure headerBytes offPrev
                  (listBase + BitVec.ofNat 64 offPrev) endPtr⌝) h)) **
          (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
           hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ status : Word,
          (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 84 + 4)) **
             bytesRegion listBase headerBytes) **
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x11 ↦ᵣ status) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜status ≠ (0 : Word) ∧
               RlpListNthItemSAsm.WalkFailure headerBytes offPrev
                 (listBase + BitVec.ofNat 64 offPrev) endPtr⌝)) **
            (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
             hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hst⟩ := hrf
          obtain ⟨status, hstatus⟩ := hst
          exact ⟨status, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hstatus⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun status => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜status ≠ (0 : Word) ∧
              RlpListNthItemSAsm.WalkFailure headerBytes offPrev
                (listBase + BitVec.ofNat 64 offPrev) endPtr⌝ **
          (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 84 + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x12 ↦ᵣ (0 : Word)) **
             (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
              hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hP => ?_)
      have hbne := bne_spec_gen_within .x11 .x0 (148 : BitVec 13) status (0 : Word) (hesrBase + 88)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemono hbne
      have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        exact hP.1 ((sepConj_pure_right _).1 hQ).2)
      have htkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 84 + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x12 ↦ᵣ (0 : Word)) **
         (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (by repeat' first
          | exact pcFree_hesrWalkAmbient _ _ _ _ _ _ | exact pcFree_hesrSpill _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) htk
      have hs1 := cpsTripleWithin_extend_code hcr_prog
        (hesrStatus1Bundled newSp listBase v9 outPtr (listBase + BitVec.ofNat 64 offPrev)
          (hesrBase + 84 + 4) saved
          ((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** regOwn .x5 **
           regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           bytesRegion listBase headerBytes ** hesrAmbConst outPtr outBytes **
           hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr)
          (by repeat' first
            | exact pcFree_hesrAmbConst _ _ | exact pcFree_hesrSpill _ _ _ | exact hFr
            | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
            | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj))
      have s := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by unfold hesrWalkAmbient at hp; xperm_chunked hp) htkF hs1
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => hp)
          (fun h hq => by
            refine ⟨(1 : Word), outBytes, (0 : Word), (0 : Word), ?_⟩
            refine (sepConj_pure_right h).2 ⟨?_, Or.inr (Or.inr ⟨rfl,
              RlpListNthItemSAsm.Failure.walk cursorOff 1 offPrev endPtr hpayload (by omega)
                hprefixPrev hP.2⟩)⟩
            unfold hesrAmbConst hesrSpill at hq
            have hq2 : ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ saved.ra) ** hesrAmbRegsRestored newSp saved) **
               (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x12 ↦ᵣ (0 : Word)) ** regOwn .x28 **
                regOwn .x29 ** hesrScratchConst ** (.x0 ↦ᵣ (0 : Word)) **
                bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
                ((.x11 ↦ᵣ status) ** regOwn .x30 ** regOwn .x31 **
                 ((newSp + 32) ↦ₘ (listBase + BitVec.ofNat 64 offPrev)) **
                 ((newSp + 40) ↦ₘ endPtr) ** Fr)))) h := by
              xperm_chunked hq
            exact sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (regIs_implies_regOwn .x12)
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono (regIs_implies_regOwn .x11)
                        (sepConj_mono_right (sepConj_mono_right
                          (sepConj_mono memIs_implies_memOwn (fun _ hh => hh)))))))))))))))
              h hq2) s)
    -- OK arm: x11 = 0 → ntaken → marshal + recurse into hesrStage3.
    have hOK : cpsTripleWithin
        (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204))))))))) (hesrBase + 88)
        (saved.ra &&& ~~~(1 : Word)) cr
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 84 + 4)) **
           bytesRegion listBase headerBytes) **
          rlpWalkNextOk (listBase + BitVec.ofNat 64 offPrev) endPtr headerBytes offPrev) **
          (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
           hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ next len : Word,
          (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 84 + 4)) **
             bytesRegion listBase headerBytes) **
            ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
             ⌜rlpItemDecode headerBytes offPrev (listBase + BitVec.ofNat 64 offPrev) endPtr next len⌝)) **
            (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
             hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hwlk⟩ := hrf
          obtain ⟨next, len, hw⟩ := hwlk
          exact ⟨next, len, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hw⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
      refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜rlpItemDecode headerBytes offPrev (listBase + BitVec.ofNat 64 offPrev) endPtr next len⌝ **
          (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 84 + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
             (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
              hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hdecode => ?_)
      -- advance the walked prefix from 1 to 2 items.
      have hend : endPtr = listBase + BitVec.ofNat 64 listLen := hpayload.end_eq
      have hover' : listBase.toNat + listLen + 9 < 2 ^ 64 := by omega
      obtain ⟨hnexteq, hlt, hle, hprefixK⟩ :=
        RlpListNthItemSAsm.StrictPrefix.step_bounds (endOff := listLen)
          (hend ▸ hprefixPrev) (hend ▸ hdecode) hoffPrev hover'
      set offK : Nat := (next - listBase).toNat with hoffKdef
      have hbne := bne_spec_gen_within .x11 .x0 (148 : BitVec 13) (0 : Word) (0 : Word) (hesrBase + 88)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemono hbne
      have hntk := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        exact ((sepConj_pure_right _).1 hQ).2 rfl)
      have hntkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 84 + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
         (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (by repeat' first
          | exact pcFree_hesrWalkAmbient _ _ _ _ _ _ | exact pcFree_hesrSpill _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) hntk
      -- marshalNext [+92 → +104], ambient/spill folded.
      have hmb := cpsTripleWithin_extend_code hcr_prog
        (hesrMarshalNextBundled (hesrBase + 92) (listBase + BitVec.ofNat 64 offK) endPtr newSp
          listBase v9 outPtr (listBase + BitVec.ofNat 64 offPrev) saved outBytes
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ (hesrBase + 84 + 4)) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** bytesRegion listBase headerBytes ** Fr)
          (by repeat' first
            | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
            | exact pcFree_regOwn | apply pcFree_sepConj)
          (fun a i hs => CodeReq.ofProg_mem_at hesrBase (hesrBase + 92)
            Codegen.headerExtractStateRoot_prog 23 (.SD .x2 .x10 (32 : BitVec 12)) (by bv_omega)
            (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) a i hs)
          (fun a i hs => CodeReq.ofProg_mem_at hesrBase (hesrBase + 96)
            Codegen.headerExtractStateRoot_prog 24 (.LD .x10 .x2 (32 : BitVec 12)) (by bv_omega)
            (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) a i hs)
          (fun a i hs => CodeReq.ofProg_mem_at hesrBase (hesrBase + 100)
            Codegen.headerExtractStateRoot_prog 25 (.LD .x11 .x2 (40 : BitVec 12)) (by bv_omega)
            (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) a i hs))
      -- recurse into hesrStage3 at +104; the fresh spill is stage 3's precond spill.
      have hstage3 : ∀ w5 w6 w7 w28 w29 w30 w31,
          cpsTripleWithin (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))
            (hesrBase + 104) (saved.ra &&& ~~~(1 : Word)) cr
            (((.x1 ↦ᵣ (hesrBase + 84 + 4)) **
              ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
               (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
               (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
                hesrSpill newSp (listBase + BitVec.ofNat 64 offK) endPtr ** Fr))) **
             (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) **
             (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
            (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
              (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
               memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) :=
        fun w5 w6 w7 w28 w29 w30 w31 =>
          cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
            (hesrStage3 listBase endPtr outPtr newSp offK listLen cursorOff
              (hesrBase + 84 + 4) len w5 w6 w7 w28 w29 w30 w31 v9 saved headerBytes outBytes
              Fr hFr hcr_prog hcr_wn h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound
              h_src_valid h_dst_valid hpayload (hend ▸ hprefixK) hle hbound)
      have hstage3' := cpsTripleWithin_of_forall_regIs_to_regOwn7 hstage3
      have hrec := cpsTripleWithin_seq_perm_same_cr
        (fun h hq => by xperm_chunked hq) hmb hstage3'
      exact cpsTripleWithin_seq_perm_same_cr
        (fun h hq => by rw [hnexteq] at hq; xperm_chunked hq) hntkF hrec
    refine cpsTripleWithin_weaken
      (fun h hp => by
        obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
        obtain ⟨ha, hb, hd', hu', hreg, hnorm⟩ := hrf
        unfold hesrNextNorm at hnorm
        rcases hnorm with hok | hfail
        · exact Or.inl ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hok⟩, hab⟩
        · exact Or.inr ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hfail⟩, hab⟩)
      (fun _ h => h) (cpsTripleWithin_or_pre hOK hFAIL)
  rw [show (hesrBase + 84 : Word) + 4 = hesrBase + 88 from by bv_omega] at hwalk'
  exact cpsTripleWithin_seq_same_cr hwalk' hdisp

set_option maxRecDepth 8000 in
private theorem hesrStage1
    (listBase endPtr outPtr newSp : Word) (offPrev listLen cursorOff : Nat)
    (oldRa v12 v5 v6 v7 v28 v29 v30 v31 v9 : Word)
    (saved : Saved) (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree)
    {cr : CodeReq}
    (hcr_prog : ∀ a i, hesrCode a = some i → cr a = some i)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ headerBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLen cursorOff endPtr)
    (hprefixPrev : RlpListNthItemSAsm.StrictPrefix headerBytes listBase endPtr cursorOff 0 offPrev)
    (hoffPrev : offPrev ≤ listLen)
    (hbound : ∀ o next len, o ≤ listLen →
      rlpItemDecode headerBytes o (listBase + BitVec.ofNat 64 o) endPtr next len →
      (next - len - listBase).toNat + 32 ≤ headerBytes.length) :
    cpsTripleWithin
      (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))))))))
      (hesrBase + 64) (saved.ra &&& ~~~(1 : Word)) cr
      ((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ v12) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr)))
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
  have hFpc : (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
      hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr).pcFree :=
    pcFree_sepConj (pcFree_hesrWalkAmbient _ _ _ _ _ _)
      (pcFree_sepConj (pcFree_hesrSpill _ _ _) hFr)
  -- the walk call [+64 → +68]
  have hwalk := hesrNextStep (hesrBase + 64)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_state_root + 64))
    listBase endPtr offPrev listLen
    oldRa v12 v5 v6 v7 v28 v29 v30 v31 headerBytes
    (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
     hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr) hFpc
    h_src_align h_slack h_src_over h_src_valid hoffPrev
    (by simp only [wnBase, hesrBase]; decide)
    (by simp only [hesrBase]; decide)
    (by simp only [wnBase, hesrBase]
        exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by
      refine CodeReq.union_sub (CodeReq.singleton_mono (hcr_prog _ _ ?_)) hcr_wn
      exact CodeReq.ofProg_mem_at hesrBase (hesrBase + 64) Codegen.headerExtractStateRoot_prog 16
        (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next
          (Codegen.GuestAddrs.header_extract_state_root + 64))) (by bv_omega)
        (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) _ _
        (by simp [CodeReq.singleton]))
  have hwalk' := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      exact sepConj_mono_left
        (sepConj_mono_right (hesrNextOutcome_to_norm listBase endPtr headerBytes offPrev)) h hq) hwalk
  -- the BNE dispatch [+68 → ret]
  have hdisp : cpsTripleWithin
      (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))))))) (hesrBase + 68)
      (saved.ra &&& ~~~(1 : Word)) cr
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 64 + 4)) **
         bytesRegion listBase headerBytes) ** hesrNextNorm listBase endPtr headerBytes offPrev) **
        (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
         hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
    have ha_t : (hesrBase + 68 : Word) + signExtend13 (168 : BitVec 13) = hesrBase + 236 := by
      rw [show signExtend13 (168 : BitVec 13) = (168 : Word) from by decide]; bv_omega
    have ha_f : (hesrBase + 68 : Word) + 4 = hesrBase + 72 := by bv_omega
    have hbnemono : ∀ a i, CodeReq.singleton (hesrBase + 68) (.BNE .x11 .x0 (168 : BitVec 13)) a = some i
        → cr a = some i := by
      intro a i hs
      exact hcr_prog _ _ (CodeReq.ofProg_mem_at hesrBase (hesrBase + 68)
        Codegen.headerExtractStateRoot_prog 17 (.BNE .x11 .x0 (168 : BitVec 13)) (by bv_omega)
        (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) _ _ hs)
    -- FAIL arm: x11 = status ≠ 0 → taken → status1 (a0 = 1, Failure.walk).
    have hFAIL : cpsTripleWithin
        (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))))))) (hesrBase + 68)
        (saved.ra &&& ~~~(1 : Word)) cr
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 64 + 4)) **
           bytesRegion listBase headerBytes) **
          (fun h => ∃ status : Word,
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x11 ↦ᵣ status) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜status ≠ (0 : Word) ∧
                RlpListNthItemSAsm.WalkFailure headerBytes offPrev
                  (listBase + BitVec.ofNat 64 offPrev) endPtr⌝) h)) **
          (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
           hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ status : Word,
          (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 64 + 4)) **
             bytesRegion listBase headerBytes) **
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x11 ↦ᵣ status) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜status ≠ (0 : Word) ∧
               RlpListNthItemSAsm.WalkFailure headerBytes offPrev
                 (listBase + BitVec.ofNat 64 offPrev) endPtr⌝)) **
            (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
             hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hst⟩ := hrf
          obtain ⟨status, hstatus⟩ := hst
          exact ⟨status, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hstatus⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun status => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜status ≠ (0 : Word) ∧
              RlpListNthItemSAsm.WalkFailure headerBytes offPrev
                (listBase + BitVec.ofNat 64 offPrev) endPtr⌝ **
          (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 64 + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x12 ↦ᵣ (0 : Word)) **
             (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
              hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hP => ?_)
      have hbne := bne_spec_gen_within .x11 .x0 (168 : BitVec 13) status (0 : Word) (hesrBase + 68)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemono hbne
      have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        exact hP.1 ((sepConj_pure_right _).1 hQ).2)
      have htkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 64 + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x12 ↦ᵣ (0 : Word)) **
         (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (by repeat' first
          | exact pcFree_hesrWalkAmbient _ _ _ _ _ _ | exact pcFree_hesrSpill _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) htk
      have hs1 := cpsTripleWithin_extend_code hcr_prog
        (hesrStatus1Bundled newSp listBase v9 outPtr (listBase + BitVec.ofNat 64 offPrev)
          (hesrBase + 64 + 4) saved
          ((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** regOwn .x5 **
           regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           bytesRegion listBase headerBytes ** hesrAmbConst outPtr outBytes **
           hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr)
          (by repeat' first
            | exact pcFree_hesrAmbConst _ _ | exact pcFree_hesrSpill _ _ _ | exact hFr
            | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
            | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj))
      have s := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by unfold hesrWalkAmbient at hp; xperm_chunked hp) htkF hs1
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => hp)
          (fun h hq => by
            refine ⟨(1 : Word), outBytes, (0 : Word), (0 : Word), ?_⟩
            refine (sepConj_pure_right h).2 ⟨?_, Or.inr (Or.inr ⟨rfl,
              RlpListNthItemSAsm.Failure.walk cursorOff 0 offPrev endPtr hpayload (by omega)
                hprefixPrev hP.2⟩)⟩
            unfold hesrAmbConst hesrSpill at hq
            have hq2 : ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ saved.ra) ** hesrAmbRegsRestored newSp saved) **
               (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x12 ↦ᵣ (0 : Word)) ** regOwn .x28 **
                regOwn .x29 ** hesrScratchConst ** (.x0 ↦ᵣ (0 : Word)) **
                bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
                ((.x11 ↦ᵣ status) ** regOwn .x30 ** regOwn .x31 **
                 ((newSp + 32) ↦ₘ (listBase + BitVec.ofNat 64 offPrev)) **
                 ((newSp + 40) ↦ₘ endPtr) ** Fr)))) h := by
              xperm_chunked hq
            exact sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (regIs_implies_regOwn .x12)
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono (regIs_implies_regOwn .x11)
                        (sepConj_mono_right (sepConj_mono_right
                          (sepConj_mono memIs_implies_memOwn (fun _ hh => hh)))))))))))))))
              h hq2) s)
    -- OK arm: x11 = 0 → ntaken → marshal + recurse into hesrStage2.
    have hOK : cpsTripleWithin
        (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))))))) (hesrBase + 68)
        (saved.ra &&& ~~~(1 : Word)) cr
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 64 + 4)) **
           bytesRegion listBase headerBytes) **
          rlpWalkNextOk (listBase + BitVec.ofNat 64 offPrev) endPtr headerBytes offPrev) **
          (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
           hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ next len : Word,
          (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 64 + 4)) **
             bytesRegion listBase headerBytes) **
            ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
             ⌜rlpItemDecode headerBytes offPrev (listBase + BitVec.ofNat 64 offPrev) endPtr next len⌝)) **
            (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
             hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hwlk⟩ := hrf
          obtain ⟨next, len, hw⟩ := hwlk
          exact ⟨next, len, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hw⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
      refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜rlpItemDecode headerBytes offPrev (listBase + BitVec.ofNat 64 offPrev) endPtr next len⌝ **
          (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 64 + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
             (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
              hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hdecode => ?_)
      -- advance the walked prefix from 0 to 1 item.
      have hend : endPtr = listBase + BitVec.ofNat 64 listLen := hpayload.end_eq
      have hover' : listBase.toNat + listLen + 9 < 2 ^ 64 := by omega
      obtain ⟨hnexteq, hlt, hle, hprefixK⟩ :=
        RlpListNthItemSAsm.StrictPrefix.step_bounds (endOff := listLen)
          (hend ▸ hprefixPrev) (hend ▸ hdecode) hoffPrev hover'
      set offK : Nat := (next - listBase).toNat with hoffKdef
      have hbne := bne_spec_gen_within .x11 .x0 (168 : BitVec 13) (0 : Word) (0 : Word) (hesrBase + 68)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemono hbne
      have hntk := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        exact ((sepConj_pure_right _).1 hQ).2 rfl)
      have hntkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 64 + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
         (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (by repeat' first
          | exact pcFree_hesrWalkAmbient _ _ _ _ _ _ | exact pcFree_hesrSpill _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) hntk
      -- marshalNext [+72 → +84], ambient/spill folded.
      have hmb := cpsTripleWithin_extend_code hcr_prog
        (hesrMarshalNextBundled (hesrBase + 72) (listBase + BitVec.ofNat 64 offK) endPtr newSp
          listBase v9 outPtr (listBase + BitVec.ofNat 64 offPrev) saved outBytes
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ (hesrBase + 64 + 4)) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** bytesRegion listBase headerBytes ** Fr)
          (by repeat' first
            | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
            | exact pcFree_regOwn | apply pcFree_sepConj)
          (fun a i hs => CodeReq.ofProg_mem_at hesrBase (hesrBase + 72)
            Codegen.headerExtractStateRoot_prog 18 (.SD .x2 .x10 (32 : BitVec 12)) (by bv_omega)
            (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) a i hs)
          (fun a i hs => CodeReq.ofProg_mem_at hesrBase (hesrBase + 76)
            Codegen.headerExtractStateRoot_prog 19 (.LD .x10 .x2 (32 : BitVec 12)) (by bv_omega)
            (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) a i hs)
          (fun a i hs => CodeReq.ofProg_mem_at hesrBase (hesrBase + 80)
            Codegen.headerExtractStateRoot_prog 20 (.LD .x11 .x2 (40 : BitVec 12)) (by bv_omega)
            (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) a i hs))
      -- recurse into hesrStage2 at +84; the fresh spill is stage 2's precond spill.
      have hstage2 : ∀ w5 w6 w7 w28 w29 w30 w31,
          cpsTripleWithin
            (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204))))))))))
            (hesrBase + 84) (saved.ra &&& ~~~(1 : Word)) cr
            (((.x1 ↦ᵣ (hesrBase + 64 + 4)) **
              ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
               (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
               (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
                hesrSpill newSp (listBase + BitVec.ofNat 64 offK) endPtr ** Fr))) **
             (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) **
             (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
            (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
              (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
               memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) :=
        fun w5 w6 w7 w28 w29 w30 w31 =>
          cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
            (hesrStage2 listBase endPtr outPtr newSp offK listLen cursorOff
              (hesrBase + 64 + 4) len w5 w6 w7 w28 w29 w30 w31 v9 saved headerBytes outBytes
              Fr hFr hcr_prog hcr_wn h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound
              h_src_valid h_dst_valid hpayload (hend ▸ hprefixK) hle hbound)
      have hstage2' := cpsTripleWithin_of_forall_regIs_to_regOwn7 hstage2
      have hrec := cpsTripleWithin_seq_perm_same_cr
        (fun h hq => by xperm_chunked hq) hmb hstage2'
      exact cpsTripleWithin_seq_perm_same_cr
        (fun h hq => by rw [hnexteq] at hq; xperm_chunked hq) hntkF hrec
    refine cpsTripleWithin_weaken
      (fun h hp => by
        obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
        obtain ⟨ha, hb, hd', hu', hreg, hnorm⟩ := hrf
        unfold hesrNextNorm at hnorm
        rcases hnorm with hok | hfail
        · exact Or.inl ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hok⟩, hab⟩
        · exact Or.inr ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hfail⟩, hab⟩)
      (fun _ h => h) (cpsTripleWithin_or_pre hOK hFAIL)
  rw [show (hesrBase + 64 : Word) + 4 = hesrBase + 68 from by bv_omega] at hwalk'
  exact cpsTripleWithin_seq_same_cr hwalk' hdisp

/-! ## The init-call dispatch and the whole-program caller contract

    The init phase in front of `hesrStage1`: the `rlp_walk_init` call at [10]
    (`+40 → +44`), the `BNE x12, x0, 192`[11] init-status dispatch (`+44`;
    failure → status-1 return at `+236`, success → marshal + `hesrStage1`), and
    the final whole-program `header_extract_state_root` caller `Fn.Spec`. -/

/-- Weaken the residual frame of `hesrRetPost` monotonically. -/
theorem hesrRetPost_frame_mono {newSp listBase outPtr : Word} {saved : Saved}
    {headerBytes outBytes : List (BitVec 8)} {listLen index : Nat}
    {Fr Fr' : Assertion} (himp : ∀ h, Fr h → Fr' h) :
    ∀ h, hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen index Fr h →
      hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen index Fr' h := by
  intro h hq
  unfold hesrRetPost at hq ⊢
  obtain ⟨a0v, finalOut, fo, len, hq'⟩ := hq
  exact ⟨a0v, finalOut, fo, len,
    sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right himp))))))))))) h hq'⟩

/-- Bundled-entry wrapper for the init marshalling [12]-[15] (`+48 → +64`): from
    the init-phase ambient (`hesrAmbient`, whose two spill slots are still
    `memOwn`) plus the two folded global scratch cells, seed the spill slots and
    re-fold to the walk-phase `hesrWalkAmbient` + `hesrSpill` shape `hesrStage1`
    consumes. -/
private theorem hesrMarshalInitBundled
    (cursor endPtr newSp listBase v9 outPtr : Word)
    (saved : Saved) (outBytes : List (BitVec 8)) (Fr : Assertion) (hFr : Fr.pcFree) :
    cpsTripleWithin 4 (hesrBase + 48) (hesrBase + 64) hesrCode
      (((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) **
        (hesrAmbient newSp outPtr listBase v9 saved outBytes ** hesrScratchConst ** Fr))
      (((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr)) **
        (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
         hesrSpill newSp cursor endPtr ** Fr)) := by
  have hm := hesrMarshalInit cursor endPtr newSp
  have hmF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ outPtr) ** savedFrame newSp saved **
     bytesRegion outPtr outBytes ** hesrScratchConst ** Fr)
    (by repeat' first
      | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_hesrScratchConst
      | unfold savedFrame | exact pcFree_regIs | exact pcFree_memIs | exact pcFree_memOwn
      | apply pcFree_sepConj) hm
  refine cpsTripleWithin_weaken
    (fun h hp => by unfold hesrAmbient at hp; xperm_chunked hp)
    (fun h hq => by
      unfold hesrWalkAmbient hesrAmbRegs hesrAmbConst hesrSpill; xperm_chunked hq) hmF

set_option maxRecDepth 8000 in
theorem hesrInitDispatch
    (listBase outPtr newSp oldRa v5 v6 v7 v28 v29 v30 v31 : Word)
    (saved : Saved) (headerBytes outBytes : List (BitVec 8)) (listLenN : Nat)
    {cr : CodeReq}
    (hcr_prog : ∀ a i, hesrCode a = some i → cr a = some i)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → cr a = some i)
    (hcr_wi : ∀ a i,
      (CodeReq.singleton (hesrBase + 40) (.JAL .x1 hesrInitOffset)).union
        (rlp_walk_init_code wiBase) a = some i → cr a = some i)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_dst_align : outPtr.toNat % 8 = 0)
    (h_slack : listLenN + 9 ≤ headerBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_dst_over : outPtr.toNat + outBytes.length < 2 ^ 64)
    (h_dst_bound : 32 ≤ outBytes.length)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)
    (hbound : ∀ o next len, o ≤ listLenN →
      rlpItemDecode headerBytes o (listBase + BitVec.ofNat 64 o)
        (listBase + BitVec.ofNat 64 listLenN) next len →
      (next - len - listBase).toNat + 32 ≤ headerBytes.length) :
    cpsTripleWithin
      (1 + 81 + (1 + (4 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 +
        (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204))))))))))))))))
      (hesrBase + 40) (saved.ra &&& ~~~(1 : Word)) cr
      (((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 listLenN) **
         (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes)) **
        (memOwn hesrOffAddr ** memOwn hesrLenAddr))
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLenN 3
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
  -- init call [+40 → +44]
  have hinit := hesrInitStep listBase outPtr newSp oldRa v5 v6 v7 v28 v29 v30 v31 saved
    headerBytes outBytes listLenN h_src_align h_slack h_src_over h_src_valid hcr_wi
  have hinitF := cpsTripleWithin_frameR (memOwn hesrOffAddr ** memOwn hesrLenAddr)
    (pcFree_sepConj pcFree_memOwn pcFree_memOwn) hinit
  have hinit' := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      exact sepConj_mono_left (sepConj_mono_left (sepConj_mono_right
        (RlpListNthItemSAsm.initOutcome_to_normalized listBase headerBytes listLenN 3 (by omega)
          h_slack h_src_over))) h hq)
    hinitF
  rw [show (hesrBase + 40 : Word) + 4 = hesrBase + 44 from by bv_omega] at hinit'
  -- BNE x12, x0, 192 at [11] (+44): taken → +236, not-taken → +48.
  have ha_t : (hesrBase + 44 : Word) + signExtend13 (192 : BitVec 13) = hesrBase + 236 := by
    rw [show signExtend13 (192 : BitVec 13) = (192 : Word) from by decide]; bv_omega
  have ha_f : (hesrBase + 44 : Word) + 4 = hesrBase + 48 := by bv_omega
  have hbnemono : ∀ a i, CodeReq.singleton (hesrBase + 44) (.BNE .x12 .x0 (192 : BitVec 13)) a = some i
      → cr a = some i := by
    intro a i hs
    exact hcr_prog _ _ (CodeReq.ofProg_mem_at hesrBase (hesrBase + 44)
      Codegen.headerExtractStateRoot_prog 11 (.BNE .x12 .x0 (192 : BitVec 13)) (by bv_omega)
      (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) _ _ hs)
  have hdisp : cpsTripleWithin
      (1 + (4 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 +
        (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))))))))))
      (hesrBase + 44) (saved.ra &&& ~~~(1 : Word)) cr
      (((hesrInitCommon listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
        RlpListNthItemSAsm.initNormalized listBase headerBytes listLenN 3) **
        (hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
         hesrScratchConst))
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLenN 3
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
    -- FAIL arm: x12 = status ≠ 0 → taken → status1 (a0 = 1, Failure.init carried).
    have hFAIL : cpsTripleWithin
        (1 + (4 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 +
          (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))))))))))
        (hesrBase + 44) (saved.ra &&& ~~~(1 : Word)) cr
        (((hesrInitCommon listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
          (fun h => ∃ status cursor endPtr,
            ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
             ⌜status ≠ (0 : Word) ∧
               RlpListNthItemSAsm.Failure headerBytes listBase listLenN 3⌝) h)) **
          (hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
           hesrScratchConst))
        (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLenN 3
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ status cursor endPtr,
          (((hesrInitCommon listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
            ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) **
             ⌜status ≠ (0 : Word) ∧
               RlpListNthItemSAsm.Failure headerBytes listBase listLenN 3⌝)) **
            (hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
             hesrScratchConst)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hst⟩ := hrf
          obtain ⟨status, cursor, endPtr, hstatus⟩ := hst
          exact ⟨status, cursor, endPtr, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hstatus⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun status => ?_)
      refine cpsTripleWithin_exists_pre_gen (fun cursor => ?_)
      refine cpsTripleWithin_exists_pre_gen (fun endPtr => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜status ≠ (0 : Word) ∧
              RlpListNthItemSAsm.Failure headerBytes listBase listLenN 3⌝ **
          (((.x12 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
            (hesrInitCommon listBase headerBytes ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
             (hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
              hesrScratchConst))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hP => ?_)
      have hbne := bne_spec_gen_within .x12 .x0 (192 : BitVec 13) status (0 : Word) (hesrBase + 44)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemono hbne
      have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        exact hP.1 ((sepConj_pure_right _).1 hQ).2)
      have htkF := cpsTripleWithin_frameR
        (hesrInitCommon listBase headerBytes ** (.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) **
         (hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrScratchConst))
        (by unfold hesrInitCommon
            repeat' first
              | exact pcFree_hesrScratchConst | exact pcFree_hesrAmbient _ _ _ _ _ _
              | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
              | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj) htk
      have hs1 := cpsTripleWithin_extend_code hcr_prog
        (hesrStatus1Bundled newSp listBase (BitVec.ofNat 64 listLenN) outPtr cursor
          (hesrBase + 40 + 4) saved
          ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 **
           regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           bytesRegion listBase headerBytes ** memOwn (newSp + 32) ** memOwn (newSp + 40) **
           bytesRegion outPtr outBytes ** hesrScratchConst)
          (by repeat' first
            | exact pcFree_hesrScratchConst | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
            | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj))
      have s := cpsTripleWithin_seq_perm_same_cr
        (fun h hq => by
          unfold hesrAmbient hesrInitCommon at hq
          unfold hesrAmbRegs
          xperm_chunked hq) htkF hs1
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => hp)
          (fun h hq => by
            refine ⟨(1 : Word), outBytes, (0 : Word), (0 : Word), ?_⟩
            refine (sepConj_pure_right h).2 ⟨?_, Or.inr (Or.inr ⟨rfl, hP.2⟩)⟩
            have hq2 : (((( .x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ saved.ra) **
                hesrAmbRegsRestored newSp saved) **
               (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x12 ↦ᵣ status) ** regOwn .x28 **
                regOwn .x29 ** hesrScratchConst ** (.x0 ↦ᵣ (0 : Word)) **
                bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
                ((.x11 ↦ᵣ endPtr) ** regOwn .x30 ** regOwn .x31 **
                 memOwn (newSp + 32) ** memOwn (newSp + 40))))) h := by
              xperm_chunked hq
            exact sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (regIs_implies_regOwn .x12)
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono (regIs_implies_regOwn .x11) (fun _ hh => hh))))))))))))
              h hq2) s)
    -- OK arm: x12 = 0 → not taken → marshalInit + recurse into hesrStage1.
    have hOK : cpsTripleWithin
        (1 + (4 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 +
          (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))))))))))
        (hesrBase + 44) (saved.ra &&& ~~~(1 : Word)) cr
        (((hesrInitCommon listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
          (fun h => ∃ cursorOff endPtr,
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ endPtr) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff
               endPtr⌝) h)) **
          (hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
           hesrScratchConst))
        (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLenN 3
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** memOwn (newSp + 40))) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ cursorOff endPtr,
          (((hesrInitCommon listBase headerBytes ** (.x0 ↦ᵣ (0 : Word))) **
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ endPtr) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff
               endPtr⌝)) **
            (hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
             hesrScratchConst)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hok⟩ := hrf
          obtain ⟨cursorOff, endPtr, hw⟩ := hok
          exact ⟨cursorOff, endPtr, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hw⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun cursorOff => ?_)
      refine cpsTripleWithin_exists_pre_gen (fun endPtr => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLenN cursorOff
              endPtr⌝ **
          (((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
            (hesrInitCommon listBase headerBytes **
             (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) ** (.x11 ↦ᵣ endPtr) **
             (hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
              hesrScratchConst))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hpayload => ?_)
      have hend : endPtr = listBase + BitVec.ofNat 64 listLenN := hpayload.end_eq
      subst hend
      have hbne := bne_spec_gen_within .x12 .x0 (192 : BitVec 13) (0 : Word) (0 : Word) (hesrBase + 44)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemono hbne
      have hntk := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        exact ((sepConj_pure_right _).1 hQ).2 rfl)
      have hntkF := cpsTripleWithin_frameR
        (hesrInitCommon listBase headerBytes **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
         (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) **
         (hesrAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
          hesrScratchConst))
        (by unfold hesrInitCommon
            repeat' first
              | exact pcFree_hesrScratchConst | exact pcFree_hesrAmbient _ _ _ _ _ _
              | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
              | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj) hntk
      have hmi := cpsTripleWithin_extend_code hcr_prog
        (hesrMarshalInitBundled (listBase + BitVec.ofNat 64 cursorOff)
          (listBase + BitVec.ofNat 64 listLenN) newSp listBase (BitVec.ofNat 64 listLenN) outPtr
          saved outBytes
          ((.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** hesrInitCommon listBase headerBytes)
          (by unfold hesrInitCommon
              repeat' first
                | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
                | apply pcFree_sepConj))
      have hstage1 : ∀ w5 w6 w7 w28 w29 w30 w31,
          cpsTripleWithin
            (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 + (1 + (3 + (1 + 87 +
              (1 + (9 + 4 + (1 + 204))))))))))))) (hesrBase + 64) (saved.ra &&& ~~~(1 : Word)) cr
            (((.x1 ↦ᵣ (hesrBase + 40 + 4)) **
              ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 cursorOff)) **
               (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 listLenN)) ** (.x12 ↦ᵣ (0 : Word)) **
               (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
               (hesrWalkAmbient newSp outPtr listBase (BitVec.ofNat 64 listLenN) saved outBytes **
                hesrSpill newSp (listBase + BitVec.ofNat 64 cursorOff)
                  (listBase + BitVec.ofNat 64 listLenN)))) **
             (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) **
             (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
            (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLenN 3
              (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
               memOwn (newSp + 32) **
               ((newSp + 40) ↦ₘ (listBase + BitVec.ofNat 64 listLenN)) ** empAssertion)) :=
        fun w5 w6 w7 w28 w29 w30 w31 =>
          cpsTripleWithin_weaken
            (fun h hp => by simp only [sepConj_emp_right']; xperm_chunked hp) (fun _ h => h)
            (hesrStage1 listBase (listBase + BitVec.ofNat 64 listLenN) outPtr newSp cursorOff
              listLenN cursorOff (hesrBase + 40 + 4) (0 : Word) w5 w6 w7 w28 w29 w30 w31
              (BitVec.ofNat 64 listLenN) saved headerBytes outBytes empAssertion pcFree_emp
              hcr_prog hcr_wn h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound
              h_src_valid h_dst_valid hpayload RlpListNthItemSAsm.StrictPrefix.zero
              hpayload.cursor_le hbound)
      have hstage1' := cpsTripleWithin_of_forall_regIs_to_regOwn7 hstage1
      have hrec := cpsTripleWithin_seq_perm_same_cr
        (fun h hq => by unfold hesrInitCommon at hq; xperm_chunked hq) hmi hstage1'
      have hrec' := cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hq => hesrRetPost_frame_mono
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (fun h' hh => by rw [sepConj_emp_right'] at hh; exact memIs_implies_memOwn h' hh)))))
          h hq) hrec
      exact cpsTripleWithin_seq_perm_same_cr (fun h hq => by xperm_chunked hq) hntkF hrec'
    -- combine OK / FAIL over the two `initNormalized` disjuncts.
    refine cpsTripleWithin_weaken
      (fun h hp => by
        obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
        obtain ⟨ha, hb, hd', hu', hreg, hnorm⟩ := hrf
        unfold RlpListNthItemSAsm.initNormalized at hnorm
        rcases hnorm with hok | hfail
        · exact Or.inl ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hok⟩, hab⟩
        · exact Or.inr ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hfail⟩, hab⟩)
      (fun _ h => h) (cpsTripleWithin_or_pre hOK hFAIL)
  refine cpsTripleWithin_seq_perm_same_cr ?_ hinit' hdisp
  intro h hq
  unfold hesrScratchConst
  xperm_chunked hq


end EvmAsm.Codegen.HeaderFieldsSpec
