import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.RlpWalkCallSAsm
import EvmAsm.Codegen.Programs.RlpWalkInitFlatSAsm
import EvmAsm.Codegen.Programs.RlpWalkNextFlatSAsm
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase
import EvmAsm.Codegen.Programs.AccountBalanceHelperSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Codegen.Programs.HeaderFieldsSpecBlocksTail

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

/-- Next marshalling [18]-[20] (and [23]-[25], [28]-[30]): `SD x10; LD x10; LD x11`
    — re-spill the fresh cursor to `sp+32` and reload the preserved `endPtr` from
    `sp+40` into `x11` (which the status return clobbered).  Parametric in the entry
    PC; the caller supplies the three per-instruction code-membership facts. -/
private theorem hesrMarshalNext (entryPC newcursor endPtr newSp v11 g1 : Word)
    (hc0 : ∀ a i, CodeReq.singleton entryPC (.SD .x2 .x10 (32 : BitVec 12)) a = some i
      → hesrCode a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (entryPC + 4) (.LD .x10 .x2 (32 : BitVec 12)) a = some i
      → hesrCode a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (entryPC + 8) (.LD .x11 .x2 (40 : BitVec 12)) a = some i
      → hesrCode a = some i) :
    cpsTripleWithin 3 entryPC (entryPC + 12) hesrCode
      ((.x10 ↦ᵣ newcursor) ** (.x11 ↦ᵣ v11) ** (.x2 ↦ᵣ newSp) **
       ((newSp + 32) ↦ₘ g1) ** ((newSp + 40) ↦ₘ endPtr))
      ((.x10 ↦ᵣ newcursor) ** (.x11 ↦ᵣ endPtr) ** (.x2 ↦ᵣ newSp) **
       ((newSp + 32) ↦ₘ newcursor) ** ((newSp + 40) ↦ₘ endPtr)) := by
  -- [SD x2 x10 32] : (newSp+32) := newcursor
  have h0 := sd_spec_gen_within .x2 .x10 newSp newcursor g1 (32 : BitVec 12) entryPC
  rw [show newSp + signExtend12 (32 : BitVec 12) = newSp + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]] at h0
  have e0 := cpsTripleWithin_extend_code hc0 h0
  have f0 := cpsTripleWithin_frameR ((.x11 ↦ᵣ v11) ** ((newSp + 40) ↦ₘ endPtr)) (by pcFreeR) e0
  -- [LD x10 x2 32] : x10 := newcursor
  have h1 := ld_spec_gen_within .x10 .x2 newSp newcursor newcursor (32 : BitVec 12) (entryPC + 4) (by decide)
  rw [show newSp + signExtend12 (32 : BitVec 12) = newSp + 32 from by
        rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide],
      show (entryPC + 4 : Word) + 4 = entryPC + 8 from by bv_omega] at h1
  have e1 := cpsTripleWithin_extend_code hc1 h1
  have f1 := cpsTripleWithin_frameR ((.x11 ↦ᵣ v11) ** ((newSp + 40) ↦ₘ endPtr)) (by pcFreeR) e1
  -- [LD x11 x2 40] : x11 := endPtr
  have h2 := ld_spec_gen_within .x11 .x2 newSp v11 endPtr (40 : BitVec 12) (entryPC + 8) (by decide)
  rw [show newSp + signExtend12 (40 : BitVec 12) = newSp + 40 from by
        rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide],
      show (entryPC + 8 : Word) + 4 = entryPC + 12 from by bv_omega] at h2
  have e2 := cpsTripleWithin_extend_code hc2 h2
  have f2 := cpsTripleWithin_frameR ((.x10 ↦ᵣ newcursor) ** ((newSp + 32) ↦ₘ newcursor)) (by pcFreeR) e2
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f0 f1
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) s2

set_option maxRecDepth 8000 in
private theorem hesrStage4
    (listBase endPtr outPtr newSp : Word) (off3 listLen cursorOff : Nat)
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
    (hprefix3 : RlpListNthItemSAsm.StrictPrefix headerBytes listBase endPtr cursorOff 3 off3)
    (hoff3 : off3 ≤ listLen)
    (hbound : ∀ next len, rlpItemDecode headerBytes off3 (listBase + BitVec.ofNat 64 off3) endPtr next len →
      (next - len - listBase).toNat + 32 ≤ headerBytes.length) :
    cpsTripleWithin (1 + 87 + (1 + (9 + 4 + (1 + 204)))) (hesrBase + 124) (saved.ra &&& ~~~(1 : Word)) cr
      ((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off3)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ v12) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr)))
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr)) := by
  have hFpc : (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr).pcFree :=
    pcFree_sepConj (pcFree_hesrWalkAmbient _ _ _ _ _ _) hFr
  -- the walk call [+124 → +128]
  have hwalk := hesrNextStep (hesrBase + 124)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_state_root + 124))
    listBase endPtr off3 listLen
    oldRa v12 v5 v6 v7 v28 v29 v30 v31 headerBytes
    (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr) hFpc
    h_src_align h_slack h_src_over h_src_valid hoff3
    (by simp only [wnBase, hesrBase]; decide)
    (by simp only [hesrBase]; decide)
    (by simp only [wnBase, hesrBase]
        exact CodeReq.Disjoint.singleton_ofProg (by decide))
    (by
      refine CodeReq.union_sub (CodeReq.singleton_mono (hcr_prog _ _ ?_)) hcr_wn
      exact CodeReq.ofProg_mem_at hesrBase (hesrBase + 124) Codegen.headerExtractStateRoot_prog 31
        (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next
          (Codegen.GuestAddrs.header_extract_state_root + 124))) (by bv_omega)
        (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) _ _
        (by simp [CodeReq.singleton]))
  -- weaken the raw 6-way outcome to the 2-way normalized form
  have hwalk' := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      exact sepConj_mono_left
        (sepConj_mono_right (hesrNextOutcome_to_norm listBase endPtr headerBytes off3)) h hq) hwalk
  -- the BNE dispatch [+128 → ret]
  have hdisp : cpsTripleWithin (1 + (9 + 4 + (1 + 204))) (hesrBase + 128)
      (saved.ra &&& ~~~(1 : Word)) cr
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 124 + 4)) **
         bytesRegion listBase headerBytes) ** hesrNextNorm listBase endPtr headerBytes off3) **
        (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr))
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr)) := by
    -- BNE [32] x11, x0, +108 : taken (x11≠0) → +236 (status1), ntaken (x11=0) → +132.
    -- The ambient stays folded (`hesrWalkAmbient`) through the reshapes; it is
    -- unfolded only at the two `xperm` bridges that feed the explicit-register tails.
    have ha_t : (hesrBase + 128 : Word) + signExtend13 (108 : BitVec 13) = hesrBase + 236 := by
      rw [show signExtend13 (108 : BitVec 13) = (108 : Word) from by decide]; bv_omega
    have ha_f : (hesrBase + 128 : Word) + 4 = hesrBase + 132 := by bv_omega
    have hbnemono : ∀ a i, CodeReq.singleton (hesrBase + 128) (.BNE .x11 .x0 (108 : BitVec 13)) a = some i
        → cr a = some i := by
      intro a i hs
      exact hcr_prog _ _ (CodeReq.ofProg_mem_at hesrBase (hesrBase + 128)
        Codegen.headerExtractStateRoot_prog 32 (.BNE .x11 .x0 (108 : BitVec 13)) (by bv_omega)
        (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) _ _ hs)
    -- FAIL arm: x11 = status ≠ 0 → taken → status1 (a0 = 1, Failure.walk).
    have hFAIL : cpsTripleWithin (1 + (9 + 4 + (1 + 204))) (hesrBase + 128)
        (saved.ra &&& ~~~(1 : Word)) cr
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 124 + 4)) **
           bytesRegion listBase headerBytes) **
          (fun h => ∃ status : Word,
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off3)) ** (.x11 ↦ᵣ status) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜status ≠ (0 : Word) ∧
                RlpListNthItemSAsm.WalkFailure headerBytes off3
                  (listBase + BitVec.ofNat 64 off3) endPtr⌝) h)) **
          (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr))
        (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr)) := by
      -- expose the status register and its nonzero/failure facts:
      -- float ∃status to the top, then pull ⌜status≠0 ∧ WalkFailure⌝ to the front.
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ status : Word,
          (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 124 + 4)) **
             bytesRegion listBase headerBytes) **
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off3)) ** (.x11 ↦ᵣ status) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜status ≠ (0 : Word) ∧
               RlpListNthItemSAsm.WalkFailure headerBytes off3
                 (listBase + BitVec.ofNat 64 off3) endPtr⌝)) **
            (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hst⟩ := hrf
          obtain ⟨status, hstatus⟩ := hst
          exact ⟨status, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hstatus⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun status => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜status ≠ (0 : Word) ∧
              RlpListNthItemSAsm.WalkFailure headerBytes off3
                (listBase + BitVec.ofNat 64 off3) endPtr⌝ **
          (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 124 + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off3)) ** (.x12 ↦ᵣ (0 : Word)) **
             (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hP => ?_)
      -- BNE: taken since status ≠ 0.
      have hbne := bne_spec_gen_within .x11 .x0 (108 : BitVec 13) status (0 : Word) (hesrBase + 128)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemono hbne
      have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        exact hP.1 ((sepConj_pure_right _).1 hQ).2)
      have htkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 124 + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 off3)) ** (.x12 ↦ᵣ (0 : Word)) **
         (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr))
        (by repeat' first
          | exact pcFree_hesrWalkAmbient _ _ _ _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) htk
      -- status1 return with BUNDLED ambient entry — the ambient stays folded, so the
      -- feeding permutation sees ~15 atoms (well under the ~18-atom cliff).
      have hs1 := cpsTripleWithin_extend_code hcr_prog
        (hesrStatus1Bundled newSp listBase v9 outPtr (listBase + BitVec.ofNat 64 off3)
          (hesrBase + 124 + 4) saved
          ((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** regOwn .x5 **
           regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           bytesRegion listBase headerBytes ** hesrAmbConst outPtr outBytes ** Fr)
          (by repeat' first
            | exact pcFree_hesrAmbConst _ _ | exact hFr | exact bytesRegion_pcFree _ _
            | exact pcFree_regIs | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
            | apply pcFree_sepConj))
      have s := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by unfold hesrWalkAmbient at hp; xperm_chunked hp) htkF hs1
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => hp)
          (fun h hq => by
            refine ⟨(1 : Word), outBytes, (0 : Word), (0 : Word), ?_⟩
            refine (sepConj_pure_right h).2 ⟨?_, Or.inr (Or.inr ⟨rfl,
              RlpListNthItemSAsm.Failure.walk cursorOff 3 off3 endPtr hpayload (le_refl 3)
                hprefix3 hP.2⟩)⟩
            unfold hesrAmbConst at hq
            have hq2 : ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ saved.ra) ** hesrAmbRegsRestored newSp saved) **
               (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x12 ↦ᵣ (0 : Word)) ** regOwn .x28 **
                regOwn .x29 ** hesrScratchConst ** (.x0 ↦ᵣ (0 : Word)) **
                bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
                ((.x11 ↦ᵣ status) ** regOwn .x30 ** regOwn .x31 ** Fr)))) h := by
              xperm_chunked hq
            exact sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (regIs_implies_regOwn .x12)
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono (regIs_implies_regOwn .x11) (fun _ hh => hh))))))))))))
              h hq2) s)
    -- OK arm: x11 = 0 → ntaken → success tail (a0 ∈ {0,2}, Success).
    have hOK : cpsTripleWithin (1 + (9 + 4 + (1 + 204))) (hesrBase + 128)
        (saved.ra &&& ~~~(1 : Word)) cr
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 124 + 4)) **
           bytesRegion listBase headerBytes) **
          rlpWalkNextOk (listBase + BitVec.ofNat 64 off3) endPtr headerBytes off3) **
          (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr))
        (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr)) := by
      -- float ∃ next len out of `rlpWalkNextOk`, then pull ⌜rlpItemDecode⌝ to the front.
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ next len : Word,
          (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 124 + 4)) **
             bytesRegion listBase headerBytes) **
            ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
             ⌜rlpItemDecode headerBytes off3 (listBase + BitVec.ofNat 64 off3) endPtr next len⌝)) **
            (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hwalk⟩ := hrf
          obtain ⟨next, len, hw⟩ := hwalk
          exact ⟨next, len, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hw⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
      refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜rlpItemDecode headerBytes off3 (listBase + BitVec.ofNat 64 off3) endPtr next len⌝ **
          (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 124 + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
             (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hdecode => ?_)
      -- BNE: not taken since x11 = 0.
      have hbne := bne_spec_gen_within .x11 .x0 (108 : BitVec 13) (0 : Word) (0 : Word) (hesrBase + 128)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemono hbne
      have hntk := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        exact ((sepConj_pure_right _).1 hQ).2 rfl)
      -- release x11 (unused by the tail) to ownership so it rides the frame.
      have hntk' := cpsTripleWithin_weaken (fun _ hp => hp)
        (sepConj_mono_left (regIs_implies_regOwn .x11)) hntk
      have hntkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 124 + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
         (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes ** Fr))
        (by repeat' first
          | exact pcFree_hesrWalkAmbient _ _ _ _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) hntk'
      -- the selected item is the zero-based 3rd child: upgrade the walked prefix.
      have hsucc : RlpListNthItemSAsm.Success headerBytes listBase listLen 3
          (next - len - listBase) len :=
        ⟨cursorOff, endPtr, next, hpayload, hprefix3.select hdecode, rfl⟩
      -- success tail with BUNDLED ambient entry, x11/x30/x31 riding the frame.
      have hst := cpsTripleWithin_extend_code hcr_prog
        (hesrSuccessTailBundled next len listBase outPtr newSp (hesrBase + 124 + 4) v9 saved
          headerBytes outBytes listLen (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr)
          (by repeat' first
            | exact hFr | exact pcFree_regIs | exact pcFree_regOwn | apply pcFree_sepConj)
          h_src_align h_dst_align (hbound next len hdecode) h_dst_bound h_src_over h_dst_over
          h_src_valid h_dst_valid hsucc)
      exact cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by unfold hesrWalkAmbient hesrAmbConst at hp; xperm_chunked hp) hntkF hst
    -- distribute the normalized outcome over the two arms
    refine cpsTripleWithin_weaken
      (fun h hp => by
        obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
        obtain ⟨ha, hb, hd', hu', hreg, hnorm⟩ := hrf
        unfold hesrNextNorm at hnorm
        rcases hnorm with hok | hfail
        · exact Or.inl ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hok⟩, hab⟩
        · exact Or.inr ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hfail⟩, hab⟩)
      (fun _ h => h) (cpsTripleWithin_or_pre hOK hFAIL)
  -- compose walk ;; dispatch
  rw [show (hesrBase + 124 : Word) + 4 = hesrBase + 128 from by bv_omega] at hwalk'
  exact cpsTripleWithin_seq_same_cr hwalk' hdisp

/-- Bundled-entry wrapper for the inter-call marshalling: the ambient registers
    and the two spill cells stay folded (`hesrWalkAmbient`/`hesrSpill`) so the
    stage feeds it over few atoms.  Internally it unfolds them, frames the
    concrete `hesrMarshalNext`, and re-folds. -/
theorem hesrMarshalNextBundled
    (entryPC next endPtr newSp listBase v9 outPtr g1 : Word)
    (saved : Saved) (outBytes : List (BitVec 8)) (Fr : Assertion) (hFr : Fr.pcFree)
    (hc0 : ∀ a i, CodeReq.singleton entryPC (.SD .x2 .x10 (32 : BitVec 12)) a = some i
      → hesrCode a = some i)
    (hc1 : ∀ a i, CodeReq.singleton (entryPC + 4) (.LD .x10 .x2 (32 : BitVec 12)) a = some i
      → hesrCode a = some i)
    (hc2 : ∀ a i, CodeReq.singleton (entryPC + 8) (.LD .x11 .x2 (40 : BitVec 12)) a = some i
      → hesrCode a = some i) :
    cpsTripleWithin 3 entryPC (entryPC + 12) hesrCode
      (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word))) **
        (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
         hesrSpill newSp g1 endPtr ** Fr))
      (((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ endPtr)) **
        (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
         hesrSpill newSp next endPtr ** Fr)) := by
  have hm := hesrMarshalNext entryPC next endPtr newSp (0 : Word) g1 hc0 hc1 hc2
  have hmF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ outPtr) ** savedFrame newSp saved **
     hesrAmbConst outPtr outBytes ** Fr)
    (by
      repeat' first
        | exact hFr | exact pcFree_hesrAmbConst _ _ | unfold savedFrame
        | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hm
  refine cpsTripleWithin_weaken
    (fun h hp => by unfold hesrWalkAmbient hesrAmbRegs hesrSpill at hp; xperm_chunked hp)
    (fun h hq => by unfold hesrWalkAmbient hesrAmbRegs hesrSpill; xperm_chunked hq) hmF

set_option maxRecDepth 8000 in
theorem hesrStage3
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
    (hprefixPrev : RlpListNthItemSAsm.StrictPrefix headerBytes listBase endPtr cursorOff 2 offPrev)
    (hoffPrev : offPrev ≤ listLen)
    (hbound : ∀ o next len, o ≤ listLen →
      rlpItemDecode headerBytes o (listBase + BitVec.ofNat 64 o) endPtr next len →
      (next - len - listBase).toNat + 32 ≤ headerBytes.length) :
    cpsTripleWithin (1 + 87 + (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))))
      (hesrBase + 104) (saved.ra &&& ~~~(1 : Word)) cr
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
  -- the walk call [+104 → +108]
  have hwalk := hesrNextStep (hesrBase + 104)
    (jalOff Codegen.GuestAddrs.rlp_walk_next (Codegen.GuestAddrs.header_extract_state_root + 104))
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
      exact CodeReq.ofProg_mem_at hesrBase (hesrBase + 104) Codegen.headerExtractStateRoot_prog 26
        (.JAL .x1 (jalOff Codegen.GuestAddrs.rlp_walk_next
          (Codegen.GuestAddrs.header_extract_state_root + 104))) (by bv_omega)
        (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) _ _
        (by simp [CodeReq.singleton]))
  -- weaken the raw 6-way outcome to the 2-way normalized form
  have hwalk' := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      exact sepConj_mono_left
        (sepConj_mono_right (hesrNextOutcome_to_norm listBase endPtr headerBytes offPrev)) h hq) hwalk
  -- the BNE dispatch [+108 → ret]
  have hdisp : cpsTripleWithin (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))) (hesrBase + 108)
      (saved.ra &&& ~~~(1 : Word)) cr
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 104 + 4)) **
         bytesRegion listBase headerBytes) ** hesrNextNorm listBase endPtr headerBytes offPrev) **
        (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
         hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
      (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
    have ha_t : (hesrBase + 108 : Word) + signExtend13 (128 : BitVec 13) = hesrBase + 236 := by
      rw [show signExtend13 (128 : BitVec 13) = (128 : Word) from by decide]; bv_omega
    have ha_f : (hesrBase + 108 : Word) + 4 = hesrBase + 112 := by bv_omega
    have hbnemono : ∀ a i, CodeReq.singleton (hesrBase + 108) (.BNE .x11 .x0 (128 : BitVec 13)) a = some i
        → cr a = some i := by
      intro a i hs
      exact hcr_prog _ _ (CodeReq.ofProg_mem_at hesrBase (hesrBase + 108)
        Codegen.headerExtractStateRoot_prog 27 (.BNE .x11 .x0 (128 : BitVec 13)) (by bv_omega)
        (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) _ _ hs)
    -- FAIL arm: x11 = status ≠ 0 → taken → status1 (a0 = 1, Failure.walk).
    have hFAIL : cpsTripleWithin (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))) (hesrBase + 108)
        (saved.ra &&& ~~~(1 : Word)) cr
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 104 + 4)) **
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
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 104 + 4)) **
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
             regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 104 + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x12 ↦ᵣ (0 : Word)) **
             (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
              hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hP => ?_)
      have hbne := bne_spec_gen_within .x11 .x0 (128 : BitVec 13) status (0 : Word) (hesrBase + 108)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemono hbne
      have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        exact hP.1 ((sepConj_pure_right _).1 hQ).2)
      have htkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 104 + 4)) ** bytesRegion listBase headerBytes **
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
          (hesrBase + 104 + 4) saved
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
              RlpListNthItemSAsm.Failure.walk cursorOff 2 offPrev endPtr hpayload (by omega)
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
    -- OK arm: x11 = 0 → ntaken → marshal + recurse into hesrStage4.
    have hOK : cpsTripleWithin (1 + (3 + (1 + 87 + (1 + (9 + 4 + (1 + 204)))))) (hesrBase + 108)
        (saved.ra &&& ~~~(1 : Word)) cr
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 104 + 4)) **
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
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hesrBase + 104 + 4)) **
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
             regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 104 + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
             (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
              hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hdecode => ?_)
      -- advance the walked prefix from 2 to 3 items.
      have hend : endPtr = listBase + BitVec.ofNat 64 listLen := hpayload.end_eq
      have hover' : listBase.toNat + listLen + 9 < 2 ^ 64 := by omega
      obtain ⟨hnexteq, hlt, hle, hprefixK⟩ :=
        RlpListNthItemSAsm.StrictPrefix.step_bounds (endOff := listLen)
          (hend ▸ hprefixPrev) (hend ▸ hdecode) hoffPrev hover'
      set offK : Nat := (next - listBase).toNat with hoffKdef
      -- BNE: not taken since x11 = 0.
      have hbne := bne_spec_gen_within .x11 .x0 (128 : BitVec 13) (0 : Word) (0 : Word) (hesrBase + 108)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemono hbne
      have hntk := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        exact ((sepConj_pure_right _).1 hQ).2 rfl)
      have hntkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (hesrBase + 104 + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
         (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (by repeat' first
          | exact pcFree_hesrWalkAmbient _ _ _ _ _ _ | exact pcFree_hesrSpill _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) hntk
      -- marshalNext [+112 → +124], ambient/spill folded.
      have hmb := cpsTripleWithin_extend_code hcr_prog
        (hesrMarshalNextBundled (hesrBase + 112) (listBase + BitVec.ofNat 64 offK) endPtr newSp
          listBase v9 outPtr (listBase + BitVec.ofNat 64 offPrev) saved outBytes
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ (hesrBase + 104 + 4)) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** bytesRegion listBase headerBytes ** Fr)
          (by repeat' first
            | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
            | exact pcFree_regOwn | apply pcFree_sepConj)
          (fun a i hs => CodeReq.ofProg_mem_at hesrBase (hesrBase + 112)
            Codegen.headerExtractStateRoot_prog 28 (.SD .x2 .x10 (32 : BitVec 12)) (by bv_omega)
            (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) a i hs)
          (fun a i hs => CodeReq.ofProg_mem_at hesrBase (hesrBase + 116)
            Codegen.headerExtractStateRoot_prog 29 (.LD .x10 .x2 (32 : BitVec 12)) (by bv_omega)
            (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) a i hs)
          (fun a i hs => CodeReq.ofProg_mem_at hesrBase (hesrBase + 120)
            Codegen.headerExtractStateRoot_prog 30 (.LD .x11 .x2 (40 : BitVec 12)) (by bv_omega)
            (by rw [hesr_prog_length]; norm_num) rfl (by rw [hesr_prog_length]; norm_num) a i hs))
      -- recurse into hesrStage4 at +124 with the freshly-marshalled spill in Fr.
      have hstage4 : ∀ w5 w6 w7 w28 w29 w30 w31,
          cpsTripleWithin (1 + 87 + (1 + (9 + 4 + (1 + 204)))) (hesrBase + 124)
            (saved.ra &&& ~~~(1 : Word)) cr
            (((.x1 ↦ᵣ (hesrBase + 104 + 4)) **
              ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
               (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
               (hesrWalkAmbient newSp outPtr listBase v9 saved outBytes **
                (memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)))) **
             (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) **
             (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
            (hesrRetPost newSp listBase outPtr saved headerBytes outBytes listLen 3
              (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
               memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) :=
        fun w5 w6 w7 w28 w29 w30 w31 =>
          cpsTripleWithin_weaken (fun h hp => by xperm_chunked hp) (fun _ h => h)
            (hesrStage4 listBase endPtr outPtr newSp offK listLen cursorOff
              (hesrBase + 104 + 4) len w5 w6 w7 w28 w29 w30 w31 v9 saved headerBytes outBytes
              (memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)
              (by repeat' first
                | exact hFr | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj)
              hcr_prog hcr_wn h_src_align h_dst_align h_slack h_src_over h_dst_over h_dst_bound
              h_src_valid h_dst_valid hpayload (hend ▸ hprefixK) hle
              (fun n l hd => hbound offK n l hle hd))
      have hstage4' := cpsTripleWithin_of_forall_regIs_to_regOwn7 hstage4
      have hrec := cpsTripleWithin_seq_perm_same_cr
        (fun h hq => by
          have hq' := sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (fun h' hs => by unfold hesrSpill at hs
                             exact sepConj_mono_left memIs_implies_memOwn h' hs))) h hq
          xperm_chunked hq') hmb hstage4'
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
  rw [show (hesrBase + 104 : Word) + 4 = hesrBase + 108 from by bv_omega] at hwalk'
  exact cpsTripleWithin_seq_same_cr hwalk' hdisp


end EvmAsm.Codegen.HeaderFieldsSpec
