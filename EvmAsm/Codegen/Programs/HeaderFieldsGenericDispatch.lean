/-
  EvmAsm.Codegen.Programs.HeaderFieldsGenericDispatch

  The generic per-field walk-stage dispatch lemmas, abstracted over the guest
  base / ambient code / PCs / scratch addresses so a single stage lemma can be
  applied N times (6 for receipts, 17 for withdrawals) instead of hand-unrolling
  one hesrStageK per field index.

  `hfStageRec` is the non-selecting stage (mirrors `hesrStage3`): walk-call, BNE
  dispatch, on OK advance the strict prefix by one and marshal into the supplied
  continuation, on FAIL return status-1 with `Failure.walk`.

  `hfStageSel` is the selecting stage (mirrors `hesrStage4`): walk-call, BNE
  dispatch, on OK `StrictPrefix.select` into the supplied success tail, on FAIL
  return status-1 with `Failure.walk`.

  Both take the FAIL tail (`hfStatus1Bundled`, generic) internally and the OK
  continuation / success tail as a hypothesis, so they are pure glue.

  Classical-3 axioms only; no `sorry`/`native_decide`/`bv_decide`.
-/
import EvmAsm.Codegen.Programs.HeaderFieldsGenericBlocks

namespace EvmAsm.Codegen.HeaderFieldsSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)

set_option maxRecDepth 8000 in
/-- Generic non-selecting walk stage.  Walk-call at `entryPC`, `BNE x11,x0,bneOff`
    at `entryPC+4` (taken → `status1PC`, not-taken → `entryPC+8`), then on the OK
    arm marshal `[entryPC+8 .. entryPC+20]` and enter the supplied continuation at
    `entryPC+20`; on FAIL emit the status-1 return with `Failure.walk count`. -/
theorem hfStageRec {code : CodeReq} {nCont : Nat}
    (offAddr lenAddr listBase endPtr outPtr newSp : Word)
    (offPrev listLen cursorOff count index : Nat)
    (oldRa v12 v5 v6 v7 v28 v29 v30 v31 v9 : Word)
    (saved : Saved) (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree) (hnCont : 5 ≤ nCont)
    (entryPC status1PC : Word) (bneOff : BitVec 13) (walkOffset : BitVec 21)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → code a = some i)
    (hwoff : entryPC + signExtend21 walkOffset = wnBase)
    (halign : (entryPC + 4) &&& ~~~(1 : Word) = entryPC + 4)
    (hdisj : (CodeReq.singleton entryPC (.JAL .x1 walkOffset)).Disjoint (rlp_walk_next_code wnBase))
    (hbne_t : entryPC + 4 + signExtend13 bneOff = status1PC)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ headerBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hcount : count ≤ index)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLen cursorOff endPtr)
    (hprefixPrev : RlpListNthItemSAsm.StrictPrefix headerBytes listBase endPtr cursorOff count offPrev)
    (hoffPrev : offPrev ≤ listLen)
    (hwjal : ∀ a i, CodeReq.singleton entryPC (.JAL .x1 walkOffset) a = some i → code a = some i)
    (hbnemem : ∀ a i, CodeReq.singleton (entryPC + 4) (.BNE .x11 .x0 bneOff) a = some i → code a = some i)
    (hm0 : ∀ a i, CodeReq.singleton (entryPC + 8) (.SD .x2 .x10 (32 : BitVec 12)) a = some i → code a = some i)
    (hm1 : ∀ a i, CodeReq.singleton (entryPC + 12) (.LD .x10 .x2 (32 : BitVec 12)) a = some i → code a = some i)
    (hm2 : ∀ a i, CodeReq.singleton (entryPC + 16) (.LD .x11 .x2 (40 : BitVec 12)) a = some i → code a = some i)
    (hs0 : ∀ a i, CodeReq.singleton status1PC (.LI .x10 (1 : Word)) a = some i → code a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (status1PC + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → code a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (status1PC + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → code a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (status1PC + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → code a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (status1PC + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → code a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (status1PC + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → code a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (status1PC + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → code a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (status1PC + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → code a = some i)
    (hcont : ∀ (offK : Nat) (len : Word),
      offK ≤ listLen →
      RlpListNthItemSAsm.StrictPrefix headerBytes listBase endPtr cursorOff (count + 1) offK →
      ∀ w5 w6 w7 w28 w29 w30 w31,
      cpsTripleWithin nCont (entryPC + 20) (saved.ra &&& ~~~(1 : Word)) code
        (((.x1 ↦ᵣ (entryPC + 4)) **
          ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offK)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ len) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
           (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
            hesrSpill newSp (listBase + BitVec.ofNat 64 offK) endPtr ** Fr))) **
         (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) **
         (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
        (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr))) :
    cpsTripleWithin (1 + 87 + (1 + (3 + nCont))) entryPC (saved.ra &&& ~~~(1 : Word)) code
      ((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ v12) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr)))
      (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
  have hFpc : (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
      hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr).pcFree :=
    pcFree_sepConj (pcFree_hfWalkAmbient _ _ _ _ _ _ _ _)
      (pcFree_sepConj (pcFree_hesrSpill _ _ _) hFr)
  -- the walk call [entryPC → entryPC+4]
  have hwalk := hesrNextStep entryPC walkOffset listBase endPtr offPrev listLen
    oldRa v12 v5 v6 v7 v28 v29 v30 v31 headerBytes
    (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
     hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr) hFpc
    h_src_align h_slack h_src_over h_src_valid hoffPrev hwoff halign hdisj
    (CodeReq.union_sub hwjal hcr_wn)
  have hwalk' := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      exact sepConj_mono_left
        (sepConj_mono_right (hesrNextOutcome_to_norm listBase endPtr headerBytes offPrev)) h hq) hwalk
  -- the BNE dispatch [entryPC+4 → ret]
  have hdisp : cpsTripleWithin (1 + (3 + nCont)) (entryPC + 4)
      (saved.ra &&& ~~~(1 : Word)) code
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
         bytesRegion listBase headerBytes) ** hesrNextNorm listBase endPtr headerBytes offPrev) **
        (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
         hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
      (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
         memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
    have ha_t : (entryPC + 4 : Word) + signExtend13 bneOff = status1PC := hbne_t
    have ha_f : (entryPC + 4 : Word) + 4 = entryPC + 8 := by bv_omega
    -- FAIL arm
    have hFAIL : cpsTripleWithin (1 + (3 + nCont)) (entryPC + 4)
        (saved.ra &&& ~~~(1 : Word)) code
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
           bytesRegion listBase headerBytes) **
          (fun h => ∃ status : Word,
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x11 ↦ᵣ status) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜status ≠ (0 : Word) ∧
                RlpListNthItemSAsm.WalkFailure headerBytes offPrev
                  (listBase + BitVec.ofNat 64 offPrev) endPtr⌝) h)) **
          (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
           hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ status : Word,
          (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
             bytesRegion listBase headerBytes) **
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x11 ↦ᵣ status) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜status ≠ (0 : Word) ∧
               RlpListNthItemSAsm.WalkFailure headerBytes offPrev
                 (listBase + BitVec.ofNat 64 offPrev) endPtr⌝)) **
            (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
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
             regOwn .x31 ** (.x1 ↦ᵣ (entryPC + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x12 ↦ᵣ (0 : Word)) **
             (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
              hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hP => ?_)
      have hbne := bne_spec_gen_within .x11 .x0 bneOff status (0 : Word) (entryPC + 4)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemem hbne
      have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        exact hP.1 ((sepConj_pure_right _).1 hQ).2)
      have htkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (entryPC + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offPrev)) ** (.x12 ↦ᵣ (0 : Word)) **
         (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (by repeat' first
          | exact pcFree_hfWalkAmbient _ _ _ _ _ _ _ _ | exact pcFree_hesrSpill _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) htk
      have hst := cpsTripleWithin_extend_code (fun a i h => h)
        (hfStatus1Bundled (code := code) status1PC newSp listBase v9 outPtr
          (listBase + BitVec.ofNat 64 offPrev) (entryPC + 4) saved
          ((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** regOwn .x5 **
           regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           bytesRegion listBase headerBytes ** hfAmbConst offAddr lenAddr outPtr outBytes **
           hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr)
          (by repeat' first
            | exact pcFree_hfAmbConst _ _ _ _ | exact pcFree_hesrSpill _ _ _ | exact hFr
            | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
            | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj)
          hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7)
      have s := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by unfold hfWalkAmbient at hp; xperm_chunked hp) htkF hst
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => hp)
          (fun h hq => by
            refine ⟨(1 : Word), outBytes, (0 : Word), (0 : Word), ?_⟩
            refine (sepConj_pure_right h).2 ⟨?_, Or.inr (Or.inr ⟨rfl,
              RlpListNthItemSAsm.Failure.walk cursorOff count offPrev endPtr hpayload hcount
                hprefixPrev hP.2⟩)⟩
            unfold hfAmbConst hesrSpill at hq
            have hq2 : ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ saved.ra) ** hesrAmbRegsRestored newSp saved) **
               (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x12 ↦ᵣ (0 : Word)) ** regOwn .x28 **
                regOwn .x29 ** hfScratchConst offAddr lenAddr ** (.x0 ↦ᵣ (0 : Word)) **
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
    -- OK arm
    have hOK : cpsTripleWithin (1 + (3 + nCont)) (entryPC + 4)
        (saved.ra &&& ~~~(1 : Word)) code
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
           bytesRegion listBase headerBytes) **
          rlpWalkNextOk (listBase + BitVec.ofNat 64 offPrev) endPtr headerBytes offPrev) **
          (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
           hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 **
           memOwn (newSp + 32) ** ((newSp + 40) ↦ₘ endPtr) ** Fr)) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ next len : Word,
          (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
             bytesRegion listBase headerBytes) **
            ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
             ⌜rlpItemDecode headerBytes offPrev (listBase + BitVec.ofNat 64 offPrev) endPtr next len⌝)) **
            (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
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
             regOwn .x31 ** (.x1 ↦ᵣ (entryPC + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
             (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
              hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hdecode => ?_)
      have hend : endPtr = listBase + BitVec.ofNat 64 listLen := hpayload.end_eq
      have hover' : listBase.toNat + listLen + 9 < 2 ^ 64 := by omega
      obtain ⟨hnexteq, hlt, hle, hprefixK⟩ :=
        RlpListNthItemSAsm.StrictPrefix.step_bounds (endOff := listLen)
          (hend ▸ hprefixPrev) (hend ▸ hdecode) hoffPrev hover'
      set offK : Nat := (next - listBase).toNat with hoffKdef
      have hbne := bne_spec_gen_within .x11 .x0 bneOff (0 : Word) (0 : Word) (entryPC + 4)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemem hbne
      have hntk := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        exact ((sepConj_pure_right _).1 hQ).2 rfl)
      have hntkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (entryPC + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
         (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes **
          hesrSpill newSp (listBase + BitVec.ofNat 64 offPrev) endPtr ** Fr))
        (by repeat' first
          | exact pcFree_hfWalkAmbient _ _ _ _ _ _ _ _ | exact pcFree_hesrSpill _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) hntk
      have hmb := cpsTripleWithin_extend_code (fun a i h => h)
        (hfMarshalNextBundled (code := code) offAddr lenAddr (entryPC + 8)
          (listBase + BitVec.ofNat 64 offK) endPtr newSp listBase v9 outPtr
          (listBase + BitVec.ofNat 64 offPrev) saved outBytes
          ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) ** (.x1 ↦ᵣ (entryPC + 4)) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** bytesRegion listBase headerBytes ** Fr)
          (by repeat' first
            | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
            | exact pcFree_regOwn | apply pcFree_sepConj)
          hm0
          (fun a i h => hm1 a i (by rw [show (entryPC + 8 + 4 : Word) = entryPC + 12 from by bv_omega] at h; exact h))
          (fun a i h => hm2 a i (by rw [show (entryPC + 8 + 8 : Word) = entryPC + 16 from by bv_omega] at h; exact h)))
      rw [show (entryPC + 8 : Word) + 12 = entryPC + 20 from by bv_omega] at hmb
      have hstage := fun w5 w6 w7 w28 w29 w30 w31 =>
        hcont offK len hle (hend ▸ hprefixK) w5 w6 w7 w28 w29 w30 w31
      have hstage' := cpsTripleWithin_of_forall_regIs_to_regOwn7 hstage
      have hrec := cpsTripleWithin_seq_perm_same_cr
        (fun h hq => by xperm_chunked hq) hmb hstage'
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
  exact cpsTripleWithin_seq_same_cr hwalk' hdisp

#print axioms hfStageRec

set_option maxRecDepth 8000 in
/-- Generic selecting walk stage (the final field walk).  Walk-call at `entryPC`,
    `BNE x11,x0,bneOff` at `entryPC+4` (taken → `status1PC`, not-taken →
    `entryPC+8`), then on the OK arm `StrictPrefix.select` upgrades the walked
    `count`-item prefix to the selected `index`-th child and enters the supplied
    success tail at `entryPC+8`; on FAIL emit status-1 with `Failure.walk count`. -/
theorem hfStageSel {code : CodeReq} {nTail : Nat}
    (offAddr lenAddr listBase endPtr outPtr newSp : Word)
    (offSel listLen cursorOff index : Nat)
    (oldRa v12 v5 v6 v7 v28 v29 v30 v31 v9 : Word)
    (saved : Saved) (headerBytes outBytes : List (BitVec 8))
    (Fr : Assertion) (hFr : Fr.pcFree) (hnTail : 8 ≤ nTail)
    (entryPC status1PC : Word) (bneOff : BitVec 13) (walkOffset : BitVec 21)
    (hcr_wn : ∀ a i, rlp_walk_next_code wnBase a = some i → code a = some i)
    (hwoff : entryPC + signExtend21 walkOffset = wnBase)
    (halign : (entryPC + 4) &&& ~~~(1 : Word) = entryPC + 4)
    (hdisj : (CodeReq.singleton entryPC (.JAL .x1 walkOffset)).Disjoint (rlp_walk_next_code wnBase))
    (hbne_t : entryPC + 4 + signExtend13 bneOff = status1PC)
    (h_src_align : listBase.toNat % 8 = 0)
    (h_slack : listLen + 9 ≤ headerBytes.length)
    (h_src_over : listBase.toNat + headerBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < headerBytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hpayload : RlpListNthItemSAsm.StrictListPayload headerBytes listBase listLen cursorOff endPtr)
    (hprefixSel : RlpListNthItemSAsm.StrictPrefix headerBytes listBase endPtr cursorOff index offSel)
    (hoffSel : offSel ≤ listLen)
    (hwjal : ∀ a i, CodeReq.singleton entryPC (.JAL .x1 walkOffset) a = some i → code a = some i)
    (hbnemem : ∀ a i, CodeReq.singleton (entryPC + 4) (.BNE .x11 .x0 bneOff) a = some i → code a = some i)
    (hs0 : ∀ a i, CodeReq.singleton status1PC (.LI .x10 (1 : Word)) a = some i → code a = some i)
    (hs1 : ∀ a i, CodeReq.singleton (status1PC + 4) (.JAL .x0 (8 : BitVec 21)) a = some i → code a = some i)
    (hs2 : ∀ a i, CodeReq.singleton (status1PC + 12) (.LD .x1 .x2 (0 : BitVec 12)) a = some i → code a = some i)
    (hs3 : ∀ a i, CodeReq.singleton (status1PC + 16) (.LD .x8 .x2 (8 : BitVec 12)) a = some i → code a = some i)
    (hs4 : ∀ a i, CodeReq.singleton (status1PC + 20) (.LD .x9 .x2 (16 : BitVec 12)) a = some i → code a = some i)
    (hs5 : ∀ a i, CodeReq.singleton (status1PC + 24) (.LD .x18 .x2 (24 : BitVec 12)) a = some i → code a = some i)
    (hs6 : ∀ a i, CodeReq.singleton (status1PC + 28) (.ADDI .x2 .x2 (48 : BitVec 12)) a = some i → code a = some i)
    (hs7 : ∀ a i, CodeReq.singleton (status1PC + 32) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i → code a = some i)
    (hsuccTail : ∀ (next len : Word),
      RlpListNthItemSAsm.Success headerBytes listBase listLen index (next - len - listBase) len →
      cpsTripleWithin nTail (entryPC + 8) (saved.ra &&& ~~~(1 : Word)) code
        ((((.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
           bytesRegion listBase headerBytes ** bytesRegion outPtr outBytes **
           hesrAmbRegs newSp listBase v9 outPtr saved **
           (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr)) ** hfScratchConst offAddr lenAddr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29)
        (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr))) :
    cpsTripleWithin (1 + 87 + (1 + nTail)) entryPC (saved.ra &&& ~~~(1 : Word)) code
      ((.x1 ↦ᵣ oldRa) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offSel)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ v12) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
         (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase headerBytes **
         (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr)))
      (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr)) := by
  have hFpc : (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr).pcFree :=
    pcFree_sepConj (pcFree_hfWalkAmbient _ _ _ _ _ _ _ _) hFr
  -- the walk call [entryPC → entryPC+4]
  have hwalk := hesrNextStep entryPC walkOffset listBase endPtr offSel listLen
    oldRa v12 v5 v6 v7 v28 v29 v30 v31 headerBytes
    (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr) hFpc
    h_src_align h_slack h_src_over h_src_valid hoffSel hwoff halign hdisj
    (CodeReq.union_sub hwjal hcr_wn)
  have hwalk' := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      exact sepConj_mono_left
        (sepConj_mono_right (hesrNextOutcome_to_norm listBase endPtr headerBytes offSel)) h hq) hwalk
  have hdisp : cpsTripleWithin (1 + nTail) (entryPC + 4)
      (saved.ra &&& ~~~(1 : Word)) code
      (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
         bytesRegion listBase headerBytes) ** hesrNextNorm listBase endPtr headerBytes offSel) **
        (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr))
      (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index
        (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr)) := by
    have ha_t : (entryPC + 4 : Word) + signExtend13 bneOff = status1PC := hbne_t
    have ha_f : (entryPC + 4 : Word) + 4 = entryPC + 8 := by bv_omega
    -- FAIL arm
    have hFAIL : cpsTripleWithin (1 + nTail) (entryPC + 4)
        (saved.ra &&& ~~~(1 : Word)) code
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
           bytesRegion listBase headerBytes) **
          (fun h => ∃ status : Word,
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offSel)) ** (.x11 ↦ᵣ status) **
              (.x12 ↦ᵣ (0 : Word)) **
              ⌜status ≠ (0 : Word) ∧
                RlpListNthItemSAsm.WalkFailure headerBytes offSel
                  (listBase + BitVec.ofNat 64 offSel) endPtr⌝) h)) **
          (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr))
        (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr)) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ status : Word,
          (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
             bytesRegion listBase headerBytes) **
            ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offSel)) ** (.x11 ↦ᵣ status) **
             (.x12 ↦ᵣ (0 : Word)) **
             ⌜status ≠ (0 : Word) ∧
               RlpListNthItemSAsm.WalkFailure headerBytes offSel
                 (listBase + BitVec.ofNat 64 offSel) endPtr⌝)) **
            (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hst⟩ := hrf
          obtain ⟨status, hstatus⟩ := hst
          exact ⟨status, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hstatus⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun status => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜status ≠ (0 : Word) ∧
              RlpListNthItemSAsm.WalkFailure headerBytes offSel
                (listBase + BitVec.ofNat 64 offSel) endPtr⌝ **
          (((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word))) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x1 ↦ᵣ (entryPC + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offSel)) ** (.x12 ↦ᵣ (0 : Word)) **
             (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hP => ?_)
      have hbne := bne_spec_gen_within .x11 .x0 bneOff status (0 : Word) (entryPC + 4)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemem hbne
      have htk := cpsBranchWithin_takenStripPure2 hbnee (fun hp hQf => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQf
        exact hP.1 ((sepConj_pure_right _).1 hQ).2)
      have htkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (entryPC + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 offSel)) ** (.x12 ↦ᵣ (0 : Word)) **
         (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr))
        (by repeat' first
          | exact pcFree_hfWalkAmbient _ _ _ _ _ _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) htk
      have hst := hfStatus1Bundled (code := code) status1PC newSp listBase v9 outPtr
          (listBase + BitVec.ofNat 64 offSel) (entryPC + 4) saved
          ((.x11 ↦ᵣ status) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** regOwn .x5 **
           regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           bytesRegion listBase headerBytes ** hfAmbConst offAddr lenAddr outPtr outBytes ** Fr)
          (by repeat' first
            | exact pcFree_hfAmbConst _ _ _ _ | exact hFr
            | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn
            | exact pcFree_memIs | exact pcFree_memOwn | apply pcFree_sepConj)
          hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
      have s := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by unfold hfWalkAmbient at hp; xperm_chunked hp) htkF hst
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => hp)
          (fun h hq => by
            refine ⟨(1 : Word), outBytes, (0 : Word), (0 : Word), ?_⟩
            refine (sepConj_pure_right h).2 ⟨?_, Or.inr (Or.inr ⟨rfl,
              RlpListNthItemSAsm.Failure.walk cursorOff index offSel endPtr hpayload (le_refl index)
                hprefixSel hP.2⟩)⟩
            unfold hfAmbConst at hq
            have hq2 : ((((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ saved.ra) ** hesrAmbRegsRestored newSp saved) **
               (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** (.x12 ↦ᵣ (0 : Word)) ** regOwn .x28 **
                regOwn .x29 ** hfScratchConst offAddr lenAddr ** (.x0 ↦ᵣ (0 : Word)) **
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
    -- OK arm
    have hOK : cpsTripleWithin (1 + nTail) (entryPC + 4)
        (saved.ra &&& ~~~(1 : Word)) code
        (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
           regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
           bytesRegion listBase headerBytes) **
          rlpWalkNextOk (listBase + BitVec.ofNat 64 offSel) endPtr headerBytes offSel) **
          (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr))
        (hfRetPost offAddr lenAddr newSp listBase outPtr saved headerBytes outBytes listLen index
          (regOwn .x11 ** regOwn .x30 ** regOwn .x31 ** Fr)) := by
      refine cpsTripleWithin_weaken
        (P := fun h => ∃ next len : Word,
          (((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (entryPC + 4)) **
             bytesRegion listBase headerBytes) **
            ((.x10 ↦ᵣ next) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len) **
             ⌜rlpItemDecode headerBytes offSel (listBase + BitVec.ofNat 64 offSel) endPtr next len⌝)) **
            (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr)) h)
        (fun h hp => by
          obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
          obtain ⟨ha, hb, hd', hu', hreg, hwlk⟩ := hrf
          obtain ⟨next, len, hw⟩ := hwlk
          exact ⟨next, len, ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hw⟩, hab⟩⟩)
        (fun _ h => h) ?_
      refine cpsTripleWithin_exists_pre_gen (fun next => ?_)
      refine cpsTripleWithin_exists_pre_gen (fun len => ?_)
      refine cpsTripleWithin_weaken
        (P := ⌜rlpItemDecode headerBytes offSel (listBase + BitVec.ofNat 64 offSel) endPtr next len⌝ **
          (((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
             regOwn .x31 ** (.x1 ↦ᵣ (entryPC + 4)) ** bytesRegion listBase headerBytes **
             (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
             (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr))))
        (fun h hp => by xperm_chunked hp)
        (fun _ h => h) ?_
      refine cpsTripleWithin_pure_pre (fun hdecode => ?_)
      have hbne := bne_spec_gen_within .x11 .x0 bneOff (0 : Word) (0 : Word) (entryPC + 4)
      rw [ha_t, ha_f] at hbne
      have hbnee := cpsBranchWithin_extend_code hbnemem hbne
      have hntk := cpsBranchWithin_ntakenStripPure2 hbnee (fun hp hQt => by
        obtain ⟨_, _, _, _, _, hQ⟩ := hQt
        exact ((sepConj_pure_right _).1 hQ).2 rfl)
      have hntk' := cpsTripleWithin_weaken (fun _ hp => hp)
        (sepConj_mono_left (regIs_implies_regOwn .x11)) hntk
      have hntkF := cpsTripleWithin_frameR
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** (.x1 ↦ᵣ (entryPC + 4)) ** bytesRegion listBase headerBytes **
         (.x10 ↦ᵣ next) ** (.x12 ↦ᵣ len) **
         (hfWalkAmbient offAddr lenAddr newSp outPtr listBase v9 saved outBytes ** Fr))
        (by repeat' first
          | exact pcFree_hfWalkAmbient _ _ _ _ _ _ _ _
          | exact hFr | exact bytesRegion_pcFree _ _ | exact pcFree_regIs
          | exact pcFree_regOwn | exact pcFree_memIs | exact pcFree_memOwn
          | apply pcFree_sepConj) hntk'
      have hsucc : RlpListNthItemSAsm.Success headerBytes listBase listLen index
          (next - len - listBase) len :=
        ⟨cursorOff, endPtr, next, hpayload, hprefixSel.select hdecode, rfl⟩
      have hst := hsuccTail next len hsucc
      exact cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by unfold hfWalkAmbient hfAmbConst at hp; xperm_chunked hp) hntkF hst
    refine cpsTripleWithin_weaken
      (fun h hp => by
        obtain ⟨h1, h2, hd, hu, hrf, hab⟩ := hp
        obtain ⟨ha, hb, hd', hu', hreg, hnorm⟩ := hrf
        unfold hesrNextNorm at hnorm
        rcases hnorm with hok | hfail
        · exact Or.inl ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hok⟩, hab⟩
        · exact Or.inr ⟨h1, h2, hd, hu, ⟨ha, hb, hd', hu', hreg, hfail⟩, hab⟩)
      (fun _ h => h) (cpsTripleWithin_or_pre hOK hFAIL)
  exact cpsTripleWithin_seq_same_cr hwalk' hdisp

#print axioms hfStageSel

end EvmAsm.Codegen.HeaderFieldsSpec
