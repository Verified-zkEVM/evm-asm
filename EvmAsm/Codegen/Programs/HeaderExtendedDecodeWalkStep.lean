/-
  The walk-step back-half dispatch of `headerExtendedDecode_prog`
  (`Programs/HeaderDecode.lean`, PR-K39).

  A sequential-walk step occupies five instructions at `S = HB + 4·k`:

    [k]   MV x10, x19     [k+1] MV x11, x9     [k+2] JAL rlp_walk_next
    [k+3] MV x19, x10     [k+4] BNE x11, x0, →fail

  The front three (`hedWalkCall`, `HeaderExtendedDecodeCall.lean`) invoke the
  merged cursor walker, yielding the six-way status disjunction.  This module
  builds the BACK half — the `MV x19, x10` cursor-save plus the `BNE x11, x0`
  status dispatch — as a `cpsBranchWithin`: the not-taken (ok) exit advances the
  cursor with a genuine `rlpItemDecode` witness (`hedWalkOk`), the taken exit
  short-circuits to `HB + 664` with a `walkStepFail` witness (`hedWalkFail`).
  The six callee statuses (`rlpWalkNextOk` ∨ statuses 2..6) collapse to the
  ok / fail two-way here.  `hedWalkStep` = `hedWalkCall ;; dispatch`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodeCall
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.SAsm.TwoBreakWritable

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

/-- The `rlp_walk_next` callee post as re-based onto `fullCode`: the clobbered
    temporaries `t0..t6`, the preserved `x0`/`ra`/input bytes, and the six-way
    status disjunction (`rlpWalkNextOk` ∨ statuses 2..6).  This is exactly the
    post of `rlp_walk_next_spec_within` with `base := WNB`, so the backbone can
    produce the `hcall` argument by `change`/defeq. -/
def hedWalkNextPost (srcBase endPtr raVal : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) : Assertion :=
  (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) **
  (fun h =>
    rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr srcBytes srcOff h ∨
    (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (2 : Word)) **
       (.x12 ↦ᵣ (0 : Word)) **
       ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h) ∨
    (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (3 : Word)) **
       (.x12 ↦ᵣ (0 : Word)) **
       ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
         endPtr next len⌝) h) ∨
    (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (4 : Word)) **
       (.x12 ↦ᵣ (0 : Word)) **
       ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
         endPtr next len⌝) h) ∨
    (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (5 : Word)) **
       (.x12 ↦ᵣ (0 : Word)) **
       ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
         endPtr next len⌝) h) ∨
    (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (6 : Word)) **
       (.x12 ↦ᵣ (0 : Word)) **
       ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
         endPtr next len⌝) h))

/-- The ok (not-taken) post at `S + 20`: the cursor is advanced to `next` (saved
    into both `x10` and `s3 = x19`), the reported length sits in `x12`, and the
    step's genuine `rlpItemDecode` witness is pinned. -/
def hedWalkOk (srcBase endPtr raVal : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (Extra : Assertion) : Assertion :=
  fun h => ∃ next len : Word,
    ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ len) **
      ((.x19 : Reg) ↦ᵣ next) ** ((.x9 : Reg) ↦ᵣ endPtr) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion srcBase srcBytes ** Extra) **
     ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h

/-- The fail (taken) post at `HB + 664`: the working registers are surrendered
    and a `walkStepFail` witness (cursor at/past `end`, or no canonical item)
    is carried for the caller. -/
def hedWalkFail (srcBase endPtr raVal : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat) (Extra : Assertion) : Assertion :=
  (((.x9 : Reg) ↦ᵣ endPtr) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
    regOwn .x19 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion srcBase srcBytes ** Extra) **
   ⌜walkStepFail srcBytes endPtr (srcBase + BitVec.ofNat 64 srcOff) srcOff⌝

set_option maxRecDepth 8000 in
/-- **Walk-step back-half dispatch + full step.**  Given the front-half
    invocation `hcall` (the wrapped `jal rlp_walk_next` yielding
    `hedWalkNextPost ** Extra`), the two argument `MV`s (`hMV0`/`hMV1`), the
    cursor-save `MV x19, x10` (`hMV2`), and the status `BNE x11, x0` targeting
    `HB + 664` (`hBNE`), the whole five-instruction step is a branch: ok →
    `S + 20` (`hedWalkOk`), fail → `HB + 664` (`hedWalkFail`). -/
theorem hedWalkStep {n : Nat} {Prest Extra : Assertion}
    (S srcBase endPtr raOld v10 v11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (boff : BitVec 13)
    (hExtra : Extra.pcFree) (hPrest : Prest.pcFree)
    (htgt : (S + 16) + signExtend13 boff = HB + 664)
    (hMV0 : ∀ a i, CodeReq.singleton S (.MV .x10 .x19) a = some i → fullCode a = some i)
    (hMV1 : ∀ a i, CodeReq.singleton (S + 4) (.MV .x11 .x9) a = some i → fullCode a = some i)
    (hMV2 : ∀ a i, CodeReq.singleton (S + 12) (.MV .x19 .x10) a = some i → fullCode a = some i)
    (hBNE : ∀ a i, CodeReq.singleton (S + 16) (.BNE .x11 .x0 boff) a = some i → fullCode a = some i)
    (hcall : cpsTripleWithin n (S + 8) (S + 12) fullCode
      (((.x1 : Reg) ↦ᵣ raOld) **
        (((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ endPtr) ** Prest))
      (hedWalkNextPost srcBase endPtr raOld srcBytes srcOff ** Extra)) :
    cpsBranchWithin (2 + n + 2) S fullCode
      (((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x1 : Reg) ↦ᵣ raOld) ** Prest)
      (HB + 664) (hedWalkFail srcBase endPtr raOld srcBytes srcOff Extra)
      (S + 20) (hedWalkOk srcBase endPtr raOld srcBytes srcOff Extra) := by
  -- front half: hedWalkCall  (S → S + 12)
  have hfront := hedWalkCall S (srcBase + BitVec.ofNat 64 srcOff) endPtr v10 v11 raOld
    hPrest hMV0 hMV1 hcall
  -- ===== ok continuation: BNE falls through, cursor already saved =====
  have hokc : cpsBranchWithin 2 (S + 12) fullCode
      (fun h => ∃ next len : Word,
        ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) ** ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Extra) **
         ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h)
      (HB + 664) (hedWalkFail srcBase endPtr raOld srcBytes srcOff Extra)
      (S + 20) (hedWalkOk srcBase endPtr raOld srcBytes srcOff Extra) := by
    refine cpsBranchWithin_exists_pre (fun next => ?_)
    refine cpsBranchWithin_exists_pre (fun len => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hdec => ?_)
    have hmv := mv_spec_gen_within .x19 .x10 next (srcBase + BitVec.ofNat 64 srcOff) (S + 12) (by decide)
    rw [show (S + 12) + 4 = S + 16 from by bv_omega] at hmv
    have hmvL := cpsTripleWithin_extend_code hMV2 hmv
    have hmvF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
       ((.x12 : Reg) ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ raOld) **
       bytesRegion srcBase srcBytes ** Extra)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact hExtra | apply pcFree_sepConj)
      hmvL
    have hbne := bne_spec_gen_within .x11 .x0 boff (0 : Word) (0 : Word) (S + 16)
    rw [show (S + 16) + 4 = S + 20 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code hBNE hbne
    have hfall := cpsBranchWithin_ntakenStripPure2 hbneL (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl ((sepConj_pure_right _).1 h_pure).2)
    have hfallF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ next) ** ((.x19 : Reg) ↦ᵣ next) ** ((.x9 : Reg) ↦ᵣ endPtr) **
       ((.x12 : Reg) ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ raOld) **
       bytesRegion srcBase srcBytes ** Extra)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact hExtra | apply pcFree_sepConj)
      hfall
    have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hmvF hfallF
    have hout : cpsTripleWithin 2 (S + 12) (S + 20) fullCode
        (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) ** ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Extra)
        (hedWalkOk srcBase endPtr raOld srcBytes srcOff Extra) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      exact ⟨next, len, (sepConj_pure_right _).2 ⟨by xperm_hyp hq, hdec⟩⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right (HB + 664)
        (hedWalkFail srcBase endPtr raOld srcBytes srcOff Extra) hout)
  -- ===== fail continuation: BNE taken, short-circuit to HB + 664 =====
  have hfailc : cpsBranchWithin 2 (S + 12) fullCode
      (fun h => ∃ st : Word,
        ((((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x11 : Reg) ↦ᵣ st) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Extra) **
         ⌜st ≠ (0 : Word) ∧
           walkStepFail srcBytes endPtr (srcBase + BitVec.ofNat 64 srcOff) srcOff⌝) h)
      (HB + 664) (hedWalkFail srcBase endPtr raOld srcBytes srcOff Extra)
      (S + 20) (hedWalkOk srcBase endPtr raOld srcBytes srcOff Extra) := by
    refine cpsBranchWithin_exists_pre (fun st => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hst => ?_)
    obtain ⟨hst_ne, hfail⟩ := hst
    have hmv := mv_spec_gen_within .x19 .x10 (srcBase + BitVec.ofNat 64 srcOff)
      (srcBase + BitVec.ofNat 64 srcOff) (S + 12) (by decide)
    rw [show (S + 12) + 4 = S + 16 from by bv_omega] at hmv
    have hmvL := cpsTripleWithin_extend_code hMV2 hmv
    have hmvF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ st) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x9 : Reg) ↦ᵣ endPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ raOld) **
       bytesRegion srcBase srcBytes ** Extra)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact hExtra | apply pcFree_sepConj)
      hmvL
    have hbne := bne_spec_gen_within .x11 .x0 boff st (0 : Word) (S + 16)
    rw [htgt, show (S + 16) + 4 = S + 20 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code hBNE hbne
    have htk := cpsBranchWithin_takenStripPure2 hbneL (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact hst_ne ((sepConj_pure_right _).1 h_pure).2)
    have htkF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
       ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x9 : Reg) ↦ᵣ endPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ raOld) **
       bytesRegion srcBase srcBytes ** Extra)
      (by repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact pcFree_regOwn | exact hExtra | apply pcFree_sepConj)
      htk
    have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hmvF htkF
    have hout : cpsTripleWithin 2 (S + 12) (HB + 664) fullCode
        (((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x11 : Reg) ↦ᵣ st) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Extra)
        (hedWalkFail srcBase endPtr raOld srcBytes srcOff Extra) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      refine (sepConj_pure_right _).2 ⟨?_, hfail⟩
      have hq' : ((((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ st) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          (((.x9 : Reg) ↦ᵣ endPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raOld) **
           bytesRegion srcBase srcBytes ** Extra))) h := by xperm_hyp hq
      have hq2 := sepConj_mono (regIs_implies_regOwn .x10)
        (sepConj_mono (regIs_implies_regOwn .x11)
          (sepConj_mono (regIs_implies_regOwn .x12)
            (sepConj_mono (regIs_implies_regOwn .x19) (fun _ x => x)))) h hq'
      xperm_hyp hq2
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_left (S + 20)
        (hedWalkOk srcBase endPtr raOld srcBytes srcOff Extra) hout)
  -- ===== dispatch branch: fold the six callee arms into ok ∨ fail =====
  have hdisp : cpsBranchWithin 2 (S + 12) fullCode
      (((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
        (hedWalkNextPost srcBase endPtr raOld srcBytes srcOff ** Extra))
      (HB + 664) (hedWalkFail srcBase endPtr raOld srcBytes srcOff Extra)
      (S + 20) (hedWalkOk srcBase endPtr raOld srcBytes srcOff Extra) := by
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ x => x) (fun _ x => x)
      (cpsBranchWithin_pre_or hokc hfailc)
    unfold hedWalkNextPost at hp
    obtain ⟨e1, e2, ed, eu, h19, hr1⟩ := hp
    obtain ⟨f1, f2, fd, fu, h9, hr2⟩ := hr1
    obtain ⟨g1, g2, gd, gu, hFD, hExtraPart⟩ := hr2
    obtain ⟨k1, k2, kd, ku, hFrame, hDisj⟩ := hFD
    -- rebuild the whole heap with any chosen `arm` where the disjunction sat.
    have rebuild : ∀ (arm : Assertion), arm k2 →
        (((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
          ((((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
              regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes) ** arm)) ** Extra)) h :=
      fun arm ha => ⟨e1, e2, ed, eu, h19, f1, f2, fd, fu, h9,
        g1, g2, gd, gu, ⟨k1, k2, kd, ku, hFrame, ha⟩, hExtraPart⟩
    rcases hDisj with a1 | a2 | a3 | a4 | a5 | a6
    · -- ok arm
      obtain ⟨next, len, hok⟩ := a1
      refine Or.inl ⟨next, len, ?_⟩
      have hR := rebuild _ hok
      xperm_hyp hR
    · -- status 2: end-of-list  (¬ ult cursor end)
      refine Or.inr ⟨(2 : Word), ?_⟩
      have hR := rebuild _ a2
      have hR2 : ((((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ (2 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Extra) **
         ⌜¬ BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true⌝) h := by xperm_hyp hR
      obtain ⟨hreg, hP⟩ := (sepConj_pure_right _).1 hR2
      exact (sepConj_pure_right _).2 ⟨hreg, by decide, Or.inl hP⟩
    · -- status 3
      refine Or.inr ⟨(3 : Word), ?_⟩
      have hR := rebuild _ a3
      have hR2 : ((((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ (3 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Extra) **
         ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
           endPtr next len⌝) h := by xperm_hyp hR
      obtain ⟨hreg, hP⟩ := (sepConj_pure_right _).1 hR2
      exact (sepConj_pure_right _).2 ⟨hreg, by decide, Or.inr hP⟩
    · -- status 4
      refine Or.inr ⟨(4 : Word), ?_⟩
      have hR := rebuild _ a4
      have hR2 : ((((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ (4 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Extra) **
         ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
           endPtr next len⌝) h := by xperm_hyp hR
      obtain ⟨hreg, hP⟩ := (sepConj_pure_right _).1 hR2
      exact (sepConj_pure_right _).2 ⟨hreg, by decide, Or.inr hP⟩
    · -- status 5
      refine Or.inr ⟨(5 : Word), ?_⟩
      have hR := rebuild _ a5
      have hR2 : ((((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ (5 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Extra) **
         ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
           endPtr next len⌝) h := by xperm_hyp hR
      obtain ⟨hreg, hP⟩ := (sepConj_pure_right _).1 hR2
      exact (sepConj_pure_right _).2 ⟨hreg, by decide, Or.inr hP⟩
    · -- status 6
      refine Or.inr ⟨(6 : Word), ?_⟩
      have hR := rebuild _ a6
      have hR2 : ((((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ (6 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raOld) ** bytesRegion srcBase srcBytes ** Extra) **
         ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
           endPtr next len⌝) h := by xperm_hyp hR
      obtain ⟨hreg, hP⟩ := (sepConj_pure_right _).1 hR2
      exact (sepConj_pure_right _).2 ⟨hreg, by decide, Or.inr hP⟩
  -- ===== assemble: front ;; dispatch =====
  exact cpsTripleWithin_seq_branch_same_cr hfront hdisp

#print axioms hedWalkStep

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
