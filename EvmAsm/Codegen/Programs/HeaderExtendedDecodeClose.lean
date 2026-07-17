/-
  Backbone composition of `headerExtendedDecode_prog` (`Programs/HeaderDecode.lean`,
  PR-K39): the 19-step sequential RLP walk chain (with the nine interleaved field
  extractions) plus the whole-program caller-contract theorem
  `header_extended_decode_spec_within`.

  All leaves are proven (`HeaderExtendedDecode{Prologue,WalkStep,LenCheck,Loop,
  Num,U256,Epilogue,Slots}.lean`).  This module wires a walk step's slot call
  adapter (`hedCall_walkNext_slotN`) to `rlp_walk_next_spec_within` (rebased onto
  `fullCode`, framed) to obtain the `hcall` argument of the corrected walk step
  `hedWalkStep'`, giving the per-field walk-step branch on `fullCode`, then chains
  the sub-blocks.

  `hedWalkStep'` corrects `hedWalkStep`'s single-`raOld` pinning (which forces the
  entry `x1` to equal the step's own JAL-return address) by splitting the entry
  return address `raEntry` from the callee return `raRet`, so consecutive walk
  steps chain on `x1` (`raEntry (k+1) = raRet k`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.HeaderExtendedDecodePrologue
import EvmAsm.Codegen.Programs.HeaderExtendedDecodeWalkStep
import EvmAsm.Codegen.Programs.HeaderExtendedDecodeLenCheck
import EvmAsm.Codegen.Programs.HeaderExtendedDecodeLoop
import EvmAsm.Codegen.Programs.HeaderExtendedDecodeNum
import EvmAsm.Codegen.Programs.HeaderExtendedDecodeU256
import EvmAsm.Codegen.Programs.HeaderExtendedDecodeSlots

namespace EvmAsm.Codegen.HeaderExtendedDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm EvmAsm.EL.RLP

set_option maxRecDepth 8000 in
/-- **Corrected walk-step** (`hedWalkStep` with the entry return address `raEntry`
    split from the callee return `raRet`).  `hedWalkStep` reuses a single `raOld`
    for the entry `x1` and the callee post, which forces `x1 = S+12` (the step's
    own JAL return) at entry — never true between chained steps.  Splitting the
    two lets each step take `raEntry` = its actual incoming `x1` (the previous
    step's return) and produce `raRet = S+12`, so consecutive steps chain
    (`raEntry (k+1) = raRet k`).  Same code/proof as `hedWalkStep`. -/
theorem hedWalkStep' {n : Nat} {Prest Extra : Assertion}
    (S srcBase endPtr raEntry raRet v10 v11 : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (boff : BitVec 13)
    (hExtra : Extra.pcFree) (hPrest : Prest.pcFree)
    (htgt : (S + 16) + signExtend13 boff = HB + 664)
    (hMV0 : ∀ a i, CodeReq.singleton S (.MV .x10 .x19) a = some i → fullCode a = some i)
    (hMV1 : ∀ a i, CodeReq.singleton (S + 4) (.MV .x11 .x9) a = some i → fullCode a = some i)
    (hMV2 : ∀ a i, CodeReq.singleton (S + 12) (.MV .x19 .x10) a = some i → fullCode a = some i)
    (hBNE : ∀ a i, CodeReq.singleton (S + 16) (.BNE .x11 .x0 boff) a = some i → fullCode a = some i)
    (hcall : cpsTripleWithin n (S + 8) (S + 12) fullCode
      (((.x1 : Reg) ↦ᵣ raEntry) **
        (((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ endPtr) ** Prest))
      (hedWalkNextPost srcBase endPtr raRet srcBytes srcOff ** Extra)) :
    cpsBranchWithin (2 + n + 2) S fullCode
      (((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x1 : Reg) ↦ᵣ raEntry) ** Prest)
      (HB + 664) (hedWalkFail srcBase endPtr raRet srcBytes srcOff Extra)
      (S + 20) (hedWalkOk srcBase endPtr raRet srcBytes srcOff Extra) := by
  -- front half: hedWalkCall  (S → S + 12)
  have hfront := hedWalkCall S (srcBase + BitVec.ofNat 64 srcOff) endPtr v10 v11 raEntry
    hPrest hMV0 hMV1 hcall
  -- ===== ok continuation: BNE falls through, cursor already saved =====
  have hokc : cpsBranchWithin 2 (S + 12) fullCode
      (fun h => ∃ next len : Word,
        ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) ** ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raRet) ** bytesRegion srcBase srcBytes ** Extra) **
         ⌜rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff) endPtr next len⌝) h)
      (HB + 664) (hedWalkFail srcBase endPtr raRet srcBytes srcOff Extra)
      (S + 20) (hedWalkOk srcBase endPtr raRet srcBytes srcOff Extra) := by
    refine cpsBranchWithin_exists_pre (fun next => ?_)
    refine cpsBranchWithin_exists_pre (fun len => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hdec => ?_)
    have hmv := mv_spec_gen_within .x19 .x10 next (srcBase + BitVec.ofNat 64 srcOff) (S + 12) (by decide)
    rw [show (S + 12) + 4 = S + 16 from by bv_omega] at hmv
    have hmvL := cpsTripleWithin_extend_code hMV2 hmv
    have hmvF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
       ((.x12 : Reg) ↦ᵣ len) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ raRet) **
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
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ raRet) **
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
          ((.x1 : Reg) ↦ᵣ raRet) ** bytesRegion srcBase srcBytes ** Extra)
        (hedWalkOk srcBase endPtr raRet srcBytes srcOff Extra) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      exact ⟨next, len, (sepConj_pure_right _).2 ⟨by xperm_hyp hq, hdec⟩⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right (HB + 664)
        (hedWalkFail srcBase endPtr raRet srcBytes srcOff Extra) hout)
  -- ===== fail continuation: BNE taken, short-circuit to HB + 664 =====
  have hfailc : cpsBranchWithin 2 (S + 12) fullCode
      (fun h => ∃ st : Word,
        ((((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x11 : Reg) ↦ᵣ st) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x9 : Reg) ↦ᵣ endPtr) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ raRet) ** bytesRegion srcBase srcBytes ** Extra) **
         ⌜st ≠ (0 : Word) ∧
           walkStepFail srcBytes endPtr (srcBase + BitVec.ofNat 64 srcOff) srcOff⌝) h)
      (HB + 664) (hedWalkFail srcBase endPtr raRet srcBytes srcOff Extra)
      (S + 20) (hedWalkOk srcBase endPtr raRet srcBytes srcOff Extra) := by
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
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ raRet) **
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
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x1 : Reg) ↦ᵣ raRet) **
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
          ((.x1 : Reg) ↦ᵣ raRet) ** bytesRegion srcBase srcBytes ** Extra)
        (hedWalkFail srcBase endPtr raRet srcBytes srcOff Extra) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      refine (sepConj_pure_right _).2 ⟨?_, hfail⟩
      have hq' : ((((.x10 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ st) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
          (((.x9 : Reg) ↦ᵣ endPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ raRet) **
           bytesRegion srcBase srcBytes ** Extra))) h := by xperm_hyp hq
      have hq2 := sepConj_mono (regIs_implies_regOwn .x10)
        (sepConj_mono (regIs_implies_regOwn .x11)
          (sepConj_mono (regIs_implies_regOwn .x12)
            (sepConj_mono (regIs_implies_regOwn .x19) (fun _ x => x)))) h hq'
      xperm_hyp hq2
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_left (S + 20)
        (hedWalkOk srcBase endPtr raRet srcBytes srcOff Extra) hout)
  -- ===== dispatch branch: fold the six callee arms into ok ∨ fail =====
  have hdisp : cpsBranchWithin 2 (S + 12) fullCode
      (((.x19 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
        (hedWalkNextPost srcBase endPtr raRet srcBytes srcOff ** Extra))
      (HB + 664) (hedWalkFail srcBase endPtr raRet srcBytes srcOff Extra)
      (S + 20) (hedWalkOk srcBase endPtr raRet srcBytes srcOff Extra) := by
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
              ((.x1 : Reg) ↦ᵣ raRet) ** bytesRegion srcBase srcBytes) ** arm)) ** Extra)) h :=
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
          ((.x1 : Reg) ↦ᵣ raRet) ** bytesRegion srcBase srcBytes ** Extra) **
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
          ((.x1 : Reg) ↦ᵣ raRet) ** bytesRegion srcBase srcBytes ** Extra) **
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
          ((.x1 : Reg) ↦ᵣ raRet) ** bytesRegion srcBase srcBytes ** Extra) **
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
          ((.x1 : Reg) ↦ᵣ raRet) ** bytesRegion srcBase srcBytes ** Extra) **
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
          ((.x1 : Reg) ↦ᵣ raRet) ** bytesRegion srcBase srcBytes ** Extra) **
         ⌜¬ ∃ next len, rlpItemDecode srcBytes srcOff (srcBase + BitVec.ofNat 64 srcOff)
           endPtr next len⌝) h := by xperm_hyp hR
      obtain ⟨hreg, hP⟩ := (sepConj_pure_right _).1 hR2
      exact (sepConj_pure_right _).2 ⟨hreg, by decide, Or.inr hP⟩
  -- ===== assemble: front ;; dispatch =====
  exact cpsTripleWithin_seq_branch_same_cr hfront hdisp

#print axioms hedWalkStep'

set_option maxRecDepth 8000 in
/-- The first sequential-walk step (field 0, parent_hash), `S = HB + 48`
    (slots 12-16), `jal rlp_walk_next` at slot 14 (`HB + 56`, return `HB + 60`).
    Builds `hcall` from `hedCall_walkNext_slot14` + `rlp_walk_next_spec_within` and
    feeds `hedWalkStep'`.  `raEntry` is the actual incoming `x1` (the prologue's
    `rlp_walk_init` return `HB + 36`); `raRet = HB + 60`. -/
theorem hedWalk0 {Extra : Assertion}
    (hdrBase endPtr raEntry a2junk t0 t1 t2 t3 t4 t5 t6 v10 v11 : Word)
    (listBytes : List (BitVec 8)) (srcOff : Nat)
    (hExtra : Extra.pcFree)
    (hsalign : hdrBase.toNat % 8 = 0)
    (hoff : srcOff < listBytes.length)
    (hover : hdrBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (hdrBase + BitVec.ofNat 64 srcOff) = true)
    (hss : ¬ BitVec.ult ((listBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true →
        BitVec.ult ((listBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        srcOff + 1 < listBytes.length ∧ hdrBase.toNat + (srcOff + 1) < 2 ^ 64 ∧
          isValidByteAccess (hdrBase + BitVec.ofNat 64 (srcOff + 1)) = true)
    (hls : ¬ BitVec.ult ((listBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true →
        BitVec.ult ((listBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true →
        srcOff + 1 + ((listBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
          ≤ listBytes.length ∧
        hdrBase.toNat + (srcOff + 1 +
          ((listBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((listBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
          isValidByteAccess (hdrBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true)
    (hll : ¬ BitVec.ult ((listBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        srcOff + 1 + ((listBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ listBytes.length ∧
        hdrBase.toNat + (srcOff + 1 +
          ((listBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64 ∧
        ∀ k, k < ((listBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (hdrBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsBranchWithin (2 + (1 + 87) + 2) (HB + 48) fullCode
      (((.x19 : Reg) ↦ᵣ (hdrBase + BitVec.ofNat 64 srcOff)) ** ((.x9 : Reg) ↦ᵣ endPtr) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x1 : Reg) ↦ᵣ raEntry) **
        (((.x12 : Reg) ↦ᵣ a2junk) ** ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) **
          ((.x7 : Reg) ↦ᵣ t2) ** ((.x28 : Reg) ↦ᵣ t3) ** ((.x29 : Reg) ↦ᵣ t4) **
          ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion hdrBase listBytes ** Extra))
      (HB + 664) (hedWalkFail hdrBase endPtr (HB + 60) listBytes srcOff Extra)
      (HB + 68) (hedWalkOk hdrBase endPtr (HB + 60) listBytes srcOff Extra) := by
  set Prest : Assertion :=
    ((.x12 : Reg) ↦ᵣ a2junk) ** ((.x5 : Reg) ↦ᵣ t0) ** ((.x6 : Reg) ↦ᵣ t1) **
      ((.x7 : Reg) ↦ᵣ t2) ** ((.x28 : Reg) ↦ᵣ t3) ** ((.x29 : Reg) ↦ᵣ t4) **
      ((.x30 : Reg) ↦ᵣ t5) ** ((.x31 : Reg) ↦ᵣ t6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion hdrBase listBytes ** Extra with hPrestDef
  have hPrest : Prest.pcFree := by
    rw [hPrestDef]
    repeat' first | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact hExtra | apply pcFree_sepConj
  have hspec := rlp_walk_next_spec_within WNB hdrBase endPtr (HB + 60) a2junk t0 t1 t2 t3 t4 t5 t6
    listBytes srcOff hsalign hoff hover hvalid hss hls hll
  have hspecF := cpsTripleWithin_frameR Extra hExtra hspec
  have hcallee : cpsTripleWithin 87 WNB ((HB + 56 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WNB)
      (((.x1 : Reg) ↦ᵣ (HB + 56 + 4)) **
        (((.x10 : Reg) ↦ᵣ (hdrBase + BitVec.ofNat 64 srcOff)) **
          ((.x11 : Reg) ↦ᵣ endPtr) ** Prest))
      (hedWalkNextPost hdrBase endPtr (HB + 60) listBytes srcOff ** Extra) := by
    rw [show (HB + 56 + 4 : Word) = HB + 60 from by bv_omega]
    refine cpsTripleWithin_weaken (fun h hp => by rw [hPrestDef] at hp; xperm_hyp hp)
      (fun _ x => x) hspecF
  have hcall := hedCall_walkNext_slot14 (n := 87) raEntry
    (Prest := ((.x10 : Reg) ↦ᵣ (hdrBase + BitVec.ofNat 64 srcOff)) **
      ((.x11 : Reg) ↦ᵣ endPtr) ** Prest)
    (by
      repeat' first
        | exact bytesRegion_pcFree _ _ | exact pcFree_regIs | exact hPrest | apply pcFree_sepConj)
    (by rw [show (HB + 56 + 4 : Word) = HB + 60 from by bv_omega]; exact hcallee)
  rw [show (HB + 56 + 4 : Word) = HB + 60 from by bv_omega] at hcall
  have htgt : ((HB + 48) + 16) + signExtend13 (600 : BitVec 13) = HB + 664 := by
    rw [show signExtend13 (600 : BitVec 13) = (600 : Word) from by decide]; bv_omega
  refine hedWalkStep' (HB + 48) hdrBase endPtr raEntry (HB + 60) v10 v11 listBytes srcOff
    (600 : BitVec 13) hExtra hPrest htgt ?_ ?_ ?_ ?_ ?_
  · exact fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 48) headerExtendedDecode_prog 12 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  · exact fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 52) headerExtendedDecode_prog 13 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  · exact fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 60) headerExtendedDecode_prog 15 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  · exact fun a i h => hed_mono a i
      (CodeReq.ofProg_mem_at HB (HB + 64) headerExtendedDecode_prog 16 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h)
  · rw [show (HB + 48 + 8 : Word) = HB + 56 from by bv_omega,
        show (HB + 48 + 12 : Word) = HB + 60 from by bv_omega]
    exact hcall

#print axioms hedWalk0

end EvmAsm.Codegen.HeaderExtendedDecodeSpec
