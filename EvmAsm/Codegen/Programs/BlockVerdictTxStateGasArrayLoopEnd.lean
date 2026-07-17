/-
  Loop end-offset path + bal=0 tail for `block_verdict_tx_state_gas_array` (a4gbr).
  Split for Codegen/Programs 1500-line file-size guard.
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayLoop
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec
  (wordArray wordArrayFrom wordArray_split pcFree_wordArray pcFree_wordArrayFrom)

local macro "bvt_pcf" : tactic => `(tactic|
  repeat' first
    | exact pcFree_stackFree _ _
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_regOwns _
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact bytesRegion_pcFree _ _
    | exact pcFree_wordArray _ _
    | exact pcFree_wordArrayFrom _ _ _
    | exact pcFree_emp
    | exact pcFree_pure
    | unfold payload; skip
    | unfold savedFrame; skip
    | unfold scratchRegs; skip)

set_option maxRecDepth 8000 in
/-- Non-last end path: `i+1 ≠ n`. ADDI; BEQ ntaken; SLLI/ADD; bgv@LinkLoopBgv2;
    MV x23; JAL skip → AfterEndOffset with `x23 = leU32(4*(i+1))`. -/

theorem bvtIterEndNext (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (startW tableW old6 old10 : Word)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : IterOk txBlob n i)
    (hNext : i + 1 ≠ n)
    (hnW : nW = BitVec.ofNat 64 n)
    (_hStart : startW = leU32 txBlob (4 * i))
    (_htab : tableW = BitVec.ofNat 64 (4 * n))
    (htxAlign : txBase.toNat % 8 = 0) :
    let iW := BitVec.ofNat 64 i
    let endW := leU32 txBlob (4 * (i + 1))
    let lenW := BitVec.ofNat 64 txBlob.length
    cpsTripleWithin (2 + 2 + (1 + nBgvSteps) + 2) AfterSpanChecks AfterEndOffset
      fullCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ old10) **
        (.x5 ↦ᵣ tableW) ** (.x6 ↦ᵣ old6) ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro iW endW lenW
  let ip1W : Word := BitVec.ofNat 64 (i + 1)
  let loadPtr := txBase + BitVec.ofNat 64 (4 * (i + 1))
  have hip1_ne : ip1W ≠ nW := by
    intro heq
    apply hNext
    have hi1 : i + 1 < 2 ^ 64 := by
      have := hok.hi; have := hok.hNBound; omega
    have hn : n < 2 ^ 64 := by
      have := hok.hNBound; omega
    have hEqNat : (BitVec.ofNat 64 (i + 1)).toNat = (BitVec.ofNat 64 n).toNat := by
      have := congrArg BitVec.toNat heq
      simp only [ip1W, hnW] at this
      exact this
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi1,
      Nat.mod_eq_of_lt hn] at hEqNat
    exact hEqNat
  have hEndOff : 4 * (i + 1) + 4 ≤ txBlob.length := by
    rcases hok.hEndOff with h | h
    · exact False.elim (hNext h)
    · exact h
  have hNoWrapN : txBase.toNat + 4 * (i + 1) + 3 < 2 ^ 64 := by
    rcases hok.hNoWrapNext with h | h
    · exact False.elim (hNext h)
    · exact h txBase htxAlign
  have hValidN : ∀ k, k < 4 →
      isValidByteAccess (txBase + BitVec.ofNat 64 (4 * (i + 1) + k)) = true := by
    rcases hok.hValidNext with h | h
    · exact False.elim (hNext h)
    · exact fun k hk => h txBase k hk
  have hip1_lt : i + 1 < 2 ^ 62 := by
    have := hok.hi; have := hok.hNBound; omega
  -- [40] ADDI x5, x21, 1
  have e40 :
      cpsTripleWithin 1 AfterSpanChecks (AfterSpanChecks + 4) bvtCode
        ((.x21 ↦ᵣ iW) ** (.x5 ↦ᵣ tableW))
        ((.x21 ↦ᵣ iW) ** (.x5 ↦ᵣ ip1W)) := by
    have h0 := addi_spec_gen_within .x5 .x21 tableW iW (1 : BitVec 12)
      AfterSpanChecks (by decide)
    rw [ofNat_addi1 i] at h0
    exact cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at B AfterSpanChecks bvtProg 40
        (.ADDI .x5 .x21 (1 : BitVec 12))
        (by simp only [AfterSpanChecks]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide)) h0
  have e40F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ old10) **
      (.x6 ↦ᵣ old6) ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e40
  -- [41] BEQ ntaken
  have hbr41 := beq_spec_gen_within .x5 .x20 (24 : BitVec 13) ip1W nW (B + 164)
  have hbr41C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 164) bvtProg 41
      (.BEQ .x5 .x20 (24 : BitVec 13))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr41
  have hnt41 : cpsTripleWithin 1 (B + 164) (B + 168) bvtCode
      ((.x5 ↦ᵣ ip1W) ** (.x20 ↦ᵣ nW))
      ((.x5 ↦ᵣ ip1W) ** (.x20 ↦ᵣ nW)) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr41C (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hrest).2 hip1_ne)
    have hpc : B + 164 + 4 = B + 168 := by bv_omega
    rwa [hpc] at hnt
  have e41F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ old10) **
      (.x6 ↦ᵣ old6) ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) hnt41
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e40F e41F
  have c01C := cpsTripleWithin_extend_code bvt_mono c01
  -- [42] SLLI x6, x5, 2
  have hslli := slli2_ofNat (i + 1) hip1_lt
  have e42 := slli_spec_gen_within .x6 .x5 old6 ip1W (2 : BitVec 6)
    (B + 168) (by decide)
  rw [show (2 : BitVec 6).toNat = 2 from by decide, hslli] at e42
  have e42C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 168) bvtProg 42
      (.SLLI .x6 .x5 (2 : BitVec 6))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e42
  have e42F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ old10) **
      regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e42C
  -- [43] ADD x10, x8, x6
  have e43 := add_spec_gen_within .x10 .x8 .x6 txBase
    (BitVec.ofNat 64 (4 * (i + 1))) old10 (B + 172) (by decide)
  have e43C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 172) bvtProg 43
      (.ADD .x10 .x8 .x6)
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e43
  have e43F := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ LinkLoopBgv1) **
      (.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x5 ↦ᵣ ip1W) **
      regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
      regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e43C
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e42F e43F
  have c02C := cpsTripleWithin_extend_code bvt_mono c02
  -- reshape setup post → call pre (pack scratch; peel payload)
  have hsetup' : cpsTripleWithin 2 (B + 168) (B + 176) fullCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x10 ↦ᵣ old10) **
        (.x5 ↦ᵣ ip1W) ** (.x6 ↦ᵣ old6) ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
        regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x10 ↦ᵣ loadPtr) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ c02C
    intro h hq
    unfold payload at hq
    have hq1 :
        (((.x5 ↦ᵣ ip1W) ** (.x6 ↦ᵣ BitVec.ofNat 64 (4 * (i + 1))) ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17) **
          ((.x1 ↦ᵣ LinkLoopBgv1) ** (.x10 ↦ᵣ loadPtr) **
            bytesRegion txBase txBlob **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** regOwn .x23 **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            wordArray outBase outVals **
            (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
            (.x0 ↦ᵣ (0 : Word)))) h := by
      xperm_hyp hq
    -- x5 ** (x6 ** restTemps) → x5 ** (regOwn x6 ** restTemps)
    have hq2 :
        (((.x5 ↦ᵣ ip1W) ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x15 ** regOwn .x16 ** regOwn .x17) **
          ((.x1 ↦ᵣ LinkLoopBgv1) ** (.x10 ↦ᵣ loadPtr) **
            bytesRegion txBase txBlob **
            (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** regOwn .x23 **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            wordArray outBase outVals **
            (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
            (.x0 ↦ᵣ (0 : Word)))) h := by
      refine sepConj_mono ?_ (fun _ hh => hh) h hq1
      intro h0 hp0
      -- left is x5 ** (x6 ** restTemps); convert middle x6 to regOwn
      refine sepConj_mono (fun _ => id) ?_ h0 hp0
      intro h1 hp1
      exact sepConj_mono
        (regIs_to_regOwn .x6 (BitVec.ofNat 64 (4 * (i + 1))))
        (fun _ => id) h1 hp1
    have hq3 :=
      sepConj_mono (pack_loop_bgvScratch_is ip1W)
        (fun _ hh => hh) h hq2
    xperm_hyp hq3
  -- Bgv call
  have hflat := hbgv.success_flat LinkLoopBgv2 loadPtr txBase txBlob (4 * (i + 1))
    (by show LinkLoopBgv2 &&& ~~~(1 : Word) = LinkLoopBgv2; decide)
    rfl hEndOff htxAlign hNoWrapN hValidN
  have hframe :
      (((.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) ** regOwn .x23 **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          wordArray outBase outVals **
          (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
          (.x0 ↦ᵣ (0 : Word))) : Assertion).pcFree := by
    unfold savedFrame; cases balEnabled <;> bvt_pcf
  have hflatF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** regOwn .x23 **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      wordArray outBase outVals **
      (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
      (.x0 ↦ᵣ (0 : Word)))
    hframe hflat
  have hcallee : cpsTripleWithin nBgvSteps Bgv LinkLoopBgv2 fullCode
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        ((.x10 ↦ᵣ loadPtr) ** regOwns bgvScratch **
          bytesRegion txBase txBlob **
          ((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** regOwn .x23 **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            wordArray outBase outVals **
            (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
            (.x0 ↦ᵣ (0 : Word)))))
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        ((.x10 ↦ᵣ endW) ** regOwns bgvScratch **
          bytesRegion txBase txBlob **
          ((.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
            (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
            (.x22 ↦ᵣ startW) ** regOwn .x23 **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
            savedFrame spC csaved **
            stackFree spC nCalleeStackDwords **
            wordArray outBase outVals **
            (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
            (.x0 ↦ᵣ (0 : Word))))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hflatF
  have hcall : cpsTripleWithin (1 + nBgvSteps) (B + 176) LinkLoopBgv2 fullCode
      ((.x1 ↦ᵣ LinkLoopBgv1) **
        (.x10 ↦ᵣ loadPtr) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** regOwn .x23 **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word))) := by
    have h0 := callWithin_spec (B + 176) Bgv LinkLoopBgv1 loopBgv2JalOff nBgvSteps
      (by show (B + 176) + signExtend21 loopBgv2JalOff = Bgv; decide)
      (fun a off hi => bvt_mono a off
        (CodeReq.ofProg_mem_at B (B + 176) bvtProg 44
          (.JAL .x1 loopBgv2JalOff) (by bv_omega)
          (by rw [bvt_length]; decide) rfl
          (by rw [bvt_length]; decide) a off hi))
      (by
        apply pcFree_sepConj
        · exact pcFree_regIs
        · apply pcFree_sepConj
          · exact pcFree_regOwns _
          · apply pcFree_sepConj
            · exact bytesRegion_pcFree _ _
            · exact hframe)
      hcallee
    rw [show (B + 176 + 4 : Word) = LinkLoopBgv2 from by
      simp only [LinkLoopBgv2]; bv_omega] at h0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0
  -- [45] MV x23, x10
  have e45Own : cpsTripleWithin 1 LinkLoopBgv2 (B + 184) fullCode
      (((.x1 ↦ᵣ LinkLoopBgv2) **
          (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
          bytesRegion txBase txBlob **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
          (.x22 ↦ᵣ startW) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          wordArray outBase outVals **
          (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
          (.x0 ↦ᵣ (0 : Word))) **
        regOwn .x23)
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x23) (fun o23 => ?_)
    have e45 := mv_spec_gen_within .x23 .x10 endW o23 LinkLoopBgv2 (by decide)
    have e45C := cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at B LinkLoopBgv2 bvtProg 45
        (.MV .x23 .x10)
        (by simp only [LinkLoopBgv2]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide)) e45
    have e45F := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ LinkLoopBgv2) **
        regOwns bgvScratch **
        bytesRegion txBase txBlob **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        wordArray outBase outVals **
        (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
        (.x0 ↦ᵣ (0 : Word)))
      (by unfold savedFrame; cases balEnabled <;> bvt_pcf) e45C
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code bvt_mono e45F)
  -- [46] JAL x0, +8 → AfterEndOffset
  have e46 :
      cpsTripleWithin 1 (B + 184) AfterEndOffset fullCode
        empAssertion empAssertion := by
    have h0 := jal_x0_spec_gen_within (8 : BitVec 21) (B + 184)
    have hpc : B + 184 + signExtend21 (8 : BitVec 21) = AfterEndOffset := by
      simp only [AfterEndOffset]
      rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
      bv_omega
    rw [hpc] at h0
    have hmem := CodeReq.ofProg_mem_at B (B + 184) bvtProg 46
      (.JAL .x0 (8 : BitVec 21))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)
    exact cpsTripleWithin_extend_code
      (fun a off hi => bvt_mono a off (hmem a off hi)) h0
  let ambient : Assertion :=
    (.x1 ↦ᵣ LinkLoopBgv2) **
      (.x10 ↦ᵣ endW) ** regOwns bgvScratch **
      bytesRegion txBase txBlob **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      wordArray outBase outVals **
      (if balEnabled then bytesRegion balBase balBytes else empAssertion) **
      (.x0 ↦ᵣ (0 : Word))
  have e46F : cpsTripleWithin 1 (B + 184) AfterEndOffset fullCode
      ambient ambient := by
    have h0 := cpsTripleWithin_frameR ambient
      (by unfold ambient savedFrame; cases balEnabled <;> bvt_pcf) e46
    -- frameR gives ambient ** emp; cancel emp via equality
    exact cpsTripleWithin_weaken
      (fun h hp => by
        -- ambient → emp ** ambient
        show (empAssertion ** ambient) h
        rwa [sepConj_emp_left' ambient])
      (fun h hq => by
        -- emp ** ambient → ambient
        have hq' : (empAssertion ** ambient) h := hq
        rwa [sepConj_emp_left' ambient] at hq')
      h0
  -- Compose: c01 ;; setup' ;; call ;; mv ;; jal
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01C hsetup'
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c03 hcall
  have c05 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c04 e45Own
  have c06 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c05 e46F
  change cpsTripleWithin
    ((1 + 1) + (2 + ((1 + nBgvSteps) + (1 + 1)))) AfterSpanChecks AfterEndOffset
    fullCode _ _ at c06
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      unfold ambient at hq
      xperm_hyp hq) c06

/-! ## End-offset span checks + intrinsic ABI setup (instr 48–53) -/

abbrev AfterEndSpan : Word := B + 216

/-- Pure: `¬ ult endW startW` when `startW.toNat ≤ endW.toNat`. -/
private theorem not_ult_end_start (startW endW : Word)
    (hGe : startW.toNat ≤ endW.toNat) :
    ¬ (BitVec.ult endW startW = true) := by
  simp only [BitVec.ult, decide_eq_true_eq, not_lt]
  omega

/-- Pure: `¬ ult lenW endW` when `endW.toNat ≤ len` and `lenW = ofNat len`. -/
private theorem not_ult_len_end (endW lenW : Word) (len : Nat)
    (hlen : lenW = BitVec.ofNat 64 len) (hLenBound : len < 2 ^ 64)
    (hLe : endW.toNat ≤ len) :
    ¬ (BitVec.ult lenW endW = true) := by
  simp only [BitVec.ult, decide_eq_true_eq, not_lt, hlen, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hLenBound]
  omega

/-- Pure: `ofNat i <<< 3 = ofNat (8*i)` when `i < 2^61`. -/
theorem slli3_ofNat (i : Nat) (hi : i < 2 ^ 61) :
    BitVec.ofNat 64 i <<< (3 : Nat) = BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hi' : i < 2 ^ 64 := by omega
  have h8i : 8 * i < 2 ^ 64 := by
    have : i * 8 < 2 ^ 61 * 8 := Nat.mul_lt_mul_of_pos_right hi (by decide)
    omega
  rw [Nat.mod_eq_of_lt hi', Nat.shiftLeft_eq, show 2 ^ (3 : Nat) = 8 from rfl,
    Nat.mod_eq_of_lt h8i]
  omega

set_option maxRecDepth 8000 in
/-- End span checks + ABI setup for intrinsic (instr 48–53).
    Lands at AfterEndSpan with a0=txBase+start, a1=end-start, a2=outBase+8*i.
    Requires `i < 2^61` so `8*i` fits in a Word (stricter than IterOk `n < 2^62`). -/
theorem bvtIterEndSpanSetup (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) (n i : Nat)
    (startW endW old5 old10 old11 old12 : Word)
    (hok : IterOk txBlob n i)
    (hStart : startW = hok.startW)
    (hEnd : endW = hok.endW)
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let lenW := BitVec.ofNat 64 txBlob.length
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    cpsTripleWithin 6 AfterEndOffset AfterEndSpan bvtCode
      ((.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        payload txBase outBase balBase txBlob outVals balBytes balEnabled **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro iW lenW txPtr txLenW outPtr
  -- Align IterOk start/end with concrete regs
  have hGe' : startW.toNat ≤ endW.toNat := by
    simpa [hStart, hEnd] using hok.hEndGeStart
  have hLe' : endW.toNat ≤ txBlob.length := by
    simpa [hEnd] using hok.hEndLeLen
  have hnot1 := not_ult_end_start startW endW hGe'
  have hnot2 := not_ult_len_end endW lenW txBlob.length rfl hok.hLenBound hLe'
  have hslli3 := slli3_ofNat i hi61
  -- Ambient frame atoms shared by all steps (scratch focus peels per instr)
  let ambient : Assertion :=
    (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word))
  have hAmb : ambient.pcFree := by
    unfold ambient savedFrame payload; cases balEnabled <;> bvt_pcf
  -- [48] BLTU x23, x22 ntaken  (focus x23,x22 — exclude from frame)
  have hbr48 := bltu_spec_gen_within .x23 .x22 (112 : BitVec 13) endW startW
    AfterEndOffset
  have hbr48C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B AfterEndOffset bvtProg 48
      (.BLTU .x23 .x22 (112 : BitVec 13))
      (by simp only [AfterEndOffset]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr48
  have hnt48 : cpsTripleWithin 1 AfterEndOffset (B + 196) bvtCode
      ((.x23 ↦ᵣ endW) ** (.x22 ↦ᵣ startW))
      ((.x23 ↦ᵣ endW) ** (.x22 ↦ᵣ startW)) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr48C (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hrest).2 hnot1)
    have hpc : AfterEndOffset + 4 = B + 196 := by
      simp only [AfterEndOffset]; bv_omega
    rwa [hpc] at hnt
  have e48F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) hnt48
  -- [49] BLTU x9, x23 ntaken  (focus x9,x23)
  have hbr49 := bltu_spec_gen_within .x9 .x23 (108 : BitVec 13) lenW endW (B + 196)
  have hbr49C := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 196) bvtProg 49
      (.BLTU .x9 .x23 (108 : BitVec 13))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr49
  have hnt49 : cpsTripleWithin 1 (B + 196) (B + 200) bvtCode
      ((.x9 ↦ᵣ lenW) ** (.x23 ↦ᵣ endW))
      ((.x9 ↦ᵣ lenW) ** (.x23 ↦ᵣ endW)) := by
    have hnt := cpsBranchWithin_ntakenStripPure2 hbr49C (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hrest⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hrest).2 hnot2)
    have hpc : B + 196 + 4 = B + 200 := by bv_omega
    rwa [hpc] at hnt
  have e49F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) hnt49
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e48F e49F
  -- [50] ADD x10, x8, x22  (focus x10,x8,x22)
  have e50 := add_spec_gen_within .x10 .x8 .x22 txBase startW old10 (B + 200) (by decide)
  have e50C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 200) bvtProg 50
      (.ADD .x10 .x8 .x22)
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e50
  have e50F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x5 ↦ᵣ old5) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e50C
  -- [51] SUB x11, x23, x22  (focus x11,x23,x22)
  have e51 := sub_spec_gen_within .x11 .x23 .x22 endW startW old11 (B + 204) (by decide)
  have e51C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 204) bvtProg 51
      (.SUB .x11 .x23 .x22)
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e51
  have e51F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x5 ↦ᵣ old5) ** (.x10 ↦ᵣ (txBase + startW)) ** (.x12 ↦ᵣ old12) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e51C
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e50F e51F
  -- [52] SLLI x5, x21, 3  (focus x5,x21)
  have e52 := slli_spec_gen_within .x5 .x21 old5 iW (3 : BitVec 6) (B + 208) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 from by decide, hslli3] at e52
  have e52C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 208) bvtProg 52
      (.SLLI .x5 .x21 (3 : BitVec 6))
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e52
  have e52F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ (txBase + startW)) ** (.x11 ↦ᵣ (endW - startW)) ** (.x12 ↦ᵣ old12) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e52C
  -- [53] ADD x12, x19, x5  (focus x12,x19,x5)
  have e53 := add_spec_gen_within .x12 .x19 .x5 outBase (BitVec.ofNat 64 (8 * i))
    old12 (B + 212) (by decide)
  have e53C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 212) bvtProg 53
      (.ADD .x12 .x19 .x5)
      (by bv_omega) (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e53
  have e53F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ lenW) **
      (.x18 ↦ᵣ nW) **
      (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      (.x10 ↦ᵣ (txBase + startW)) ** (.x11 ↦ᵣ (endW - startW)) **
      regOwn .x1 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      payload txBase outBase balBase txBlob outVals balBytes balEnabled **
      (.x0 ↦ᵣ (0 : Word)))
    (by unfold savedFrame payload; cases balEnabled <;> bvt_pcf) e53C
  have c02' := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e50F e51F
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) e52F e53F
  have c12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c01 c02'
  have c13 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) c12 c03
  change cpsTripleWithin ((1 + 1) + ((1 + 1) + (1 + 1))) AfterEndOffset AfterEndSpan
    bvtCode _ _ at c13
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c13

/-! ## Intrinsic call (instr 54) under IntrinsicAssumed -/

abbrev intrinsicJalOff : BitVec 21 :=
  jalOff GuestAddrs.tx_intrinsic_state_gas
    (GuestAddrs.block_verdict_tx_state_gas_array + 216)

/-- Caller-private frame across intrinsic (non-saved temps + end + bal + saved).
    sp + stackFree + s0–s6 (x8/x9/x18–x22) ride in the callee footprint
    (IntrinsicAssumed now owns them for dischargeability).
    Ambient tx region + out cell + ABI a-regs also in callee footprint.
    Unused binder names kept for call-site positional stability. -/
def loopIntrinsicFrame (spC _txBase _outBase balBase chainIdW _nW _iW
    _startW endW _lenW : Word)
    (csaved : Saved) (balBytes : List (BitVec 8)) (balEnabled : Bool)
    : Assertion :=
  -- x8/x9/x18–x22 are in IntrinsicAssumed (leaf save/restore); not here.
  (.x23 ↦ᵣ endW) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  regOwn .x17 **
  savedFrame spC csaved **
  (if balEnabled then bytesRegion balBase balBytes else empAssertion)
  -- x0 stays in the callee footprint (not framed) to avoid double-own.
  -- x17 is not in IntrinsicAssumed footprint; frame it across the call.
  -- x2 + stackFree + s-regs are in the callee footprint (framed leaf).

theorem loopIntrinsicFrame_pcFree (spC txBase outBase balBase chainIdW nW iW
    startW endW lenW : Word)
    (csaved : Saved) (balBytes : List (BitVec 8)) (balEnabled : Bool) :
    (loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
      startW endW lenW csaved balBytes balEnabled).pcFree := by
  unfold loopIntrinsicFrame savedFrame
  cases balEnabled <;> bvt_pcf

set_option maxRecDepth 8000 in
/-- Intrinsic success call (instr 54) under framed `IntrinsicAssumed`.
    Pre: sp + stackFree 8 + s0–s6 + full `bytesRegion txBase txBlob` + out cell.
    Post: a0=0, *out=pure, sp+stackFree+s-regs restored, ambient tx preserved. -/
theorem bvtIterIntrinsic
    (hintr : IntrinsicAssumed fullCode)
    (spC txBase outBase balBase chainIdW nW bodyLenW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (balBytes : List (BitVec 8))
    (balEnabled : Bool) (i off len : Nat)
    (startW endW oldOut old1 : Word)
    (hentry : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hret : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hstart : startW = BitVec.ofNat 64 off)
    (hlen : off + len ≤ txBlob.length)
    (htxLen : endW - startW = BitVec.ofNat 64 len) :
    let iW := BitVec.ofNat 64 i
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    cpsTripleWithin (1 + nIntrinsicSteps) AfterEndSpan LinkIntrinsic fullCode
      ((.x1 ↦ᵣ old1) **
        (.x2 ↦ᵣ spC) ** stackFree spC nIntrinsicStackDwords **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        bytesRegion txBase txBlob **
        (outPtr ↦ₘ oldOut) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW csaved balBytes balEnabled)
      ((.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) ** stackFree spC nIntrinsicStackDwords **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBlob **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW csaved balBytes balEnabled) := by
  intro iW txPtr txLenW outPtr
  have hload : txPtr = txBase + BitVec.ofNat 64 off := by
    simp only [txPtr, hstart]
  have hlenW : txLenW = BitVec.ofNat 64 len := by
    simp only [txLenW, htxLen]
  have hflat0 := hintr.success_flat LinkIntrinsic spC txBase txPtr outPtr oldOut
    txBase bodyLenW nW outBase nW iW startW
    txBlob off len hret hload hlen
  have hflatLen : cpsTripleWithin nIntrinsicSteps hintr.entry LinkIntrinsic fullCode
      ((.x1 ↦ᵣ LinkIntrinsic) ** (.x2 ↦ᵣ spC) **
        stackFree spC nIntrinsicStackDwords **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ outPtr) ** bytesRegion txBase txBlob **
        (outPtr ↦ₘ oldOut) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkIntrinsic) ** (.x2 ↦ᵣ spC) **
        stackFree spC nIntrinsicStackDwords **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBlob **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) := by
    simpa [hlenW] using hflat0
  have hflatF := cpsTripleWithin_frameR
    (loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
      startW endW bodyLenW csaved balBytes balEnabled)
    (loopIntrinsicFrame_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _) hflatLen
  have hcallee : cpsTripleWithin nIntrinsicSteps hintr.entry LinkIntrinsic fullCode
      ((.x1 ↦ᵣ LinkIntrinsic) **
        ((.x2 ↦ᵣ spC) ** stackFree spC nIntrinsicStackDwords **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
          (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) **
          (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
          bytesRegion txBase txBlob ** (outPtr ↦ₘ oldOut) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
            startW endW bodyLenW csaved balBytes balEnabled))
      ((.x1 ↦ᵣ LinkIntrinsic) **
        ((.x2 ↦ᵣ spC) ** stackFree spC nIntrinsicStackDwords **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
          (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBlob **
          (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x15 ** regOwn .x16 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (.x0 ↦ᵣ (0 : Word)) **
          loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
            startW endW bodyLenW csaved balBytes balEnabled)) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hflatF
  have hcall := callWithin_spec AfterEndSpan hintr.entry old1 intrinsicJalOff
    nIntrinsicSteps
    (by
      rw [hentry]
      show AfterEndSpan + signExtend21 intrinsicJalOff =
        (GuestAddrs.tx_intrinsic_state_gas : Word)
      simp only [AfterEndSpan, intrinsicJalOff, B]
      decide)
    (fun a off' hi => bvt_mono a off'
      (CodeReq.ofProg_mem_at B AfterEndSpan bvtProg 54
        (.JAL .x1 intrinsicJalOff)
        (by simp only [AfterEndSpan]; bv_omega)
        (by rw [bvt_length]; decide) rfl
        (by rw [bvt_length]; decide) a off' hi))
    (by
      unfold loopIntrinsicFrame savedFrame
      cases balEnabled <;> bvt_pcf)
    hcallee
  have hlink : AfterEndSpan + 4 = LinkIntrinsic := by
    simp only [AfterEndSpan, LinkIntrinsic]; bv_omega
  rw [hlink] at hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hcall

/-! ## Post-intrinsic bal=0 success tail (instr 55–56 + 72–73)

    a0=0 → BNE ntaken; bal=0 → BEQ taken → LoopAdvance; ADDI i++; back-edge.
    Post keeps concrete temps (convert to regOwn at LoopInv glue).
-/

abbrev AfterIntrinsicBne : Word := B + 224
abbrev LoopAdvance : Word := B + 288

/-- Caller-private footprint for the bal=0 tail (no x0/x10/x24 focus regs).
    Carries full nested free stack (`nCalleeStackDwords`) for LoopInv reassembly. -/
def bal0Rest (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balLenW startW endW iW : Word) : Assertion :=
  (.x1 ↦ᵣ LinkIntrinsic) **
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ nW) ** (.x21 ↦ᵣ iW) **
  (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
  (.x25 ↦ᵣ balLenW) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  savedFrame spC csaved **
  stackFree spC nCalleeStackDwords **
  bytesRegion txBase txBlob **
  wordArray outBase outVals **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31

theorem bal0Rest_pcFree (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balLenW startW endW iW : Word) :
    (bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
      balLenW startW endW iW).pcFree := by
  unfold bal0Rest savedFrame
  bvt_pcf

set_option maxRecDepth 8000 in
/-- Instr 55: BNE a0,x0 ntaken when a0=0 → AfterIntrinsicBne. -/
theorem bvtIterBneOk
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balLenW startW endW iW : Word) :
    cpsTripleWithin 1 LinkIntrinsic AfterIntrinsicBne bvtCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          balLenW startW endW iW)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          balLenW startW endW iW) := by
  have hbr := bne_spec_gen_within .x10 .x0 (100 : BitVec 13)
    (0 : Word) (0 : Word) LinkIntrinsic
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B LinkIntrinsic bvtProg 55
      (.BNE .x10 .x0 (100 : BitVec 13))
      (by simp only [LinkIntrinsic]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrC (fun _ hQt => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQt
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : LinkIntrinsic + 4 = AfterIntrinsicBne := by
    simp only [LinkIntrinsic, AfterIntrinsicBne]; bv_omega
  rw [hpc] at hnt
  have hF :
      (((.x24 ↦ᵣ (0 : Word)) **
          bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
            balLenW startW endW iW) : Assertion).pcFree := by
    unfold bal0Rest savedFrame; bvt_pcf
  have hntF := cpsTripleWithin_frameR
    ((.x24 ↦ᵣ (0 : Word)) **
      bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
        balLenW startW endW iW) hF hnt
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hntF

set_option maxRecDepth 8000 in
/-- Instr 56: BEQ bal,x0 taken when bal=0 → LoopAdvance. -/
theorem bvtIterBal0Skip
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balLenW startW endW iW : Word) :
    cpsTripleWithin 1 AfterIntrinsicBne LoopAdvance bvtCode
      ((.x24 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          balLenW startW endW iW)
      ((.x24 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          balLenW startW endW iW) := by
  have hbr := beq_spec_gen_within .x24 .x0 (64 : BitVec 13)
    (0 : Word) (0 : Word) AfterIntrinsicBne
  have hbrC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at B AfterIntrinsicBne bvtProg 56
      (.BEQ .x24 .x0 (64 : BitVec 13))
      (by simp only [AfterIntrinsicBne]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) hbr
  have htk := cpsBranchWithin_takenStripPure2 hbrC (fun _ hQf => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hQf
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  have hpc : AfterIntrinsicBne + signExtend13 (64 : BitVec 13) = LoopAdvance := by
    simp only [AfterIntrinsicBne, LoopAdvance]
    rw [show signExtend13 (64 : BitVec 13) = (64 : Word) from by decide]
    bv_omega
  rw [hpc] at htk
  have hF :
      (((.x10 ↦ᵣ (0 : Word)) **
          bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
            balLenW startW endW iW) : Assertion).pcFree := by
    unfold bal0Rest savedFrame; bvt_pcf
  have htkF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) **
      bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
        balLenW startW endW iW) hF htk
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) htkF

set_option maxRecDepth 8000 in
/-- Instr 72–73: ADDI i++ + JAL back → LoopGuard at i+1. -/
theorem bvtIterAdvanceBack
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balLenW startW endW : Word) (i : Nat) :
    let iW := BitVec.ofNat 64 i
    cpsTripleWithin 2 LoopAdvance LoopGuard bvtCode
      ((.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ balLenW) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ balLenW) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW
  -- ADDI same-reg
  have e72_0 := addi_spec_gen_same_within .x21 iW (1 : BitVec 12) LoopAdvance (by decide)
  have e72_1 : cpsTripleWithin 1 LoopAdvance (LoopAdvance + 4)
      (CodeReq.singleton LoopAdvance (.ADDI .x21 .x21 (1 : BitVec 12)))
      (.x21 ↦ᵣ iW) (.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) := by
    have h := e72_0; rw [ofNat_addi1 i] at h; exact h
  have e72C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B LoopAdvance bvtProg 72
      (.ADDI .x21 .x21 (1 : BitVec 12))
      (by simp only [LoopAdvance]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e72_1
  have hF72 :
      ((((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x24 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkIntrinsic) **
          (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ nW) **
          (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (.x25 ↦ᵣ balLenW) **
          (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          bytesRegion txBase txBlob **
          wordArray outBase outVals **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) : Assertion).pcFree) := by
    unfold savedFrame; bvt_pcf
  have e72 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x24 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x25 ↦ᵣ balLenW) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    hF72 e72C
  have hpc72 : LoopAdvance + 4 = B + 292 := by simp only [LoopAdvance]; bv_omega
  rw [hpc72] at e72
  -- JAL back
  have e73_0 := jal_x0_spec_gen_within (-164 : BitVec 21) (B + 292)
  have e73C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 292) bvtProg 73
      (.JAL .x0 (-164 : BitVec 21))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e73_0
  have hpc73 : (B + 292) + signExtend21 (-164 : BitVec 21) = LoopGuard := by
    -- Concrete guest base: avoid bv_omega recursion on large addrs.
    simp only [LoopGuard, B, GuestAddrs.block_verdict_tx_state_gas_array]
    rw [show signExtend21 (-164 : BitVec 21) = (-164 : Word) from by decide]
    decide
  rw [hpc73] at e73C
  -- Frame ambient across emp jal (EndNext pattern)
  let ambient : Assertion :=
    (.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
      (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x24 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ LinkIntrinsic) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x25 ↦ᵣ balLenW) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  have e73 : cpsTripleWithin 1 (B + 292) LoopGuard bvtCode ambient ambient := by
    have h0 := cpsTripleWithin_frameR ambient
      (by unfold ambient savedFrame; bvt_pcf) e73C
    exact cpsTripleWithin_weaken
      (fun h hp => by
        show (empAssertion ** ambient) h
        rwa [sepConj_emp_left' ambient])
      (fun h hq => by
        have hq' : (empAssertion ** ambient) h := hq
        rwa [sepConj_emp_left' ambient] at hq')
      h0
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) e72 e73

set_option maxRecDepth 8000 in
/-- Instr 72–73 with balBase ≠ 0 retained in x24 (concrete temps match store). -/
theorem bvtIterAdvanceBackBal
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW : Word) (i : Nat)
    (chargeW v5 v6 v7 : Word) :
    let iW := BitVec.ofNat 64 i
    cpsTripleWithin 2 LoopAdvance LoopGuard bvtCode
      ((.x21 ↦ᵣ iW) **
        (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ balBase) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ balBase) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW
  have e72_0 := addi_spec_gen_same_within .x21 iW (1 : BitVec 12) LoopAdvance (by decide)
  have e72_1 : cpsTripleWithin 1 LoopAdvance (LoopAdvance + 4)
      (CodeReq.singleton LoopAdvance (.ADDI .x21 .x21 (1 : BitVec 12)))
      (.x21 ↦ᵣ iW) (.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) := by
    have h := e72_0; rw [ofNat_addi1 i] at h; exact h
  have e72C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B LoopAdvance bvtProg 72
      (.ADDI .x21 .x21 (1 : BitVec 12))
      (by simp only [LoopAdvance]; bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e72_1
  have e72 := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x24 ↦ᵣ balBase) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    (by unfold savedFrame; bvt_pcf) e72C
  have hpc72 : LoopAdvance + 4 = B + 292 := by simp only [LoopAdvance]; bv_omega
  rw [hpc72] at e72
  have e73_0 := jal_x0_spec_gen_within (-164 : BitVec 21) (B + 292)
  have e73C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at B (B + 292) bvtProg 73
      (.JAL .x0 (-164 : BitVec 21))
      (by bv_omega)
      (by rw [bvt_length]; decide) rfl
      (by rw [bvt_length]; decide)) e73_0
  have hpc73 : (B + 292) + signExtend21 (-164 : BitVec 21) = LoopGuard := by
    simp only [LoopGuard, B, GuestAddrs.block_verdict_tx_state_gas_array]
    rw [show signExtend21 (-164 : BitVec 21) = (-164 : Word) from by decide]
    decide
  rw [hpc73] at e73C
  let ambient : Assertion :=
    (.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
      (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x24 ↦ᵣ balBase) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x1 ↦ᵣ LinkTeer) **
      (.x2 ↦ᵣ spC) **
      (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
      (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
      (.x20 ↦ᵣ nW) **
      (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
      (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
      (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
      savedFrame spC csaved **
      stackFree spC nCalleeStackDwords **
      bytesRegion txBase txBlob **
      wordArray outBase outVals **
      bytesRegion balBase balBytes **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  have e73 : cpsTripleWithin 1 (B + 292) LoopGuard bvtCode ambient ambient := by
    have h0 := cpsTripleWithin_frameR ambient
      (by unfold ambient savedFrame; bvt_pcf) e73C
    exact cpsTripleWithin_weaken
      (fun h hp => by
        show (empAssertion ** ambient) h
        rwa [sepConj_emp_left' ambient])
      (fun h hq => by
        have hq' : (empAssertion ** ambient) h := hq
        rwa [sepConj_emp_left' ambient] at hq')
      h0
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) e72 e73

set_option maxRecDepth 8000 in
/-- Composite bal=0 tail: LinkIntrinsic → LoopGuard at i+1. -/
theorem bvtIterBal0Tail
    (spC txBase outBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (i : Nat)
    (startW endW : Word) :
    let iW := BitVec.ofNat 64 i
    let balLenW := BitVec.ofNat 64 balBytes.length
    cpsTripleWithin 4 LinkIntrinsic LoopGuard bvtCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        bal0Rest spC txBase outBase chainIdW nW csaved txBlob outVals
          balLenW startW endW iW)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ balLenW) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW balLenW
  have e55 := bvtIterBneOk spC txBase outBase chainIdW nW csaved txBlob outVals
    balLenW startW endW iW
  have e56 := bvtIterBal0Skip spC txBase outBase chainIdW nW csaved txBlob outVals
    balLenW startW endW iW
  have e72 := bvtIterAdvanceBack spC txBase outBase chainIdW nW csaved txBlob outVals
    balLenW startW endW i
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) e55 e56
  have c12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by
      unfold bal0Rest at hq
      xperm_hyp hq) c01 e72
  exact c12

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
