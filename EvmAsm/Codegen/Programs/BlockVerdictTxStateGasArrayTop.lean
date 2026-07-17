/-
  Top-level composition for `block_verdict_tx_state_gas_array` (a4gbr PR-1).

  prologue ;; headerSuccess ;; loop → postOk under named leaf hypotheses
  (IntrinsicAssumed / TeerAssumed / BgvOffsetAssumed). Conditional modular
  array-fill half only — full eip8037_tx_gas_gate is out of scope.
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayLoopClose
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayHeader
import EvmAsm.Codegen.Programs.SgLoadU32leSAsm
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.ChainValidateExtraDataLengthSpec (wordArray pcFree_wordArray)
open EvmAsm.Codegen.SgLoadU32leSAsm (leU32)

/-- Whole-program step budget: prologue(21) + header + loop. -/
def nTopSteps (n : Nat) : Nat := 21 + nHeaderSuccessSteps + nLoopFrom n

/-- Ambient framed across prologue (out array + optional BAL). -/
private def topPayloadRest (outBase balBase : Word) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) : Assertion :=
  wordArray outBase outVals **
    if balEnabled then bytesRegion balBase balBytes else empAssertion

private theorem topPayloadRest_pcFree (outBase balBase : Word) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (balEnabled : Bool) :
    (topPayloadRest outBase balBase outVals balBytes balEnabled).pcFree := by
  unfold topPayloadRest
  apply pcFree_sepConj
  · exact pcFree_wordArray _ _
  · cases balEnabled
    · exact pcFree_emp
    · exact bytesRegion_pcFree _ _

private theorem savedFrame_pcFree (spC : Word) (s : Saved) :
    (savedFrame spC s).pcFree := by
  unfold savedFrame
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_memIs

/-- Pack a-temps (x11..x16 concrete + x17 own) into `regOwns bgvScratchATemps`. -/
private theorem pack_aTemps
    (v11 v12 v13 v14 v15 v16 : Word) :
    ∀ h, (((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
            (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
            regOwn .x17) h) →
      (regOwns bgvScratchATemps) h := by
  intro h hp
  simp only [bgvScratchATemps, regOwns_cons, regOwns_nil, sepConj_emp_right']
  have hp' :=
    sepConj_mono (regIs_to_regOwn .x11 v11)
      (sepConj_mono (regIs_to_regOwn .x12 v12)
        (sepConj_mono (regIs_to_regOwn .x13 v13)
          (sepConj_mono (regIs_to_regOwn .x14 v14)
            (sepConj_mono (regIs_to_regOwn .x15 v15)
              (sepConj_mono (regIs_to_regOwn .x16 v16)
                (fun _ hh => hh)))))) h hp
  xperm_hyp hp'

/-- Pack header post scratch (x5/x10 concrete + bgvScratchTail) into scratchRegs. -/
private theorem pack_header_scratch (first : Word) :
    ∀ h, (((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ first) **
            regOwns bgvScratchTail ** (.x0 ↦ᵣ (0 : Word))) h) →
      (scratchRegs) h := by
  intro h hp
  simp only [scratchRegs, bgvScratchTail, regOwns_cons, regOwns_nil,
    sepConj_emp_right'] at hp ⊢
  have hp1 :
      (((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ first)) **
        (regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
          regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
          (.x0 ↦ᵣ (0 : Word)))) h := by
    xperm_hyp hp
  have hp2 :=
    sepConj_mono
      (sepConj_mono (regIs_to_regOwn .x5 (0 : Word))
        (regIs_to_regOwn .x10 first))
      (fun _ hh => hh) h hp1
  xperm_hyp hp2

/-- Prologue post + regOwn x17 + bytes → header pre + savedFrame (bal=0). -/
private theorem prologuePost_to_headerPre_bal0
    (spC : Word) (s : Saved)
    (txBase txLenW countW outBase balLenW chainIdW : Word)
    (old5 old6 old7 : Word) (txBlob : List (BitVec 8)) :
    ∀ h,
      (prologuePost spC s txBase txLenW countW outBase (0 : Word) balLenW chainIdW
          old5 old6 old7 **
        regOwn .x17 ** bytesRegion txBase txBlob) h →
      (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
          (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ s.s11) **
          (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
          (.x10 ↦ᵣ txBase) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwns bgvScratchATemps **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)) **
          savedFrame spC s) h) := by
  intro h hp
  unfold prologuePost prologueAbiRest at hp
  have hp1 :
      (((.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ countW) ** (.x13 ↦ᵣ outBase) **
          (.x14 ↦ᵣ (0 : Word)) ** (.x15 ↦ᵣ balLenW) ** (.x16 ↦ᵣ chainIdW) **
          regOwn .x17) **
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
          (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ s.s11) **
          savedFrame spC s **
          (.x10 ↦ᵣ txBase) **
          (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)))) h := by
    xperm_hyp hp
  have hp2 :=
    sepConj_mono (pack_aTemps txLenW countW outBase (0 : Word) balLenW chainIdW)
      (fun _ hh => hh) h hp1
  xperm_hyp hp2

/-- Intermediate: header post after packing owns (pre-LoopInv order). -/
private def headerPostPacked (spC txBase outBase chainIdW countW : Word)
    (s : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ BitVec.ofNat 64 0) **
  (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) **
  regOwn .x1 ** regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
  savedFrame spC s **
  bytesRegion txBase txBlob ** wordArray outBase outVals **
  scratchRegs

private theorem headerPost_to_packed
    (spC txBase outBase chainIdW : Word) (s : Saved)
    (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (n : Nat) :
    let first := leU32 txBlob 0
    let countW := BitVec.ofNat 64 n
    ∀ h,
      (((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ (0 : Word)) **
          (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ s.s11) **
          (.x10 ↦ᵣ first) ** (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)) **
          savedFrame spC s **
          topPayloadRest outBase (0 : Word) outVals balBytes false) h) →
      (headerPostPacked spC txBase outBase chainIdW countW s txBlob outVals
        balBytes) h := by
  intro first countW h hp
  unfold topPayloadRest at hp
  simp only [Bool.false_eq_true, ↓reduceIte, sepConj_emp_right'] at hp
  have h0 : (0 : Word) = BitVec.ofNat 64 0 := by decide
  -- Group: (scratch pack) ** (clobber regs) ** stable
  have hp1 :
      (((( (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ first) ** regOwns bgvScratchTail **
            (.x0 ↦ᵣ (0 : Word))) **
          ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
            (.x27 ↦ᵣ s.s11))) **
        ((.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ (0 : Word)) **
          (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) **
          bytesRegion txBase txBlob **
          savedFrame spC s **
          wordArray outBase outVals)) h) := by
    xperm_hyp hp
  have hp2 :=
    sepConj_mono
      (sepConj_mono (pack_header_scratch first)
        (sepConj_mono (regIs_to_regOwn .x1 LinkHeaderBgv)
          (sepConj_mono (regIs_to_regOwn .x22 s.s6)
            (sepConj_mono (regIs_to_regOwn .x23 s.s7)
              (regIs_to_regOwn .x27 s.s11)))))
      (fun _ hh => hh) h hp1
  unfold headerPostPacked
  rw [← h0]
  xperm_hyp hp2

private theorem packed_to_loopInv0
    (spC txBase outBase chainIdW : Word) (s : Saved)
    (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (n : Nat) :
    let countW := BitVec.ofNat 64 n
    ∀ h, (headerPostPacked spC txBase outBase chainIdW countW s txBlob outVals
        balBytes) h →
      (LoopInv spC txBase outBase (0 : Word) chainIdW countW s txBlob outVals
        balBytes false 0) h := by
  intro countW h hp
  unfold headerPostPacked LoopInv payload at *
  simp only [Bool.false_eq_true, ↓reduceIte, sepConj_emp_right'] at hp ⊢
  xperm_hyp hp

private theorem headerPost_to_loopInv0_bal0
    (spC txBase outBase chainIdW : Word) (s : Saved)
    (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (n : Nat) :
    let first := leU32 txBlob 0
    let countW := BitVec.ofNat 64 n
    ∀ h,
      (((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ (0 : Word)) **
          (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ s.s11) **
          (.x10 ↦ᵣ first) ** (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)) **
          savedFrame spC s **
          topPayloadRest outBase (0 : Word) outVals balBytes false) h) →
      (LoopInv spC txBase outBase (0 : Word) chainIdW countW s txBlob outVals
        balBytes false 0) h := by
  intro first countW h hp
  exact packed_to_loopInv0 spC txBase outBase chainIdW s txBlob outVals balBytes n h
    (headerPost_to_packed spC txBase outBase chainIdW s txBlob outVals balBytes n
      h hp)

set_option maxRecDepth 8000 in
/-- Top-level success path bal=0: B → postOk under IntrinsicAssumed + BgvOffsetAssumed.
    Conditional modular array-fill (PR-1). Requires `HeaderOk` (hence n ≠ 0). -/
theorem blockVerdictTxStateGasArray_bal0_spec_within
    (hintr : IntrinsicAssumed fullCode)
    (sp0 spC txBase outBase chainIdW : Word)
    (csaved : Saved) (teer : TeerApplied)
    (txs : List (List (BitVec 8))) (txBlob : List (BitVec 8))
    (outVals : List Nat) (balBytes : List (BitVec 8))
    (chainId n : Nat)
    (old5 old6 old7 : Word)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : HeaderOk txBlob n)
    (hwf : (Region.mk txBase txBlob).wf)
    (hAllOk : ∀ i, i < n → IterOk txBlob n i)
    (hAllLen : n ≤ outVals.length)
    (hAllCell : ∀ i, i < n → outVals[i]! = pureIntrinsicStateGasSuccess)
    (hnLe61 : n ≤ 2 ^ 61)
    (htxAlign : txBase.toNat % 8 = 0)
    (hentry : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hretI : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12))
    (hret : csaved.ra &&& ~~~(1 : Word) = csaved.ra)
    (hsucc : successCells teer txs balBytes chainId false outVals) :
    let countW := BitVec.ofNat 64 n
    let txLenW := BitVec.ofNat 64 txBlob.length
    let balLenW := BitVec.ofNat 64 balBytes.length
    cpsTripleWithin (nTopSteps n) B csaved.ra fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt bvtFrame (savedVals csaved) **
        frameSlotsOwn bvtFrame spC **
        prologueAbiRest txBase txLenW countW outBase (0 : Word) balLenW chainIdW
          old5 old6 old7 **
        regOwn .x17 **
        bytesRegion txBase txBlob **
        topPayloadRest outBase (0 : Word) outVals balBytes false)
      (postOk sp0 spC txBase outBase (0 : Word) csaved teer txs txBlob balBytes
        chainId false outVals) := by
  intro countW txLenW balLenW
  -- 1. Prologue framed with ambient, lifted to fullCode
  have hpro0 := bvtPrologue sp0 spC csaved txBase txLenW countW outBase
    (0 : Word) balLenW chainIdW old5 old6 old7 hspC
  have hproF := cpsTripleWithin_frameR
    (regOwn .x17 ** bytesRegion txBase txBlob **
      topPayloadRest outBase (0 : Word) outVals balBytes false)
    (by
      apply pcFree_sepConj
      · exact pcFree_regOwn
      · apply pcFree_sepConj
        · exact bytesRegion_pcFree _ _
        · exact topPayloadRest_pcFree _ _ _ _ _)
    hpro0
  have hproC := cpsTripleWithin_extend_code bvt_mono hproF
  -- 2. Header success framed with savedFrame + payload rest
  have hhdr0 := bvtHeaderSuccess spC csaved txBase txLenW countW outBase
    (0 : Word) balLenW chainIdW old5 old6 old7 txBlob n rfl rfl hok hwf
  have hhdrF := cpsTripleWithin_frameR
    (savedFrame spC csaved **
      topPayloadRest outBase (0 : Word) outVals balBytes false)
    (by
      apply pcFree_sepConj
      · exact savedFrame_pcFree _ _
      · exact topPayloadRest_pcFree _ _ _ _ _)
    hhdr0
  -- 3. Reshape prologue post → header pre + framed ambient
  have hpro' : cpsTripleWithin 21 B (B + 84) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt bvtFrame (savedVals csaved) **
        frameSlotsOwn bvtFrame spC **
        prologueAbiRest txBase txLenW countW outBase (0 : Word) balLenW chainIdW
          old5 old6 old7 **
        regOwn .x17 **
        bytesRegion txBase txBlob **
        topPayloadRest outBase (0 : Word) outVals balBytes false)
      (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ csaved.ra) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
          (.x22 ↦ᵣ csaved.s6) ** (.x23 ↦ᵣ csaved.s7) **
          (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ csaved.s11) **
          (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
          (.x10 ↦ᵣ txBase) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwns bgvScratchATemps **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)) **
          savedFrame spC csaved **
          topPayloadRest outBase (0 : Word) outVals balBytes false)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ hproC
    intro h hq
    -- frameR post: prologuePost ** (x17 ** bytes ** topPayloadRest)
    -- reassociate without unfolding prologuePost (counts as one atom)
    have hq1 :
        ((prologuePost spC csaved txBase txLenW countW outBase (0 : Word) balLenW
            chainIdW old5 old6 old7 **
          regOwn .x17 ** bytesRegion txBase txBlob) **
          topPayloadRest outBase (0 : Word) outVals balBytes false) h := by
      xperm_hyp hq
    have hq2 :=
      sepConj_mono (prologuePost_to_headerPre_bal0 spC csaved txBase txLenW
        countW outBase balLenW chainIdW old5 old6 old7 txBlob)
        (fun _ hh => hh) h hq1
    xperm_hyp hq2
  -- 4. Header reshape post → LoopInv
  have hhdr' : cpsTripleWithin nHeaderSuccessSteps (B + 84) LoopGuard fullCode
      (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ csaved.ra) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
          (.x22 ↦ᵣ csaved.s6) ** (.x23 ↦ᵣ csaved.s7) **
          (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ csaved.s11) **
          (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
          (.x10 ↦ᵣ txBase) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwns bgvScratchATemps **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)) **
          savedFrame spC csaved **
          topPayloadRest outBase (0 : Word) outVals balBytes false))
      (LoopInv spC txBase outBase (0 : Word) chainIdW countW csaved txBlob outVals
        balBytes false 0) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ hhdrF
    intro h hq
    have hq' :
        (((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ (0 : Word)) **
            (.x22 ↦ᵣ csaved.s6) ** (.x23 ↦ᵣ csaved.s7) **
            (.x24 ↦ᵣ (0 : Word)) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** (.x27 ↦ᵣ csaved.s11) **
            (.x10 ↦ᵣ leU32 txBlob 0) ** (.x5 ↦ᵣ (0 : Word)) **
            regOwns bgvScratchTail **
            bytesRegion txBase txBlob **
            (.x0 ↦ᵣ (0 : Word)) **
            savedFrame spC csaved **
            topPayloadRest outBase (0 : Word) outVals balBytes false) h) := by
      simp only [txLenW, balLenW, countW] at hq
      xperm_hyp hq
    exact headerPost_to_loopInv0_bal0 spC txBase outBase chainIdW csaved
      txBlob outVals balBytes n h hq'
  -- 5. Loop bal=0
  have hloop := bvtLoop_bal0 hintr sp0 spC txBase outBase chainIdW countW
    csaved teer txs txBlob outVals balBytes chainId n hbgv hAllOk hAllLen
    hAllCell hnLe61 htxAlign rfl hentry hretI hspC hret hsucc
  -- 6. Compose
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hpro' hhdr'
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hloop
  change cpsTripleWithin (21 + nHeaderSuccessSteps + nLoopFrom n) B csaved.ra
    fullCode _ _ at c02
  simpa [nTopSteps] using c02

/-! ## bal≠0 reshape helpers -/

private theorem prologuePost_to_headerPre_balNez
    (spC : Word) (s : Saved)
    (txBase txLenW countW outBase balBase balLenW chainIdW : Word)
    (old5 old6 old7 : Word) (txBlob : List (BitVec 8)) :
    ∀ h,
      (prologuePost spC s txBase txLenW countW outBase balBase balLenW chainIdW
          old5 old6 old7 **
        regOwn .x17 ** bytesRegion txBase txBlob) h →
      (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
          (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ s.s11) **
          (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
          (.x10 ↦ᵣ txBase) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwns bgvScratchATemps **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)) **
          savedFrame spC s) h) := by
  intro h hp
  unfold prologuePost prologueAbiRest at hp
  have hp1 :
      (((.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ countW) ** (.x13 ↦ᵣ outBase) **
          (.x14 ↦ᵣ balBase) ** (.x15 ↦ᵣ balLenW) ** (.x16 ↦ᵣ chainIdW) **
          regOwn .x17) **
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) **
          (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ s.s11) **
          savedFrame spC s **
          (.x10 ↦ᵣ txBase) **
          (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)))) h := by
    xperm_hyp hp
  have hp2 :=
    sepConj_mono (pack_aTemps txLenW countW outBase balBase balLenW chainIdW)
      (fun _ hh => hh) h hp1
  xperm_hyp hp2

private def headerPostPackedBal (spC txBase outBase balBase chainIdW countW : Word)
    (s : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
  (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
  (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ BitVec.ofNat 64 0) **
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) **
  regOwn .x1 ** regOwn .x22 ** regOwn .x23 ** regOwn .x27 **
  savedFrame spC s **
  bytesRegion txBase txBlob ** wordArray outBase outVals **
  bytesRegion balBase balBytes **
  scratchRegs

private theorem headerPost_to_packed_bal
    (spC txBase outBase balBase chainIdW : Word) (s : Saved)
    (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (n : Nat) :
    let first := leU32 txBlob 0
    let countW := BitVec.ofNat 64 n
    ∀ h,
      (((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ (0 : Word)) **
          (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ s.s11) **
          (.x10 ↦ᵣ first) ** (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)) **
          savedFrame spC s **
          topPayloadRest outBase balBase outVals balBytes true) h) →
      (headerPostPackedBal spC txBase outBase balBase chainIdW countW s txBlob
        outVals balBytes) h := by
  intro first countW h hp
  unfold topPayloadRest at hp
  simp only [↓reduceIte] at hp
  have h0 : (0 : Word) = BitVec.ofNat 64 0 := by decide
  have hp1 :
      (((( (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ first) ** regOwns bgvScratchTail **
            (.x0 ↦ᵣ (0 : Word))) **
          ((.x1 ↦ᵣ LinkHeaderBgv) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
            (.x27 ↦ᵣ s.s11))) **
        ((.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ (0 : Word)) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) **
          bytesRegion txBase txBlob **
          savedFrame spC s **
          wordArray outBase outVals **
          bytesRegion balBase balBytes)) h) := by
    xperm_hyp hp
  have hp2 :=
    sepConj_mono
      (sepConj_mono (pack_header_scratch first)
        (sepConj_mono (regIs_to_regOwn .x1 LinkHeaderBgv)
          (sepConj_mono (regIs_to_regOwn .x22 s.s6)
            (sepConj_mono (regIs_to_regOwn .x23 s.s7)
              (regIs_to_regOwn .x27 s.s11)))))
      (fun _ hh => hh) h hp1
  unfold headerPostPackedBal
  rw [← h0]
  xperm_hyp hp2

private theorem packed_to_loopInv0_bal
    (spC txBase outBase balBase chainIdW : Word) (s : Saved)
    (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (n : Nat) :
    let countW := BitVec.ofNat 64 n
    ∀ h, (headerPostPackedBal spC txBase outBase balBase chainIdW countW s
        txBlob outVals balBytes) h →
      (LoopInv spC txBase outBase balBase chainIdW countW s txBlob outVals
        balBytes true 0) h := by
  intro countW h hp
  unfold headerPostPackedBal LoopInv payload at *
  simp only [↓reduceIte] at hp ⊢
  xperm_hyp hp

private theorem headerPost_to_loopInv0_balNez
    (spC txBase outBase balBase chainIdW : Word) (s : Saved)
    (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (n : Nat) :
    let first := leU32 txBlob 0
    let countW := BitVec.ofNat 64 n
    ∀ h,
      (((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ (0 : Word)) **
          (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ s.s11) **
          (.x10 ↦ᵣ first) ** (.x5 ↦ᵣ (0 : Word)) ** regOwns bgvScratchTail **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)) **
          savedFrame spC s **
          topPayloadRest outBase balBase outVals balBytes true) h) →
      (LoopInv spC txBase outBase balBase chainIdW countW s txBlob outVals
        balBytes true 0) h := by
  intro first countW h hp
  exact packed_to_loopInv0_bal spC txBase outBase balBase chainIdW s txBlob
    outVals balBytes n h
    (headerPost_to_packed_bal spC txBase outBase balBase chainIdW s txBlob
      outVals balBytes n h hp)

set_option maxRecDepth 8000 in
/-- Top-level success path bal≠0: B → postOk under Intrinsic+Teer+BgvOffset.
    Conditional modular array-fill (PR-1). Requires `HeaderOk` (hence n ≠ 0).
    `outVals0` is the pure-initial array; `finalOut` is the model success array. -/
theorem blockVerdictTxStateGasArray_balNez_spec_within
    (hintr : IntrinsicAssumed fullCode)
    (teer : TeerApplied) (hteer : TeerAssumed fullCode teer)
    (sp0 spC txBase outBase balBase chainIdW : Word)
    (csaved : Saved)
    (txs : List (List (BitVec 8))) (txBlob balBytes : List (BitVec 8))
    (finalOut outVals0 : List Nat) (chainId n : Nat)
    (old5 old6 old7 : Word)
    (hbgv : BgvOffsetAssumed fullCode)
    (hok : HeaderOk txBlob n)
    (hwf : (Region.mk txBase txBlob).wf)
    (hAllOk : ∀ i, i < n → IterOk txBlob n i)
    (hFinalLen : finalOut.length = n)
    (hWrite : ∀ j, j < n →
      finalOut[j]! =
        pureIntrinsicStateGasSuccess +
          iterCharge teer txBlob balBytes chainId n j)
    (hnLe61 : n ≤ 2 ^ 61)
    (htxAlign : txBase.toNat % 8 = 0)
    (hentryI : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hentryT : hteer.entry =
      (GuestAddrs.tx_eip7702_existing_authority_refund : Word))
    (hretI : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hretT : (LinkTeer &&& ~~~(1 : Word)) = LinkTeer)
    (hbal : balBase ≠ 0)
    (hchain : chainIdW = BitVec.ofNat 64 chainId)
    (hspC : spC = sp0 + signExtend12 (-112 : BitVec 12))
    (hret : csaved.ra &&& ~~~(1 : Word) = csaved.ra)
    (hsucc : successCells teer txs balBytes chainId true finalOut)
    (hlen0 : outVals0.length = n)
    (hrest0 : ∀ j, j < n → outVals0[j]! = pureIntrinsicStateGasSuccess) :
    let countW := BitVec.ofNat 64 n
    let txLenW := BitVec.ofNat 64 txBlob.length
    let balLenW := BitVec.ofNat 64 balBytes.length
    cpsTripleWithin (nTopSteps n) B csaved.ra fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt bvtFrame (savedVals csaved) **
        frameSlotsOwn bvtFrame spC **
        prologueAbiRest txBase txLenW countW outBase balBase balLenW chainIdW
          old5 old6 old7 **
        regOwn .x17 **
        bytesRegion txBase txBlob **
        topPayloadRest outBase balBase outVals0 balBytes true)
      (postOk sp0 spC txBase outBase balBase csaved teer txs txBlob balBytes
        chainId true finalOut) := by
  intro countW txLenW balLenW
  have hpro0 := bvtPrologue sp0 spC csaved txBase txLenW countW outBase
    balBase balLenW chainIdW old5 old6 old7 hspC
  have hproF := cpsTripleWithin_frameR
    (regOwn .x17 ** bytesRegion txBase txBlob **
      topPayloadRest outBase balBase outVals0 balBytes true)
    (by
      apply pcFree_sepConj
      · exact pcFree_regOwn
      · apply pcFree_sepConj
        · exact bytesRegion_pcFree _ _
        · exact topPayloadRest_pcFree _ _ _ _ _)
    hpro0
  have hproC := cpsTripleWithin_extend_code bvt_mono hproF
  have hhdr0 := bvtHeaderSuccess spC csaved txBase txLenW countW outBase
    balBase balLenW chainIdW old5 old6 old7 txBlob n rfl rfl hok hwf
  have hhdrF := cpsTripleWithin_frameR
    (savedFrame spC csaved **
      topPayloadRest outBase balBase outVals0 balBytes true)
    (by
      apply pcFree_sepConj
      · exact savedFrame_pcFree _ _
      · exact topPayloadRest_pcFree _ _ _ _ _)
    hhdr0
  have hpro' : cpsTripleWithin 21 B (B + 84) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt bvtFrame (savedVals csaved) **
        frameSlotsOwn bvtFrame spC **
        prologueAbiRest txBase txLenW countW outBase balBase balLenW chainIdW
          old5 old6 old7 **
        regOwn .x17 **
        bytesRegion txBase txBlob **
        topPayloadRest outBase balBase outVals0 balBytes true)
      (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ csaved.ra) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
          (.x22 ↦ᵣ csaved.s6) ** (.x23 ↦ᵣ csaved.s7) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ csaved.s11) **
          (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
          (.x10 ↦ᵣ txBase) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwns bgvScratchATemps **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)) **
          savedFrame spC csaved **
          topPayloadRest outBase balBase outVals0 balBytes true)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ hproC
    intro h hq
    have hq1 :
        ((prologuePost spC csaved txBase txLenW countW outBase balBase balLenW
            chainIdW old5 old6 old7 **
          regOwn .x17 ** bytesRegion txBase txBlob) **
          topPayloadRest outBase balBase outVals0 balBytes true) h := by
      xperm_hyp hq
    have hq2 :=
      sepConj_mono (prologuePost_to_headerPre_balNez spC csaved txBase txLenW
        countW outBase balBase balLenW chainIdW old5 old6 old7 txBlob)
        (fun _ hh => hh) h hq1
    xperm_hyp hq2
  have hhdr' : cpsTripleWithin nHeaderSuccessSteps (B + 84) LoopGuard fullCode
      (((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ csaved.ra) **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
          (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
          (.x20 ↦ᵣ csaved.s4) ** (.x21 ↦ᵣ csaved.s5) **
          (.x22 ↦ᵣ csaved.s6) ** (.x23 ↦ᵣ csaved.s7) **
          (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
          (.x27 ↦ᵣ csaved.s11) **
          (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
          (.x10 ↦ᵣ txBase) **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          regOwns bgvScratchATemps **
          bytesRegion txBase txBlob **
          (.x0 ↦ᵣ (0 : Word)) **
          savedFrame spC csaved **
          topPayloadRest outBase balBase outVals0 balBytes true))
      (LoopInv spC txBase outBase balBase chainIdW countW csaved txBlob outVals0
        balBytes true 0) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ hhdrF
    intro h hq
    have hq' :
        (((.x1 ↦ᵣ LinkHeaderBgv) ** (.x2 ↦ᵣ spC) **
            (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
            (.x18 ↦ᵣ countW) ** (.x19 ↦ᵣ outBase) **
            (.x20 ↦ᵣ countW) ** (.x21 ↦ᵣ (0 : Word)) **
            (.x22 ↦ᵣ csaved.s6) ** (.x23 ↦ᵣ csaved.s7) **
            (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
            (.x26 ↦ᵣ chainIdW) ** (.x27 ↦ᵣ csaved.s11) **
            (.x10 ↦ᵣ leU32 txBlob 0) ** (.x5 ↦ᵣ (0 : Word)) **
            regOwns bgvScratchTail **
            bytesRegion txBase txBlob **
            (.x0 ↦ᵣ (0 : Word)) **
            savedFrame spC csaved **
            topPayloadRest outBase balBase outVals0 balBytes true) h) := by
      simp only [txLenW, balLenW, countW] at hq
      xperm_hyp hq
    exact headerPost_to_loopInv0_balNez spC txBase outBase balBase chainIdW
      csaved txBlob outVals0 balBytes n h hq'
  have hloop := bvtLoop_balNez hintr teer hteer sp0 spC txBase outBase balBase
    chainIdW countW csaved txs txBlob balBytes finalOut outVals0 chainId n
    hbgv hAllOk hFinalLen hWrite hnLe61 htxAlign rfl hentryI hentryT hretI
    hretT hbal hchain hspC hret hsucc hlen0 hrest0
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hpro' hhdr'
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hloop
  change cpsTripleWithin (21 + nHeaderSuccessSteps + nLoopFrom n) B csaved.ra
    fullCode _ _ at c02
  simpa [nTopSteps] using c02

#print axioms blockVerdictTxStateGasArray_bal0_spec_within
#print axioms blockVerdictTxStateGasArray_balNez_spec_within

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec

