/-
  Loop bal≠0 FromIntrinsic composite for `block_verdict_tx_state_gas_array` (a4gbr).
  Split for Codegen/Programs 1500-line file-size guard.
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayLoopTeer
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
    | exact pcFree_tisScratchOwn
    | exact pcFree_teerScratchOwn
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


/-! ## bal≠0 composite: intrinsic + teer + store + advance -/

/-- `ofNat 0 + ofNat c = ofNat c` (pure=0 case for store sum). -/
private theorem ofNat_zero_add (c : Nat) :
    BitVec.ofNat 64 0 + BitVec.ofNat 64 c = BitVec.ofNat 64 c := by
  simp [BitVec.zero_add]

/-- Introduce THREE trailing owned registers (right-assoc `**` chain). -/
private theorem of_forall3
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 r3 : Reg} {P Q : Assertion}
    {cr : CodeReq}
    (h : ∀ v1 v2 v3, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, ⟨v3, hv3⟩⟩ := hO2
  exact h v1 v2 v3 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3, hv2, hv3⟩, hRb⟩ hpc

/-- Introduce FIVE trailing owned registers (right-assoc `**` chain). -/
private theorem of_forall5
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 r3 r4 r5 : Reg}
    {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) **
        (r5 ↦ᵣ v5)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, ⟨v5, hv5⟩⟩ := hO4
  exact h v1 v2 v3 v4 v5 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3, hv2,
        g6, g7, d4, u4, hv3, g8, g9, d5, u5, hv4, hv5⟩, hRb⟩ hpc

set_option maxRecDepth 8000 in
/-- Store-fold under regOwn x5–x7 (teer-call post shape). -/
theorem bvtIterStoreAdd_fold_own
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8))
    (startW endW chargeW : Word) (i chargeNat : Nat)
    (hi : i < outVals.length)
    (hcell : outVals[i] = pureIntrinsicStateGasSuccess)
    (hcharge : chargeW = BitVec.ofNat 64 chargeNat)
    (hsum : BitVec.ofNat 64 pureIntrinsicStateGasSuccess + chargeW =
      BitVec.ofNat 64 (pureIntrinsicStateGasSuccess + chargeNat))
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    let pureW := BitVec.ofNat 64 pureIntrinsicStateGasSuccess
    let sumW := pureW + chargeW
    let outVals' := outVals.set i (pureIntrinsicStateGasSuccess + chargeNat)
    let core : Assertion :=
      ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
        wordArray outBase outVals **
        (.x1 ↦ᵣ LinkTeer) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        teerScratchOwn **
        bytesRegion txBase txBlob **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
    cpsTripleWithin 5 LinkTeer AfterStore bvtCode
      (core ** regOwn .x5 ** regOwn .x6 ** regOwn .x7)
      ((.x10 ↦ᵣ chargeW) ** (.x21 ↦ᵣ iW) ** (.x19 ↦ᵣ outBase) **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ outPtr) ** (.x7 ↦ᵣ sumW) **
        wordArray outBase outVals' **
        (.x1 ↦ᵣ LinkTeer) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        teerScratchOwn **
        bytesRegion txBase txBlob **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW outPtr pureW sumW outVals' core
  refine of_forall3 (r1 := .x5) (r2 := .x6) (r3 := .x7) (fun o5 o6 o7 => ?_)
  have h := bvtIterStoreAdd_fold spC txBase outBase balBase chainIdW nW
    csaved txBlob outVals balBytes startW endW chargeW o5 o6 o7 i chargeNat
    hi hcell hcharge hsum hi61
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [core] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) h

set_option maxRecDepth 8000 in
/-- Teer ABI setup with owned a1–a5 (a0=0); right-assoc owns for of_forall5. -/
theorem bvtIterTeerSetup_own
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob : List (BitVec 8)) (outVals : List Nat)
    (balBytes : List (BitVec 8)) (startW endW : Word) (i : Nat)
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let balLenW := BitVec.ofNat 64 balBytes.length
    let baiW := BitVec.ofNat 64 (i + 1)
    let rest : Assertion :=
      (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ balLenW) ** (.x26 ↦ᵣ chainIdW) **
        (.x21 ↦ᵣ iW) **
        (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ LinkIntrinsic) **
        (.x2 ↦ᵣ spC) **
        (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        teerScratchOwn **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        bytesRegion balBase balBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
    cpsTripleWithin 6 AfterBalCheck AfterTeerSetup bvtCode
      ((rest ** (.x10 ↦ᵣ (0 : Word))) ** regOwn .x11 ** regOwn .x12 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15)
      ((.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ balBase) **
        (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) ** (.x15 ↦ᵣ baiW) **
        rest) := by
  intro iW txPtr txLenW balLenW baiW rest
  refine of_forall5 (r1 := .x11) (r2 := .x12) (r3 := .x13) (r4 := .x14)
    (r5 := .x15) (fun o11 o12 o13 o14 o15 => ?_)
  have h := bvtIterTeerSetup spC txBase outBase balBase chainIdW nW
    csaved txBlob outVals balBytes startW endW i
    (0 : Word) o11 o12 o13 o14 o15 hi61
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [rest, balLenW, iW] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [rest, balLenW, iW, txPtr, txLenW, baiW] at hq ⊢
      xperm_hyp hq) h

set_option maxRecDepth 8000 in
/-- bal≠0 tail from LinkIntrinsic → LoopGuard i+1 with cell updated. -/
theorem bvtIterBalNezTail
    (teer : TeerApplied) (hteer : TeerAssumed fullCode teer)
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob balBytes : List (BitVec 8))
    (outVals : List Nat) (chainId i off len : Nat)
    (startW endW : Word)
    (hentry : hteer.entry =
      (GuestAddrs.tx_eip7702_existing_authority_refund : Word))
    (hretTeer : (LinkTeer &&& ~~~(1 : Word)) = LinkTeer)
    (hbal : balBase ≠ 0)
    (hstart : startW = BitVec.ofNat 64 off)
    (hlen : off + len ≤ txBlob.length)
    (htxLen : endW - startW = BitVec.ofNat 64 len)
    (hchain : chainIdW = BitVec.ofNat 64 chainId)
    (hi : i < outVals.length)
    (hcell : outVals[i] = pureIntrinsicStateGasSuccess)
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let bodyLenW := BitVec.ofNat 64 txBlob.length
    let chargeNat := teer ((txBlob.drop off).take len) balBytes chainId (i + 1)
    let chargeW := BitVec.ofNat 64 chargeNat
    let outVals' := outVals.set i (pureIntrinsicStateGasSuccess + chargeNat)
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    let sumW := BitVec.ofNat 64 pureIntrinsicStateGasSuccess + chargeW
    cpsTripleWithin (1 + 1 + 6 + (1 + nTeerSteps) + 5 + 1 + 2)
      LinkIntrinsic LoopGuard fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ balBase) **
        teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
          balBytes startW endW iW)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ balBase) **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ outPtr) **
        (.x7 ↦ᵣ sumW) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        teerScratchOwn **
        bytesRegion txBase txBlob **
        wordArray outBase outVals' **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW bodyLenW chargeNat chargeW outVals' outPtr sumW
  have hbneF := cpsTripleWithin_extend_code bvt_mono
    (bvtIterBneOkBal spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals balBytes startW endW iW)
  have hfallF := cpsTripleWithin_extend_code bvt_mono
    (bvtIterBalNezFall spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals balBytes startW endW iW hbal)
  have hsetupF := cpsTripleWithin_extend_code bvt_mono
    (bvtIterTeerSetup_own spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals balBytes startW endW i hi61)
  have hcall := bvtIterTeerCall teer hteer spC txBase outBase balBase chainIdW nW
    bodyLenW csaved txBlob balBytes outVals chainId i off len startW endW
    LinkIntrinsic hentry hretTeer hbal hstart hlen htxLen hchain
  have hsum : BitVec.ofNat 64 pureIntrinsicStateGasSuccess + chargeW =
      BitVec.ofNat 64 (pureIntrinsicStateGasSuccess + chargeNat) := by
    simp only [pureIntrinsicStateGasSuccess, chargeW, chargeNat, Nat.zero_add]
    exact ofNat_zero_add chargeNat
  have hstoreF := cpsTripleWithin_extend_code bvt_mono
    (bvtIterStoreAdd_fold_own spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals balBytes startW endW chargeW i chargeNat
      hi hcell rfl hsum hi61)
  have hjalF := cpsTripleWithin_extend_code bvt_mono
    (bvtIterAfterStoreJal spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals' balBytes startW endW iW chargeW
      (BitVec.ofNat 64 (8 * i)) outPtr sumW)
  have hadvF := cpsTripleWithin_extend_code bvt_mono
    (bvtIterAdvanceBackBal spC txBase outBase balBase chainIdW nW
      csaved txBlob outVals' balBytes startW endW i chargeW
      (BitVec.ofNat 64 (8 * i)) outPtr sumW)
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) hbneF hfallF
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by
      unfold teerRest at hq
      xperm_hyp hq)
    c01 hsetupF
  have hsetupPost_to_callPre : ∀ h,
      (((.x10 ↦ᵣ (txBase + startW)) **
          (.x11 ↦ᵣ (endW - startW)) **
          (.x12 ↦ᵣ balBase) **
          (.x13 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x14 ↦ᵣ chainIdW) **
          (.x15 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
          (.x8 ↦ᵣ txBase) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (.x24 ↦ᵣ balBase) **
          (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) **
          (.x21 ↦ᵣ iW) **
          (.x0 ↦ᵣ (0 : Word)) **
          (.x1 ↦ᵣ LinkIntrinsic) **
          (.x2 ↦ᵣ spC) **
          (.x9 ↦ᵣ BitVec.ofNat 64 txBlob.length) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
          regOwn .x27 **
          savedFrame spC csaved **
          stackFree spC nCalleeStackDwords **
          tisScratchOwn **
          teerScratchOwn **
          bytesRegion txBase txBlob **
          wordArray outBase outVals **
          bytesRegion balBase balBytes **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x17 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) h) →
      -- TeerCall pre: s-regs outside loopTeerFrame; regOwn x27 rightmost.
      (((( .x1 ↦ᵣ LinkIntrinsic) **
          (.x2 ↦ᵣ spC) **
          stackFree spC nTeerStackDwords **
          (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
          (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
          (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
          (.x24 ↦ᵣ balBase) **
          (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x26 ↦ᵣ chainIdW) **
          (.x10 ↦ᵣ (txBase + startW)) **
          (.x11 ↦ᵣ (endW - startW)) **
          (.x12 ↦ᵣ balBase) **
          (.x13 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
          (.x14 ↦ᵣ chainIdW) **
          (.x15 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
          bytesRegion txBase txBlob **
          bytesRegion balBase balBytes **
          teerScratchOwn **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x16 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          loopTeerFrame spC txBase outBase balBase chainIdW nW iW
            startW endW bodyLenW (BitVec.ofNat 64 balBytes.length) csaved
            outVals) **
          regOwn .x27) h) := by
    intro h hp
    unfold loopTeerFrame
    simp only [bodyLenW, nTeerStackDwords, nCalleeStackDwords] at hp ⊢
    xperm_hyp hp
  have c03 := cpsTripleWithin_seq_perm_same_cr
    hsetupPost_to_callPre c02 hcall
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by
      -- TeerCall post: s-regs + loopTeerFrame (savedFrame/wordArray/x17) + regOwn x27
      unfold loopTeerFrame at hq
      simp only [bodyLenW, chargeW, nTeerStackDwords, nCalleeStackDwords] at hq ⊢
      xperm_hyp hq)
    c03 hstoreF
  have c05 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c04 hjalF
  have c06 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hq => by xperm_hyp hq) c05 hadvF
  change cpsTripleWithin
    ((((((1 + 1) + 6) + (1 + nTeerSteps)) + 5) + 1) + 2)
    LinkIntrinsic LoopGuard fullCode _ _ at c06
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [outVals', outPtr, chargeW, bodyLenW, sumW] at hq ⊢
      xperm_hyp hq) c06

set_option maxRecDepth 8000 in
/-- bal≠0 success half-iter: preserveCell + teer tail. -/
theorem bvtIterBalNezFromIntrinsic
    (hintr : IntrinsicAssumed fullCode)
    (teer : TeerApplied) (hteer : TeerAssumed fullCode teer)
    (spC txBase outBase balBase chainIdW nW : Word)
    (csaved : Saved) (txBlob balBytes : List (BitVec 8))
    (outVals : List Nat) (chainId i off len : Nat)
    (startW endW old1 : Word)
    (hentryI : hintr.entry = (GuestAddrs.tx_intrinsic_state_gas : Word))
    (hentryT : hteer.entry =
      (GuestAddrs.tx_eip7702_existing_authority_refund : Word))
    (hretI : (LinkIntrinsic &&& ~~~(1 : Word)) = LinkIntrinsic)
    (hretT : (LinkTeer &&& ~~~(1 : Word)) = LinkTeer)
    (hbal : balBase ≠ 0)
    (hstart : startW = BitVec.ofNat 64 off)
    (hlen : off + len ≤ txBlob.length)
    (htxLen : endW - startW = BitVec.ofNat 64 len)
    (hchain : chainIdW = BitVec.ofNat 64 chainId)
    (hi : i < outVals.length)
    (hcell : outVals[i] = pureIntrinsicStateGasSuccess)
    (hi61 : i < 2 ^ 61) :
    let iW := BitVec.ofNat 64 i
    let bodyLenW := BitVec.ofNat 64 txBlob.length
    let chargeNat := teer ((txBlob.drop off).take len) balBytes chainId (i + 1)
    let chargeW := BitVec.ofNat 64 chargeNat
    let outVals' := outVals.set i (pureIntrinsicStateGasSuccess + chargeNat)
    let txPtr := txBase + startW
    let txLenW := endW - startW
    let outPtr := outBase + BitVec.ofNat 64 (8 * i)
    let sumW := BitVec.ofNat 64 pureIntrinsicStateGasSuccess + chargeW
    cpsTripleWithin ((1 + nIntrinsicSteps) + (1 + 1 + 6 + (1 + nTeerSteps) + 5 + 1 + 2))
      AfterEndSpan LoopGuard fullCode
      ((.x1 ↦ᵣ old1) **
        (.x2 ↦ᵣ spC) ** stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        bytesRegion txBase txBlob **
        wordArray outBase outVals **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        loopIntrinsicFrame spC txBase outBase balBase chainIdW nW iW
          startW endW bodyLenW csaved balBytes true)
      ((.x21 ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        (.x10 ↦ᵣ chargeW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x24 ↦ᵣ balBase) **
        (.x5 ↦ᵣ BitVec.ofNat 64 (8 * i)) **
        (.x6 ↦ᵣ outPtr) **
        (.x7 ↦ᵣ sumW) **
        (.x1 ↦ᵣ LinkTeer) **
        (.x2 ↦ᵣ spC) **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) **
        (.x20 ↦ᵣ nW) **
        (.x22 ↦ᵣ startW) ** (.x23 ↦ᵣ endW) **
        (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
        (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
        savedFrame spC csaved **
        stackFree spC nCalleeStackDwords **
        tisScratchOwn **
        teerScratchOwn **
        bytesRegion txBase txBlob **
        wordArray outBase outVals' **
        bytesRegion balBase balBytes **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  intro iW bodyLenW chargeNat chargeW outVals' txPtr txLenW outPtr sumW
  have hintrP := bvtIterIntrinsic_preserveCell hintr spC txBase outBase balBase
    chainIdW nW bodyLenW csaved txBlob outVals balBytes true i off len
    startW endW old1 hentryI hretI hstart hlen htxLen hi hcell
  have htail := bvtIterBalNezTail teer hteer spC txBase outBase balBase chainIdW nW
    csaved txBlob balBytes outVals chainId i off len startW endW
    hentryT hretT hbal hstart hlen htxLen hchain hi hcell hi61
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hq => by
      -- preserveCell post has loopIntrinsicFrame (teerScratchOwn inside);
      -- teerRest wants teerScratchOwn after stackFree/tis.
      unfold loopIntrinsicFrame at hq
      simp only [↓reduceIte] at hq
      have hq' :
          ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            (.x24 ↦ᵣ balBase) **
            teerRest spC txBase outBase balBase chainIdW nW csaved txBlob outVals
              balBytes startW endW iW) h := by
        unfold teerRest
        xperm_hyp hq
      exact hq')
    hintrP htail

end EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
