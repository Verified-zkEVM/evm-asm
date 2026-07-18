/-
  Intrinsic call + bal=0 tail for `block_verdict_tx_state_gas_array` (a4gbr).
  Split from LoopEnd for Codegen/Programs 1500-line file-size guard.
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayLoopEnd
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
  -- x8/x9/x18–x22/x23 are in IntrinsicAssumed (leaf save/restore); not here.
  -- teerScratchOwn is teer-only global scratch; frame across intrinsic.
  (.x24 ↦ᵣ balBase) ** (.x25 ↦ᵣ BitVec.ofNat 64 balBytes.length) **
  (.x26 ↦ᵣ chainIdW) ** regOwn .x27 **
  regOwn .x17 **
  savedFrame spC csaved **
  teerScratchOwn **
  (if balEnabled then bytesRegion balBase balBytes else empAssertion)
  -- x0 stays in the callee footprint (not framed) to avoid double-own.
  -- x17 is not in IntrinsicAssumed footprint; frame it across the call.
  -- x2 + stackFree + s-regs + tisScratchOwn are in the callee footprint.

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
        (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) ** (Reg.x23 ↦ᵣ endW) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
        bytesRegion txBase txBlob **
        (outPtr ↦ₘ oldOut) **
        tisScratchOwn **
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
        (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) ** (Reg.x23 ↦ᵣ endW) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBlob **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        tisScratchOwn **
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
    txBase bodyLenW nW outBase nW iW startW endW
    txBlob off len hret hload hlen
  have hflatLen : cpsTripleWithin nIntrinsicSteps hintr.entry LinkIntrinsic fullCode
      ((.x1 ↦ᵣ LinkIntrinsic) ** (.x2 ↦ᵣ spC) **
        stackFree spC nIntrinsicStackDwords **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) ** (Reg.x23 ↦ᵣ endW) **
        (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ outPtr) ** bytesRegion txBase txBlob **
        (outPtr ↦ₘ oldOut) **
        tisScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ LinkIntrinsic) ** (.x2 ↦ᵣ spC) **
        stackFree spC nIntrinsicStackDwords **
        (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ bodyLenW) **
        (.x18 ↦ᵣ nW) ** (.x19 ↦ᵣ outBase) ** (.x20 ↦ᵣ nW) **
        (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) ** (Reg.x23 ↦ᵣ endW) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion txBase txBlob **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        tisScratchOwn **
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
          (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) ** (Reg.x23 ↦ᵣ endW) **
          (.x10 ↦ᵣ txPtr) ** (.x11 ↦ᵣ txLenW) ** (.x12 ↦ᵣ outPtr) **
          bytesRegion txBase txBlob ** (outPtr ↦ₘ oldOut) **
          tisScratchOwn **
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
          (.x21 ↦ᵣ iW) ** (.x22 ↦ᵣ startW) ** (Reg.x23 ↦ᵣ endW) **
          (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion txBase txBlob **
          (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
          tisScratchOwn **
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
  tisScratchOwn **
  teerScratchOwn **
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
        tisScratchOwn **
        teerScratchOwn **
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
        tisScratchOwn **
        teerScratchOwn **
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
          tisScratchOwn **
          teerScratchOwn **
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
      tisScratchOwn **
      teerScratchOwn **
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
      tisScratchOwn **
      teerScratchOwn **
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
        tisScratchOwn **
        teerScratchOwn **
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
        tisScratchOwn **
        teerScratchOwn **
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
      tisScratchOwn **
      teerScratchOwn **
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
      tisScratchOwn **
      teerScratchOwn **
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
        tisScratchOwn **
        teerScratchOwn **
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
