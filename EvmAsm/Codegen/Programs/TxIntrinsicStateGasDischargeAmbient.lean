/-
  Multi-tx Option A: discharge IntrinsicAssumed success at general off/len
  from ambient TIS success_spec_within_ambient.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasDischarge
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasTopAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressAmbient
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArraySpec
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.DualReadByteScan (validByteRange)
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel (pureIntrinsicStateGasSuccess)
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
  (nIntrinsicSteps nIntrinsicStackDwords tisScratchOwn IntrinsicAssumed)
open EvmAsm.Codegen.TxTypeDispatchSpec
  (teerTxTypeDispatch txSlice)
open EvmAsm.Codegen.TxExtractToAddressModel (extractSuccess)
open EvmAsm.Codegen.TxExtractToAddressSpec (TisCalleeAssumptionsAmbient)

private theorem regsAt_savedOf_amb (ret s0 s1 s2 s3 s4 s5 s6 : Word) :
    regsAt tisFrame (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) =
      ((.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6)) := by
  simpa only [savedOf] using regsAt_tisFrame
    { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4, s5 := s5, s6 := s6 }

set_option maxRecDepth 8000 in
/-- Ambient general off/len success discharge (pre temps concrete). -/
theorem intrinsicAssumed_success_flat_ambient
    (asm : TisCalleeAssumptionsAmbient fullCode)
    (hextract : asm.extract.entry = ExtractEntry)
    (htype : asm.typeDispatch.entry = TypeEntry)
    (ret spVal regionBase loadPtr outPtr oldOut : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (old5 old6 old7 old13 old14 old15 old16 : Word)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts)
    (hextractOk : extractSuccess (txSlice bs off len))
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htvalid : isValidMemAccess (ToBufAddr + (16 : Word)) = true) :
    let lenW := BitVec.ofNat 64 len
    cpsTripleWithin nIntrinsicSteps T ret fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ loadPtr) **
        (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ outPtr) ** bytesRegion regionBase bs **
        (outPtr ↦ₘ oldOut) **
        tisScratchOwn **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
        (.x16 ↦ᵣ old16) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        tisScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro lenW
  let s : TisSaved := savedOf ret s0 s1 s2 s3 s4 s5 s6
  let spC : Word := spVal + signExtend12 (-64 : BitVec 12)
  have hspC : spC = spVal + signExtend12 (-64 : BitVec 12) := rfl
  have hlen : lenW = BitVec.ofNat 64 len := rfl
  have htop0 :=
    txIntrinsicStateGas_success_spec_within_ambient asm hextract htype
      spVal spC s regionBase loadPtr lenW outPtr oldOut s7 bs off len
      old5 old6 old7 old13 old14 old15 old16
      hspC hret hptr hlen hlink hextractOk hsuccess halign hbound hover
      hvalidBuf htvalid
  have hle : nTisTopSteps ≤ nIntrinsicSteps := by
    simp only [nTisTopSteps, nExtractSteps, nTypeSteps, nIntrinsicSteps]
    omega
  have htop := cpsTripleWithin_mono_nSteps hle htop0
  refine cpsTripleWithin_weaken (fun h hp => ?pre) (fun h hq => ?post) htop
  · have heq := stackFree18_split spVal
    have heq' :
        stackFree spVal nIntrinsicStackDwords =
          (frameSlotsOwn tisFrame spC ** stackFree spC nExtractStackDwords) := by
      simpa [spC, nIntrinsicStackDwords, nExtractStackDwords] using heq
    have hp' :
        ((.x2 ↦ᵣ spVal) **
          regsAt tisFrame (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) **
          stackFree spVal nIntrinsicStackDwords **
          prologueAbiRest loadPtr lenW outPtr
            old5 old6 old7 old13 old14 old15 old16 **
          bodyPayloadAmbient regionBase bs outPtr oldOut **
          (Reg.x23 ↦ᵣ s7)) h := by
      rw [regsAt_savedOf_amb]
      unfold prologueAbiRest bodyPayloadAmbient extractToBufOwn teaScratchOwn
        ToBufAddr IsCreationAddr TypeAddr InnerOffAddr
      unfold tisScratchOwn at hp
      xperm_hyp hp
    rw [heq'] at hp'
    have hp'' :
        ((.x2 ↦ᵣ spVal) **
          regsAt tisFrame (tisSavedVals s) **
          frameSlotsOwn tisFrame spC **
          stackFree spC nExtractStackDwords **
          prologueAbiRest loadPtr lenW outPtr
            old5 old6 old7 old13 old14 old15 old16 **
          bodyPayloadAmbient regionBase bs outPtr oldOut **
          (Reg.x23 ↦ᵣ s7)) h := by
      change
        ((.x2 ↦ᵣ spVal) **
          regsAt tisFrame (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) **
          frameSlotsOwn tisFrame spC **
          stackFree spC nExtractStackDwords **
          prologueAbiRest loadPtr lenW outPtr
            old5 old6 old7 old13 old14 old15 old16 **
          bodyPayloadAmbient regionBase bs outPtr oldOut **
          (Reg.x23 ↦ᵣ s7)) h
      xperm_hyp hp'
    exact hp''
  · change
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) **
        (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
        (Reg.x23 ↦ᵣ s7) **
        frameSlotsSaved tisFrame spC
          (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) **
        stackFree spC nExtractStackDwords **
        bodyPayloadOkAmbient regionBase bs outPtr **
        bodyScratch ** (.x0 ↦ᵣ (0 : Word))) h at hq
    have hq1 :
        ((frameSlotsSaved tisFrame spC
            (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) **
          stackFree spC nExtractStackDwords) **
          ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
            (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
            (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) **
            (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
            (Reg.x23 ↦ᵣ s7) **
            bodyPayloadOkAmbient regionBase bs outPtr **
            bodyScratch ** (.x0 ↦ᵣ (0 : Word)))) h := by
      xperm_hyp hq
    have hq2 :=
      sepConj_mono
        (frameSlotsSaved_imp_stackFree18 spVal
          (savedOf ret s0 s1 s2 s3 s4 s5 s6))
        (fun _ hh => hh) h hq1
    unfold bodyPayloadOkAmbient bodyScratch extractToBufOwn teaScratchOwn
      ToBufAddr IsCreationAddr TypeAddr InnerOffAddr at hq2
    have hout : BitVec.ofNat 64 pureIntrinsicStateGasSuccess = (0 : Word) := rfl
    simp only [nIntrinsicStackDwords, hout] at hq2 ⊢
    unfold tisScratchOwn
    xperm_hyp hq2

/-- Peel IntrinsicAssumed temp owns (ambient). -/
private theorem of_forall_intrinsic_temps_amb
    {nSteps : Nat} {entry exit_ : Word} {P Q : Assertion} {cr : CodeReq}
    (h : ∀ (v5 v6 v7 v13 v14 v15 v16 : Word),
      cpsTripleWithin nSteps entry exit_ cr
        (P **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v5, hv5⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v6, hv6⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v7, hv7⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v13, hv13⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v14, hv14⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v15, hv15⟩, ⟨v16, hv16⟩⟩ := hO6
  exact h v5 v6 v7 v13 v14 v15 v16 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0,
        g2, g3, d2, u2, hv5,
        g4, g5, d3, u3, hv6,
        g6, g7, d4, u4, hv7,
        g8, g9, d5, u5, hv13,
        g10, g11, d6, u6, hv14,
        g12, g13, d7, u7, hv15, hv16⟩, hRb⟩ hpc

set_option maxRecDepth 8000 in
/-- IntrinsicAssumed-shaped ambient success (regOwn temps).
    Residual: structure fill still needs ExtractAssumedAmbient body +
    path-domain hyps (extractSuccess/type success/statics) on Assumed. -/
theorem intrinsicAssumed_success_flat_ambient_own
    (asm : TisCalleeAssumptionsAmbient fullCode)
    (hextract : asm.extract.entry = ExtractEntry)
    (htype : asm.typeDispatch.entry = TypeEntry)
    (ret spVal regionBase loadPtr outPtr oldOut : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8)) (off len : Nat)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts)
    (hextractOk : extractSuccess (txSlice bs off len))
    (hsuccess : (teerTxTypeDispatch (txSlice bs off len)).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htvalid : isValidMemAccess (ToBufAddr + (16 : Word)) = true) :
    let lenW := BitVec.ofNat 64 len
    cpsTripleWithin nIntrinsicSteps T ret fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ loadPtr) **
        (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ outPtr) ** bytesRegion regionBase bs **
        (outPtr ↦ₘ oldOut) **
        tisScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        tisScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) := by
  intro lenW
  let Pcore : Assertion :=
    (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
      stackFree spVal nIntrinsicStackDwords **
      (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
      (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
      (.x10 ↦ᵣ loadPtr) **
      (.x11 ↦ᵣ lenW) **
      (.x12 ↦ᵣ outPtr) ** bytesRegion regionBase bs **
      (outPtr ↦ₘ oldOut) **
      tisScratchOwn **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))
  let Qown : Assertion :=
    (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
      stackFree spVal nIntrinsicStackDwords **
      (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
      (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
      (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
      (.x10 ↦ᵣ (0 : Word)) **
      bytesRegion regionBase bs **
      (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
      tisScratchOwn **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
      regOwn .x15 ** regOwn .x16 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))
  have hpeel :
      cpsTripleWithin nIntrinsicSteps T ret fullCode
        (Pcore **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16)
        Qown := by
    refine of_forall_intrinsic_temps_amb (fun v5 v6 v7 v13 v14 v15 v16 => ?_)
    have hf := intrinsicAssumed_success_flat_ambient asm hextract htype
      ret spVal regionBase loadPtr outPtr oldOut s0 s1 s2 s3 s4 s5 s6 s7 bs off len
      v5 v6 v7 v13 v14 v15 v16
      hret hptr hbound hlink hextractOk hsuccess halign hover hvalidBuf htvalid
    refine cpsTripleWithin_weaken (fun _ hp => by
      dsimp only [Pcore] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      dsimp only [Qown] at hq ⊢
      exact hq) hf
  refine cpsTripleWithin_weaken (fun _ hp => by
    dsimp only [Pcore] at hp ⊢
    xperm_hyp hp) (fun _ hq => by
    dsimp only [Qown] at hq ⊢
    exact hq) hpeel

#print axioms intrinsicAssumed_success_flat_ambient
#print axioms intrinsicAssumed_success_flat_ambient_own

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
