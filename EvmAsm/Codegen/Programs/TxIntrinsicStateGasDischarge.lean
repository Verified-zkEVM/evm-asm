/-
  Discharge `IntrinsicAssumed.success_flat` from the framed
  `txIntrinsicStateGas_success_spec_within` (#10434).

  Reshape:
  * `stackFree sp 8` ↔ `frameSlotsOwn tisFrame (sp-64)` (pre)
  * `frameSlotsSaved` → `stackFree` via `memIs_implies_memOwn` (post)
  * s-regs + `tisScratchOwn` already match
  * region: **off = 0 only** (slice-base = ambient); multi-tx ambient residual

  Result is under leaf `fullCode` (tis∪ets). Array compose later mono-lifts
  into the guest image CodeReq once callees are linked in.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasTop
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArraySpec
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel (pureIntrinsicStateGasSuccess)
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
  (nIntrinsicSteps nIntrinsicStackDwords tisScratchOwn)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)

private theorem se12_neg64 :
    signExtend12 (-64 : BitVec 12) = BitVec.ofInt 64 (-64) := by decide

private theorem spC_eq (sp0 : Word) :
    sp0 + signExtend12 (-64 : BitVec 12) = sp0 - (64 : Word) := by
  rw [se12_neg64]; bv_omega

private theorem slot0 (sp : Word) : (sp - (64 : Word)) + (0 : Word) = sp - (64 : Word) := by
  bv_omega
private theorem slot8 (sp : Word) : (sp - (64 : Word)) + (8 : Word) = sp - (56 : Word) := by
  bv_omega
private theorem slot16 (sp : Word) : (sp - (64 : Word)) + (16 : Word) = sp - (48 : Word) := by
  bv_omega
private theorem slot24 (sp : Word) : (sp - (64 : Word)) + (24 : Word) = sp - (40 : Word) := by
  bv_omega
private theorem slot32 (sp : Word) : (sp - (64 : Word)) + (32 : Word) = sp - (32 : Word) := by
  bv_omega
private theorem slot40 (sp : Word) : (sp - (64 : Word)) + (40 : Word) = sp - (24 : Word) := by
  bv_omega
private theorem slot48 (sp : Word) : (sp - (64 : Word)) + (48 : Word) = sp - (16 : Word) := by
  bv_omega
private theorem slot56 (sp : Word) : (sp - (64 : Word)) + (56 : Word) = sp - (8 : Word) := by
  bv_omega

private theorem se12s :
    signExtend12 (0 : BitVec 12) = (0 : Word) ∧
    signExtend12 (8 : BitVec 12) = (8 : Word) ∧
    signExtend12 (16 : BitVec 12) = (16 : Word) ∧
    signExtend12 (24 : BitVec 12) = (24 : Word) ∧
    signExtend12 (32 : BitVec 12) = (32 : Word) ∧
    signExtend12 (40 : BitVec 12) = (40 : Word) ∧
    signExtend12 (48 : BitVec 12) = (48 : Word) ∧
    signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

/-- Pre: free stack under entry sp equals owned frame slots at sp-64. -/
private theorem mul8s :
    BitVec.ofNat 64 (8 * (7 + 1)) = BitVec.ofNat 64 64 ∧
    BitVec.ofNat 64 (8 * (6 + 1)) = BitVec.ofNat 64 56 ∧
    BitVec.ofNat 64 (8 * (5 + 1)) = BitVec.ofNat 64 48 ∧
    BitVec.ofNat 64 (8 * (4 + 1)) = BitVec.ofNat 64 40 ∧
    BitVec.ofNat 64 (8 * (3 + 1)) = BitVec.ofNat 64 32 ∧
    BitVec.ofNat 64 (8 * (2 + 1)) = BitVec.ofNat 64 24 ∧
    BitVec.ofNat 64 (8 * (1 + 1)) = BitVec.ofNat 64 16 ∧
    BitVec.ofNat 64 (8 * (0 + 1)) = BitVec.ofNat 64 8 := by decide

theorem stackFree8_eq_frameSlotsOwn (sp0 : Word) :
    stackFree sp0 8
      = frameSlotsOwn tisFrame (sp0 + signExtend12 (-64 : BitVec 12)) := by
  rw [spC_eq]
  obtain ⟨e0, e8, e16, e24, e32, e40, e48, e56⟩ := se12s
  obtain ⟨n64, n56, n48, n40, n32, n24, n16, n8⟩ := mul8s
  simp only [tisFrame, frameSlotsOwn, stackFree_succ, stackFree_zero,
    sepConj_emp_right', List.foldr_cons, List.foldr_nil, e0, e8, e16, e24,
    e32, e40, e48, e56, slot0, slot8, slot16, slot24, slot32, slot40, slot48,
    slot56, n64, n56, n48, n40, n32, n24, n16, n8]
  rfl

private theorem frameSlotsSaved_imp_own (spC : Word) (s : TisSaved) :
    ∀ h, frameSlotsSaved tisFrame spC (tisSavedVals s) h →
      frameSlotsOwn tisFrame spC h := by
  intro h hp
  obtain ⟨e0, e8, e16, e24, e32, e40, e48, e56⟩ := se12s
  simp only [tisFrame, frameSlotsSaved, frameSlotsOwn, tisSavedVals,
    List.foldr_cons, List.foldr_nil, sepConj_emp_right',
    e0, e8, e16, e24, e32, e40, e48, e56] at hp ⊢
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn
                memIs_implies_memOwn)))))) h hp

/-- Post: saved frame slots weaken to free-stack ownership. -/
theorem frameSlotsSaved_imp_stackFree8 (sp0 : Word) (s : TisSaved) :
    ∀ h,
      frameSlotsSaved tisFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (tisSavedVals s) h →
      stackFree sp0 8 h := by
  intro h hp
  have hown := frameSlotsSaved_imp_own
    (sp0 + signExtend12 (-64 : BitVec 12)) s h hp
  rw [← stackFree8_eq_frameSlotsOwn sp0] at hown
  exact hown

def savedOf (ret s0 s1 s2 s3 s4 s5 s6 : Word) : TisSaved :=
  { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4, s5 := s5, s6 := s6 }

private theorem regsAt_savedOf (ret s0 s1 s2 s3 s4 s5 s6 : Word) :
    regsAt tisFrame (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) =
      ((.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6)) := by
  simp only [tisFrame, regsAt, tisSavedVals, savedOf, List.foldr_cons,
    List.foldr_nil, sepConj_emp_right']

set_option maxRecDepth 8000 in
theorem intrinsicAssumed_success_flat_off0
    (asm : TisCalleeAssumptions fullCode)
    (hextract : asm.extract.entry = ExtractEntry)
    (htype : asm.typeDispatch.entry = TypeEntry)
    (ret spVal regionBase outPtr oldOut : Word)
    (s0 s1 s2 s3 s4 s5 s6 : Word)
    (bs : List (BitVec 8))
    (old5 old6 old7 old13 old14 old15 old16 : Word)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts)
    (hsuccess : (teerTxTypeDispatch bs).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 0) = true) :
    let lenW := BitVec.ofNat 64 bs.length
    cpsTripleWithin nIntrinsicSteps T ret fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
        (.x10 ↦ᵣ regionBase) **
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
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
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
  have hlen : lenW = BitVec.ofNat 64 bs.length := rfl
  have htop0 :=
    txIntrinsicStateGas_success_spec_within asm hextract htype
      spVal spC s regionBase lenW outPtr oldOut bs
      old5 old6 old7 old13 old14 old15 old16
      hspC hret hlen hlink hsuccess halign hover hvalid0
  have hle : nTisTopSteps ≤ nIntrinsicSteps := by
    simp only [nTisTopSteps, nExtractSteps, nTypeSteps, nIntrinsicSteps]
    omega
  have htop := cpsTripleWithin_mono_nSteps hle htop0
  refine cpsTripleWithin_weaken (fun h hp => ?pre) (fun h hq => ?post) htop
  · have heq := stackFree8_eq_frameSlotsOwn spVal
    simp only [nIntrinsicStackDwords] at hp heq
    have hp1 :
        ((.x2 ↦ᵣ spVal) **
          regsAt tisFrame (tisSavedVals s) **
          frameSlotsOwn tisFrame spC **
          prologueAbiRest regionBase lenW outPtr
            old5 old6 old7 old13 old14 old15 old16 **
          bodyPayload regionBase bs outPtr oldOut) h := by
      -- Expand named defs on both sides for xperm.
      change
        ((.x2 ↦ᵣ spVal) **
          regsAt tisFrame (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) **
          frameSlotsOwn tisFrame spC **
          prologueAbiRest regionBase lenW outPtr
            old5 old6 old7 old13 old14 old15 old16 **
          bodyPayload regionBase bs outPtr oldOut) h
      rw [regsAt_savedOf, ← heq]
      unfold prologueAbiRest bodyPayload
      have hscratch :
          tisScratchOwn =
            (memOwn ToBufAddr ** memOwn IsCreationAddr **
              memOwn TypeAddr ** memOwn InnerOffAddr) := by
        unfold tisScratchOwn ToBufAddr IsCreationAddr TypeAddr InnerOffAddr
        rfl
      simp only [hscratch] at hp
      xperm_hyp hp
    exact hp1
  · -- Post reshape: release frameSlotsSaved; pin pure out=0.
    change
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) **
        (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
        frameSlotsSaved tisFrame spC
          (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) **
        bodyPayloadOk regionBase bs outPtr **
        bodyScratch ** (.x0 ↦ᵣ (0 : Word))) h at hq
    have hq1 :
        (frameSlotsSaved tisFrame spC
            (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) **
          ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
            (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
            (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) **
            (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
            bodyPayloadOk regionBase bs outPtr **
            bodyScratch ** (.x0 ↦ᵣ (0 : Word)))) h := by
      xperm_hyp hq
    have hq2 :=
      sepConj_mono
        (frameSlotsSaved_imp_stackFree8 spVal
          (savedOf ret s0 s1 s2 s3 s4 s5 s6))
        (fun _ hh => hh) h hq1
    -- Expand bodyPayloadOk / bodyScratch / tisScratchOwn for final xperm.
    unfold bodyPayloadOk bodyScratch at hq2
    have hscratch :
        tisScratchOwn =
          (memOwn ToBufAddr ** memOwn IsCreationAddr **
            memOwn TypeAddr ** memOwn InnerOffAddr) := by
      unfold tisScratchOwn ToBufAddr IsCreationAddr TypeAddr InnerOffAddr
      rfl
    have hout : BitVec.ofNat 64 pureIntrinsicStateGasSuccess = (0 : Word) := rfl
    simp only [nIntrinsicStackDwords, hout, hscratch] at hq2 ⊢
    xperm_hyp hq2

#print axioms stackFree8_eq_frameSlotsOwn
#print axioms intrinsicAssumed_success_flat_off0

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
