/-
  Discharge `IntrinsicAssumed.success_flat` from the framed
  `txIntrinsicStateGas_success_spec_within` (#10434).

  Reshape:
  * `stackFree sp 18` ↔ `frameSlotsOwn tisFrame (sp-64) ** stackFree (sp-64) 10`
    (own frame 8 + nested extract free stack 10)
  * `frameSlotsSaved` → own → rejoin with nested free → `stackFree sp 18` (post)
  * s-regs + `tisScratchOwn` already match
  * region: **off = 0 only** (slice-base = ambient); multi-tx ambient residual

  Result is under leaf `fullCode` (tis∪ets∪type∪extract∪walks).
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGasTop
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArraySpec
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxIntrinsicStateGasSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.DualReadByteScan (validByteRange)
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel (pureIntrinsicStateGasSuccess)
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
  (nIntrinsicSteps nIntrinsicStackDwords tisScratchOwn)
open EvmAsm.Codegen.TxTypeDispatchSpec (teerTxTypeDispatch)
open EvmAsm.Codegen.TxExtractToAddressModel (extractSuccess)

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

private theorem sepConj_emp_left_eq {P : Assertion} : (empAssertion ** P) = P := by
  funext h; exact propext (sepConj_emp_left h)

private theorem sepConj_assoc_eq {P Q R : Assertion} :
    ((P ** Q) ** R) = (P ** (Q ** R)) := by
  funext h; exact propext (sepConj_assoc h)

/-- `stackFree sp (n+m) = stackFree (sp - 8n) m ** stackFree sp n`. -/
private theorem stackFree_add (sp : Word) (n m : Nat) :
    stackFree sp (n + m) =
      (stackFree (sp - BitVec.ofNat 64 (8 * n)) m ** stackFree sp n) := by
  induction m with
  | zero =>
    change stackFree sp n = (empAssertion ** stackFree sp n)
    exact sepConj_emp_left_eq.symm
  | succ m ih =>
    have hnm : n + (m + 1) = (n + m) + 1 := by omega
    rw [hnm, stackFree_succ, ih, stackFree_succ]
    have haddr :
        sp - BitVec.ofNat 64 (8 * (n + m + 1)) =
          (sp - BitVec.ofNat 64 (8 * n)) - BitVec.ofNat 64 (8 * (m + 1)) := by
      have hmul : (8 * (n + m + 1) : Nat) = 8 * n + 8 * (m + 1) := by omega
      rw [hmul]
      -- ofNat (a+b) = ofNat a + ofNat b when a+b < 2^64 (always for small n,m in practice)
      -- Use ring on BitVec via bv_omega after rewriting ofNat_add when in range.
      have ha : BitVec.ofNat 64 (8 * n + 8 * (m + 1)) =
          BitVec.ofNat 64 (8 * n) + BitVec.ofNat 64 (8 * (m + 1)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
        -- both sides mod 2^64; concrete small sums
        omega
      rw [ha]
      bv_omega
    rw [haddr]
    exact (sepConj_assoc_eq
      (P := memOwn ((sp - BitVec.ofNat 64 (8 * n)) - BitVec.ofNat 64 (8 * (m + 1))))
      (Q := stackFree (sp - BitVec.ofNat 64 (8 * n)) m)
      (R := stackFree sp n)).symm

/-- Nested extract free stack at spC lives in the deeper half of entry stackFree 18. -/
theorem stackFree18_split (sp0 : Word) :
    let spC := sp0 + signExtend12 (-64 : BitVec 12)
    stackFree sp0 nIntrinsicStackDwords =
      (frameSlotsOwn tisFrame spC ** stackFree spC nExtractStackDwords) := by
  intro spC
  simp only [nIntrinsicStackDwords, nExtractStackDwords]
  have hadd := stackFree_add sp0 8 10
  -- hadd: stackFree sp0 18 = stackFree (sp0-64) 10 ** stackFree sp0 8
  have h8 := stackFree8_eq_frameSlotsOwn sp0
  have hsp : sp0 - BitVec.ofNat 64 (8 * 8) = spC := by
    change sp0 - (64 : Word) = spC
    exact (spC_eq sp0).symm
  have h1 :
      stackFree sp0 18 =
        (stackFree spC 10 ** stackFree sp0 8) := by
    simpa [hsp] using hadd
  have h2 :
      stackFree sp0 18 =
        (stackFree spC 10 ** frameSlotsOwn tisFrame spC) := by
    rw [h1, h8]
  rw [h2, sepConj_comm']

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

/-- Post: saved frame + nested free rejoin to entry stackFree 18. -/
theorem frameSlotsSaved_imp_stackFree18 (sp0 : Word) (s : TisSaved) :
    ∀ h,
      (frameSlotsSaved tisFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (tisSavedVals s) **
        stackFree (sp0 + signExtend12 (-64 : BitVec 12)) nExtractStackDwords) h →
      stackFree sp0 nIntrinsicStackDwords h := by
  intro h hp
  simp only [nIntrinsicStackDwords, nExtractStackDwords] at hp ⊢
  have hown :=
    sepConj_mono
      (frameSlotsSaved_imp_own (sp0 + signExtend12 (-64 : BitVec 12)) s)
      (fun _ hh => hh) h hp
  have heq := stackFree18_split sp0
  simp only [nExtractStackDwords] at heq
  rw [← heq] at hown
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
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8))
    (old5 old6 old7 old13 old14 old15 old16 : Word)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts)
    (hextractOk : extractSuccess bs)
    (hsuccess : (teerTxTypeDispatch bs).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htvalid : isValidMemAccess (ToBufAddr + (16 : Word)) = true) :
    let lenW := BitVec.ofNat 64 bs.length
    cpsTripleWithin nIntrinsicSteps T ret fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
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
  have hlen : lenW = BitVec.ofNat 64 bs.length := rfl
  have htop0 :=
    txIntrinsicStateGas_success_spec_within asm hextract htype
      spVal spC s regionBase lenW outPtr oldOut s7 bs
      old5 old6 old7 old13 old14 old15 old16
      hspC hret hlen hlink hextractOk hsuccess halign hover hvalidBuf htvalid
  have hle : nTisTopSteps ≤ nIntrinsicSteps := by
    simp only [nTisTopSteps, nExtractSteps, nTypeSteps, nIntrinsicSteps]
    omega
  have htop := cpsTripleWithin_mono_nSteps hle htop0
  refine cpsTripleWithin_weaken (fun h hp => ?pre) (fun h hq => ?post) htop
  · have heq := stackFree18_split spVal
    -- heq (after unfold): stackFree spVal 18 = frameOwn spC ** stackFree spC 10
    have heq' :
        stackFree spVal nIntrinsicStackDwords =
          (frameSlotsOwn tisFrame spC ** stackFree spC nExtractStackDwords) := by
      simpa [spC, nIntrinsicStackDwords, nExtractStackDwords] using heq
    have hp1 :
        ((.x2 ↦ᵣ spVal) **
          regsAt tisFrame (tisSavedVals s) **
          frameSlotsOwn tisFrame spC **
          stackFree spC nExtractStackDwords **
          prologueAbiRest regionBase lenW outPtr
            old5 old6 old7 old13 old14 old15 old16 **
          bodyPayload regionBase bs outPtr oldOut **
          (Reg.x23 ↦ᵣ s7)) h := by
      have hp' :
          ((.x2 ↦ᵣ spVal) **
            regsAt tisFrame (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) **
            stackFree spVal nIntrinsicStackDwords **
            prologueAbiRest regionBase lenW outPtr
              old5 old6 old7 old13 old14 old15 old16 **
            bodyPayload regionBase bs outPtr oldOut **
            (Reg.x23 ↦ᵣ s7)) h := by
        rw [regsAt_savedOf]
        unfold prologueAbiRest bodyPayload extractToBufOwn teaScratchOwn
          ToBufAddr IsCreationAddr TypeAddr InnerOffAddr
        unfold tisScratchOwn at hp
        xperm_hyp hp
      -- rewrite stackFree nIntrinsic → frameOwn ** nested free; reassoc.
      rw [heq'] at hp'
      -- hp' has (frame ** stack) grouped; goal wants frame ** stack flat.
      have hp'' :
          ((.x2 ↦ᵣ spVal) **
            regsAt tisFrame (tisSavedVals s) **
            frameSlotsOwn tisFrame spC **
            stackFree spC nExtractStackDwords **
            prologueAbiRest regionBase lenW outPtr
              old5 old6 old7 old13 old14 old15 old16 **
            bodyPayload regionBase bs outPtr oldOut **
            (Reg.x23 ↦ᵣ s7)) h := by
        -- s = savedOf ...
        change
          ((.x2 ↦ᵣ spVal) **
            regsAt tisFrame (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) **
            frameSlotsOwn tisFrame spC **
            stackFree spC nExtractStackDwords **
            prologueAbiRest regionBase lenW outPtr
              old5 old6 old7 old13 old14 old15 old16 **
            bodyPayload regionBase bs outPtr oldOut **
            (Reg.x23 ↦ᵣ s7)) h
        -- reassoc (A ** (B ** C)) → (A ** B ** C) via xperm
        xperm_hyp hp'
      exact hp''
    exact hp1
  · -- Post reshape: frameSlotsSaved + nested free → stackFree 18; pin pure out=0.
    change
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) **
        (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
        (Reg.x23 ↦ᵣ s7) **
        frameSlotsSaved tisFrame spC
          (tisSavedVals (savedOf ret s0 s1 s2 s3 s4 s5 s6)) **
        stackFree spC nExtractStackDwords **
        bodyPayloadOk regionBase bs outPtr **
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
            bodyPayloadOk regionBase bs outPtr **
            bodyScratch ** (.x0 ↦ᵣ (0 : Word)))) h := by
      xperm_hyp hq
    have hq2 :=
      sepConj_mono
        (frameSlotsSaved_imp_stackFree18 spVal
          (savedOf ret s0 s1 s2 s3 s4 s5 s6))
        (fun _ hh => hh) h hq1
    unfold bodyPayloadOk bodyScratch extractToBufOwn teaScratchOwn
      ToBufAddr IsCreationAddr TypeAddr InnerOffAddr at hq2
    have hout : BitVec.ofNat 64 pureIntrinsicStateGasSuccess = (0 : Word) := rfl
    simp only [nIntrinsicStackDwords, hout] at hq2 ⊢
    -- hq2 already expanded; goal still has `tisScratchOwn` (flat 8-own chain).
    unfold tisScratchOwn
    xperm_hyp hq2

/-- Peel IntrinsicAssumed temp owns x5–x7, x13–x16 (BgvOffset-style). -/
private theorem of_forall_intrinsic_temps
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
/-- IntrinsicAssumed-shaped success for **off = 0, len = bs.length** with
    regOwn temps (peel). Multi-tx ambient (off ≠ 0) remains residual. -/
theorem intrinsicAssumed_success_flat_off0_own
    (asm : TisCalleeAssumptions fullCode)
    (hextract : asm.extract.entry = ExtractEntry)
    (htype : asm.typeDispatch.entry = TypeEntry)
    (ret spVal regionBase outPtr oldOut : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (bs : List (BitVec 8))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts)
    (hextractOk : extractSuccess bs)
    (hsuccess : (teerTxTypeDispatch bs).1 = (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalidBuf : validByteRange regionBase bs.length)
    (htvalid : isValidMemAccess (ToBufAddr + (16 : Word)) = true) :
    let lenW := BitVec.ofNat 64 bs.length
    cpsTripleWithin nIntrinsicSteps T ret fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** (Reg.x23 ↦ᵣ s7) **
        (.x10 ↦ᵣ regionBase) **
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
      (.x10 ↦ᵣ regionBase) **
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
    refine of_forall_intrinsic_temps (fun v5 v6 v7 v13 v14 v15 v16 => ?_)
    have hf := intrinsicAssumed_success_flat_off0 asm hextract htype
      ret spVal regionBase outPtr oldOut s0 s1 s2 s3 s4 s5 s6 s7 bs
      v5 v6 v7 v13 v14 v15 v16
      hret hlink hextractOk hsuccess halign hover hvalidBuf htvalid
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

#print axioms stackFree8_eq_frameSlotsOwn
#print axioms stackFree18_split
#print axioms intrinsicAssumed_success_flat_off0
#print axioms intrinsicAssumed_success_flat_off0_own

end EvmAsm.Codegen.TxIntrinsicStateGasSpec
