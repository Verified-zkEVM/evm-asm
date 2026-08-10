/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakWrap

  Pad → final CSRS → 4× digest → LI a0,0 compose for `zkvm_keccak256`.
  Geometry (base = GuestAddrs.zkvm_keccak256):
    padHdr  = base+180 (idx 45)
    csrsHdr = base+208 (idx 52) = padHdr+28
    digHdr  = base+216 (idx 54) = padHdr+36
    li0     = base+248 (idx 62) = padHdr+68
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakTail
import EvmAsm.Codegen.Proofs.HashBridgeKeccakOuter
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000

/-- Temps that stay owned through pad (csrsRest minus x5/x28 which pad uses). -/
def keccakPadRestOwns : List Reg :=
  [.x6, .x7, .x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem padRest_nodup : keccakPadRestOwns.Nodup := by decide

/-- Ambient through pad→csrs→digest (output + rest owns + free A). -/
def keccakPadCsrsAmb (scratchBase outputBase : Word)
    (st out : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
    (regOwn .x10) **
    regOwns keccakPadRestOwns **
    bytesRegion scratchBase st ** bytesRegion outputBase out ** A

theorem keccakPadCsrsAmb_pcFree (scratchBase outputBase : Word)
    (st out : List (BitVec 8)) (A : Assertion) (hA : A.pcFree) :
    (keccakPadCsrsAmb scratchBase outputBase st out A).pcFree :=
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (pcFree_regOwns _) <|
  pcFree_sepConj (bytesRegion_pcFree _ _) <|
  pcFree_sepConj (bytesRegion_pcFree _ _) hA

/-- Pad entry shaped for pad block: cursor at +rem, own x5, ambient. -/
def keccakPadPre (scratchBase outputBase : Word) (rem : Nat)
    (st out : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
    (regOwn .x5) **
    keccakPadCsrsAmb scratchBase outputBase st out A

/-- After pad: cursor at +135, own x5, padded state. -/
def keccakPadPost (scratchBase outputBase : Word)
    (st out : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
    (regOwn .x5) **
    keccakPadCsrsAmb scratchBase outputBase st out A

private theorem of_forall1 {n : Nat} {entry exit : Word} {cr : CodeReq}
    {P Q : Assertion} {r : Reg}
    (h : ∀ v, cpsTripleWithin n entry exit cr (P ** (r ↦ᵣ v)) Q) :
    cpsTripleWithin n entry exit cr (P ** regOwn r) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hP0, hOwn, hd0, hu0, hp0, hpOwn⟩ := hpP
  obtain ⟨v, hv⟩ := hpOwn
  have hPR' :
      ((P ** (r ↦ᵣ v)) ** R).holdsFor s :=
    ⟨hMem, hcompat, h_P, h_R, hdisj, hunion,
      ⟨hP0, hOwn, hd0, hu0, hp0, hv⟩, hpR⟩
  exact h v R hR s hcr hPR' hpc

/-- Pad block under pad ambient (fuel 7, padHdr → csrsHdr). -/
theorem keccakPad_framed (cr : CodeReq) (padHdr : Word)
    (scratchBase outputBase : Word) (st out : List (BitVec 8)) (rem : Nat)
    (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200) (_hout : out.length = 32)
    (hrem : rem ≤ 135)
    (halign : scratchBase.toNat % 8 = 0)
    (h_over : scratchBase.toNat + 200 ≤ 2 ^ 64)
    (hvalidRem : isValidByteAccess (scratchBase + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess (scratchBase + BitVec.ofNat 64 135) = true)
    (hmem0 : ∀ a i, CodeReq.singleton padHdr (.LBU .x5 .x28 0) a = some i →
      cr a = some i)
    (hmem1 : ∀ a i, CodeReq.singleton (padHdr + 4) (.XORI .x5 .x5 1) a = some i →
      cr a = some i)
    (hmem2 : ∀ a i, CodeReq.singleton (padHdr + 8) (.SB .x28 .x5 0) a = some i →
      cr a = some i)
    (hmem3 : ∀ a i, CodeReq.singleton (padHdr + 12) (.ADDI .x28 .x8 135) a = some i →
      cr a = some i)
    (hmem4 : ∀ a i, CodeReq.singleton (padHdr + 16) (.LBU .x5 .x28 0) a = some i →
      cr a = some i)
    (hmem5 : ∀ a i, CodeReq.singleton (padHdr + 20) (.XORI .x5 .x5 128) a = some i →
      cr a = some i)
    (hmem6 : ∀ a i, CodeReq.singleton (padHdr + 24) (.SB .x28 .x5 0) a = some i →
      cr a = some i) :
    cpsTripleWithin 7 padHdr (padHdr + 28) cr
      (keccakPadPre scratchBase outputBase rem st out A)
      (keccakPadPost scratchBase outputBase (keccakGuestPad st rem) out A) := by
  -- concrete x5 via of_forall1
  have hcore (v5 : Word) :
      cpsTripleWithin 7 padHdr (padHdr + 28) cr
        ((.x8 ↦ᵣ scratchBase) **
          (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
          (.x5 ↦ᵣ v5) **
          bytesRegion scratchBase st)
        ((.x8 ↦ᵣ scratchBase) **
          (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
          (regOwn .x5) **
          bytesRegion scratchBase (keccakGuestPad st rem)) :=
    keccakPadBlock_spec cr padHdr scratchBase st rem v5
      hst hrem halign h_over hvalidRem hvalid135
      hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 hmem6
  have hcoreOwn : cpsTripleWithin 7 padHdr (padHdr + 28) cr
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (regOwn .x5) **
        bytesRegion scratchBase st)
      ((.x8 ↦ᵣ scratchBase) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
        (regOwn .x5) **
        bytesRegion scratchBase (keccakGuestPad st rem)) := by
    -- reassoc to P ** own x5 then of_forall1
    have h (v5 : Word) : cpsTripleWithin 7 padHdr (padHdr + 28) cr
        ((((.x8 ↦ᵣ scratchBase) **
          (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem))) **
          bytesRegion scratchBase st) ** (.x5 ↦ᵣ v5))
        ((.x8 ↦ᵣ scratchBase) **
          (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
          (regOwn .x5) **
          bytesRegion scratchBase (keccakGuestPad st rem)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (hcore v5)
    have hown := of_forall1 h
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hown
  have hF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
      (regOwn .x10) **
      regOwns keccakPadRestOwns **
      bytesRegion outputBase out ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (pcFree_regOwns _) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA) hcoreOwn
  refine cpsTripleWithin_weaken (fun _ hp => by
      simp only [keccakPadPre, keccakPadCsrsAmb] at hp ⊢; xperm_hyp hp)
    (fun _ hq => by
      simp only [keccakPadPost, keccakPadCsrsAmb] at hq ⊢; xperm_hyp hq) hF

/-- Drop x28 to own and assemble full `keccakCsrsRest` for final CSRS. -/
theorem padPost_to_csrsPre (h : PartialState)
    (scratchBase outputBase : Word) (st out : List (BitVec 8)) (A : Assertion)
    (hp : keccakPadPost scratchBase outputBase st out A h) :
    ((.x8 ↦ᵣ scratchBase) ** (regOwn .x10) **
      regOwns keccakCsrsRest **
      bytesRegion scratchBase st **
      ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion outputBase out ** A)) h := by
  have hp1 : (
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 135)) **
        (regOwn .x5) **
        (.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        regOwns keccakPadRestOwns **
        bytesRegion scratchBase st ** bytesRegion outputBase out ** A) h := by
    simpa [keccakPadPost, keccakPadCsrsAmb] using hp
  -- drop x28 value → own
  have hp2 : (
      (regOwn .x28) **
        (regOwn .x5) **
        (.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        regOwns keccakPadRestOwns **
        bytesRegion scratchBase st ** bytesRegion outputBase out ** A) h :=
    sepConj_mono (regIs_implies_regOwn .x28) (fun _ => id) _ hp1
  -- unfold padRest, xperm into csrsRest shape, fold
  have unfolded : (
      (regOwn .x28) ** (regOwn .x5) **
        (.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
        (regOwn .x10) **
        ((regOwn .x6) ** (regOwn .x7) ** (regOwn .x29) ** (regOwn .x30) **
          (regOwn .x31) ** (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) **
          (regOwn .x14) ** (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) **
          empAssertion) **
        bytesRegion scratchBase st ** bytesRegion outputBase out ** A) h := by
    simpa [regOwns, keccakPadRestOwns, regOwn] using hp2
  have goal : (
      (.x8 ↦ᵣ scratchBase) ** (regOwn .x10) **
        ((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) **
          (regOwn .x29) ** (regOwn .x30) ** (regOwn .x31) **
          (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
          (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion) **
        bytesRegion scratchBase st **
        ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion outputBase out ** A)) h := by
    xperm_hyp unfolded
  simpa [regOwns, keccakCsrsRest, regOwn] using goal

/-- Final CSRS under pad ambient (peel own x10). Fuel 2. -/
theorem keccakFinalCsrs_framed (cr : CodeReq) (csrsHdr : Word)
    (scratchBase outputBase : Word) (st out : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200) (_hout : out.length = 32)
    (halign : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmemMv : ∀ a i, CodeReq.singleton csrsHdr (.MV .x10 .x8) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (csrsHdr + 4)
        (.CSRS (2048 : BitVec 12) .x10) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 csrsHdr (csrsHdr + 8) cr
      ((.x8 ↦ᵣ scratchBase) ** (regOwn .x10) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase st **
        ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion outputBase out ** A))
      ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) **
        ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion outputBase out ** A)) := by
  have hA' : ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion outputBase out ** A).pcFree :=
    pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA
  have hcore (v10 : Word) :
      cpsTripleWithin 2 csrsHdr (csrsHdr + 8) cr
        ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ v10) **
          regOwns keccakCsrsRest ** bytesRegion scratchBase st **
          ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion outputBase out ** A))
        ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
          regOwns keccakCsrsRest **
          bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) **
          ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion outputBase out ** A)) :=
    keccakFinalCsrs_spec cr csrsHdr scratchBase st
      ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion outputBase out ** A)
      hA' hst halign hvalid v10 hmemMv hmemCsrs
  -- peel own x10: reassoc to (x8 ** rest) ** own x10
  have h (v10 : Word) : cpsTripleWithin 2 csrsHdr (csrsHdr + 8) cr
      (((.x8 ↦ᵣ scratchBase) **
          regOwns keccakCsrsRest ** bytesRegion scratchBase st **
          ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion outputBase out ** A)) ** (.x10 ↦ᵣ v10))
      ((.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) **
        ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion outputBase out ** A)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (hcore v10)
  have hown := of_forall1 h
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) hown

/-- Digest under post-CSRS ambient (own x5 from csrsRest). Fuel 8. -/
theorem keccakDigest_framed (cr : CodeReq) (digHdr : Word)
    (scratchBase outputBase : Word) (st : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200)
    (hmemLd0 : ∀ a i, CodeReq.singleton digHdr
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 0))) a = some i → cr a = some i)
    (hmemSd0 : ∀ a i, CodeReq.singleton (digHdr + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 0))) a = some i → cr a = some i)
    (hmemLd1 : ∀ a i, CodeReq.singleton (digHdr + 8)
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 1))) a = some i → cr a = some i)
    (hmemSd1 : ∀ a i, CodeReq.singleton ((digHdr + 8) + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 1))) a = some i → cr a = some i)
    (hmemLd2 : ∀ a i, CodeReq.singleton (digHdr + 16)
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 2))) a = some i → cr a = some i)
    (hmemSd2 : ∀ a i, CodeReq.singleton ((digHdr + 16) + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 2))) a = some i → cr a = some i)
    (hmemLd3 : ∀ a i, CodeReq.singleton (digHdr + 24)
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 3))) a = some i → cr a = some i)
    (hmemSd3 : ∀ a i, CodeReq.singleton ((digHdr + 24) + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 3))) a = some i → cr a = some i) :
    cpsTripleWithin 8 digHdr (digHdr + 32) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (regOwn .x5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) ** A)
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (regOwn .x5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase (keccakDigestCopy st) ** A) := by
  have hcore (v5 : Word) :
      cpsTripleWithin 8 digHdr (digHdr + 32) cr
        ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (.x5 ↦ᵣ v5) **
          bytesRegion scratchBase st **
          bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)))
        ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (regOwn .x5) **
          bytesRegion scratchBase st **
          bytesRegion outputBase (keccakDigestCopy st)) :=
    keccakDigestAll_spec cr digHdr scratchBase outputBase st hst v5
      hmemLd0 hmemSd0 hmemLd1 hmemSd1 hmemLd2 hmemSd2 hmemLd3 hmemSd3
  have h (v5 : Word) : cpsTripleWithin 8 digHdr (digHdr + 32) cr
      ((((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase)) **
          bytesRegion scratchBase st **
          bytesRegion outputBase (List.replicate 32 (0 : BitVec 8))) **
        (.x5 ↦ᵣ v5))
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (regOwn .x5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase (keccakDigestCopy st)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (hcore v5)
  have hown := of_forall1 h
  have hcoreOwn : cpsTripleWithin 8 digHdr (digHdr + 32) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (regOwn .x5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)))
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) ** (regOwn .x5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase (keccakDigestCopy st)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hown
  have hF := cpsTripleWithin_frameR A hA hcoreOwn
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hF

/-- Post-CSRS ambient before digest: x10=scratch, full csrsRest owns, final state. -/
def keccakPostCsrsAmb (scratchBase outputBase : Word)
    (st out : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
    regOwns keccakCsrsRest **
    bytesRegion scratchBase st **
    ((.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion outputBase out ** A)

/-- csrsRest without x5 (digest clobbers x5). -/
def keccakCsrsRestNoX5 : List Reg :=
  [.x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Peel own x5 from csrsRest for digest focus. -/
theorem postCsrs_to_digestPre (h : PartialState)
    (scratchBase outputBase : Word) (st : List (BitVec 8)) (A : Assertion)
    (hp : keccakPostCsrsAmb scratchBase outputBase st
      (List.replicate 32 (0 : BitVec 8)) A h) :
    ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
      (regOwn .x5) **
      bytesRegion scratchBase st **
      bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) **
      ((.x10 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakCsrsRestNoX5 ** A)) h := by
  have hp1 : (
      (.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase st **
        (.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) ** A) h := by
    simpa [keccakPostCsrsAmb] using hp
  have unfolded : (
      (.x8 ↦ᵣ scratchBase) ** (.x10 ↦ᵣ scratchBase) **
        ((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) **
          (regOwn .x29) ** (regOwn .x30) ** (regOwn .x31) **
          (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
          (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion) **
        bytesRegion scratchBase st **
        (.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) ** A) h := by
    simpa [regOwns, keccakCsrsRest, regOwn] using hp1
  have goal : (
      (.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (regOwn .x5) **
        bytesRegion scratchBase st **
        bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) **
        (.x10 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        ((regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) **
          (regOwn .x29) ** (regOwn .x30) ** (regOwn .x31) **
          (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
          (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion) **
        A) h := by
    xperm_hyp unfolded
  simpa [regOwns, keccakCsrsRestNoX5, regOwn] using goal

/-- Full pad → final CSRS → digest → LI0 (fuel 7+2+8+1 = 18).
    Starts at padHdr, ends at li0+4. Output must be zeroed 32 B on entry. -/
theorem keccakPadCsrsDigestLi0_spec (cr : CodeReq) (padHdr : Word)
    (scratchBase outputBase : Word) (st : List (BitVec 8)) (rem : Nat)
    (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200) (hrem : rem ≤ 135)
    (halign : scratchBase.toNat % 8 = 0)
    (h_over : scratchBase.toNat + 200 ≤ 2 ^ 64)
    (hvalidRem : isValidByteAccess (scratchBase + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess (scratchBase + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    -- pad mem
    (hmemP0 : ∀ a i, CodeReq.singleton padHdr (.LBU .x5 .x28 0) a = some i →
      cr a = some i)
    (hmemP1 : ∀ a i, CodeReq.singleton (padHdr + 4) (.XORI .x5 .x5 1) a = some i →
      cr a = some i)
    (hmemP2 : ∀ a i, CodeReq.singleton (padHdr + 8) (.SB .x28 .x5 0) a = some i →
      cr a = some i)
    (hmemP3 : ∀ a i, CodeReq.singleton (padHdr + 12) (.ADDI .x28 .x8 135) a = some i →
      cr a = some i)
    (hmemP4 : ∀ a i, CodeReq.singleton (padHdr + 16) (.LBU .x5 .x28 0) a = some i →
      cr a = some i)
    (hmemP5 : ∀ a i, CodeReq.singleton (padHdr + 20) (.XORI .x5 .x5 128) a = some i →
      cr a = some i)
    (hmemP6 : ∀ a i, CodeReq.singleton (padHdr + 24) (.SB .x28 .x5 0) a = some i →
      cr a = some i)
    -- csrs mem (padHdr+28)
    (hmemMv : ∀ a i, CodeReq.singleton (padHdr + 28) (.MV .x10 .x8) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton ((padHdr + 28) + 4)
        (.CSRS (2048 : BitVec 12) .x10) a = some i →
      cr a = some i)
    -- digest mem (padHdr+36)
    (hmemLd0 : ∀ a i, CodeReq.singleton (padHdr + 36)
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 0))) a = some i → cr a = some i)
    (hmemSd0 : ∀ a i, CodeReq.singleton ((padHdr + 36) + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 0))) a = some i → cr a = some i)
    (hmemLd1 : ∀ a i, CodeReq.singleton ((padHdr + 36) + 8)
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 1))) a = some i → cr a = some i)
    (hmemSd1 : ∀ a i, CodeReq.singleton (((padHdr + 36) + 8) + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 1))) a = some i → cr a = some i)
    (hmemLd2 : ∀ a i, CodeReq.singleton ((padHdr + 36) + 16)
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 2))) a = some i → cr a = some i)
    (hmemSd2 : ∀ a i, CodeReq.singleton (((padHdr + 36) + 16) + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 2))) a = some i → cr a = some i)
    (hmemLd3 : ∀ a i, CodeReq.singleton ((padHdr + 36) + 24)
        (.LD .x5 .x8 (BitVec.ofNat 12 (8 * 3))) a = some i → cr a = some i)
    (hmemSd3 : ∀ a i, CodeReq.singleton (((padHdr + 36) + 24) + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 3))) a = some i → cr a = some i)
    -- li0 mem (padHdr+68)
    (hmemLi : ∀ a i, CodeReq.singleton (padHdr + 68) (.LI .x10 (0 : Word)) a = some i →
      cr a = some i) :
    cpsTripleWithin 18 padHdr (padHdr + 72) cr
      (keccakPadPre scratchBase outputBase rem st
        (List.replicate 32 (0 : BitVec 8)) A)
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (regOwn .x5) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase
          (setBytes (keccakGuestPad st rem) 0
            (keccakBytes (keccakGuestPad st rem) 0)) **
        bytesRegion outputBase
          (keccakDigestCopy
            (setBytes (keccakGuestPad st rem) 0
              (keccakBytes (keccakGuestPad st rem) 0))) **
        ((.x0 ↦ᵣ (0 : Word)) ** regOwns keccakCsrsRestNoX5 ** A)) := by
  let out0 := List.replicate 32 (0 : BitVec 8)
  have hout0 : out0.length = 32 := by simp only [out0, List.length_replicate]
  -- 1. pad
  have cPad := keccakPad_framed cr padHdr scratchBase outputBase st out0 rem A hA
    hst hout0 hrem halign h_over hvalidRem hvalid135
    hmemP0 hmemP1 hmemP2 hmemP3 hmemP4 hmemP5 hmemP6
  let stPad := keccakGuestPad st rem
  have hstPad : stPad.length = 200 := by
    simp only [stPad, keccakGuestPad, length_setBytes, hst]
  -- 2. reshape pad post → csrs pre + run CSRS
  have cCsrs : cpsTripleWithin 2 (padHdr + 28) (padHdr + 36) cr
      (keccakPadPost scratchBase outputBase stPad out0 A)
      (keccakPostCsrsAmb scratchBase outputBase
        (setBytes stPad 0 (keccakBytes stPad 0)) out0 A) := by
    have hpc28_8 : (padHdr + 28 : Word) + 8 = padHdr + 36 := by
      rw [BitVec.add_assoc, show ((28 : Word) + 8) = (36 : Word) from by decide]
    have hraw := keccakFinalCsrs_framed cr (padHdr + 28) scratchBase outputBase
      stPad out0 A hA hstPad hout0 halign hvalidMem hmemMv hmemCsrs
    rw [hpc28_8] at hraw
    refine cpsTripleWithin_weaken
      (fun h hp => padPost_to_csrsPre h scratchBase outputBase stPad out0 A hp)
      (fun _ hq => by simpa [keccakPostCsrsAmb] using hq) hraw
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) cPad cCsrs
  let stFinal := setBytes stPad 0 (keccakBytes stPad 0)
  have hstFinal : stFinal.length = 200 := by
    simp only [stFinal, length_setBytes, hstPad]
  -- 3. reshape → digest
  have cDig : cpsTripleWithin 8 (padHdr + 36) (padHdr + 68) cr
      (keccakPostCsrsAmb scratchBase outputBase stFinal out0 A)
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (regOwn .x5) **
        bytesRegion scratchBase stFinal **
        bytesRegion outputBase (keccakDigestCopy stFinal) **
        ((.x10 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwns keccakCsrsRestNoX5 ** A)) := by
    have hpc36_32 : (padHdr + 36 : Word) + 32 = padHdr + 68 := by
      rw [BitVec.add_assoc, show ((36 : Word) + 32) = (68 : Word) from by decide]
    have hdig := keccakDigest_framed cr (padHdr + 36) scratchBase outputBase stFinal
      ((.x10 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakCsrsRestNoX5 ** A)
      (pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (pcFree_regOwns _) hA)
      hstFinal hmemLd0 hmemSd0 hmemLd1 hmemSd1 hmemLd2 hmemSd2 hmemLd3 hmemSd3
    rw [hpc36_32] at hdig
    refine cpsTripleWithin_weaken
      (fun h hp => postCsrs_to_digestPre h scratchBase outputBase stFinal A hp)
      (fun _ hq => by xperm_hyp hq) hdig
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) c01 cDig
  -- 4. LI a0,0
  have cLi0 : cpsTripleWithin 1 (padHdr + 68) (padHdr + 72) cr
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (regOwn .x5) **
        bytesRegion scratchBase stFinal **
        bytesRegion outputBase (keccakDigestCopy stFinal) **
        ((.x10 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwns keccakCsrsRestNoX5 ** A))
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (regOwn .x5) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase stFinal **
        bytesRegion outputBase (keccakDigestCopy stFinal) **
        ((.x0 ↦ᵣ (0 : Word)) ** regOwns keccakCsrsRestNoX5 ** A)) := by
    have hli := keccakLi0_spec cr (padHdr + 68) scratchBase hmemLi
    have hpc68_4 : (padHdr + 68 : Word) + 4 = padHdr + 72 := by
      rw [BitVec.add_assoc, show ((68 : Word) + 4) = (72 : Word) from by decide]
    rw [hpc68_4] at hli
    have hliF := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ outputBase) **
        (regOwn .x5) **
        bytesRegion scratchBase stFinal **
        bytesRegion outputBase (keccakDigestCopy stFinal) **
        ((.x0 ↦ᵣ (0 : Word)) ** regOwns keccakCsrsRestNoX5 ** A))
      (pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (bytesRegion_pcFree _ _) <|
        pcFree_sepConj (bytesRegion_pcFree _ _) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (pcFree_regOwns _) hA) hli
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hliF
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) c012 cLi0
  -- fold stPad/stFinal names into post
  refine cpsTripleWithin_weaken (fun _ hp => by simpa [out0] using hp)
    (fun _ hq => by simpa [out0, stPad, stFinal] using hq) cAll

end EvmAsm.Codegen.Proofs
