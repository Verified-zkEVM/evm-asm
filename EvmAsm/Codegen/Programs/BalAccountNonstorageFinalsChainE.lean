/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainE

  Balance-station assembly, inner continuations (bead evm-asm-4ch8f.43.5,
  slice 4g).  Composed inside-out: each `bansf_balStationContNNN_spec`
  carries the station frame from program point `B + NNN` to the two station
  exits (`B + 736` reject / `B + 352` `balStationPost`), taking a
  `FieldFinal`-constructor hypothesis in place of the walk facts its callers
  have already accumulated.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainD

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- Single-register variant of the `regOwn` introduction for branches. -/
theorem cpsBranchWithin_of_forall_regIs_to_regOwn1
    {n : Nat} {entry : Word} {r1 : Reg}
    {P : Assertion} {e1 : Word} {Q1 : Assertion} {e2 : Word} {Q2 : Assertion}
    {cr : CodeReq}
    (h : ∀ v1, cpsBranchWithin n entry cr (P ** (r1 ↦ᵣ v1)) e1 Q1 e2 Q2) :
    cpsBranchWithin n entry cr (P ** regOwn r1) e1 Q1 e2 Q2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, ⟨v1, hv1⟩⟩ := hPP
  exact h v1 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu, ⟨g0, g1, d1, u1, hP0, hv1⟩, hRb⟩ hpc

#print axioms cpsBranchWithin_of_forall_regIs_to_regOwn1

/-- Continuation at `B + 324` (the value item decoded): run the capture
    block; route its exits to the station posts.  `hFF` finishes the
    `FieldFinal` derivation from the value decode (the callers hold the
    walk facts). -/
theorem bansf_balStationCont324_spec (aB newSp oB : Word)
    (aLen tEnd offV fOff fSpanN : Nat) (n3 : Word)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hoalign : oB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hovout : oB.toNat + 80 ≤ 2 ^ 64)
    (hovalid : ∀ k, k < 80 → isValidByteAccess (oB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffle : offV ≤ tEnd)
    (hFF : ∀ vNext vLen : Word,
      rlpItemDecode acctBytes offV (aB + BitVec.ofNat 64 offV)
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      vLen.toNat ≤ 32 →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsBranchWithin 300 (B + 324) bansfCR
      (fun h => ∃ vNext vLen : Word,
        (((((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
           ((.x12 : Reg) ↦ᵣ vLen) **
           ((.x2 : Reg) ↦ᵣ newSp) **
           memOwn (newSp + 64) ** memOwn (newSp + 72) **
           ((newSp + 48) ↦ₘ n3) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) **
           regOwn .x19 ** regOwn .x20 **
           (oB ↦ₘ (0 : Word)) **
           ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
           ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aB acctBytes ** F) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
         ⌜rlpItemDecode acctBytes offV (aB + BitVec.ofNat 64 offV)
           (aB + BitVec.ofNat 64 tEnd) vNext vLen⌝) h)
      (B + 736) (balStationRej aB newSp oB aLen acctBytes F)
      (B + 352) (balStationPost aB newSp oB aLen fOff fSpanN n3 acctBytes F) := by
  refine cpsBranchWithin_exists_pre (fun vNext => ?_)
  refine cpsBranchWithin_exists_pre (fun vLen => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hdecV => ?_)
  refine cpsBranchWithin_of_forall_regIs_to_regOwn8
    (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
  have hbc := bansf_balCapture_spec aB newSp oB aLen tEnd offV vNext vLen
    acctBytes v5 v6 v7 v28 v29 v30 v31 vRa F hF hsalign hoalign hslack
    hover hvalid hovout hovalid htEnd hoffle hdecV
  have hbcF := cpsBranchWithin_frameR
    (((newSp + 48) ↦ₘ n3) ** ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     memOwn (newSp + 64) ** memOwn (newSp + 72) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
     regOwn .x19 ** regOwn .x20)
    (by pcf) hbc
  refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => ?_) (fun h hq => ?_)
    (cpsBranchWithin_mono_nSteps (by omega) hbcF)
  · -- reject exit: (balCaptureRej ** frame) ⇒ balStationRej
    unfold balCaptureRej at hq
    unfold balStationRej
    have hq2 : (((((newSp + 48) ↦ₘ n3) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        (oB ↦ₘ (0 : Word))) **
       (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) **
        memOwnU256 (oB + 8) **
        regOwn .x19 ** regOwn .x20 **
        regOwn .x11 ** regOwn .x12 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F))) h := by
      xperm_hyp hq
    have hq3 := sepConj_mono
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))
      (fun _ x => x) h hq2
    xperm_hyp hq3
  · -- success exit: (balCaptureOk ** frame) ⇒ balStationPost FOUND arm
    unfold balCaptureOk at hq
    obtain ⟨g1, g2, gd, gu, hXp, hfr⟩ := hq
    obtain ⟨hX, h32⟩ := (sepConj_pure_right g1).1 hXp
    unfold balStationPost
    refine Or.inr ⟨vNext, vLen, ?_⟩
    refine (sepConj_pure_right h).2 ⟨?_, ⟨hFF vNext vLen hdecV h32, h32⟩⟩
    have hR : ((((oB ↦ₘ (1 : Word)) **
        bytesRegion (oB + 8) (copyN (List.replicate 32 (0 : BitVec 8)) acctBytes
          (32 - vLen.toNat) ((vNext - vLen - aB).toNat) vLen.toNat) **
        ((.x18 : Reg) ↦ᵣ oB) ** ((.x2 : Reg) ↦ᵣ newSp) **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F) **
       (((newSp + 48) ↦ₘ n3) ** ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        regOwn .x19 ** regOwn .x20))) h := ⟨g1, g2, gd, gu, hX, hfr⟩
    xperm_hyp hR

#print axioms bansf_balStationCont324_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
