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

/-- Continuation at `B + 308` (the tuple's INDEX item decoded, cursor
    spilled): run the value item unit, then the capture continuation.
    `hFF2` finishes the `FieldFinal` derivation from the index/value
    decode pair. -/
theorem bansf_balStationCont308_spec (aB newSp oB : Word)
    (aLen tEnd offI fOff fSpanN : Nat) (n3 : Word)
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
    (htEnd : tEnd ≤ aLen) (hoffleI : offI ≤ tEnd)
    (hFF2 : ∀ iNext iLen vNext vLen : Word,
      rlpItemDecode acctBytes offI (aB + BitVec.ofNat 64 offI)
        (aB + BitVec.ofNat 64 tEnd) iNext iLen →
      rlpItemDecode acctBytes ((iNext - aB).toNat) iNext
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      vLen.toNat ≤ 32 →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsBranchWithin 400 (B + 308) bansfCR
      (fun h => ∃ next len : Word,
        (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
           ((.x12 : Reg) ↦ᵣ len) **
           ((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 64) ↦ₘ next) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
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
         ⌜rlpItemDecode acctBytes offI (aB + BitVec.ofNat 64 offI)
           (aB + BitVec.ofNat 64 tEnd) next len⌝) h)
      (B + 736) (balStationRej aB newSp oB aLen acctBytes F)
      (B + 352) (balStationPost aB newSp oB aLen fOff fSpanN n3 acctBytes F) := by
  refine cpsBranchWithin_exists_pre (fun next => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hdecI => ?_)
  obtain ⟨hrepI, hltI, hleI⟩ := rlpItemDecode_advance hdecI hoffleI (by omega)
  set offN := (next - aB).toNat with hoffN
  rw [hrepI]
  refine cpsBranchWithin_of_forall_regIs_to_regOwn8
    (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
  -- the out cells fold back into the owned output token
  have hmemU : ∀ h, ((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
      ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) h) →
      memOwnU256 (oB + 8) h := by
    intro h hp
    rw [show oB + 16 = (oB + 8) + 8 from by bv_omega,
        show oB + 24 = (oB + 8) + 16 from by bv_omega,
        show oB + 32 = (oB + 8) + 24 from by bv_omega] at hp
    exact sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)) h hp
  -- the value item unit (slots 77–80)
  have hti := bansf_tupleItem1_spec aB newSp aLen tEnd offN
    acctBytes v5 v6 v7 (aB + BitVec.ofNat 64 offN) (0 : Word) len
    v28 v29 v30 v31 vRa F hF hsalign hslack hover hvalid htEnd hleI
  have htiF := cpsBranchWithin_frameR
    (((newSp + 48) ↦ₘ n3) ** ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
     ((.x18 : Reg) ↦ᵣ oB) **
     regOwn .x19 ** regOwn .x20 **
     (oB ↦ₘ (0 : Word)) **
     ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
     ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))
    (by pcf) hti
  -- the capture continuation at B + 324, pre-weakened to the unit's ok exit
  have hc324 := bansf_balStationCont324_spec aB newSp oB aLen tEnd
    offN fOff fSpanN n3 acctBytes F hF hsalign hoalign hslack
    hover hvalid hovout hovalid htEnd hleI
    (fun vNext vLen hdecV h32 =>
      hFF2 next len vNext vLen hdecI (by rw [← hoffN, hrepI]; exact hdecV) h32)
  have himp : ∀ h, ((tupleValOk aB newSp tEnd offN acctBytes F **
      (((newSp + 48) ↦ₘ n3) ** ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) **
       regOwn .x19 ** regOwn .x20 **
       (oB ↦ₘ (0 : Word)) **
       ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
       ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))) h) →
      (∃ vNext vLen : Word,
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
         ⌜rlpItemDecode acctBytes offN (aB + BitVec.ofNat 64 offN)
           (aB + BitVec.ofNat 64 tEnd) vNext vLen⌝) h) := by
    intro h hp
    unfold tupleValOk at hp
    obtain ⟨g1, g2, gd, gu, hVin, hfr⟩ := hp
    obtain ⟨vN, vL, hVin2⟩ := hVin
    obtain ⟨hat, hdecv⟩ := (sepConj_pure_right g1).1 hVin2
    have hR := (⟨g1, g2, gd, gu, hat, hfr⟩ :
      (((((.x10 : Reg) ↦ᵣ vN) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ vL) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F) **
       (((newSp + 48) ↦ₘ n3) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x19 ** regOwn .x20 **
        (oB ↦ₘ (0 : Word)) **
        ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
        ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))) h))
    have hR2 : ((((.x10 : Reg) ↦ᵣ vN) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ vL) **
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
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) h := by
      have heq : ((((.x10 : Reg) ↦ᵣ vN) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ vL) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          memOwn (newSp + 64) ** memOwn (newSp + 72) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F) **
         (((newSp + 48) ↦ₘ n3) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
          ((.x18 : Reg) ↦ᵣ oB) **
          regOwn .x19 ** regOwn .x20 **
          (oB ↦ₘ (0 : Word)) **
          ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
          ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))))
          = ((((.x10 : Reg) ↦ᵣ vN) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ vL) **
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
         regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) := by
        xperm
      exact (congrFun heq h).mp hR
    exact ⟨vN, vL, (sepConj_pure_right h).2 ⟨hR2, hdecv⟩⟩
  have hc324' := cpsBranchWithin_weaken himp (fun _ x => x) (fun _ x => x) hc324
  have htiW := cpsBranchWithin_weaken
    (Q_t' := balStationRej aB newSp oB aLen acctBytes F)
    (fun _ x => x)
    (fun h hq => by
      -- reject exit: (tupleRej ** frame) ⇒ balStationRej
      unfold tupleRej at hq
      unfold balStationRej
      have hq2 : (((((newSp + 48) ↦ₘ n3) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          (oB ↦ₘ (0 : Word))) **
         ((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
           ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) **
          (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
           memOwn (newSp + 64) ** memOwn (newSp + 72) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) **
           regOwn .x19 ** regOwn .x20 **
           regOwn .x11 ** regOwn .x12 **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
           bytesRegion aB acctBytes ** F)))) h := by
        xperm_hyp hq
      have hq3 := sepConj_mono
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))
        (sepConj_mono hmemU (fun _ x => x)) h hq2
      xperm_hyp hq3)
    (fun _ x => x) htiF
  have hchain := cpsBranchWithin_chain_snd htiW hc324'
  exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ x => x) (fun _ x => x)
    (cpsBranchWithin_mono_nSteps (by omega) hchain)

#print axioms bansf_balStationCont308_spec

/-- Continuation at `B + 280` (the tuple window's `rlp_walk_init`
    succeeded): spill the tuple cursor/end, run the index item unit, then
    the value/capture continuations.  `hFFT` finishes the `FieldFinal`
    derivation from the assembled `TupleValueWindow`. -/
theorem bansf_balStationCont280_spec (aB newSp oB : Word)
    (aLen tOff tSpanN fOff fSpanN : Nat) (n3 : Word)
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
    (htEnd2 : tOff + tSpanN ≤ aLen)
    (hFFT : ∀ vNext vLen : Word,
      TupleValueWindow acctBytes aB tOff tSpanN vNext vLen →
      vLen.toNat ≤ 32 →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsBranchWithin 500 (B + 280) bansfCR
      (fun h => ∃ cOff2 : Nat,
        (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff2)) **
           ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
           ((.x12 : Reg) ↦ᵣ (0 : Word)) **
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
         ⌜FieldInitOk acctBytes tOff tSpanN cOff2⌝) h)
      (B + 736) (balStationRej aB newSp oB aLen acctBytes F)
      (B + 352) (balStationPost aB newSp oB aLen fOff fSpanN n3 acctBytes F) := by
  refine cpsBranchWithin_exists_pre (fun cOff2 => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
  obtain ⟨b2, hb2, hceq2, hclt2, hcle2⟩ := hok
  refine cpsBranchWithin_of_forall_regIs_to_regOwn8
    (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
  -- the out cells fold back into the owned output token
  have hmemU : ∀ h, ((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
      ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) h) →
      memOwnU256 (oB + 8) h := by
    intro h hp
    rw [show oB + 16 = (oB + 8) + 8 from by bv_omega,
        show oB + 24 = (oB + 8) + 16 from by bv_omega,
        show oB + 32 = (oB + 8) + 24 from by bv_omega] at hp
    exact sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)) h hp
  -- slots 70–71: spill the tuple cursor/end
  have hsp := bansf_tupleSpill70_spec newSp (aB + BitVec.ofNat 64 cOff2)
    (aB + BitVec.ofNat 64 (tOff + tSpanN))
  have hspF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ (0 : Word)) **
     ((newSp + 48) ↦ₘ n3) ** ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
     ((.x18 : Reg) ↦ᵣ oB) **
     regOwn .x19 ** regOwn .x20 **
     (oB ↦ₘ (0 : Word)) **
     ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
     ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hsp
  -- the index item unit (slots 72–76)
  have hti := bansf_tupleItem0_spec aB newSp (tOff + tSpanN) cOff2 acctBytes
    v5 v6 v7 (aB + BitVec.ofNat 64 cOff2)
    (aB + BitVec.ofNat 64 (tOff + tSpanN)) (0 : Word)
    v28 v29 v30 v31 vRa F hF hsalign (by omega) hover hvalid hcle2
  have htiF := cpsBranchWithin_frameR
    (((newSp + 48) ↦ₘ n3) ** ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
     ((.x18 : Reg) ↦ᵣ oB) **
     regOwn .x19 ** regOwn .x20 **
     (oB ↦ₘ (0 : Word)) **
     ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
     ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))
    (by pcf) hti
  have htiW := cpsBranchWithin_weaken
    (Q_t' := balStationRej aB newSp oB aLen acctBytes F)
    (fun _ x => x)
    (fun h hq => by
      unfold tupleRej at hq
      unfold balStationRej
      have hq2 : (((((newSp + 48) ↦ₘ n3) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          (oB ↦ₘ (0 : Word))) **
         ((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
           ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) **
          (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
           memOwn (newSp + 64) ** memOwn (newSp + 72) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) **
           regOwn .x19 ** regOwn .x20 **
           regOwn .x11 ** regOwn .x12 **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
           bytesRegion aB acctBytes ** F)))) h := by
        xperm_hyp hq
      have hq3 := sepConj_mono
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))
        (sepConj_mono hmemU (fun _ x => x)) h hq2
      xperm_hyp hq3)
    (fun _ x => x) htiF
  -- the value/capture continuation at B + 308
  have hc308 := bansf_balStationCont308_spec aB newSp oB aLen (tOff + tSpanN)
    cOff2 fOff fSpanN n3 acctBytes F hF hsalign hoalign hslack hover hvalid
    hovout hovalid htEnd2 hcle2
    (fun iNext iLen vNext vLen hdecI hdecV h32 =>
      hFFT vNext vLen ⟨b2, hb2, iNext, iLen, hceq2 ▸ hdecI, hdecV⟩ h32)
  have himp : ∀ h, ((tupleOk aB newSp (tOff + tSpanN) cOff2 acctBytes F **
      (((newSp + 48) ↦ₘ n3) ** ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) **
       regOwn .x19 ** regOwn .x20 **
       (oB ↦ₘ (0 : Word)) **
       ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
       ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))) h) →
      (∃ next len : Word,
        (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
           ((.x12 : Reg) ↦ᵣ len) **
           ((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 64) ↦ₘ next) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
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
         ⌜rlpItemDecode acctBytes cOff2 (aB + BitVec.ofNat 64 cOff2)
           (aB + BitVec.ofNat 64 (tOff + tSpanN)) next len⌝) h) := by
    intro h hp
    unfold tupleOk at hp
    obtain ⟨g1, g2, gd, gu, hVin, hfr⟩ := hp
    obtain ⟨nn, ll, hVin2⟩ := hVin
    obtain ⟨hat, hdecn⟩ := (sepConj_pure_right g1).1 hVin2
    have hR := (⟨g1, g2, gd, gu, hat, hfr⟩ :
      (((((.x10 : Reg) ↦ᵣ nn) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ ll) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ nn) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F) **
       (((newSp + 48) ↦ₘ n3) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x19 ** regOwn .x20 **
        (oB ↦ₘ (0 : Word)) **
        ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
        ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))) h))
    have hR2 : ((((.x10 : Reg) ↦ᵣ nn) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ ll) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ nn) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
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
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) h := by
      have heq : ((((.x10 : Reg) ↦ᵣ nn) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ ll) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ nn) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F) **
         (((newSp + 48) ↦ₘ n3) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
          ((.x18 : Reg) ↦ᵣ oB) **
          regOwn .x19 ** regOwn .x20 **
          (oB ↦ₘ (0 : Word)) **
          ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
          ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))))
          = ((((.x10 : Reg) ↦ᵣ nn) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ ll) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ nn) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
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
         regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) := by
        xperm
      exact (congrFun heq h).mp hR
    exact ⟨nn, ll, (sepConj_pure_right h).2 ⟨hR2, hdecn⟩⟩
  have hc308' := cpsBranchWithin_weaken himp (fun _ x => x) (fun _ x => x) hc308
  have hchain := cpsBranchWithin_chain_snd htiW hc308'
  have hfull := cpsTripleWithin_seq_branch_same_cr hspF
    (cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ x => x) (fun _ x => x) hchain)
  exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ x => x) (fun _ x => x)
    (cpsBranchWithin_mono_nSteps (by omega) hfull)

#print axioms bansf_balStationCont280_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
