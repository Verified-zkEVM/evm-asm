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

/-- Seven-register variant of the `regOwn` introduction for branches. -/
theorem cpsBranchWithin_of_forall_regIs_to_regOwn7
    {n : Nat} {entry : Word} {r1 r2 r3 r4 r5 r6 r7 : Reg}
    {P : Assertion} {e1 : Word} {Q1 : Assertion} {e2 : Word} {Q2 : Assertion}
    {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5 v6 v7, cpsBranchWithin n entry cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) **
       (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** (r7 ↦ᵣ v7)) e1 Q1 e2 Q2) :
    cpsBranchWithin n entry cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 **
       regOwn r5 ** regOwn r6 ** regOwn r7) e1 Q1 e2 Q2 := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, hO5⟩ := hO4
  obtain ⟨g10, g11, d6, u6, ⟨v5, hv5⟩, hO6⟩ := hO5
  obtain ⟨g12, g13, d7, u7, ⟨v6, hv6⟩, ⟨v7, hv7⟩⟩ := hO6
  exact h v1 v2 v3 v4 v5 v6 v7 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3, hv2,
       g6, g7, d4, u4, hv3, g8, g9, d5, u5, hv4, g10, g11, d6, u6, hv5,
       g12, g13, d7, u7, hv6, hv7⟩, hRb⟩ hpc

#print axioms cpsBranchWithin_of_forall_regIs_to_regOwn7

/-- Continuation at `B + 264` (the find-last loop's clean exit): move the
    last tuple's span into the walker arguments, init the tuple window,
    then the item/value/capture continuations.  The field-window facts
    (`b`, `hb`, `hne`) finish the `FieldFinal.last` derivation. -/
theorem bansf_balStationCont264_spec (aB newSp oB : Word)
    (aLen fOff fSpanN : Nat) (n3 : Word) (b : BitVec 8)
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
    (hb : acctBytes[fOff]? = some b)
    (hne : fOff + listHeaderSize b ≠ fOff + fSpanN)
    (hoff0le : fOff + listHeaderSize b ≤ fOff + fSpanN)
    (hfE : fOff + fSpanN ≤ aLen) :
    cpsBranchWithin 590 (B + 264) bansfCR
      (fun h => ∃ n l : Word,
        (((((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l) **
           ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((newSp + 48) ↦ₘ n3) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) **
           (oB ↦ₘ (0 : Word)) **
           ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
           ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
           bytesRegion aB acctBytes ** F **
           regOwn .x10 ** regOwn .x11) **
          regOwn .x7 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
         ⌜LastItemAt acctBytes aB (aB + BitVec.ofNat 64 (fOff + fSpanN))
           (fOff + listHeaderSize b) n l⌝) h)
      (B + 736) (balStationRej aB newSp oB aLen acctBytes F)
      (B + 352) (balStationPost aB newSp oB aLen fOff fSpanN n3 acctBytes F) := by
  refine cpsBranchWithin_exists_pre (fun n => ?_)
  refine cpsBranchWithin_exists_pre (fun l => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hlast => ?_)
  refine cpsBranchWithin_of_forall_regIs_to_regOwn7
    (fun v7 v12 v28 v29 v30 v31 vRa => ?_)
  obtain ⟨offT, hoffTle, hdecT⟩ := LastItemAt_decode hlast hoff0le (by omega)
  obtain ⟨hrepT, hspleT, hspbT⟩ := rlpItemDecode_spanStart hdecT hoffTle (by omega)
  rw [hrepT]
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
  -- slots 66–67: move the span into the walker arguments (x10/x11 owned)
  have hmv : cpsTripleWithin 2 (B + 264) (B + 272) bansfCR
      (((((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l)) **
        regOwn .x10 ** regOwn .x11))
      ((((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l)) **
       ((.x10 : Reg) ↦ᵣ (n - l)) ** ((.x11 : Reg) ↦ᵣ l)) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v10 v11 => ?_)
    have hm := bansf_loopExitMove66_spec (n - l) l v10 v11
    have hmL := liftCode (cr' := bansfCR) hm
      (fun a i h => CodeReq.union_mono_left a i h)
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq) hmL
  have hmvF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
     ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
     ((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
     ((newSp + 48) ↦ₘ n3) **
     ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
     ((.x18 : Reg) ↦ᵣ oB) **
     (oB ↦ₘ (0 : Word)) **
     ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
     ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x7 : Reg) ↦ᵣ v7) ** ((.x12 : Reg) ↦ᵣ v12) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hmv
  rw [hrepT] at hmvF
  -- the tuple-window init (slot 68) + status check
  have hfi := bansf_fieldInit68_spec aB aLen ((n - l - aB).toNat) l acctBytes
    (aB + BitVec.ofNat 64 (fOff + fSpanN)) (aB + BitVec.ofNat 64 (fOff + fSpanN))
    v7 v12 v28 v29 v30 v31 vRa F hF hsalign hslack hover hvalid (by omega)
  have hfiF := cpsBranchWithin_frameR
    (((.x19 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n - l - aB).toNat))) **
     ((.x20 : Reg) ↦ᵣ l) **
     ((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
     ((newSp + 48) ↦ₘ n3) **
     ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
     ((.x18 : Reg) ↦ᵣ oB) **
     (oB ↦ₘ (0 : Word)) **
     ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
     ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))
    (by pcf) hfi
  have hfiW := cpsBranchWithin_weaken
    (Q_t' := balStationRej aB newSp oB aLen acctBytes F)
    (fun _ x => x)
    (fun h hq => by
      unfold fieldRej at hq
      unfold balStationRej
      have hq2 : (((((newSp + 48) ↦ₘ n3) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
          (oB ↦ₘ (0 : Word))) **
         ((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
           ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) **
          ((((.x19 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n - l - aB).toNat))) **
            ((.x20 : Reg) ↦ᵣ l)) **
           (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
            ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
            ((.x18 : Reg) ↦ᵣ oB) **
            regOwn .x11 ** regOwn .x12 **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
            bytesRegion aB acctBytes ** F))))) h := by
        xperm_hyp hq
      have hq3 := sepConj_mono
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))))
        (sepConj_mono hmemU
          (sepConj_mono
            (sepConj_mono (regIs_implies_regOwn .x19) (regIs_implies_regOwn .x20))
            (fun _ x => x))) h hq2
      xperm_hyp hq3)
    (fun _ x => x) hfiF
  -- the tuple continuation at B + 280
  have hc280 := bansf_balStationCont280_spec aB newSp oB aLen
    ((n - l - aB).toNat) l.toNat fOff fSpanN n3 acctBytes F hF hsalign hoalign
    hslack hover hvalid hovout hovalid (by omega)
    (fun vNext vLen htvw h32 =>
      FieldFinal.last b n l vNext vLen hb hne hlast htvw)
  have himp : ∀ h, ((fieldInitPost aB ((n - l - aB).toNat) l.toNat acctBytes
      (B + 272 + 4) F **
      (((.x19 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n - l - aB).toNat))) **
       ((.x20 : Reg) ↦ᵣ l) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
       ((newSp + 48) ↦ₘ n3) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) **
       (oB ↦ₘ (0 : Word)) **
       ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
       ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))) h) →
      (∃ cOff2 : Nat,
        (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff2)) **
           ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n - l - aB).toNat + l.toNat))) **
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
         ⌜FieldInitOk acctBytes ((n - l - aB).toNat) l.toNat cOff2⌝) h) := by
    intro h hp
    unfold fieldInitPost at hp
    obtain ⟨g1, g2, gd, gu, hVin, hfr⟩ := hp
    obtain ⟨cOff2, hVin2⟩ := hVin
    obtain ⟨hat, hokc⟩ := (sepConj_pure_right g1).1 hVin2
    have hR := (⟨g1, g2, gd, gu, hat, hfr⟩ :
      (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff2)) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n - l - aB).toNat + l.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 272 + 4)) **
        bytesRegion aB acctBytes ** F) **
       (((.x19 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n - l - aB).toNat))) **
        ((.x20 : Reg) ↦ᵣ l) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
        ((newSp + 48) ↦ₘ n3) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) **
        (oB ↦ₘ (0 : Word)) **
        ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
        ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))) h))
    have hconv := sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn .x19)
        (sepConj_mono (regIs_implies_regOwn .x20)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn (fun _ x => x)))))) h hR
    have hconv2 := sepConj_mono
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x)
              (sepConj_mono (fun _ x => x)
                (sepConj_mono (fun _ x => x)
                  (sepConj_mono (fun _ x => x)
                    (sepConj_mono (fun _ x => x)
                      (sepConj_mono (fun _ x => x)
                        (sepConj_mono (fun _ x => x)
                          (sepConj_mono (fun _ x => x)
                            (sepConj_mono (regIs_implies_regOwn .x1)
                              (fun _ x => x)))))))))))))
      (fun _ x => x) h hconv
    have hR2 : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff2)) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n - l - aB).toNat + l.toNat))) **
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
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) h := by
      xperm_hyp hconv2
    exact ⟨cOff2, (sepConj_pure_right h).2 ⟨hR2, hokc⟩⟩
  have hc280' := cpsBranchWithin_weaken himp (fun _ x => x) (fun _ x => x) hc280
  have hchain := cpsBranchWithin_chain_snd hfiW hc280'
  have hfull := cpsTripleWithin_seq_branch_same_cr hmvF
    (cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ x => x) (fun _ x => x) hchain)
  exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ x => x) (fun _ x => x)
    (cpsBranchWithin_mono_nSteps (by omega) hfull)

#print axioms bansf_balStationCont264_spec

/-- Continuation at `B + 208` (the balance-field `rlp_walk_init`
    succeeded): the empty-field split; on the non-empty side, spill the
    walk window and run the find-last loop into the tuple continuations. -/
theorem bansf_balStationCont208_spec (aB newSp oB : Word)
    (aLen fOff fSpanN : Nat) (n3 : Word)
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
    (hfE : fOff + fSpanN ≤ aLen) :
    cpsBranchWithin (98 * (aLen + 1) + 600) (B + 208) bansfCR
      (fun h => ∃ cOff : Nat,
        ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
          bytesRegion aB acctBytes ** F) **
         ⌜FieldInitOk acctBytes fOff fSpanN cOff⌝) h)
      (B + 736) (balStationRej aB newSp oB aLen acctBytes F)
      (B + 352) (balStationPost aB newSp oB aLen fOff fSpanN n3 acctBytes F) := by
  refine cpsBranchWithin_exists_pre (fun cOff => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
  obtain ⟨b, hbq, hceq, hclt, hcle⟩ := hok
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
  by_cases hce : cOff = fOff + fSpanN
  · -- EMPTY field list: BEQ taken straight to the nonce boundary
    have hbeq := bansf_balEmptyTaken_spec aB cOff (fOff + fSpanN) hce
    have hbeqL := liftCode (cr' := bansfCR) hbeq
      (fun a i h => CodeReq.union_mono_left a i h)
    have hbeqF := cpsTripleWithin_frameR
      (((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hbeqL
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ x => x) (fun h hq => ?_)
      (cpsBranchWithin_mono_nSteps (by omega)
        (cpsTripleWithin_as_cpsBranchWithin_right (B + 736)
          (balStationRej aB newSp oB aLen acctBytes F) hbeqF))
    unfold balStationPost
    refine Or.inl ((sepConj_pure_right h).2 ⟨?_, FieldFinal.empty b hbq (hceq ▸ hce)⟩)
    have hq2 : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
        ((oB ↦ₘ (0 : Word)) **
         ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
         ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
         ((newSp + 48) ↦ₘ n3) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         memOwn (newSp + 64) ** memOwn (newSp + 72) **
         ((.x2 : Reg) ↦ᵣ newSp) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) **
         regOwn .x19 ** regOwn .x20 **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion aB acctBytes ** F))) h := by
      xperm_hyp hq
    have hq3 := sepConj_mono (regIs_implies_regOwn .x10)
      (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x)))) h hq2
    xperm_hyp hq3
  · -- NON-EMPTY: fall through, spill the window, run the find-last loop
    have hfall := bansf_balEmptyFall_spec aB aLen cOff (fOff + fSpanN) hce
      (by omega) hfE (by omega)
    have hfallL := liftCode (cr' := bansfCR) hfall
      (fun a i h => CodeReq.union_mono_left a i h)
    have hfallF := cpsTripleWithin_frameR
      (((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hfallL
    have hentry := bansf_loopEntry53_spec aB newSp cOff (fOff + fSpanN)
    have hentryF := cpsTripleWithin_frameR
      (((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
       ((newSp + 48) ↦ₘ n3) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) **
       regOwn .x19 ** regOwn .x20 **
       (oB ↦ₘ (0 : Word)) **
       ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
       ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hentry
    -- the find-last loop with the untouched station state in its frame slot
    have hloop := bansf_findLastLoop1_spec aB newSp acctBytes cOff
      (fOff + fSpanN)
      (((newSp + 48) ↦ₘ n3) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) **
       (oB ↦ₘ (0 : Word)) **
       ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
       ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) ** F)
      (by pcf; exact hF) hsalign (by omega) hover hvalid (by omega)
      (fOff + fSpanN - cOff)
    have hloopSw := cpsBranchWithin_swap hloop
    have hloopW := cpsBranchWithin_weaken
      (Q_t' := balStationRej aB newSp oB aLen acctBytes F)
      (fun _ x => x)
      (fun h hq => by
        unfold flRej at hq
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
      (fun _ x => x) hloopSw
    -- the loop-exit continuation at B + 264
    have hc264 := bansf_balStationCont264_spec aB newSp oB aLen fOff fSpanN
      n3 b acctBytes F hF hsalign hoalign hslack hover hvalid hovout hovalid
      hbq (fun hcon => hce (hceq.trans hcon)) (hceq ▸ hcle) hfE
    have himp : ∀ h, ((flExit aB newSp acctBytes cOff (fOff + fSpanN)
        (((newSp + 48) ↦ₘ n3) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) **
         (oB ↦ₘ (0 : Word)) **
         ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
         ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) ** F)) h) →
        (∃ n l : Word,
          (((((.x2 : Reg) ↦ᵣ newSp) **
             ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
             ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
             ((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l) **
             ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
             ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
             ((.x0 : Reg) ↦ᵣ (0 : Word)) **
             ((newSp + 48) ↦ₘ n3) **
             ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
             ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
             ((.x18 : Reg) ↦ᵣ oB) **
             (oB ↦ₘ (0 : Word)) **
             ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
             ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
             bytesRegion aB acctBytes ** F **
             regOwn .x10 ** regOwn .x11) **
            regOwn .x7 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
            regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
           ⌜LastItemAt acctBytes aB (aB + BitVec.ofNat 64 (fOff + fSpanN))
             (fOff + listHeaderSize b) n l⌝) h) := by
      intro h hp
      unfold flExit at hp
      obtain ⟨n, l, hp2⟩ := hp
      obtain ⟨hat, hlastc⟩ := (sepConj_pure_right h).1 hp2
      have hR2 : ((((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l) **
           ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((newSp + 48) ↦ₘ n3) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) **
           (oB ↦ₘ (0 : Word)) **
           ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
           ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
           bytesRegion aB acctBytes ** F **
           regOwn .x10 ** regOwn .x11) **
          regOwn .x7 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x1) h := by
        xperm_hyp hat
      exact ⟨n, l, (sepConj_pure_right h).2 ⟨hR2, hceq ▸ hlastc⟩⟩
    have hc264' := cpsBranchWithin_weaken himp (fun _ x => x) (fun _ x => x) hc264
    have hchain := cpsBranchWithin_chain_snd hloopW hc264'
    -- flInv entry from the spilled state
    have hentryImp : ∀ h, (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN)))) **
       (((.x12 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
        ((newSp + 48) ↦ₘ n3) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x19 ** regOwn .x20 **
        (oB ↦ₘ (0 : Word)) **
        ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
        ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
        bytesRegion aB acctBytes ** F)) h) →
        flInv aB newSp acctBytes cOff (fOff + fSpanN)
          (((newSp + 48) ↦ₘ n3) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) **
           (oB ↦ₘ (0 : Word)) **
           ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
           ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) ** F)
          (fOff + fSpanN - cOff) h := by
      intro h hp
      unfold flInv
      have hp19 : (regOwn .x19 **
          (regOwn .x20 **
           ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
           ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((.x12 : Reg) ↦ᵣ (0 : Word)) **
           ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
           ((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((newSp + 48) ↦ₘ n3) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) **
           (oB ↦ₘ (0 : Word)) **
           ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
           ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
           bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hp
      obtain ⟨v19, hp19'⟩ := sepConj_choose_regOwn hp19
      have hp20 : (regOwn .x20 **
          (((.x19 : Reg) ↦ᵣ v19) **
           ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
           ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((.x12 : Reg) ↦ᵣ (0 : Word)) **
           ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
           ((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((newSp + 48) ↦ₘ n3) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) **
           (oB ↦ₘ (0 : Word)) **
           ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
           ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
           bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hp19'
      obtain ⟨v20, hp20'⟩ := sepConj_choose_regOwn hp20
      have hpC : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 200 + 4))) **
         (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((newSp + 48) ↦ₘ n3) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
          ((.x18 : Reg) ↦ᵣ oB) **
          (oB ↦ₘ (0 : Word)) **
          ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
          ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
          bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hp20'
      have hpC2 := sepConj_mono
        (sepConj_mono (regIs_implies_regOwn .x10)
          (sepConj_mono (regIs_implies_regOwn .x11)
            (sepConj_mono (regIs_implies_regOwn .x12) (regIs_implies_regOwn .x1))))
        (fun _ x => x) h hpC
      refine ⟨cOff, v19, v20,
        (sepConj_pure_right h).2 ⟨?_, rfl, Nat.le_refl _, hcle, Or.inl rfl⟩⟩
      xperm_hyp hpC2
    have hchainP := cpsBranchWithin_weaken hentryImp
      (fun _ x => x) (fun _ x => x) hchain
    have hfull1 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) hfallF hentryF
    have hfull := cpsTripleWithin_seq_branch_same_cr hfull1 hchainP
    exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ x => x) (fun _ x => x)
      (cpsBranchWithin_mono_nSteps (by omega) hfull)

#print axioms bansf_balStationCont208_spec

/-- **The balance station** (`B + 184 → B + 736 | B + 352`): from the SEG-B
    item-3 state (the balance-field item's walk result in `a0`/`a2`), capture
    the field span, init the field window, find the last tuple, parse its
    value, and materialise `has_balance`/`post_balance` in the out block —
    per EIP-7928 last-tuple-wins (`balStationPost`).  The field-window
    side conditions and the 9-byte walker slack are discharged from the
    account-region bounds via `rlpItemDecode_spanStart` on `hdec3`. -/
theorem bansf_balStation_spec (aB newSp oB : Word) (aLen off3 : Nat)
    (n3 l3 v19 v20 : Word)
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
    (hoff3 : off3 ≤ aLen)
    (hdec3 : rlpItemDecode acctBytes off3 (aB + BitVec.ofNat 64 off3)
      (aB + BitVec.ofNat 64 aLen) n3 l3) :
    cpsBranchWithin (98 * (aLen + 1) + 700) (B + 184) bansfCR
      ((((.x10 : Reg) ↦ᵣ n3) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ l3) **
        ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((newSp + 48) ↦ₘ n3) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) **
        (oB ↦ₘ (0 : Word)) **
        ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
        ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** F) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1)
      (B + 736) (balStationRej aB newSp oB aLen acctBytes F)
      (B + 352) (balStationPost aB newSp oB aLen ((n3 - l3 - aB).toNat)
        l3.toNat n3 acctBytes F) := by
  refine cpsBranchWithin_of_forall_regIs_to_regOwn8
    (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
  obtain ⟨hrepS, hsple, hspb⟩ := rlpItemDecode_spanStart hdec3 hoff3 (by omega)
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
  -- slots 46–49: capture the field span, set up the walk_init arguments
  have hsc := bansf_spanCapture46_spec n3 l3 v19 v20
  rw [hrepS] at hsc
  have hscL := liftCode (cr' := bansfCR) hsc
    (fun a i h => CodeReq.union_mono_left a i h)
  have hscF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
     memOwn (newSp + 64) ** memOwn (newSp + 72) **
     ((newSp + 48) ↦ₘ n3) **
     ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
     ((.x18 : Reg) ↦ᵣ oB) **
     (oB ↦ₘ (0 : Word)) **
     ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
     ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hscL
  -- slot 50–51: the balance-field walk_init dispatch
  have hfi := bansf_fieldInit50_spec aB aLen ((n3 - l3 - aB).toNat) l3 acctBytes
    v5 v6 v7 l3 v28 v29 v30 v31 vRa F hF hsalign hslack hover hvalid hspb
  have hfiF := cpsBranchWithin_frameR
    (((.x19 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n3 - l3 - aB).toNat))) **
     ((.x20 : Reg) ↦ᵣ l3) **
     ((.x2 : Reg) ↦ᵣ newSp) **
     memOwn (newSp + 64) ** memOwn (newSp + 72) **
     ((newSp + 48) ↦ₘ n3) **
     ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
     ((.x18 : Reg) ↦ᵣ oB) **
     (oB ↦ₘ (0 : Word)) **
     ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
     ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))
    (by pcf) hfi
  have hfiW := cpsBranchWithin_weaken
    (Q_t' := balStationRej aB newSp oB aLen acctBytes F)
    (fun _ x => x)
    (fun h hq => by
      unfold fieldRej at hq
      unfold balStationRej
      have hq2 : (((((newSp + 48) ↦ₘ n3) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          (oB ↦ₘ (0 : Word))) **
         ((((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
           ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word))) **
          ((((.x19 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n3 - l3 - aB).toNat))) **
            ((.x20 : Reg) ↦ᵣ l3)) **
           (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
            memOwn (newSp + 64) ** memOwn (newSp + 72) **
            ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
            ((.x18 : Reg) ↦ᵣ oB) **
            regOwn .x11 ** regOwn .x12 **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
            bytesRegion aB acctBytes ** F))))) h := by
        xperm_hyp hq
      have hq3 := sepConj_mono
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))
        (sepConj_mono hmemU
          (sepConj_mono
            (sepConj_mono (regIs_implies_regOwn .x19) (regIs_implies_regOwn .x20))
            (fun _ x => x))) h hq2
      xperm_hyp hq3)
    (fun _ x => x) hfiF
  -- the station continuation at B + 208
  have hc208 := bansf_balStationCont208_spec aB newSp oB aLen
    ((n3 - l3 - aB).toNat) l3.toNat n3 acctBytes F hF hsalign hoalign hslack
    hover hvalid hovout hovalid (by omega)
  have himp : ∀ h, ((fieldInitPost aB ((n3 - l3 - aB).toNat) l3.toNat acctBytes
      (B + 200 + 4) F **
      (((.x19 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n3 - l3 - aB).toNat))) **
       ((.x20 : Reg) ↦ᵣ l3) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 64) ** memOwn (newSp + 72) **
       ((newSp + 48) ↦ₘ n3) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) **
       (oB ↦ₘ (0 : Word)) **
       ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
       ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))) h) →
      (∃ cOff : Nat,
        ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n3 - l3 - aB).toNat + l3.toNat))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
          bytesRegion aB acctBytes ** F) **
         ⌜FieldInitOk acctBytes ((n3 - l3 - aB).toNat) l3.toNat cOff⌝) h) := by
    intro h hp
    unfold fieldInitPost at hp
    obtain ⟨g1, g2, gd, gu, hVin, hfr⟩ := hp
    obtain ⟨cOff, hVin2⟩ := hVin
    obtain ⟨hat, hokc⟩ := (sepConj_pure_right g1).1 hVin2
    have hR := (⟨g1, g2, gd, gu, hat, hfr⟩ :
      (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n3 - l3 - aB).toNat + l3.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
        bytesRegion aB acctBytes ** F) **
       (((.x19 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n3 - l3 - aB).toNat))) **
        ((.x20 : Reg) ↦ᵣ l3) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((newSp + 48) ↦ₘ n3) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) **
        (oB ↦ₘ (0 : Word)) **
        ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
        ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)))) h))
    have hconv := sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn .x19)
        (sepConj_mono (regIs_implies_regOwn .x20) (fun _ x => x))) h hR
    have hR2 : (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n3 - l3 - aB).toNat + l3.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 200 + 4)) **
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
        bytesRegion aB acctBytes ** F) h := by
      xperm_hyp hconv
    exact ⟨cOff, (sepConj_pure_right h).2 ⟨hR2, hokc⟩⟩
  have hc208' := cpsBranchWithin_weaken himp (fun _ x => x) (fun _ x => x) hc208
  have hchain := cpsBranchWithin_chain_snd hfiW hc208'
  have hfull := cpsTripleWithin_seq_branch_same_cr hscF
    (cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ x => x) (fun _ x => x) hchain)
  exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ x => x) (fun _ x => x)
    (cpsBranchWithin_mono_nSteps (by omega) hfull)

#print axioms bansf_balStation_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
