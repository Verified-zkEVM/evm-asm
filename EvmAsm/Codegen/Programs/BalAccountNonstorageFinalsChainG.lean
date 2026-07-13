/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainG

  Nonce-station tuple composition (evm-asm-4ch8f.43.5).
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainE
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainF
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsLoop2

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

@[irreducible]
def nonceCont496Pre (aB newSp oB n4 : Word) (aLen tEnd off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  fun h => ∃ next len : Word,
    (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ next) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
       ((newSp + 48) ↦ₘ n4) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion aB acctBytes ** G ** F) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
     ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
       (aB + BitVec.ofNat 64 tEnd) next len⌝) h

/-- Folded adapter from the nonce index-item success post to `Cont496`. -/
theorem nonceTupleOk_to_cont496Pre (aB newSp oB n4 : Word)
    (aLen tEnd off : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (tupleOk aB newSp tEnd off acctBytes F **
        (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)) h →
      nonceCont496Pre aB newSp oB n4 aLen tEnd off acctBytes G F h := by
  intro h hp
  unfold tupleOk at hp
  obtain ⟨g1, g2, gd, gu, hVal, hfr⟩ := hp
  obtain ⟨next, len, hVal2⟩ := hVal
  obtain ⟨hregs, hdec⟩ := (sepConj_pure_right g1).1 hVal2
  have hR := (⟨g1, g2, gd, gu, hregs, hfr⟩ :
    (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ next) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)) h))
  delta nonceCont496Pre
  refine ⟨next, len, (sepConj_pure_right h).2 ⟨?_, hdec⟩⟩
  let L : Assertion :=
    (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ next) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)))
  let R : Assertion :=
    (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ next) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
      ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
      ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion aB acctBytes ** G ** F) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
     regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1
  have hL : L h := by dsimp only [L]; exact hR
  have heq : L = R := by dsimp only [L, R]; xperm
  change R h
  exact (congrFun heq h).mp hL

#print axioms nonceTupleOk_to_cont496Pre

/-- Continuation at `B + 476`: decode the nonce tuple's index item, then run
    the value/capture continuation. -/
theorem bansf_nonceStationCont476_spec (aB newSp oB : Word)
    (aLen tEnd offI fOff fSpanN : Nat) (n4 : Word)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffleI : offI ≤ tEnd)
    (hFF3 : ∀ iNext iLen vNext vLen : Word,
      rlpItemDecode acctBytes offI (aB + BitVec.ofNat 64 offI)
        (aB + BitVec.ofNat 64 tEnd) iNext iLen →
      rlpItemDecode acctBytes ((iNext - aB).toNat) iNext
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsBranchWithin (7 * acctBytes.length + 203) (B + 476) bansfCR
      ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 offI)) **
         ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 tEnd)) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 offI)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
         ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
         ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion aB acctBytes ** G ** F) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1)
      (B + 736) (nonceStationRej aB newSp oB aLen acctBytes G F)
      (B + 540)
        (nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F) := by
  refine cpsBranchWithin_of_forall_regIs_to_regOwn8
    (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
  have hti := bansf_nonceTupleItem0_spec aB newSp tEnd offI acctBytes
    v5 v6 v7 (aB + BitVec.ofNat 64 offI) (aB + BitVec.ofNat 64 tEnd) 0
    v28 v29 v30 v31 vRa F hF hsalign (by omega) hover hvalid hoffleI
  let H : Assertion :=
    G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20
  have hHF : H.pcFree := by dsimp only [H]; pcf; exact hG; pcf
  have htiF := cpsBranchWithin_frameR H hHF hti
  have hc496 := bansf_nonceStationCont496_spec aB newSp oB aLen tEnd offI
    fOff fSpanN n4 acctBytes G F hG hF hsalign hslack hover hvalid htEnd
    hoffleI hFF3
  have hc496F := cpsBranchWithin_weaken
    (P' := nonceCont496Pre aB newSp oB n4 aLen tEnd offI acctBytes G F)
    (fun _ hp => by delta nonceCont496Pre at hp; exact hp)
    (fun _ hq => hq) (fun _ hq => hq) hc496
  have hc496' := cpsBranchWithin_weaken
    (nonceTupleOk_to_cont496Pre aB newSp oB n4 aLen tEnd offI acctBytes G F)
    (fun _ hq => hq) (fun _ hq => hq) hc496F
  have htiW := cpsBranchWithin_weaken
    (Q_t' := nonceStationRej aB newSp oB aLen acctBytes G F)
    (fun _ hp => hp)
    (fun h hq => nonceTupleReject_to_stationRej
      aB newSp oB n4 aLen acctBytes G F h (by dsimp only [H] at hq; exact hq))
    (fun _ hq => hq) htiF
  have hchain := cpsBranchWithin_chain_snd htiW hc496'
  exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_mono_nSteps (by omega) hchain)

#print axioms bansf_nonceStationCont476_spec

/-- Continuation at `B + 468`: spill the tuple cursor/end, then decode its
    index and value and capture the nonce. -/
theorem bansf_nonceStationCont468_spec (aB newSp oB : Word)
    (aLen tEnd offI fOff fSpanN : Nat) (n4 : Word)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffleI : offI ≤ tEnd)
    (hFF3 : ∀ iNext iLen vNext vLen : Word,
      rlpItemDecode acctBytes offI (aB + BitVec.ofNat 64 offI)
        (aB + BitVec.ofNat 64 tEnd) iNext iLen →
      rlpItemDecode acctBytes ((iNext - aB).toNat) iNext
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsBranchWithin (7 * acctBytes.length + 205) (B + 468) bansfCR
      ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 offI)) **
         ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 tEnd)) **
         ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) **
         memOwn (newSp + 72)) **
        (((.x12 : Reg) ↦ᵣ (0 : Word)) **
         ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
         ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
         regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
         bytesRegion aB acctBytes ** G ** F))
      (B + 736) (nonceStationRej aB newSp oB aLen acctBytes G F)
      (B + 540)
        (nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F) := by
  have hsp := bansf_nonceTupleSpill117_spec newSp
    (aB + BitVec.ofNat 64 offI) (aB + BitVec.ofNat 64 tEnd)
  let H : Assertion :=
    ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
    ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
    bytesRegion aB acctBytes ** G ** F
  have hH : H.pcFree := by dsimp only [H]; pcf; exact hG; exact hF
  have hspF := cpsTripleWithin_frameR H hH hsp
  have hc := bansf_nonceStationCont476_spec aB newSp oB aLen tEnd offI
    fOff fSpanN n4 acctBytes G F hG hF hsalign hslack hover hvalid htEnd
    hoffleI hFF3
  have hfull := cpsTripleWithin_seq_branch_same_cr hspF
    (cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hc)
  exact cpsBranchWithin_mono_nSteps (by omega) hfull

#print axioms bansf_nonceStationCont468_spec

/-- A rejected tuple `walk_init` carries enough untouched frame to establish
    the shared nonce-station rejection assertion. -/
theorem nonceTupleInitReject_to_stationRej (aB newSp oB n4 v19 v20 s64 s72 : Word)
    (aLen : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (fieldRej aB acctBytes F **
        (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((newSp + 64) ↦ₘ s64) ** ((newSp + 72) ↦ₘ s72) **
         ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
         ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
         ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20))) h →
      nonceStationRej aB newSp oB aLen acctBytes G F h := by
  intro h hq
  unfold fieldRej at hq
  have hq2 :
      ((((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
        ((newSp + 48) ↦ₘ n4) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((newSp + 64) ↦ₘ s64) ** ((newSp + 72) ↦ₘ s72) **
        ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x20 : Reg) ↦ᵣ v20)) **
       (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x11 ** regOwn .x12 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F)) h := by
    xperm_hyp hq
  have hq3 := sepConj_mono
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn
                (sepConj_mono (fun _ hx => hx)
                  (sepConj_mono (regIs_implies_regOwn .x19)
                    (regIs_implies_regOwn .x20)))))))))
    (fun _ x => x) h hq2
  unfold nonceStationRej
  xperm_hyp hq3

#print axioms nonceTupleInitReject_to_stationRej

/-- Reframe a successful tuple `walk_init` as the existential precondition
    consumed by the continuation at `B + 468`. -/
theorem nonceTupleInitOk_to_cont468Pre (aB newSp oB n4 v19 v20 s64 s72 : Word)
    (aLen tOff tSpanN : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      ((fieldInitPost aB tOff tSpanN acctBytes (B + 460 + 4) F **
        (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
         ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ s64) **
         ((newSp + 72) ↦ₘ s72) **
         G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB))) h →
      (∃ cOff : Nat,
        (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
            ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
            ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) **
            memOwn (newSp + 72)) **
           (((.x12 : Reg) ↦ᵣ (0 : Word)) **
            ((newSp + 48) ↦ₘ n4) **
            ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
            ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
            ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
            ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
            ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
            ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
            bytesRegion aB acctBytes ** G ** F)) **
          ⌜FieldInitOk acctBytes tOff tSpanN cOff⌝) h)) := by
  intro h hp
  unfold fieldInitPost at hp
  obtain ⟨g1, g2, gd, gu, hInit, hfr⟩ := hp
  obtain ⟨cOff, hInit2⟩ := hInit
  obtain ⟨hregs, hok⟩ := (sepConj_pure_right g1).1 hInit2
  have hR := (⟨g1, g2, gd, gu, hregs, hfr⟩ :
    (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
      ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
      ((.x12 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 460 + 4)) **
      bytesRegion aB acctBytes ** F) **
     (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ s64) **
      ((newSp + 72) ↦ₘ s72) **
      G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB))) h))
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
  refine ⟨cOff, (sepConj_pure_right h).2 ⟨?_, hok⟩⟩
  xperm_hyp hconv2

#print axioms nonceTupleInitOk_to_cont468Pre

/-- Ownership-facing wrapper for the nonce loop-exit moves. -/
theorem bansf_nonceLoopExitMove113_own_spec (v19 v20 : Word) :
    cpsTripleWithin 2 (B + 452) (B + 460) bansfCR
      (((((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20)) **
        regOwn .x10 ** regOwn .x11))
      ((((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20)) **
       ((.x10 : Reg) ↦ᵣ v19) ** ((.x11 : Reg) ↦ᵣ v20)) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v10 v11 => ?_)
  have hm := bansf_nonceLoopExitMove113_spec v19 v20 v10 v11
  have hmL := liftCode (cr' := bansfCR) hm
    (fun a i h => CodeReq.union_mono_left a i h)
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hmL

#print axioms bansf_nonceLoopExitMove113_own_spec

/-- Continuation at `B + 452`: initialize the last nonce tuple and run its
    index/value/capture chain. -/
theorem bansf_nonceStationCont452_spec (aB newSp oB : Word)
    (aLen fOff fSpanN : Nat) (n4 : Word) (b : BitVec 8)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hb : acctBytes[fOff]? = some b)
    (hne : fOff + listHeaderSize b ≠ fOff + fSpanN)
    (hoff0le : fOff + listHeaderSize b ≤ fOff + fSpanN)
    (hfE : fOff + fSpanN ≤ aLen) :
    cpsBranchWithin (7 * acctBytes.length + 291) (B + 452) bansfCR
      (fun h => ∃ n l : Word,
        (((((((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l)) **
            regOwn .x10 ** regOwn .x11) **
           (((.x2 : Reg) ↦ᵣ newSp) **
            ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
            ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
            ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
            ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
            ((newSp + 48) ↦ₘ n4) **
            ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
            ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
            ((.x18 : Reg) ↦ᵣ oB) **
            ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
            ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
            ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion aB acctBytes ** G ** F)) **
          regOwn .x7 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
          ⌜LastItemAt acctBytes aB (aB + BitVec.ofNat 64 (fOff + fSpanN))
            (fOff + listHeaderSize b) n l⌝) h)
      (B + 736) (nonceStationRej aB newSp oB aLen acctBytes G F)
      (B + 540)
        (nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F) := by
  refine cpsBranchWithin_exists_pre (fun n => ?_)
  refine cpsBranchWithin_exists_pre (fun l => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hlast => ?_)
  refine cpsBranchWithin_of_forall_regIs_to_regOwn7
    (fun v7 v12 v28 v29 v30 v31 vRa => ?_)
  obtain ⟨offT, hoffTle, hdecT⟩ := LastItemAt_decode hlast hoff0le (by omega)
  obtain ⟨hrepT, _, _⟩ := rlpItemDecode_spanStart hdecT hoffTle (by omega)
  rw [hrepT]
  have hmv := bansf_nonceLoopExitMove113_own_spec (n - l) l
  let HM : Assertion :=
    ((.x2 : Reg) ↦ᵣ newSp) **
    ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    ((newSp + 48) ↦ₘ n4) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB) **
    ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x7 : Reg) ↦ᵣ v7) ** ((.x12 : Reg) ↦ᵣ v12) **
    ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
    ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
    ((.x1 : Reg) ↦ᵣ vRa) ** bytesRegion aB acctBytes ** G ** F
  have hHM : HM.pcFree := by dsimp only [HM]; pcf; exact hG; exact hF
  have hmvF := cpsTripleWithin_frameR HM hHM hmv
  rw [hrepT] at hmvF
  have hfi := bansf_nonceTupleInit115_spec aB aLen ((n - l - aB).toNat) l
    acctBytes (aB + BitVec.ofNat 64 (fOff + fSpanN))
    (aB + BitVec.ofNat 64 (fOff + fSpanN)) v7 v12 v28 v29 v30 v31 vRa
    F hF hsalign hslack hover hvalid (by omega)
  let HI : Assertion :=
    ((.x19 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 ((n - l - aB).toNat))) **
    ((.x20 : Reg) ↦ᵣ l) ** ((.x2 : Reg) ↦ᵣ newSp) **
    ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
    G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB)
  have hHI : HI.pcFree := by dsimp only [HI]; pcf; exact hG; pcf
  have hfiF := cpsBranchWithin_frameR HI hHI hfi
  have hfiW := cpsBranchWithin_weaken
    (Q_t' := nonceStationRej aB newSp oB aLen acctBytes G F)
    (fun _ hp => hp)
    (fun h hq => nonceTupleInitReject_to_stationRej aB newSp oB n4
      (aB + BitVec.ofNat 64 ((n - l - aB).toNat)) l
      (aB + BitVec.ofNat 64 (fOff + fSpanN))
      (aB + BitVec.ofNat 64 (fOff + fSpanN)) aLen acctBytes G F h
      (by dsimp only [HI] at hq; xperm_hyp hq))
    (fun _ hq => hq) hfiF
  have hcAll : cpsBranchWithin (7 * acctBytes.length + 205) (B + 468) bansfCR
      (fun h => ∃ cOff : Nat,
        (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
            ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64
              ((n - l - aB).toNat + l.toNat))) **
            ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) **
            memOwn (newSp + 72)) **
           (((.x12 : Reg) ↦ᵣ (0 : Word)) **
            ((newSp + 48) ↦ₘ n4) **
            ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
            ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
            ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
            ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
            ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
            ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
            bytesRegion aB acctBytes ** G ** F)) **
          ⌜FieldInitOk acctBytes ((n - l - aB).toNat) l.toNat cOff⌝) h)
      (B + 736) (nonceStationRej aB newSp oB aLen acctBytes G F)
      (B + 540)
        (nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F) := by
    refine cpsBranchWithin_exists_pre (fun cOff => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
    obtain ⟨b2, hb2, hceq2, _, hcle2⟩ := hok
    exact bansf_nonceStationCont468_spec aB newSp oB aLen
      ((n - l - aB).toNat + l.toNat) cOff fOff fSpanN n4 acctBytes G F
      hG hF hsalign hslack hover hvalid (by omega) hcle2
      (fun iNext iLen vNext vLen hdecI hdecV =>
        FieldFinal.last b n l vNext vLen hb hne hlast
          ⟨b2, hb2, iNext, iLen, hceq2 ▸ hdecI, hdecV⟩)
  have hcFromInit := cpsBranchWithin_weaken
    (nonceTupleInitOk_to_cont468Pre aB newSp oB n4
      (aB + BitVec.ofNat 64 ((n - l - aB).toNat)) l
      (aB + BitVec.ofNat 64 (fOff + fSpanN))
      (aB + BitVec.ofNat 64 (fOff + fSpanN)) aLen
      ((n - l - aB).toNat) l.toNat acctBytes G F)
    (fun _ hq => hq) (fun _ hq => hq) hcAll
  have hchain := cpsBranchWithin_chain_snd hfiW hcFromInit
  have hfull := cpsTripleWithin_seq_branch_same_cr hmvF
    (cpsBranchWithin_weaken (fun h hp => by dsimp only [HM, HI]; xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hchain)
  exact cpsBranchWithin_weaken (fun h hp => by dsimp only [HM]; xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_mono_nSteps (by omega) hfull)

#print axioms bansf_nonceStationCont452_spec

/-- Reframe the nonce find-last loop's reject exit as the shared station
    rejection assertion. -/
theorem nonceLoopReject_to_stationRej (aB newSp oB n4 : Word)
    (aLen : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      ((flRej aB newSp acctBytes F **
        (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB)))) h →
      nonceStationRej aB newSp oB aLen acctBytes G F h := by
  intro h hq
  unfold flRej at hq
  have hq2 :
      ((((.x10 : Reg) ↦ᵣ (1 : Word)) **
        ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
        ((newSp + 48) ↦ₘ n4) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen))) **
       (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
        regOwn .x12 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** F)) h := by
    xperm_hyp hq
  have hq3 := sepConj_mono
    (sepConj_mono (fun _ hx => hx)
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))))
    (fun _ x => x) h hq2
  unfold nonceStationRej
  xperm_hyp hq3

#print axioms nonceLoopReject_to_stationRej

/-- Reframe the clean find-last loop exit as the existential precondition of
    the continuation at `B + 452`. -/
theorem nonceLoopExit_to_cont452Pre (aB newSp oB n4 : Word)
    (aLen off0 endOff : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      ((flExit aB newSp acctBytes off0 endOff F **
        (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB))) h →
      (∃ n l : Word,
        (((((((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l)) **
            regOwn .x10 ** regOwn .x11) **
           (((.x2 : Reg) ↦ᵣ newSp) **
            ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
            ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
            ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
            ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
            ((newSp + 48) ↦ₘ n4) **
            ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
            ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
            ((.x18 : Reg) ↦ᵣ oB) **
            ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
            ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
            ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion aB acctBytes ** G ** F)) **
          regOwn .x7 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
         ⌜LastItemAt acctBytes aB (aB + BitVec.ofNat 64 endOff) off0 n l⌝) h)) := by
  intro h hp
  unfold flExit at hp
  obtain ⟨g1, g2, gd, gu, hExit, hfr⟩ := hp
  obtain ⟨n, l, hExit2⟩ := hExit
  obtain ⟨hregs, hlast⟩ := (sepConj_pure_right g1).1 hExit2
  refine ⟨n, l, (sepConj_pure_right h).2 ⟨?_, hlast⟩⟩
  have hR := (⟨g1, g2, gd, gu, hregs, hfr⟩ :
    (((((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
      ((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l) **
      ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
      ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) ** regOwn .x7 **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F) **
     (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB))) h))
  let L : Assertion :=
    (((((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
      ((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l) **
      ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
      ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) ** regOwn .x7 **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F) **
     (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB))))
  let R : Assertion :=
    (((((.x19 : Reg) ↦ᵣ (n - l)) ** ((.x20 : Reg) ↦ᵣ l)) **
       regOwn .x10 ** regOwn .x11) **
      (((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
       ((.x5 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
       ((.x6 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
       ((newSp + 48) ↦ₘ n4) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) **
       ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion aB acctBytes ** G ** F)) **
     regOwn .x7 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** regOwn .x1
  have hL : L h := by dsimp only [L]; exact hR
  have heq : L = R := by dsimp only [L, R]; xperm
  change R h
  exact (congrFun heq h).mp hL

#print axioms nonceLoopExit_to_cont452Pre

/-- Continuation at the nonce find-last loop header `B + 408`. -/
theorem bansf_nonceStationCont408_spec (aB newSp oB : Word)
    (aLen fOff fSpanN j : Nat) (n4 : Word) (b : BitVec 8)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hb : acctBytes[fOff]? = some b)
    (hne : fOff + listHeaderSize b ≠ fOff + fSpanN)
    (hoff0le : fOff + listHeaderSize b ≤ fOff + fSpanN)
    (hfE : fOff + fSpanN ≤ aLen) :
    cpsBranchWithin (98 * (j + 1) + (7 * acctBytes.length + 291))
      (B + 408) bansfCR
      (flInv aB newSp acctBytes (fOff + listHeaderSize b)
        (fOff + fSpanN) F j **
       (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
        ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB)))
      (B + 736) (nonceStationRej aB newSp oB aLen acctBytes G F)
      (B + 540)
        (nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F) := by
  have hloop := bansf_findLastLoop2_spec aB newSp acctBytes
    (fOff + listHeaderSize b) (fOff + fSpanN) F hF hsalign
    (by omega) hover hvalid (by omega) j
  let H : Assertion :=
    G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB)
  have hH : H.pcFree := by dsimp only [H]; pcf; exact hG; pcf
  have hloopF := cpsBranchWithin_frameR H hH hloop
  have hloopSw := cpsBranchWithin_swap hloopF
  have hloopW := cpsBranchWithin_weaken
    (Q_t' := nonceStationRej aB newSp oB aLen acctBytes G F)
    (fun _ hp => hp)
    (fun h hq => nonceLoopReject_to_stationRej aB newSp oB n4 aLen
      acctBytes G F h (by dsimp only [H] at hq; exact hq))
    (fun _ hq => hq) hloopSw
  have hc452 := bansf_nonceStationCont452_spec aB newSp oB aLen fOff fSpanN
    n4 b acctBytes G F hG hF hsalign hslack hover hvalid hb hne hoff0le hfE
  have hc452' := cpsBranchWithin_weaken
    (nonceLoopExit_to_cont452Pre aB newSp oB n4 aLen
      (fOff + listHeaderSize b) (fOff + fSpanN) acctBytes G F)
    (fun _ hq => hq) (fun _ hq => hq) hc452
  exact cpsBranchWithin_chain_snd hloopW hc452'

#print axioms bansf_nonceStationCont408_spec

/-- Reframe the taken empty-list arm at `B + 540` as the genuine empty
    disjunct of the nonce station postcondition. -/
theorem nonceEmpty_to_stationPost (aB newSp oB : Word)
    (aLen fOff fSpanN cOff : Nat) (n4 : Word) (b : BitVec 8)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hb : acctBytes[fOff]? = some b)
    (hcontent : fOff + listHeaderSize b = cOff)
    (hempty : cOff = fOff + fSpanN) :
    ∀ h,
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 64) ** memOwn (newSp + 72) **
       ((newSp + 48) ↦ₘ n4) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
       (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
        ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F)) h →
      nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F h := by
  intro h hq
  unfold nonceStationPost
  refine Or.inl ((sepConj_pure_right h).2 ⟨?_, ?_⟩)
  · have hq2 :
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
         ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) **
         ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) **
         (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
          ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
          ((oB + 72) ↦ₘ (0 : Word)) **
          ((newSp + 48) ↦ₘ n4) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          memOwn (newSp + 64) ** memOwn (newSp + 72) **
          ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
          regOwn .x19 ** regOwn .x20 ** regOwn .x5 ** regOwn .x6 **
          regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
          regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hq
    have hq3 := sepConj_mono (regIs_implies_regOwn .x10)
      (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x)))) h hq2
    xperm_hyp hq3
  · exact FieldFinal.empty b hb (hcontent.trans hempty)

#print axioms nonceEmpty_to_stationPost

/-- Turn the two slot-100/101 spills into the station-2 find-last invariant. -/
theorem nonceLoopEntry_to_flInv (aB newSp : Word) (acctBytes : List (BitVec 8))
    (cOff endOff : Nat) (H : Assertion) (hcle : cOff ≤ endOff) :
    ∀ h,
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
       regOwn .x19 ** regOwn .x20 **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion aB acctBytes ** H) h →
      flInv aB newSp acctBytes cOff endOff H (endOff - cOff) h := by
  intro h hp
  unfold flInv
  have hp19 :
      (regOwn .x19 **
       (regOwn .x20 **
        ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** H)) h := by
    xperm_hyp hp
  obtain ⟨v19, hp19'⟩ := sepConj_choose_regOwn hp19
  have hp20 :
      (regOwn .x20 **
       (((.x19 : Reg) ↦ᵣ v19) **
        ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** H)) h := by
    xperm_hyp hp19'
  obtain ⟨v20, hp20'⟩ := sepConj_choose_regOwn hp20
  have hpC :
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 endOff)) **
       (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 endOff)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x12 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x1 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion aB acctBytes ** H)) h := by
    xperm_hyp hp20'
  have hpOwn := sepConj_mono (regIs_implies_regOwn .x10)
    (sepConj_mono (regIs_implies_regOwn .x11) (fun _ x => x)) h hpC
  refine ⟨cOff, v19, v20,
    (sepConj_pure_right h).2 ⟨?_, rfl, Nat.le_refl _, hcle, Or.inl rfl⟩⟩
  xperm_hyp hpOwn

#print axioms nonceLoopEntry_to_flInv

/-- Continuation at `B + 396`: split an initialized nonce field into the empty
    result or the station-2 find-last loop. -/
theorem bansf_nonceStationCont396_spec (aB newSp oB : Word)
    (aLen fOff fSpanN : Nat) (n4 : Word)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hfE : fOff + fSpanN ≤ aLen) :
    cpsBranchWithin (98 * (aLen + 1) + (7 * acctBytes.length + 600))
      (B + 396) bansfCR
      (fun h => ∃ cOff : Nat,
        ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          memOwn (newSp + 64) ** memOwn (newSp + 72) **
          ((newSp + 48) ↦ₘ n4) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
          ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
          (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
           ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
           ((oB + 72) ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F)) **
         ⌜FieldInitOk acctBytes fOff fSpanN cOff⌝) h)
      (B + 736) (nonceStationRej aB newSp oB aLen acctBytes G F)
      (B + 540) (nonceStationPost aB newSp oB aLen fOff fSpanN n4 acctBytes G F) := by
  refine cpsBranchWithin_exists_pre (fun cOff => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
  obtain ⟨b, hb, hcontent, hclt, hcle⟩ := hok
  by_cases hempty : cOff = fOff + fSpanN
  · have hbeq := bansf_nonceEmptyTaken_spec aB cOff (fOff + fSpanN) hempty
    have hbeqL := liftCode (cr' := bansfCR) hbeq
      (fun a i h => CodeReq.union_mono_left a i h)
    have hbeqF := cpsTripleWithin_frameR
      (((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) **
       ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) ** memOwn (newSp + 72) **
       ((newSp + 48) ↦ₘ n4) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
       (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
        ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F))
      (by pcf; exact hG; pcf; exact hF) hbeqL
    refine cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ x => x) (fun h hq => ?_)
      (cpsBranchWithin_mono_nSteps (by omega)
        (cpsTripleWithin_as_cpsBranchWithin_right (B + 736)
          (nonceStationRej aB newSp oB aLen acctBytes G F) hbeqF))
    exact nonceEmpty_to_stationPost aB newSp oB aLen fOff fSpanN cOff n4 b
      acctBytes G F hb hcontent.symm hempty h (by xperm_hyp hq)
  · have hfall := bansf_nonceEmptyFall_spec aB aLen cOff (fOff + fSpanN)
      hempty (by omega) hfE (by omega)
    have hfallL := liftCode (cr' := bansfCR) hfall
      (fun a i h => CodeReq.union_mono_left a i h)
    let R : Assertion :=
      ((.x12 : Reg) ↦ᵣ (0 : Word)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) **
      ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) ** memOwn (newSp + 72) **
      ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
      (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F)
    have hfallF := cpsTripleWithin_frameR R
      (by dsimp only [R]; pcf; exact hG; pcf; exact hF) hfallL
    have hentry := bansf_nonceLoopEntry100_spec aB newSp cOff (fOff + fSpanN)
    let Rentry : Assertion :=
      ((.x12 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) **
      ((newSp + 48) ↦ₘ n4) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
      (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F)
    have hentryF := cpsTripleWithin_frameR Rentry
      (by dsimp only [Rentry]; pcf; exact hG; pcf; exact hF) hentry
    have hc408 := bansf_nonceStationCont408_spec aB newSp oB aLen fOff fSpanN
      (fOff + fSpanN - cOff) n4 b acctBytes G F hG hF hsalign hslack hover
      hvalid hb (fun h => hempty (hcontent.trans h)) (hcontent ▸ hcle) hfE
    have htoInv : ∀ h,
        (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
           ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
           ((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN)))) **
          Rentry) h) →
        (flInv aB newSp acctBytes (fOff + listHeaderSize b)
          (fOff + fSpanN) F (fOff + fSpanN - cOff) **
         (G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
          ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
          ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
          ((.x18 : Reg) ↦ᵣ oB))) h := by
      intro h hp
      let CoreRest : Assertion :=
        ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 cOff)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
        regOwn .x19 ** regOwn .x20 ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F
      let Core : Assertion := regOwn .x12 ** regOwn .x1 ** CoreRest
      let Station : Assertion :=
        G ** ((oB + 40) ↦ₘ (0 : Word)) ** ((oB + 48) ↦ₘ (0 : Word)) **
        ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n4) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB)
      have hpExact :
          (((.x12 : Reg) ↦ᵣ (0 : Word)) **
           ((.x1 : Reg) ↦ᵣ (B + 388 + 4)) ** (CoreRest ** Station)) h := by
        dsimp only [Rentry] at hp
        dsimp only [CoreRest, Station]
        xperm_hyp hp
      have hpOwned := sepConj_mono (regIs_implies_regOwn .x12)
        (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x)) h hpExact
      have hpCore : (Core ** Station) h := by
        dsimp only [Core]
        xperm_hyp hpOwned
      have hall :
          (flInv aB newSp acctBytes cOff (fOff + fSpanN) F
            (fOff + fSpanN - cOff) ** Station) h := by
        refine sepConj_mono_left
          (nonceLoopEntry_to_flInv aB newSp acctBytes cOff
            (fOff + fSpanN) F hcle) h ?_
        dsimp only [Core, CoreRest, Station] at hpCore ⊢
        xperm_hyp hpCore
      have hinvEq :
          flInv aB newSp acctBytes cOff (fOff + fSpanN) F
              (fOff + fSpanN - cOff) =
            flInv aB newSp acctBytes (fOff + listHeaderSize b)
              (fOff + fSpanN) F (fOff + fSpanN - cOff) := by
        congr 1
      rw [hinvEq] at hall
      dsimp only [Station] at hall
      xperm_hyp hall
    have hc408' := cpsBranchWithin_weaken htoInv (fun _ x => x) (fun _ x => x) hc408
    have hfirst := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by dsimp only [R, Rentry]; xperm_hyp hp) hfallF hentryF
    have hfull := cpsTripleWithin_seq_branch_same_cr hfirst hc408'
    exact cpsBranchWithin_weaken (fun h hp => by dsimp only [R]; xperm_hyp hp)
      (fun _ x => x) (fun _ x => x)
      (cpsBranchWithin_mono_nSteps (by omega) hfull)

#print axioms bansf_nonceStationCont396_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
