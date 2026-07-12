/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainE2

  Balance-station top-level theorem (bead evm-asm-4ch8f.43.5, slice 4g).
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainE

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

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
