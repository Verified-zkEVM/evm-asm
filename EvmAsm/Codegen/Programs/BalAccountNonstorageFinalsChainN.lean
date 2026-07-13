/- Top-level SEG-B and ABI assembly for bal_account_nonstorage_finals. -/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainM

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP
namespace BalAccountNonstorageFinalsSpec

/-- State preserved ambiently while the outer items 0--3 are walked. -/
def valueEntryAmbient (aB newSp oB : Word) (aLen : Nat)
    (F : Assertion) : Assertion :=
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
  ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
  (oB ↦ₘ (0 : Word)) ** ((oB + 8) ↦ₘ (0 : Word)) **
  ((oB + 16) ↦ₘ (0 : Word)) ** ((oB + 24) ↦ₘ (0 : Word)) **
  ((oB + 32) ↦ₘ (0 : Word)) ** ((oB + 40) ↦ₘ (0 : Word)) **
  ((oB + 48) ↦ₘ (0 : Word)) ** ((oB + 56) ↦ₘ (0 : Word)) **
  ((oB + 64) ↦ₘ (0 : Word)) ** ((oB + 72) ↦ₘ (0 : Word)) ** F

/-- The outer-item ambient footprint is PC-free when its caller frame is. -/
theorem valueEntryAmbient_pcFree
    (aB newSp oB : Word) (aLen : Nat) (F : Assertion) (hF : F.pcFree) :
    (valueEntryAmbient aB newSp oB aLen F).pcFree := by
  letI : Assertion.PCFree F := ⟨hF⟩
  unfold valueEntryAmbient
  exact (inferInstance : Assertion.PCFree _).proof

#print axioms valueEntryAmbient_pcFree

/-- Value-station entry with the two callee-saved temporaries existentially
    owned, as exposed by the outer item walk. -/
def valueStationsEntryOwn (aB newSp oB n3 l3 : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  (((((.x10 : Reg) ↦ᵣ n3) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ l3) ** ((.x2 : Reg) ↦ᵣ newSp) **
      memOwn (newSp + 64) ** memOwn (newSp + 72) **
      ((newSp + 48) ↦ₘ n3) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** (oB ↦ₘ (0 : Word)) **
      ((oB + 8) ↦ₘ (0 : Word)) ** ((oB + 16) ↦ₘ (0 : Word)) **
      ((oB + 24) ↦ₘ (0 : Word)) ** ((oB + 32) ↦ₘ (0 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes **
      laterFieldZeros oB F) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
   regOwn .x19 ** regOwn .x20)

/-- The value-station verdict theorem does not need the incoming values of
    `x19` and `x20`; ownership is enough. -/
theorem bansf_valueStationsVerdict_own1920
    (aB newSp oB : Word) (aLen : Nat) (b0 : BitVec 8)
    (n0 l0 n1 l1 n2 l2 n3 l3 : Word)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hoalign : oB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hovout : oB.toNat + 80 ≤ 2 ^ 64)
    (hovalid : ∀ k, k < 80 →
      isValidByteAccess (oB + BitVec.ofNat 64 k) = true)
    (hoff3 : (n2 - aB).toNat ≤ aLen)
    (hPrefix : outerPrefix acctBytes aB aLen b0
      n0 l0 n1 l1 n2 l2 n3 l3) :
    cpsTripleWithin (((98 * (aLen + 1) + 700) +
        2 * (98 * (aLen + 1) + (7 * acctBytes.length + 800))) + 2)
      (B + 184) (B + 736) bansfCR
      (valueStationsEntryOwn aB newSp oB n3 l3 aLen acctBytes F)
      (valueStationsVerdictPost aB newSp oB n3 l3 aLen acctBytes F) := by
  unfold valueStationsEntryOwn
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v19 v20 => ?_)
  have ht := bansf_valueStationsVerdict_spec aB newSp oB aLen b0
    n0 l0 n1 l1 n2 l2 n3 l3 v19 v20 acctBytes F hF hsalign hoalign
    hslack hover hvalid hovout hovalid hoff3 hPrefix
  exact cpsTripleWithin_weaken (by xsimp) (fun _ hp => hp) ht

#print axioms bansf_valueStationsVerdict_own1920

/-- Unified verdict post after entering the value stations from the existential
    item-3 accumulator produced by SEG-B. -/
def valueStationsFromAcc3Post (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion := fun h =>
  ∃ n3 l3, valueStationsVerdictPost aB newSp oB n3 l3 aLen acctBytes F h

/-- Consume the outer item-walk accumulator: recover its semantic prefix and
    the item-3 start bound, then run all three value stations to the verdict. -/
theorem bansf_valueStations_from_acc3
    (aB newSp oB : Word) (aLen off0 : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hoalign : oB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hovout : oB.toNat + 80 ≤ 2 ^ 64)
    (hovalid : ∀ k, k < 80 →
      isValidByteAccess (oB + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (((98 * (aLen + 1) + 700) +
        2 * (98 * (aLen + 1) + (7 * acctBytes.length + 800))) + 2)
      (B + 184) (B + 736) bansfCR
      (acc3 aB newSp aLen off0 acctBytes
        (valueEntryAmbient aB newSp oB aLen F) **
       ⌜OuterInitOk acctBytes aLen off0⌝)
      (valueStationsFromAcc3Post aB newSp oB aLen acctBytes F) := by
  unfold acc3
  have pureRule {fact : Prop} {P Q : Assertion}
      {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
      (ht : fact → cpsTripleWithin nSteps entry exit_ cr P Q) :
      cpsTripleWithin nSteps entry exit_ cr (P ** ⌜fact⌝) Q := by
    intro R hR s hcr hPR hpc
    obtain ⟨hp, hcompat, ha, hb, hd, hu, hPf, hRb⟩ := hPR
    obtain ⟨hP, hf⟩ := (sepConj_pure_right ha).1 hPf
    exact ht hf R hR s hcr
      ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  refine pureRule (fun hOuter => ?_)
  have existsRule {α : Sort _} {P : α → Assertion} {Q : Assertion}
      {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
      (ht : ∀ x, cpsTripleWithin nSteps entry exit_ cr (P x) Q) :
      cpsTripleWithin nSteps entry exit_ cr (fun hp => ∃ x, P x hp) Q := by
    intro R hR s hcr hPR hpc
    obtain ⟨hp, hcompat, ha, hb, hd, hu, ⟨x, hP⟩, hRb⟩ := hPR
    exact ht x R hR s hcr
      ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  refine existsRule (fun n0 => ?_)
  refine existsRule (fun l0 => ?_)
  refine existsRule (fun n1 => ?_)
  refine existsRule (fun l1 => ?_)
  refine existsRule (fun n2 => ?_)
  refine existsRule (fun l2 => ?_)
  refine existsRule (fun n3 => ?_)
  refine existsRule (fun l3 => ?_)
  rcases hOuter with ⟨b0, hb0, hoff0, _hoff0pos, hoff0le⟩
  refine pureRule (fun hAcc => ?_)
  rcases hAcc with ⟨⟨⟨⟨hdec0, hdec1⟩, hdec2⟩, hdec3⟩, _hn3le⟩
  have hover9 : aB.toNat + aLen + 9 < 2 ^ 64 := by omega
  have ha0 := rlpItemDecode_advance hdec0 hoff0le hover9
  have ha1 := rlpItemDecode_advance hdec1 ha0.2.2 hover9
  have ha2 := rlpItemDecode_advance hdec2 ha1.2.2 hover9
  have hPrefix : outerPrefix acctBytes aB aLen b0
      n0 l0 n1 l1 n2 l2 n3 l3 := by
    refine ⟨hb0, ?_, ?_, ?_, ?_⟩
    · rw [hoff0] at hdec0
      exact hdec0
    · rw [← ha0.1] at hdec1
      exact hdec1
    · rw [← ha1.1] at hdec2
      exact hdec2
    · rw [← ha2.1] at hdec3
      exact hdec3
  have ht := bansf_valueStationsVerdict_own1920 aB newSp oB aLen b0
    n0 l0 n1 l1 n2 l2 n3 l3 acctBytes F hF hsalign hoalign hslack
    hover hvalid hovout hovalid ha2.2.2 hPrefix
  exact cpsTripleWithin_weaken (by
    unfold valueEntryAmbient valueStationsEntryOwn laterFieldZeros
    xsimp) (fun _ hp => ⟨n3, l3, hp⟩) ht

#print axioms bansf_valueStations_from_acc3

/-- Common B+736 post after outer items 0--3 and all value stations. -/
def itemsVerdictPost (aB newSp oB : Word) (aLen off0 : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion := fun h =>
  (itemRej aB newSp acctBytes (valueEntryAmbient aB newSp oB aLen F) **
      ⌜OuterInitOk acctBytes aLen off0⌝) h ∨
  valueStationsFromAcc3Post aB newSp oB aLen acctBytes F h

/-- Outer items 0--3 followed by all value stations, with both parse rejection
    and the semantic verdict reaching the common epilogue entry. -/
theorem bansf_itemsVerdict_spec
    (aB newSp oB : Word) (aLen off0 : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hoalign : oB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hovout : oB.toNat + 80 ≤ 2 ^ 64)
    (hovalid : ∀ k, k < 80 →
      isValidByteAccess (oB + BitVec.ofNat 64 k) = true)
    (hoff0le : off0 ≤ aLen) :
    cpsTripleWithin (372 + (((98 * (aLen + 1) + 700) +
        2 * (98 * (aLen + 1) + (7 * acctBytes.length + 800))) + 2))
      (B + 104) (B + 736) bansfCR
      (((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off0)) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off0)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
       bytesRegion aB acctBytes **
       (valueEntryAmbient aB newSp oB aLen F **
        ⌜OuterInitOk acctBytes aLen off0⌝))
      (itemsVerdictPost aB newSp oB aLen off0 acctBytes F) := by
  have hAmbient := valueEntryAmbient_pcFree aB newSp oB aLen F hF
  have hItems := bansf_chainItems_spec aB newSp aLen off0 acctBytes
    (valueEntryAmbient aB newSp oB aLen F)
    hAmbient hsalign hslack hover hvalid hoff0le
  have hItemsF := cpsBranchWithin_frameR
    (⌜OuterInitOk acctBytes aLen off0⌝)
    (inferInstance : Assertion.PCFree
      (⌜OuterInitOk acctBytes aLen off0⌝)).proof hItems
  have hValues := bansf_valueStations_from_acc3 aB newSp oB aLen off0
    acctBytes F hF hsalign hoalign hslack hover hvalid hovout hovalid
  have hbr := cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr hItemsF
    (fun _ hp => hp) hValues (fun _ hp => hp)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => hp)
    (cpsBranchWithin_same_exit_to_triple hbr)

#print axioms bansf_itemsVerdict_spec

/-- Verdict post after eliminating the existential outer-header offset carried
    by `chainMidB`. -/
def chainMidVerdictPost (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion := fun h =>
  ∃ off0, itemsVerdictPost aB newSp oB aLen off0 acctBytes F h

/-- The spilled outer-init state contains exactly the ambient resources and
    pure header fact needed by the item/value chain. -/
theorem bansf_chainMidVerdict_spec
    (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hoalign : oB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hovout : oB.toNat + 80 ≤ 2 ^ 64)
    (hovalid : ∀ k, k < 80 →
      isValidByteAccess (oB + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (372 + (((98 * (aLen + 1) + 700) +
        2 * (98 * (aLen + 1) + (7 * acctBytes.length + 800))) + 2))
      (B + 104) (B + 736) bansfCR
      (chainMidB aB newSp oB aLen acctBytes
        (memOwn (newSp + 64) ** memOwn (newSp + 72) **
         regOwn .x19 ** regOwn .x20 ** F))
      (chainMidVerdictPost aB newSp oB aLen acctBytes F) := by
  unfold chainMidB
  have existsRule {α : Sort _} {P : α → Assertion} {Q : Assertion}
      {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
      (ht : ∀ x, cpsTripleWithin nSteps entry exit_ cr (P x) Q) :
      cpsTripleWithin nSteps entry exit_ cr (fun hp => ∃ x, P x hp) Q := by
    intro R hR s hcr hPR hpc
    obtain ⟨hp, hcompat, ha, hb, hd, hu, ⟨x, hP⟩, hRb⟩ := hPR
    exact ht x R hR s hcr
      ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  have pureRule {fact : Prop} {P Q : Assertion}
      {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
      (ht : fact → cpsTripleWithin nSteps entry exit_ cr P Q) :
      cpsTripleWithin nSteps entry exit_ cr (P ** ⌜fact⌝) Q := by
    intro R hR s hcr hPR hpc
    obtain ⟨hp, hcompat, ha, hb, hd, hu, hPf, hRb⟩ := hPR
    obtain ⟨hP, hf⟩ := (sepConj_pure_right ha).1 hPf
    exact ht hf R hR s hcr
      ⟨hp, hcompat, ha, hb, hd, hu, hP, hRb⟩ hpc
  refine existsRule (fun off0 => ?_)
  refine pureRule (fun hOuter => ?_)
  rcases hOuter with ⟨_b0, _hb0, _hoff0, _hoff0pos, hoff0le⟩
  have hOuter : OuterInitOk acctBytes aLen off0 :=
    ⟨_b0, _hb0, _hoff0, _hoff0pos, hoff0le⟩
  have ht := bansf_itemsVerdict_spec aB newSp oB aLen off0 acctBytes F
    hF hsalign hoalign hslack hover hvalid hovout hovalid hoff0le
  exact cpsTripleWithin_weaken (by
    intro h hp
    have hpp := (sepConj_pure_right h).2 ⟨hp, hOuter⟩
    unfold valueEntryAmbient
    xperm_hyp hpp) (fun _ hp => ⟨off0, hp⟩) ht

#print axioms bansf_chainMidVerdict_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
