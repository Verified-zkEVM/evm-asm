/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainJ

  Code-station continuation assembly for bal_account_nonstorage_finals.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainI

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- At `B + 700`, materialize a successfully decoded tuple value as the
    selected code window. -/
theorem bansf_codeStationCont700_spec
    (aB newSp oB n5 : Word) (aLen tEnd off fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hFF : ∀ vNext vLen : Word,
      rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsTripleWithin 6 (B + 700) (B + 724) bansfCR
      (tupleValOk aB newSp tEnd off acctBytes F **
       (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20))
      (codeStationPost aB newSp oB aLen fOff fSpanN n5 acctBytes G F) := by
  apply cpsTripleWithin_weaken
    (codeTupleValOk_to_materializePre aB newSp oB n5 aLen tEnd off acctBytes G F)
    (fun _ hq => hq)
  refine cpsTripleWithin_exists_pre_gen (fun vNext => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun vLen => ?_)
  let R : Assertion :=
    ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) **
    memOwn (newSp + 72) ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
    bytesRegion aB acctBytes ** ((newSp + 48) ↦ₘ n5) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** regOwn .x19 ** regOwn .x20 **
    ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
      (aB + BitVec.ofNat 64 tEnd) vNext vLen⌝ ** F ** G
  let P : Assertion :=
    ((.x10 : Reg) ↦ᵣ vNext) ** ((.x12 : Reg) ↦ᵣ vLen) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x18 : Reg) ↦ᵣ oB) **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** R
  apply cpsTripleWithin_weaken (P := P ** regOwn .x29 ** regOwn .x5)
    (fun h hp => by dsimp only [P, R]; xperm_hyp hp) (fun _ hq => hq)
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2
    (r1 := .x29) (r2 := .x5) (fun v29 v5 => ?_)
  have hm := bansf_codeMaterialize175_spec aB oB vNext vLen v29 v5
  have hmF := cpsTripleWithin_frameR R (by
    dsimp only [R]
    pcf
    exact hF
    exact hG) hm
  exact cpsTripleWithin_weaken (fun h hp => by dsimp only [R]; xperm_hyp hp)
    (fun h hq => by
      have hq' :
          ((((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
           ((.x12 : Reg) ↦ᵣ vLen) ** ((.x8 : Reg) ↦ᵣ aB) **
           ((.x18 : Reg) ↦ᵣ oB) ** ((.x29 : Reg) ↦ᵣ (vNext - vLen - aB)) **
           ((.x5 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((oB + 56) ↦ₘ (1 : Word)) **
           ((oB + 64) ↦ₘ (vNext - vLen - aB)) ** ((oB + 72) ↦ₘ vLen) **
           ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) **
           memOwn (newSp + 72) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
           regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
           bytesRegion aB acctBytes ** F ** G ** ((newSp + 48) ↦ₘ n5) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** regOwn .x19 ** regOwn .x20) **
          ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
            (aB + BitVec.ofNat 64 tEnd) vNext vLen⌝) h := by
        dsimp only [R] at hq
        xperm_hyp hq
      obtain ⟨hsp, hdec⟩ := (sepConj_pure_right h).1 hq'
      exact codeMaterialized_to_stationPost aB newSp oB n5 vNext vLen aLen
        fOff fSpanN acctBytes G F (hFF vNext vLen hdec) h hsp) hmF

#print axioms bansf_codeStationCont700_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
