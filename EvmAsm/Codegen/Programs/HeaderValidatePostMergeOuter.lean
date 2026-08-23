/-
  K67 `header_validate_post_merge` — authenticated outer-list station
  contracts.  This low-level module is imported by the top-level station
  composition; keeping the outer relation here keeps that composition file
  under the Codegen/Programs size cap.
-/

import EvmAsm.Codegen.Programs.HeaderValidatePostMergeRound

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpWalkNextStrictFuel
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! The init call establishes the canonical outer-list relation.  Keep it as a
    separate pure fact while the machine loop scans fields: the field-level
    `StrictPrefix` facts alone do not identify the global header list. -/
def k67OuterPayload (base : Word) (bytes : List (BitVec 8))
    (startOff : Nat) : Prop :=
  RlpListNthItemSAsm.StrictListPayload bytes base bytes.length startOff
    (base + BitVec.ofNat 64 bytes.length)

def k67QdiffOuter (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (startOff : Nat) (svals : Reg → Word) (v21 : Word) : Assertion := fun h =>
  ∃ (cur omEnd omLen : Nat) (next7 len7 n1 l1 : Word)
    (v6 v7 v28 v29 v30 v31 : Word),
    (((.x1 ↦ᵣ (K + 68)) ** (.x10 ↦ᵣ next7) ** (.x11 ↦ᵣ (0 : Word)) **
      (.x12 ↦ᵣ len7) **
      (.x8 ↦ᵣ (base + BitVec.ofNat 64 omEnd)) **
      (.x9 ↦ᵣ BitVec.ofNat 64 omLen) **
      (.x18 ↦ᵣ (base + BitVec.ofNat 64 cur)) **
      (.x19 ↦ᵣ (base + BitVec.ofNat 64 bytes.length)) **
      (.x20 ↦ᵣ (7 : Word)) ** (.x21 ↦ᵣ v21) **
      (.x5 ↦ᵣ (7 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
      (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
      (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
      frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
      bytesRegion base bytes ** bytesRegion omConst (k67OmBytes)) **
      ⌜k67OuterPayload base bytes startOff ∧
        RlpListNthItemSAsm.StrictPrefix bytes base
          (base + BitVec.ofNat 64 bytes.length) startOff 7 cur ∧
        RlpListNthItemSAsm.StrictNthItem bytes base
          (base + BitVec.ofNat 64 bytes.length) 7 startOff next7 len7 ∧
        len7 ≠ (0 : Word) ∧
        RlpListNthItemSAsm.StrictNthItem bytes base
          (base + BitVec.ofNat 64 bytes.length) 1 startOff n1 l1 ∧
        omEnd = (n1 - base).toNat ∧ omLen = l1.toNat ∧
        cur ≤ bytes.length⌝) h

theorem k67Qdiff_to_outer
    (sp0 base omConst : Word) (bytes : List (BitVec 8))
    (startOff : Nat) (svals : Reg → Word) (v21 : Word)
    (houter : k67OuterPayload base bytes startOff) :
    ∀ h, k67Qdiff sp0 base omConst bytes startOff svals v21 h →
      k67QdiffOuter sp0 base omConst bytes startOff svals v21 h := by
  intro h hq
  unfold k67Qdiff at hq
  unfold k67QdiffOuter
  rcases hq with ⟨cur, omEnd, omLen, next7, len7, n1, l1,
    v6, v7, v28, v29, v30, v31, hq⟩
  refine ⟨cur, omEnd, omLen, next7, len7, n1, l1,
    v6, v7, v28, v29, v30, v31, ?_⟩
  obtain ⟨hres, hpure⟩ := (sepConj_pure_right _).1 hq
  exact (sepConj_pure_right _).2 ⟨hres, ⟨houter, hpure⟩⟩

end EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec
