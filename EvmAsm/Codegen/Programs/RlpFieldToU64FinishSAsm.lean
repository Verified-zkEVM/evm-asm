/-
  Final status dispatch and whole-routine composition for strict K34.
-/

import EvmAsm.Codegen.Programs.RlpFieldToU64SAsm

namespace EvmAsm.Codegen.RlpFieldToU64SAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

def scalarCore
    (sp0 listBase offset len v12 value status : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) : Assertion :=
  (.x1 ↦ᵣ (B + 84)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
  (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
  ((.x10 ↦ᵣ value) ** (.x11 ↦ᵣ status)) **
  contentCarry sp0 listBase offset len v12 saved

def scalarResult
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : Assertion :=
  fun h => ∃ offset len v12 value status,
    ((scalarCore sp0 listBase offset len v12 value status saved bytes **
      ⌜EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index
        offset len⌝) **
      ⌜ScalarOutcome bytes offset.toNat len.toNat value status⌝) h

theorem contentDone_to_scalarResult
    (sp0 listBase : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    contentDone sp0 listBase saved bytes listLen index h →
      scalarResult sp0 listBase saved bytes listLen index h := by
  intro h hp
  unfold contentDone at hp
  obtain ⟨offset, len, v12, hp⟩ := hp
  unfold contentRawPost contentCallPost at hp
  extract_pure_deep hp
  obtain ⟨hp, h_ok⟩ := hp
  let R : Assertion :=
    (.x1 ↦ᵣ (B + 84)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
    contentCarry sp0 listBase offset len v12 saved
  have hsplit : (R ** contentOutcome bytes offset.toNat len.toNat) h := by
    unfold R
    xperm_hyp hp
  obtain ⟨hRState, ho, hd, hu, hRProof, hout⟩ := hsplit
  have hs := contentOutcome_semantic bytes offset.toNat len.toNat ho hout
  obtain ⟨value, status, hs⟩ := hs
  extract_pure_deep hs
  obtain ⟨hs, h_scalar⟩ := hs
  unfold scalarResult
  refine ⟨offset, len, v12, value, status, ?_⟩
  apply (sepConj_pure_right h).2
  constructor
  · apply (sepConj_pure_right h).2
    constructor
    · have hjoined : (R **
          ((.x10 ↦ᵣ value) ** (.x11 ↦ᵣ status))) h :=
        ⟨hRState, ho, hd, hu, hRProof, hs⟩
      unfold R at hjoined
      unfold scalarCore
      xperm_hyp hjoined
    · exact h_ok
  · exact h_scalar

#print axioms contentDone_to_scalarResult

end EvmAsm.Codegen.RlpFieldToU64SAsm
