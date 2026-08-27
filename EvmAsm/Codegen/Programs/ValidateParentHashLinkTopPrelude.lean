import EvmAsm.Codegen.Programs.ValidateParentHashLinkSpec
import EvmAsm.Codegen.Programs.ValidateParentHashLinkCompare

/-!
  Shared definitions and framing lemmas for `validate_parent_hash_link`.

  The final theorem is kept in `ValidateParentHashLinkTop`; the continuation
  contracts are in `ValidateParentHashLinkTopContinuation`.
-/

namespace EvmAsm.Codegen.ValidateParentHashLinkSpec
set_option maxRecDepth 8000
open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpListNthItemSAsm

theorem top_reg12_to_regOwn
    (v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 : Word) : ∀ h,
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
      (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
      (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) h →
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwn .x15 ** regOwn .x16 ** regOwn .x17 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14) h := by
  intro h hp
  exact sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x15)
          (sepConj_mono (regIs_implies_regOwn .x16)
            (sepConj_mono (regIs_implies_regOwn .x17)
              (sepConj_mono (regIs_implies_regOwn .x28)
                (sepConj_mono (regIs_implies_regOwn .x29)
                  (sepConj_mono (regIs_implies_regOwn .x30)
                    (sepConj_mono (regIs_implies_regOwn .x31)
                      (sepConj_mono (regIs_implies_regOwn .x13)
                        (regIs_implies_regOwn .x14))))))))))) h hp

theorem top_regPair_to_regOwn (a b : Word) : ∀ h,
    ((.x11 ↦ᵣ a) ** (.x12 ↦ᵣ b)) h →
      (regOwn .x11 ** regOwn .x12) h := by
  intro h hp
  exact sepConj_mono (regIs_implies_regOwn .x11)
    (regIs_implies_regOwn .x12) h hp

theorem top_reg4_to_regOwn (v5 v6 v7 v28 : Word) : ∀ h,
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) h →
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) h := by
  intro h hp
  exact sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7) (regIs_implies_regOwn .x28))) h hp

theorem top_mem4_to_memOwn
    (a0 a1 a2 a3 v0 v1 v2 v3 : Word) (rest : Assertion) : ∀ h,
    ((a0 ↦ₘ v0) ** (a1 ↦ₘ v1) ** (a2 ↦ₘ v2) ** (a3 ↦ₘ v3) ** rest) h →
      (memOwn a0 ** memOwn a1 ** memOwn a2 ** memOwn a3 ** rest) h := by
  intro h hp
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn (fun _ x => x)))) h hp

theorem top_mem4_with_owned_tail_to_memOwn
    (a0 a1 a2 a3 r0 r1 r2 r3 v0 v1 v2 v3 : Word) : ∀ h,
    ((a0 ↦ₘ v0) ** (a1 ↦ₘ v1) ** (a2 ↦ₘ v2) ** (a3 ↦ₘ v3) **
      memOwn r0 ** memOwn r1 ** memOwn r2 ** memOwn r3) h →
      (memOwn a0 ** memOwn a1 ** memOwn a2 ** memOwn a3 **
        memOwn r0 ** memOwn r1 ** memOwn r2 ** memOwn r3) h := by
  intro h hp
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (fun _ x => x)))) h hp

theorem top_reg8_to_regOwn
    (v13 v14 v15 v16 v17 v29 v30 v31 : Word) : ∀ h,
    ((.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
      (.x17 ↦ᵣ v17) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)) h →
    (regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31) h := by
  intro h hp
  exact sepConj_mono (regIs_implies_regOwn .x13)
    (sepConj_mono (regIs_implies_regOwn .x14)
      (sepConj_mono (regIs_implies_regOwn .x15)
        (sepConj_mono (regIs_implies_regOwn .x16)
          (sepConj_mono (regIs_implies_regOwn .x17)
            (sepConj_mono (regIs_implies_regOwn .x29)
              (sepConj_mono (regIs_implies_regOwn .x30)
                (regIs_implies_regOwn .x31))))))) h hp

/-
theorem top_vphl_compare_prefix_to_own
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word) : ∀ h,
    vphlTopComparePrefix spC retPC retHdr parentLenW childLenW outPtr v21
      v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 cs0 cs1 cs2 cs3 cs4 parentBase childBase h →
    vphlTopComparePrefixOwn spC retPC retHdr parentLenW childLenW outPtr v21
      v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 cs0 cs1 cs2 cs3 cs4 parentBase childBase h := by
  intro h hp
  let fixed : Assertion :=
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ retPC) **
      (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
      (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
      (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
  let regs : Assertion :=
    ((.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
      (.x17 ↦ᵣ v17) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
  let regsOwn : Assertion :=
    (regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31)
  let tail : Assertion :=
    ((.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) **
      ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** empAssertion)
  have hp' : (fixed ** regs ** tail) h := by
    unfold vphlTopComparePrefix at hp
    dsimp [fixed, regs, tail]
    xperm_chunked hp
  have hq := sepConj_mono (fun _ x => x)
    (sepConj_mono (top_reg8_to_regOwn v13 v14 v15 v16 v17 v29 v30 v31)
      (fun _ x => x)) h hp'
  unfold vphlTopComparePrefixOwn
  dsimp [fixed, regsOwn, tail]
  xperm_chunked hq

-/
theorem top_frameSlotsSaved_to_own :
    ∀ (frame : FrameDesc) (newSp : Word) (vals : Reg → Word) h,
      frameSlotsSaved frame newSp vals h → frameSlotsOwn frame newSp h := by
  intro frame
  induction frame with
  | nil =>
      intro newSp vals h hp
      simpa only [frameSlotsSaved_nil, frameSlotsOwn_nil] using hp
  | cons p rest ih =>
      intro newSp vals h hp
      have hp' :
          (((newSp + signExtend12 p.2) ↦ₘ vals p.1) **
            frameSlotsSaved rest newSp vals) h := by
        simpa only [frameSlotsSaved_cons] using hp
      have hq := sepConj_mono memIs_implies_memOwn (ih newSp vals) h hp'
      simpa only [frameSlotsOwn_cons] using hq

theorem top_keccakFrameSaved_to_own
    (newSp : Word) (vals : Reg → Word) : ∀ h,
      frameSlotsSaved keccakFrame newSp vals h →
        frameSlotsOwn keccakFrame newSp h := by
  intro h hp
  simp only [frameSlotsSaved, frameSlotsOwn, keccakFrame, List.foldr] at hp ⊢
  simp only [sepConj_emp_right'] at hp ⊢
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)) h hp

theorem top_frameSaved_with_rest_to_own
    (frame : FrameDesc) (newSp : Word) (vals : Reg → Word) (rest : Assertion) : ∀ h,
      (frameSlotsSaved frame newSp vals ** rest) h →
        (frameSlotsOwn frame newSp ** rest) h := by
  intro h hp
  exact sepConj_mono_left
    (top_frameSlotsSaved_to_own frame newSp vals) h hp

theorem top_keccak_slot_h0 (sp : Word) :
    sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12) +
        signExtend12 (0 : BitVec 12) = sp - BitVec.ofNat 64 48 := by
  simp [signExtend12]
  grind

theorem top_keccak_ret_slot (sp : Word) :
    sp + signExtend12 (-16 : BitVec 12) = sp - BitVec.ofNat 64 16 := by
  simp [signExtend12]
  grind

theorem top_keccak_slot_h8 (sp : Word) :
    sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12) +
        signExtend12 (8 : BitVec 12) = sp - BitVec.ofNat 64 40 := by
  simp [signExtend12]
  grind

theorem top_keccak_slot_h16 (sp : Word) :
    sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12) +
        signExtend12 (16 : BitVec 12) = sp - BitVec.ofNat 64 32 := by
  simp [signExtend12]
  grind

theorem top_keccak_slot_h24 (sp : Word) :
    sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12) +
        signExtend12 (24 : BitVec 12) = sp - BitVec.ofNat 64 24 := by
  simp [signExtend12]
  grind

theorem top_keccak_slots_to_stackFree
    (sp : Word) (retPC : Word) (vals : Reg → Word) :
    ∀ h,
      (memOwn (sp - BitVec.ofNat 64 8) **
        ((sp + signExtend12 (-16 : BitVec 12)) ↦ₘ retPC) **
        frameSlotsSaved keccakFrame
          (sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12)) vals **
        memOwn (sp - BitVec.ofNat 64 56) ** memOwn (sp - BitVec.ofNat 64 64)) h →
      stackFree sp 8 h := by
  intro h hp
  have hp1 :
      (((sp + signExtend12 (-16 : BitVec 12)) ↦ₘ retPC) **
        frameSlotsSaved keccakFrame
          (sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12)) vals **
        (memOwn (sp - BitVec.ofNat 64 8) **
          memOwn (sp - BitVec.ofNat 64 56) ** memOwn (sp - BitVec.ofNat 64 64))) h := by
    xperm_hyp hp
  have h0 := top_keccak_slot_h0 sp
  have h8 := top_keccak_slot_h8 sp
  have h16 := top_keccak_slot_h16 sp
  have h24 := top_keccak_slot_h24 sp
  have hp2 :
      (memOwn (sp - BitVec.ofNat 64 16) **
        memOwn (sp - BitVec.ofNat 64 48) ** memOwn (sp - BitVec.ofNat 64 40) **
        memOwn (sp - BitVec.ofNat 64 32) ** memOwn (sp - BitVec.ofNat 64 24) **
        memOwn (sp - BitVec.ofNat 64 8) ** memOwn (sp - BitVec.ofNat 64 56) **
        memOwn (sp - BitVec.ofNat 64 64)) h := by
    have hp1a :
        (memOwn (sp - BitVec.ofNat 64 16) **
          frameSlotsSaved keccakFrame
            (sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12)) vals **
          memOwn (sp - BitVec.ofNat 64 8) ** memOwn (sp - BitVec.ofNat 64 56) **
          memOwn (sp - BitVec.ofNat 64 64)) h := by
      have hp1' :
          (memOwn (sp + signExtend12 (-16 : BitVec 12)) **
            frameSlotsSaved keccakFrame
              (sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12)) vals **
            memOwn (sp - BitVec.ofNat 64 8) ** memOwn (sp - BitVec.ofNat 64 56) **
            memOwn (sp - BitVec.ofNat 64 64)) h := by
        exact sepConj_mono memIs_implies_memOwn (fun _ x => x) h hp1
      simpa only [top_keccak_ret_slot] using hp1'
    simp only [frameSlotsSaved, keccakFrame, List.foldr, sepConj_emp_right'] at hp1a
    rw [h0, h8, h16, h24] at hp1a
    have hp1r :
        (((sp - BitVec.ofNat 64 48) ↦ₘ vals .x8) **
          ((sp - BitVec.ofNat 64 40) ↦ₘ vals .x9) **
          ((sp - BitVec.ofNat 64 32) ↦ₘ vals .x18) **
          ((sp - BitVec.ofNat 64 24) ↦ₘ vals .x20) **
          memOwn (sp - BitVec.ofNat 64 16) ** memOwn (sp - BitVec.ofNat 64 8) **
          memOwn (sp - BitVec.ofNat 64 56) ** memOwn (sp - BitVec.ofNat 64 64)) h := by
      xperm_chunked hp1a
    have hp2' := top_mem4_with_owned_tail_to_memOwn
      (sp - BitVec.ofNat 64 48) (sp - BitVec.ofNat 64 40)
      (sp - BitVec.ofNat 64 32) (sp - BitVec.ofNat 64 24)
      (sp - BitVec.ofNat 64 16) (sp - BitVec.ofNat 64 8)
      (sp - BitVec.ofNat 64 56) (sp - BitVec.ofNat 64 64)
      (vals .x8) (vals .x9) (vals .x18) (vals .x20) h hp1r
    xperm_chunked hp2'
  simp only [stackFree_succ, stackFree_zero]
  show (memOwn (sp - BitVec.ofNat 64 64) ** memOwn (sp - BitVec.ofNat 64 56) **
    memOwn (sp - BitVec.ofNat 64 48) ** memOwn (sp - BitVec.ofNat 64 40) **
    memOwn (sp - BitVec.ofNat 64 32) ** memOwn (sp - BitVec.ofNat 64 24) **
    memOwn (sp - BitVec.ofNat 64 16) ** memOwn (sp - BitVec.ofNat 64 8) **
    empAssertion) h
  simp only [sepConj_emp_right']
  xperm_chunked hp2

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | assumption)

def vphlTopKFrame
    (spC retHdr outPtr : Word) (cs0 cs1 cs2 cs3 cs4 v21 : Word)
    (parentBase : Word) (parentBytes claimedOld : List (BitVec 8))
    (os : List (BitVec 8)) : Assertion :=
    regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
    (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
    ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
    bytesRegion parentBase parentBytes ** (outPtr ↦ₘ (0 : Word)) **
    bytesRegion vphlClaimedAddr claimedOld **
    bytesRegion vphlComputedAddr (List.replicate 32 (0 : BitVec 8)) **
    bytesRegion vphlZk3 os

def vphlTopKFrameCore
    (spC retHdr outPtr : Word) (cs0 cs1 cs2 cs3 cs4 : Word)
    (parentBase : Word) (parentBytes claimedOld : List (BitVec 8))
    (os : List (BitVec 8)) : Assertion :=
    (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
    ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
    bytesRegion parentBase parentBytes ** (outPtr ↦ₘ (0 : Word)) **
    bytesRegion vphlClaimedAddr claimedOld **
    bytesRegion vphlComputedAddr (List.replicate 32 (0 : BitVec 8)) **
    bytesRegion vphlZk3 os

def vphlTopContinuationPre
    (spC parentBase parentLenW childBase childLenW outPtr v21 status v11 v12 offset len : Word)
    (childBytes : List (BitVec 8))
    (kFrame F : Assertion) : Assertion :=
  ((.x1 ↦ᵣ (vphlBase + 84)) **
    (((.x2 ↦ᵣ spC) ** stackFree spC 8 **
      (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
      (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
      (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ v21) **
     ((.x10 ↦ᵣ status) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion childBase childBytes **
      (vphlOffsetAddr ↦ₘ offset) ** (vphlLengthAddr ↦ₘ len)))) **
   (kFrame ** F))

def vphlTopArmPre
    (spC parentBase parentLenW childBase childLenW outPtr v21 status v11 v12 offset len : Word)
    (childBytes : List (BitVec 8)) (kFrame F : Assertion) : Assertion :=
  ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (vphlBase + 84)) **
    (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
    (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
    (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ v21) ** (.x10 ↦ᵣ status) **
    (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x0 ↦ᵣ (0 : Word)) **
    stackFree spC 8 **
    bytesRegion childBase childBytes ** (vphlOffsetAddr ↦ₘ offset) **
    (vphlLengthAddr ↦ₘ len) ** kFrame ** F)

@[irreducible] def vphlTopHashPost
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word)
    (parentBytes childBytes claimedB computedB zk3B : List (BitVec 8))
    (fo ln : Word) : Assertion :=
  ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ retPC) **
    (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
    (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
    (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ v21) ** (.x10 ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x11 **
    regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15 **
    regOwn .x16 ** regOwn .x17 ** regOwn .x28 ** regOwn .x29 **
    regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
    (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
    ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
    ((spC + 40) ↦ₘ cs4) **
    memOwn (spC - BitVec.ofNat 64 8) **
    ((spC + signExtend12 (-16 : BitVec 12)) ↦ₘ retPC) **
    frameSlotsSaved keccakFrame
      (spC + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12))
      (keccakEntryVals parentBase parentLenW childBase outPtr) **
    memOwn (spC - BitVec.ofNat 64 56) ** memOwn (spC - BitVec.ofNat 64 64) **
    bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
    (outPtr ↦ₘ (0 : Word)) ** (vphlOffsetAddr ↦ₘ fo) **
    (vphlLengthAddr ↦ₘ ln) ** bytesRegion vphlClaimedAddr claimedB **
    bytesRegion vphlComputedAddr computedB ** bytesRegion vphlZk3 zk3B)

@[irreducible] def vphlTopHashRest
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word)
    (parentBytes childBytes claimedB computedB zk3B : List (BitVec 8))
    (fo ln : Word) : Assertion :=
  ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ retPC) **
    (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
    (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
    (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ v21) ** (.x10 ↦ᵣ (0 : Word)) **
    (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) **
    ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
    ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
    memOwn (spC - BitVec.ofNat 64 8) **
    ((spC + signExtend12 (-16 : BitVec 12)) ↦ₘ retPC) **
    frameSlotsSaved keccakFrame
      (spC + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12))
      (keccakEntryVals parentBase parentLenW childBase outPtr) **
    memOwn (spC - BitVec.ofNat 64 56) ** memOwn (spC - BitVec.ofNat 64 64) **
    bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
    (outPtr ↦ₘ (0 : Word)) ** (vphlOffsetAddr ↦ₘ fo) **
    (vphlLengthAddr ↦ₘ ln) ** bytesRegion vphlClaimedAddr claimedB **
    bytesRegion vphlComputedAddr computedB ** bytesRegion vphlZk3 zk3B)

def vphlTopComparePrefix
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word) : Assertion :=
  ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ retPC) **
    (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
    (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
    (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
    (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) **
    (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) ** (.x29 ↦ᵣ v29) **
    (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
    (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
    ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
    empAssertion)

def vphlTopComparePrefixOwn
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word) : Assertion :=
  ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ retPC) **
    (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
    (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
    (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
    regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
    (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
    ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
    empAssertion)

theorem top_vphl_compare_prefix_to_own
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word) : ∀ h,
    vphlTopComparePrefix spC retPC retHdr parentLenW childLenW outPtr v21
      v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 cs0 cs1 cs2 cs3 cs4 parentBase childBase h →
    vphlTopComparePrefixOwn spC retPC retHdr parentLenW childLenW outPtr v21
      v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 cs0 cs1 cs2 cs3 cs4 parentBase childBase h := by
  intro h hp
  let fixed : Assertion :=
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ retPC) **
      (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
      (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
      (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
  let regs : Assertion :=
    ((.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
      (.x17 ↦ᵣ v17) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
  let regsOwn : Assertion :=
    (regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31)
  let tail : Assertion :=
    ((.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) **
      ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** empAssertion)
  have hp' : (fixed ** regs ** tail) h := by
    unfold vphlTopComparePrefix at hp
    dsimp [fixed, regs, tail] at hp ⊢
    xperm_hyp hp
  have hq := sepConj_mono (fun _ x => x)
    (sepConj_mono (top_reg8_to_regOwn v13 v14 v15 v16 v17 v29 v30 v31)
      (fun _ x => x)) h hp'
  unfold vphlTopComparePrefixOwn
  dsimp [fixed, regsOwn, tail] at hq ⊢
  xperm_hyp hq

def vphlTopCompareStackSaved
    (spC retPC parentBase parentLenW childBase outPtr : Word) : Assertion :=
  (memOwn (spC - BitVec.ofNat 64 8) **
    ((spC + signExtend12 (-16 : BitVec 12)) ↦ₘ retPC) **
    frameSlotsSaved keccakFrame
      (spC + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12))
      (keccakEntryVals parentBase parentLenW childBase outPtr) **
    memOwn (spC - BitVec.ofNat 64 56) ** memOwn (spC - BitVec.ofNat 64 64))

def vphlTopCompareSuffix
    (spC parentBase childBase : Word) (parentBytes childBytes : List (BitVec 8))
  (fo ln : Word) (zk3B : List (BitVec 8)) : Assertion :=
  (bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
    (vphlOffsetAddr ↦ₘ fo) ** (vphlLengthAddr ↦ₘ ln) ** bytesRegion vphlZk3 zk3B)

def vphlTopCompareBase
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word)
    (parentBytes childBytes : List (BitVec 8)) (fo ln : Word)
    (zk3B : List (BitVec 8)) : Assertion :=
  (vphlTopComparePrefix spC retPC retHdr parentLenW childLenW outPtr v21
      v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 cs0 cs1 cs2 cs3 cs4 parentBase childBase **
    vphlTopCompareStackSaved spC retPC parentBase parentLenW childBase outPtr **
    vphlTopCompareSuffix spC parentBase childBase parentBytes childBytes fo ln zk3B)

def vphlTopCompareDword
    (claimedBytes computedBytes : List (BitVec 8)) (q : Nat)
    (compareBase : Assertion) : Assertion :=
  (.x6 ↦ᵣ vphlComputedAddr) **
    (.x7 ↦ᵣ vphlDwordAt claimedBytes q) **
    (.x28 ↦ᵣ vphlDwordAt computedBytes q) **
    bytesRegion vphlClaimedAddr claimedBytes **
    bytesRegion vphlComputedAddr computedBytes ** compareBase

def vphlTopEpiRegsExact
    (v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 : Word) : Assertion :=
  regIs .x5 v5 ** regIs .x6 v6 ** regIs .x7 v7 **
    regIs .x15 v15 ** regIs .x16 v16 ** regIs .x17 v17 **
    regIs .x28 v28 ** regIs .x29 v29 ** regIs .x30 v30 **
    regIs .x31 v31 ** regIs .x13 v13 ** regIs .x14 v14

def vphlTopEpiRegsOwn : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** regOwn .x13 ** regOwn .x14

def vphlTopEpiPreOwn
    (spC retHdr x1Val statusW v11e v12e parentBase parentLenW childBase childLenW outPtr v21 : Word)
    (cs0 cs1 cs2 cs3 cs4 outValW offV lenV : Word)
    (parentBytes childBytes claimedB computedB osPost : List (BitVec 8)) : Assertion :=
  (regIs .x2 spC ** regIs .x1 x1Val ** regIs .x8 parentBase **
    regIs .x9 parentLenW ** regIs .x18 childBase ** regIs .x19 childLenW **
    regIs .x20 outPtr ** regIs .x21 v21 ** regIs .x10 statusW **
    regIs .x11 v11e ** regIs .x12 v12e ** vphlTopEpiRegsOwn **
    regIs .x0 (0 : Word) ** memIs spC retHdr ** memIs (spC + 8) cs0 **
    memIs (spC + 16) cs1 ** memIs (spC + 24) cs2 ** memIs (spC + 32) cs3 **
    memIs (spC + 40) cs4 ** stackFree spC 8 ** bytesRegion parentBase parentBytes **
    bytesRegion childBase childBytes ** memIs outPtr outValW **
    memIs vphlOffsetAddr offV ** memIs vphlLengthAddr lenV **
    bytesRegion vphlClaimedAddr claimedB ** bytesRegion vphlComputedAddr computedB **
    bytesRegion vphlZk3 osPost)

def vphlTopEpiPreExact
    (spC retHdr x1Val statusW v11e v12e parentBase parentLenW childBase childLenW outPtr v21 : Word)
    (cs0 cs1 cs2 cs3 cs4 outValW offV lenV : Word)
    (parentBytes childBytes claimedB computedB osPost : List (BitVec 8))
    (v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 : Word) : Assertion :=
  (vphlTopEpiRegsExact v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 **
    regIs .x2 spC ** regIs .x1 x1Val ** regIs .x8 parentBase **
    regIs .x9 parentLenW ** regIs .x18 childBase ** regIs .x19 childLenW **
    regIs .x20 outPtr ** regIs .x21 v21 ** regIs .x10 statusW **
    regIs .x11 v11e ** regIs .x12 v12e **
    regIs .x0 (0 : Word) ** memIs spC retHdr ** memIs (spC + 8) cs0 **
    memIs (spC + 16) cs1 ** memIs (spC + 24) cs2 ** memIs (spC + 32) cs3 **
    memIs (spC + 40) cs4 ** stackFree spC 8 ** bytesRegion parentBase parentBytes **
    bytesRegion childBase childBytes ** memIs outPtr outValW **
    memIs vphlOffsetAddr offV ** memIs vphlLengthAddr lenV **
    bytesRegion vphlClaimedAddr claimedB ** bytesRegion vphlComputedAddr computedB **
    bytesRegion vphlZk3 osPost)

def vphlTopEpiPost
    (sp0 spC retHdr statusW v11e v12e parentBase parentLenW childBase childLenW outPtr v21 : Word)
    (cs0 cs1 cs2 cs3 cs4 outValW offV lenV : Word)
    (parentBytes childBytes claimedB computedB osPost : List (BitVec 8)) : Assertion :=
  (regIs .x2 sp0 ** regIs .x1 retHdr ** regIs .x8 cs0 **
    regIs .x9 cs1 ** regIs .x18 cs2 ** regIs .x19 cs3 **
    regIs .x20 cs4 ** regIs .x21 v21 ** regIs .x10 statusW **
    regIs .x11 v11e ** regIs .x12 v12e ** regOwn .x5 ** regOwn .x6 **
    regOwn .x7 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    regOwn .x13 ** regOwn .x14 ** regIs .x0 (0 : Word) ** memIs spC retHdr **
    memIs (spC + 8) cs0 ** memIs (spC + 16) cs1 ** memIs (spC + 24) cs2 **
    memIs (spC + 32) cs3 ** memIs (spC + 40) cs4 ** stackFree spC 8 **
    bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
    memIs outPtr outValW ** memIs vphlOffsetAddr offV ** memIs vphlLengthAddr lenV **
    bytesRegion vphlClaimedAddr claimedB ** bytesRegion vphlComputedAddr computedB **
    bytesRegion vphlZk3 osPost)

/- private theorem vphl_epilogue_values
    (spC sp0 retHdr x1Val statusW v11e v12e parentBase parentLenW childBase childLenW
      outPtr v21 : Word)
    (cs0 cs1 cs2 cs3 cs4 outValW offV lenV : Word)
    (parentBytes childBytes claimedB computedB osPost : List (BitVec 8))
    (v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 : Word)
    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))
    (hret : retHdr &&& ~~~(1 : Word) = retHdr) :
    cpsTripleWithin 8 (vphlBase + 288) retHdr vphlCode
      (vphlTopEpiPreExact spC retHdr x1Val statusW v11e v12e parentBase parentLenW
        childBase childLenW outPtr v21 cs0 cs1 cs2 cs3 cs4 outValW offV lenV
        parentBytes childBytes claimedB computedB osPost
        v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14)
      (vphlTopEpiPost sp0 spC retHdr statusW v11e v12e parentBase parentLenW
        childBase childLenW outPtr v21 cs0 cs1 cs2 cs3 cs4 outValW offV lenV
        parentBytes childBytes claimedB computedB osPost) := by
  have hE := vphl_epilogue_spec_within spC sp0 retHdr x1Val statusW v11e v12e
    parentBase parentLenW childBase childLenW outPtr v21 cs0 cs1 cs2 cs3 cs4
    outValW offV lenV parentBytes childBytes claimedB computedB osPost hspC hret
  have hW :
      cpsTripleWithin 8 (vphlBase + 288) retHdr vphlCode
        (vphlTopEpiPreExact spC retHdr x1Val statusW v11e v12e parentBase parentLenW
          childBase childLenW outPtr v21 cs0 cs1 cs2 cs3 cs4 outValW offV lenV
          parentBytes childBytes claimedB computedB osPost
          v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14)
        (vphlTopEpiPost sp0 spC retHdr statusW v11e v12e parentBase parentLenW
          childBase childLenW outPtr v21 cs0 cs1 cs2 cs3 cs4 outValW offV lenV
          parentBytes childBytes claimedB computedB osPost) := by
    exact cpsTripleWithin_weaken
      (by
      intro h hp
      let rest : Assertion :=
        (regIs .x2 spC ** regIs .x1 x1Val ** regIs .x8 parentBase **
          regIs .x9 parentLenW ** regIs .x18 childBase ** regIs .x19 childLenW **
          regIs .x20 outPtr ** regIs .x21 v21 ** regIs .x10 statusW **
          regIs .x11 v11e ** regIs .x12 v12e ** regIs .x0 (0 : Word) **
          memIs spC retHdr ** memIs (spC + 8) cs0 ** memIs (spC + 16) cs1 **
          memIs (spC + 24) cs2 ** memIs (spC + 32) cs3 ** memIs (spC + 40) cs4 **
          stackFree spC 8 ** bytesRegion parentBase parentBytes **
          bytesRegion childBase childBytes ** memIs outPtr outValW **
          memIs vphlOffsetAddr offV ** memIs vphlLengthAddr lenV **
          bytesRegion vphlClaimedAddr claimedB ** bytesRegion vphlComputedAddr computedB **
          bytesRegion vphlZk3 osPost)
      have hs :
          (vphlTopEpiRegsExact v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 ** rest) h := by
        simp only [vphlTopEpiPreExact, vphlTopEpiRegsExact, rest] at hp ⊢
        xperm_chunked hp
      have hs' : (vphlTopEpiRegsOwn ** rest) h := by
        exact sepConj_mono
          (top_reg12_to_regOwn v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14)
          (fun _ h => h) h hs
      xperm_chunked hs'
      )
      (by intro h hq; simpa only [vphlTopEpiPost] using hq) hE
  exact hW
-/




end EvmAsm.Codegen.ValidateParentHashLinkSpec
