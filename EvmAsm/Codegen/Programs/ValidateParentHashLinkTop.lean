import EvmAsm.Codegen.Programs.ValidateParentHashLinkSpec
import EvmAsm.Codegen.Programs.ValidateParentHashLinkCompare

/-!
  Top-level composition for `validate_parent_hash_link`.

  The body file carries the routine-local contracts and the compare module
  carries the four-dword branch.  Keeping this composition separate keeps the
  source file below the Codegen/Programs line cap while the final theorem still
  quantifies over the linked union `vphlCode`.
-/

namespace EvmAsm.Codegen.ValidateParentHashLinkSpec
set_option maxRecDepth 8000
open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpListNthItemSAsm

private theorem top_reg12_to_regOwn
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

private theorem top_regPair_to_regOwn (a b : Word) : ∀ h,
    ((.x11 ↦ᵣ a) ** (.x12 ↦ᵣ b)) h →
      (regOwn .x11 ** regOwn .x12) h := by
  intro h hp
  exact sepConj_mono (regIs_implies_regOwn .x11)
    (regIs_implies_regOwn .x12) h hp

private theorem top_reg4_to_regOwn (v5 v6 v7 v28 : Word) : ∀ h,
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) h →
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) h := by
  intro h hp
  exact sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7) (regIs_implies_regOwn .x28))) h hp

private theorem top_mem4_to_memOwn
    (a0 a1 a2 a3 v0 v1 v2 v3 : Word) (rest : Assertion) : ∀ h,
    ((a0 ↦ₘ v0) ** (a1 ↦ₘ v1) ** (a2 ↦ₘ v2) ** (a3 ↦ₘ v3) ** rest) h →
      (memOwn a0 ** memOwn a1 ** memOwn a2 ** memOwn a3 ** rest) h := by
  intro h hp
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn (fun _ x => x)))) h hp

private theorem top_mem4_with_owned_tail_to_memOwn
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

private theorem top_reg8_to_regOwn
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
private theorem top_vphl_compare_prefix_to_own
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
private theorem top_frameSlotsSaved_to_own :
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

private theorem top_keccakFrameSaved_to_own
    (newSp : Word) (vals : Reg → Word) : ∀ h,
      frameSlotsSaved keccakFrame newSp vals h →
        frameSlotsOwn keccakFrame newSp h := by
  intro h hp
  simp only [frameSlotsSaved, frameSlotsOwn, keccakFrame, List.foldr] at hp ⊢
  simp only [sepConj_emp_right'] at hp ⊢
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)) h hp

private theorem top_frameSaved_with_rest_to_own
    (frame : FrameDesc) (newSp : Word) (vals : Reg → Word) (rest : Assertion) : ∀ h,
      (frameSlotsSaved frame newSp vals ** rest) h →
        (frameSlotsOwn frame newSp ** rest) h := by
  intro h hp
  exact sepConj_mono_left
    (top_frameSlotsSaved_to_own frame newSp vals) h hp

private theorem top_keccak_slots_to_stackFree
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
  have h0 :
      sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12) +
          signExtend12 (0 : BitVec 12) = sp - 48 := by
    norm_num
    bv_omega
  have h8 :
      sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12) +
          signExtend12 (8 : BitVec 12) = sp - 40 := by
    norm_num
    bv_omega
  have h16 :
      sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12) +
          signExtend12 (16 : BitVec 12) = sp - 32 := by
    norm_num
    bv_omega
  have h24 :
      sp + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12) +
          signExtend12 (24 : BitVec 12) = sp - 24 := by
    norm_num
    bv_omega
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
      exact sepConj_mono memIs_implies_memOwn (fun _ x => x) h hp1
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
    exact top_mem4_with_owned_tail_to_memOwn
      (sp - BitVec.ofNat 64 48) (sp - BitVec.ofNat 64 40)
      (sp - BitVec.ofNat 64 32) (sp - BitVec.ofNat 64 24)
      (sp - BitVec.ofNat 64 16) (sp - BitVec.ofNat 64 8)
      (sp - BitVec.ofNat 64 56) (sp - BitVec.ofNat 64 64)
      (vals .x8) (vals .x9) (vals .x18) (vals .x20) h hp1r
  simp only [stackFree_succ, stackFree_zero]
  show (memOwn (sp - BitVec.ofNat 64 64) ** memOwn (sp - BitVec.ofNat 64 56) **
    memOwn (sp - BitVec.ofNat 64 48) ** memOwn (sp - BitVec.ofNat 64 40) **
    memOwn (sp - BitVec.ofNat 64 32) ** memOwn (sp - BitVec.ofNat 64 24) **
    memOwn (sp - BitVec.ofNat 64 16) ** memOwn (sp - BitVec.ofNat 64 8) **
    empAssertion) h
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

private def vphlTopKFrame
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

private def vphlTopContinuationPre
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

private def vphlTopArmPre
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

@[irreducible] private def vphlTopHashPost
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

@[irreducible] private def vphlTopHashRest
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

private def vphlTopComparePrefix
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

private def vphlTopComparePrefixOwn
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

private theorem top_vphl_compare_prefix_to_own
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

private def vphlTopCompareStackSaved
    (spC retPC parentBase parentLenW childBase outPtr : Word) : Assertion :=
  (memOwn (spC - BitVec.ofNat 64 8) **
    ((spC + signExtend12 (-16 : BitVec 12)) ↦ₘ retPC) **
    frameSlotsSaved keccakFrame
      (spC + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12))
      (keccakEntryVals parentBase parentLenW childBase outPtr) **
    memOwn (spC - BitVec.ofNat 64 56) ** memOwn (spC - BitVec.ofNat 64 64))

private def vphlTopCompareSuffix
    (spC parentBase childBase : Word) (parentBytes childBytes : List (BitVec 8))
  (fo ln : Word) (zk3B : List (BitVec 8)) : Assertion :=
  (bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
    (vphlOffsetAddr ↦ₘ fo) ** (vphlLengthAddr ↦ₘ ln) ** bytesRegion vphlZk3 zk3B)

private def vphlTopCompareBase
    (spC retPC retHdr parentLenW childLenW outPtr v21 : Word)
    (v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) (parentBase childBase : Word)
    (parentBytes childBytes : List (BitVec 8)) (fo ln : Word)
    (zk3B : List (BitVec 8)) : Assertion :=
  (vphlTopComparePrefix spC retPC retHdr parentLenW childLenW outPtr v21
      v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 cs0 cs1 cs2 cs3 cs4 parentBase childBase **
    vphlTopCompareStackSaved spC retPC parentBase parentLenW childBase outPtr **
    vphlTopCompareSuffix spC parentBase childBase parentBytes childBytes fo ln zk3B)

private def vphlTopCompareDword
    (claimedBytes computedBytes : List (BitVec 8)) (q : Nat)
    (compareBase : Assertion) : Assertion :=
  (.x6 ↦ᵣ vphlComputedAddr) **
    (.x7 ↦ᵣ vphlDwordAt claimedBytes q) **
    (.x28 ↦ᵣ vphlDwordAt computedBytes q) **
    bytesRegion vphlClaimedAddr claimedBytes **
    bytesRegion vphlComputedAddr computedBytes ** compareBase

private def vphlTopEpiRegsExact
    (v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 : Word) : Assertion :=
  regIs .x5 v5 ** regIs .x6 v6 ** regIs .x7 v7 **
    regIs .x15 v15 ** regIs .x16 v16 ** regIs .x17 v17 **
    regIs .x28 v28 ** regIs .x29 v29 ** regIs .x30 v30 **
    regIs .x31 v31 ** regIs .x13 v13 ** regIs .x14 v14

private def vphlTopEpiRegsOwn : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
    regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
    regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
    regOwn .x31 ** regOwn .x13 ** regOwn .x14

private def vphlTopEpiPreOwn
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

private def vphlTopEpiPreExact
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

private def vphlTopEpiPost
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

theorem validate_parent_hash_link_spec_within    (sp0 spC retHdr parentBase parentLenW childBase childLenW outPtr : Word)    (cs0 cs1 cs2 cs3 cs4 v21 oldOut oldOffset oldLen : Word)    (parentBytes childBytes claimedOld : List (BitVec 8)) (childLen N rem : Nat)    (os : List (BitVec 8)) (F : Assertion)    (hret : retHdr &&& ~~~(1 : Word) = retHdr)    (hspC : spC = sp0 + signExtend12 (-48 : BitVec 12))    (hplenW : parentLenW = BitVec.ofNat 64 parentBytes.length)    (hclenW : childLenW = BitVec.ofNat 64 childLen)    (hpalign : parentBase.toNat % 8 = 0)    (hpover : parentBase.toNat + parentBytes.length < 2 ^ 64)    (hpvalid : ∀ k, k < parentBytes.length →      isValidByteAccess (parentBase + BitVec.ofNat 64 k) = true)    (hcalign : childBase.toNat % 8 = 0)    (hcslack : childLen + 9 ≤ childBytes.length)    (hcover : childBase.toNat + childBytes.length < 2 ^ 64)    (hcvalid : ∀ k, k < childBytes.length →      isValidByteAccess (childBase + BitVec.ofNat 64 k) = true)    (hfieldBound : ∀ fo ln,      RlpListNthItemSAsm.Success childBytes childBase childLen 0 fo ln →      ln = (32 : Word) → fo.toNat + 32 ≤ childBytes.length)    (houtAlign : outPtr.toNat % 8 = 0)    (houtValid : isValidDwordAccess outPtr = true)    (hkeccakLen : parentBytes.length = keccakAbsorbStep * N + rem)    (hrem_le : rem ≤ 135)    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)    (hb8i : (keccakAbsorbCursor parentBase N).toNat % 8 = 0)    (hos : os.length = 200)    (hclaimedLen : claimedOld.length = 32)    (hF : F.pcFree) :    cpsTripleWithin (583 + keccakBodyFuel N rem) vphlBase retHdr vphlCode      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ retHdr) **        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) **        (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ v21) **        (.x10 ↦ᵣ parentBase) ** (.x11 ↦ᵣ parentLenW) ** (.x12 ↦ᵣ childBase) **        (.x13 ↦ᵣ childLenW) ** (.x14 ↦ᵣ outPtr) **        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x15 ** regOwn .x16 **        regOwn .x17 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **        memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) ** memOwn (spC + 24) **        memOwn (spC + 32) ** memOwn (spC + 40) ** stackFree spC 8 **        bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **        (outPtr ↦ₘ oldOut) ** (vphlOffsetAddr ↦ₘ oldOffset) **        (vphlLengthAddr ↦ₘ oldLen) **        bytesRegion vphlClaimedAddr claimedOld **        bytesRegion vphlComputedAddr (List.replicate 32 (0 : BitVec 8)) **        bytesRegion vphlZk3 os ** F)      (vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21        parentBase childBase parentBytes childBytes claimedOld childLen        oldOffset oldLen os ** F)  := by
  have hbody_sub : ∀ a i, vphlCompareBodyCode a = some i → vphlCode a = some i := by
    intro a i h
    exact vphlCode_vphl a i h
  have hpro0 := vphl_prologue_spec_within sp0 spC retHdr cs0 cs1 cs2 cs3 cs4 v21
    parentBase parentLenW childBase childLenW outPtr oldOut oldOffset oldLen
    parentBytes childBytes claimedOld os hspC
  have hpro := cpsTripleWithin_extend_code hbody_sub hpro0
  have hproF := cpsTripleWithin_frameR F hF hpro
  let kFrame : Assertion :=
    vphlTopKFrame spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21 parentBase parentBytes
      claimedOld os
  let kFrameCore : Assertion :=
    (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
      bytesRegion parentBase parentBytes ** (outPtr ↦ₘ (0 : Word)) **
      bytesRegion vphlClaimedAddr claimedOld **
      bytesRegion vphlComputedAddr (List.replicate 32 (0 : BitVec 8)) **
      bytesRegion vphlZk3 os
  have hcover_le : childBase.toNat + childBytes.length ≤ 2 ^ 64 := Nat.le_of_lt hcover
  have hk := vphl_k20_call_spec_within spC retHdr parentBase parentLenW
    childBase childLenW outPtr v21 oldOffset oldLen parentBytes childBytes claimedOld os
    childLen cs0 cs1 cs2 cs3 cs4 hclenW hcalign hcslack hcover_le hcvalid
  have hkF := cpsTripleWithin_frameR F hF hk
  have hcont : ∀ status offset len v11 v12,
      RlpListNthItemSAsm.Result childBytes childBase childLen 0 oldOffset oldLen
        status offset len →
      cpsTripleWithin (264 + keccakBodyFuel N rem) (vphlBase + 84) retHdr vphlCode
        (((.x1 ↦ᵣ (vphlBase + 84)) **
          (((.x2 ↦ᵣ spC) ** stackFree spC 8 **
            (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
            (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
            (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ v21)) **
            ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** bytesRegion childBase childBytes **
              (vphlOffsetAddr ↦ₘ offset) ** (vphlLengthAddr ↦ₘ len)))) **
          (kFrame ** F))
        (vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
          parentBase childBase parentBytes childBytes claimedOld childLen
          oldOffset oldLen os ** F) := by
    intro status offset len v11 v12 hres
    have hres' :
        (status = (1 : Word) ∧ offset = oldOffset ∧ len = oldLen ∧
            RlpListNthItemSAsm.Failure childBytes childBase childLen 0) ∨
          ∃ fo ln, status = (0 : Word) ∧ offset = fo ∧ len = ln ∧
            RlpListNthItemSAsm.Success childBytes childBase childLen 0 fo ln := by
      cases hres
      · exact Or.inr ⟨_, _, rfl, rfl, rfl, by assumption⟩
      · exact Or.inl ⟨rfl, rfl, rfl, by assumption⟩
    rcases hres' with ⟨hstatus, hoffset, hlen, hfail⟩ |
      ⟨fo, ln, hstatus, hoffset, hlen, hsucc⟩
    · subst status
      subst offset
      subst len
      let pFail : Assertion :=
        (vphlTopArmPre spC parentBase parentLenW childBase childLenW outPtr v21
          (1 : Word) v11 v12 oldOffset oldLen childBytes kFrame F) **
          (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
            regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      have hFailVals := vphl_arm_fail_spec_within sp0 spC retHdr parentBase
        parentLenW childBase childLenW outPtr v21 cs0 cs1 cs2 cs3 cs4
        (v5 := (0 : Word)) (v6 := (0 : Word)) (v7 := (0 : Word))
        (v15 := (0 : Word)) (v16 := (0 : Word)) (v17 := (0 : Word))
        (v28 := (0 : Word)) (v29 := (0 : Word)) (v30 := (0 : Word))
        (v31 := (0 : Word)) (v13 := (0 : Word)) (v14 := (0 : Word))
        v11 v12 parentBytes childBytes claimedOld childLen oldOffset oldLen os
        hspC hret hfail
      have hFailValsF := cpsTripleWithin_frameR F hF hFailVals
      have hFailBound := cpsTripleWithin_mono_nSteps
        (nSteps' := 264 + keccakBodyFuel N rem) (by omega) hFailValsF
      exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [kFrame, vphlTopKFrame] at hp ⊢
        xperm_chunked hp)
        (fun _ hq => hq) hFailBound
    · subst status
      subst offset
      subst len
      by_cases hne : ln ≠ (32 : Word)
      · let pSucc : Assertion :=
          (vphlTopArmPre spC parentBase parentLenW childBase childLenW outPtr v21
            (0 : Word) v11 v12 fo ln childBytes kFrame F) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        let pSuccCore : Assertion :=
          vphlTopArmPre spC parentBase parentLenW childBase childLenW outPtr v21
            (0 : Word) v11 v12 fo ln childBytes kFrameCore F
        have hOwn := vphl_of_forall_regIs_to_regOwn12
          (P := pSuccCore)
          (Q := vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
            parentBase childBase parentBytes childBytes claimedOld childLen oldOffset oldLen os ** F)
          (hspec := by
            intro v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14
            have h := vphl_arm_len_ne32_spec_within sp0 spC retHdr parentLenW
              childLenW outPtr cs0 cs1 cs2 cs3 cs4 v21 parentBase childBase
              parentBytes childBytes claimedOld childLen fo ln oldOffset oldLen v5 v6 v7 v15 v16
              v17 v28 v29 v30 v31 v13 v14 v11 v12 os hspC hret hsucc hne
            have hFArm := cpsTripleWithin_frameR F hF h
            exact cpsTripleWithin_weaken
              (fun _ hp => by
                simp only [pSuccCore, kFrameCore, vphlTopArmPre, vphlTopKFrame] at hp ⊢
                xperm_chunked hp) (fun _ hq => hq) hFArm)
        have hOwnBound := cpsTripleWithin_mono_nSteps
          (nSteps' := 264 + keccakBodyFuel N rem) (by omega) hOwn
        exact cpsTripleWithin_weaken
          (fun _ hp => by
            simp only [pSucc, pSuccCore, kFrame, vphlTopArmPre, vphlTopKFrame] at hp ⊢
            xperm_chunked hp)
          (fun _ hq => hq) hOwnBound
      · have hln32 : ln = (32 : Word) := not_not.mp hne
        let p32 : Assertion :=
          (vphlTopArmPre spC parentBase parentLenW childBase childLenW outPtr v21
            (0 : Word) v11 v12 fo ln childBytes kFrame F) **
            (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
        let p32Core : Assertion :=
          vphlTopArmPre spC parentBase parentLenW childBase childLenW outPtr v21
            (0 : Word) v11 v12 fo ln childBytes kFrameCore empAssertion
        let finalPost :=
          vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
            parentBase childBase parentBytes childBytes claimedOld childLen
            oldOffset oldLen os
        have hWhole : ∀ v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14,
            cpsTripleWithin (264 + keccakBodyFuel N rem) (vphlBase + 84) retHdr vphlCode
              (p32Core ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
                (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
                (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
              (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) finalPost := by
          intro v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14
          have hprefix0 := vphl_arm_len_eq32_prefix_spec_within
            sp0 spC retHdr parentLenW childLenW outPtr cs0 cs1 cs2 cs3 cs4 v21
            parentBase childBase parentBytes childBytes claimedOld childLen fo ln
            v5 v6 v7 v15 v16 v17 v28 v29 v30 v31 v13 v14 v11 v12 os
            hspC hret hsucc hln32
          have hprefix := hprefix0
          have hfb : fo.toNat + 32 ≤ childBytes.length :=
            hfieldBound fo ln hsucc hln32
          have hcopy0 := vphl_copy_claimed_spec_within
            spC retHdr parentLenW childLenW outPtr cs0 cs1 cs2 cs3 cs4 v21
            parentBase childBase parentBytes childBytes claimedOld fo ln
            v15 v16 v17 v28 v29 v30 v31 v13 v14 v11 v12 os
            hfb hcalign hcover hcvalid hclaimedLen
          have hcopy := hcopy0
          let prepP : Assertion :=
            (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (vphlBase + 84)) **
              (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
              (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
              (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ v21) **
              (.x6 ↦ᵣ fo) ** (.x7 ↦ᵣ (32 : Word)) ** (.x15 ↦ᵣ v15) **
              (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) ** (.x28 ↦ᵣ (childBase + fo)) **
              (.x29 ↦ᵣ vphlClaimedAddr) **
              (.x30 ↦ᵣ (packBytes ((((childBytes.drop fo.toNat)).drop (24)).take 8))) **
              (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
              (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ retHdr) **
              ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
              ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
              ((spC + 40) ↦ₘ cs4) ** stackFree spC 8 **
              bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
              (outPtr ↦ₘ (0 : Word)) ** (vphlOffsetAddr ↦ₘ fo) **
              (vphlLengthAddr ↦ₘ ln) **
              bytesRegion vphlClaimedAddr (((childBytes.drop fo.toNat)).take 32) **
              bytesRegion vphlComputedAddr (List.replicate 32 (0 : BitVec 8)) **
              bytesRegion vphlZk3 os
          have hprepHashAny :=
            cpsTripleWithin_peel_regOwns [.x5, .x10, .x11, .x12] (by decide)
              (P := prepP)
              (fun vf => by
                have hprep := vphl_hash_prep_spec_within
                  spC retHdr parentLenW childLenW outPtr cs0 cs1 cs2 cs3 cs4 v21
                  parentBase childBase parentBytes childBytes fo ln
                  v15 v16 v17 v31 v13 v14 (vf .x11) (vf .x12) os
                  (vf .x5) (vf .x10)
                have hhash := vphl_hash_call_spec_within
                  spC retHdr parentLenW childLenW outPtr cs0 cs1 cs2 cs3 cs4 v21
                  parentBase childBase parentBytes childBytes N rem fo ln (vf .x5)
                  v13 v14 v15 v16 v17 v31 os
                  hplenW hkeccakLen hrem_le hNbound hb8i hos hpover hpvalid
                have hseq := cpsTripleWithin_seq_perm_same_cr
                  (fun _ hp => by xperm_chunked hp) hprep hhash
                exact cpsTripleWithin_weaken
                  (P' := prepP ** regAtomsOf vf [.x5, .x10, .x11, .x12])
                  (fun _ hp => by
                    simp only [prepP, regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right'] at hp ⊢
                    xperm_hyp hp)
                  (fun _ hq => hq) hseq)
          have hclaimed32 : ((childBytes.drop fo.toNat).take 32).length = 32 := by
            rw [List.length_take, List.length_drop]
            omega
          have hpc := cpsTripleWithin_seq_perm_same_cr
            (fun _ hp => by xperm_chunked hp) hprefix hcopy
          have hpcp := cpsTripleWithin_seq_perm_same_cr
            (fun _ hp => by
              simp only [regOwns_cons, regOwns_nil, sepConj_emp_right'] at hp ⊢
              xperm_chunked hp) hpc hprepHashAny
          let hashPost : Assertion :=
            vphlTopHashPost spC (vphlBase + 184) retHdr parentLenW childLenW outPtr v21
              cs0 cs1 cs2 cs3 cs4 parentBase childBase parentBytes childBytes
              ((childBytes.drop fo.toNat).take 32)
              (EvmAsm.Stateless.SpecRef.keccak256 parentBytes)
              (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0))
              fo ln
          have hTail : cpsTripleWithin 28 (vphlBase + 184) retHdr vphlCode
              hashPost finalPost := by
            intro R hR s hcr hPR hpc
            let hashRest : Assertion :=
              vphlTopHashRest spC (vphlBase + 184) retHdr parentLenW childLenW outPtr v21
                cs0 cs1 cs2 cs3 cs4 parentBase childBase parentBytes childBytes
                ((childBytes.drop fo.toNat).take 32)
                (EvmAsm.Stateless.SpecRef.keccak256 parentBytes)
                (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                  (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0))
                fo ln
            obtain ⟨hOwned, hcompat, hOwnedAll⟩ := hPR
            have hOwnedAll' :
                (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x13 **
                  regOwn .x14 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
                  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                  (regOwn .x11 ** regOwn .x12 ** hashRest ** R)) hOwned := by
              unfold hashRest vphlTopHashRest
              unfold hashPost vphlTopHashPost at hOwnedAll
              xperm_hyp hOwnedAll
            obtain ⟨v5, v6, v7, v13, v14, v15, v16, v17, v28, v29, v30, v31,
              hVals⟩ := vphl_choose12 hOwnedAll'
            let prefixVals : Assertion :=
              ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
                (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) **
                (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) ** (.x28 ↦ᵣ v28) **
                (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31))
            obtain ⟨v11, hPair⟩ := sepConj_choose_regOwn
              (B := prefixVals ** (regOwn .x12 ** hashRest ** R))
              (by xperm_hyp hVals)
            obtain ⟨v12, hRest⟩ := sepConj_choose_regOwn
              (B := prefixVals ** ((.x11 ↦ᵣ v11) ** hashRest ** R))
              (by xperm_hyp hPair)
            let pVal : Assertion :=
              ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
                (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) **
                (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) ** (.x28 ↦ᵣ v28) **
                (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
                (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** hashRest)
            have hVal : cpsTripleWithin 28 (vphlBase + 184) retHdr vphlCode
                pVal finalPost := by
              let g5 : Assertion :=
                ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
                  (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
                  (.x31 ↦ᵣ v31) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** hashRest)
              let g6 : Assertion :=
                ((.x7 ↦ᵣ v7) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
                  (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
                  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
                  (.x31 ↦ᵣ v31) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** hashRest)
              have h5 := cpsTripleWithin_frameR g5 (by
                unfold g5 hashRest vphlTopHashRest
                pcf)
                (vphlLa_claimed_5c v5)
              have h6 := cpsTripleWithin_frameR g6 (by
                unfold g6 hashRest vphlTopHashRest
                pcf)
                (vphlLa_computed_6 v6)
              have h6f := cpsTripleWithin_frameL
                ((.x5 ↦ᵣ vphlClaimedAddr) : Assertion)
                (by exact pcFree_regIs)
                h6
              have h56 := cpsTripleWithin_seq_perm_same_cr
                (fun _ hp => by xperm_chunked hp) h5 h6f
              let claimedB := (childBytes.drop fo.toNat).take 32
              let computedB := EvmAsm.Stateless.SpecRef.keccak256 parentBytes
              have hclen : claimedB.length = 32 := by
                unfold claimedB
                exact hclaimed32
              have hcdlen : computedB.length = 32 := by
                unfold computedB
                exact EvmAsm.Stateless.SpecRef.keccak256_length _
              let G0 : Assertion :=
                vphlTopCompareBase spC (vphlBase + 184) retHdr parentLenW childLenW outPtr v21
                  v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 cs0 cs1 cs2 cs3 cs4
                  parentBase childBase parentBytes childBytes fo ln
                  (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                    (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0))
              let G0Own : Assertion :=
                (vphlTopComparePrefixOwn spC (vphlBase + 184) retHdr parentLenW childLenW outPtr v21
                    v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 cs0 cs1 cs2 cs3 cs4
                    parentBase childBase **
                  stackFree spC 8 **
                  vphlTopCompareSuffix spC parentBase childBase parentBytes childBytes fo ln
                    (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                      (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)))
              have hG0 : G0.pcFree := by unfold G0 vphlTopCompareBase; pcf
              have hG0Own : ∀ h, G0 h → G0Own h := by
                intro h hp
                dsimp [G0] at hp
                dsimp [G0Own]
                unfold vphlTopCompareBase at hp
                have hp1 := sepConj_mono
                  (top_vphl_compare_prefix_to_own spC (vphlBase + 184) retHdr parentLenW childLenW outPtr v21
                    v11 v12 v13 v14 v15 v16 v17 v29 v30 v31 cs0 cs1 cs2 cs3 cs4 parentBase childBase)
                  (fun _ x => x) h hp
                exact sepConj_mono (fun _ x => x)
                  (sepConj_mono
                    (top_keccak_slots_to_stackFree spC (vphlBase + 184)
                      (keccakEntryVals parentBase parentLenW childBase outPtr))
                    (fun _ x => x)) h hp1
              let Gcmp : Assertion :=
                (.x20 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) **
                  (outPtr ↦ₘ (0 : Word)) ** G0
              have hGcmp : Gcmp.pcFree := by unfold Gcmp; pcf
              let epiPre : Word → Assertion := fun outVal =>
                ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (vphlBase + 184)) **
                  (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
                  (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
                  (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ v21) ** (.x10 ↦ᵣ (0 : Word)) **
                  (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x5 ** regOwn .x6 **
                  regOwn .x7 ** regOwn .x15 ** regOwn .x16 ** regOwn .x17 **
                  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
                  regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
                  (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) **
                  ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
                  ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** stackFree spC 8 **
                  bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
                  (outPtr ↦ₘ outVal) ** (vphlOffsetAddr ↦ₘ fo) **
                  (vphlLengthAddr ↦ₘ ln) ** bytesRegion vphlClaimedAddr claimedB **
                  bytesRegion vphlComputedAddr computedB **
                  bytesRegion vphlZk3
                    (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                      (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)))
/-              have hAdapt : ∀ (v5 vClaim vComp outVal : Word) (h : PartialState),
                  (((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ (0 : Word)) **
                    (outPtr ↦ₘ outVal) ** (.x6 ↦ᵣ vphlComputedAddr) **
                    (.x7 ↦ᵣ vClaim) ** (.x28 ↦ᵣ vComp) **
                    bytesRegion vphlClaimedAddr claimedB **
                    bytesRegion vphlComputedAddr computedB **
                    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (vphlBase + 184)) **
                      (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
                      (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
                      (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
                      (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) **
                      (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) ** (.x29 ↦ᵣ v29) **
                      (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
                      (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) **
                      ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
                      ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** stackFree spC 8 **
                      memOwn (spC - BitVec.ofNat 64 8) **
                      ((spC + signExtend12 (-16 : BitVec 12)) ↦ₘ (vphlBase + 184)) **
                      frameSlotsSaved keccakFrame
                        (spC + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12))
                        (keccakEntryVals parentBase parentLenW childBase outPtr) **
                      memOwn (spC - BitVec.ofNat 64 56) ** memOwn (spC - BitVec.ofNat 64 64) **
                      bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
                      (vphlOffsetAddr ↦ₘ fo) ** (vphlLengthAddr ↦ₘ ln) **
                      bytesRegion vphlZk3
                        (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                          (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0))))))) h →
                  (epiPre outVal) h := by
                intro v5 vClaim vComp outVal h hp
                have hExact :
                    (((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ vphlComputedAddr) ** (.x7 ↦ᵣ vClaim) **
                      (.x28 ↦ᵣ vComp)) **
                      ((.x20 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ outVal) **
                        ((.x2 ↦ᵣ spC) **
                          (.x1 ↦ᵣ ((GuestAddrs.validate_parent_hash_link : Word) + (184 : Word))) **
                          (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
                          (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
                          (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
                          (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x15 ↦ᵣ v15) **
                          (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) ** (.x29 ↦ᵣ v29) **
                          (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
                          (spC ↦ₘ retHdr) ** ((spC + 8) ↦ₘ cs0) **
                          ((spC + 16) ↦ₘ cs1) ** ((spC + 24) ↦ₘ cs2) **
                          ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) ** stackFree spC 8 **
                          memOwn (spC - BitVec.ofNat 64 8) **
                          ((spC + signExtend12 (-16 : BitVec 12)) ↦ₘ (vphlBase + 184)) **
                          frameSlotsSaved keccakFrame
                            (spC + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12))
                            (keccakEntryVals parentBase parentLenW childBase outPtr) **
                          memOwn (spC - BitVec.ofNat 64 56) ** memOwn (spC - BitVec.ofNat 64 64) **
                          bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
                          (vphlOffsetAddr ↦ₘ fo) ** (vphlLengthAddr ↦ₘ ln) **
                          bytesRegion (BitVec.ofNat 64 GuestAddrs.vphl_claimed) claimedB **
                          bytesRegion (BitVec.ofNat 64 GuestAddrs.vphl_computed) computedB **
                          bytesRegion vphlZk3
                            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0))))))) h := by
                  xperm_chunked hp
                have hOwn := sepConj_mono
                  (top_reg12_to_regOwn v5 vphlComputedAddr vClaim v15 v16 v17
                    vComp v29 v30 v31 v13 v14)
                  (fun _ h => h) hExact
                unfold epiPre
                xperm_hyp hOwn
-/
              let adaptSrc (v5 vClaim vComp outVal : Word) : Assertion :=
                ((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ (0 : Word)) **
                  (outPtr ↦ₘ outVal) ** (.x6 ↦ᵣ vphlComputedAddr) **
                  (.x7 ↦ᵣ vClaim) ** (.x28 ↦ᵣ vComp) **
                  bytesRegion vphlClaimedAddr claimedB **
                  bytesRegion vphlComputedAddr computedB ** G0)
              have hAdapt : ∀ (v5 vClaim vComp outVal : Word) (h : PartialState),
                  (adaptSrc v5 vClaim vComp outVal) h → (epiPre outVal) h := by
                intro v5 vClaim vComp outVal h hp
                /-
                have hExact :
                    (((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ (BitVec.ofNat 64 GuestAddrs.vphl_computed)) **
                      (.x7 ↦ᵣ vClaim) ** (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) **
                      (.x17 ↦ᵣ v17) ** (.x28 ↦ᵣ vComp) ** (.x29 ↦ᵣ v29) **
                      (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x13 ↦ᵣ v13) **
                      (.x14 ↦ᵣ v14)) **
                      ((.x20 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) **
                        (outPtr ↦ₘ outVal) **
                        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (vphlBase + 184)) **
                          (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
                          (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
                          (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
                          (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ retHdr) **
                          ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
                          ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
                          ((spC + 40) ↦ₘ cs4) **
                          memOwn (spC - BitVec.ofNat 64 8) **
                          ((spC + signExtend12 (-16 : BitVec 12)) ↦ₘ (vphlBase + 184)) **
                          frameSlotsSaved keccakFrame
                            (spC + signExtend12 (-16 : BitVec 12) + signExtend12 (-32 : BitVec 12))
                            (keccakEntryVals parentBase parentLenW childBase outPtr) **
                          memOwn (spC - BitVec.ofNat 64 56) **
                          memOwn (spC - BitVec.ofNat 64 64) **
                          bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
                          (vphlOffsetAddr ↦ₘ fo) ** (vphlLengthAddr ↦ₘ ln) **
                          bytesRegion (BitVec.ofNat 64 GuestAddrs.vphl_claimed) claimedB **
                          bytesRegion (BitVec.ofNat 64 GuestAddrs.vphl_computed) computedB **
                          bytesRegion vphlZk3
                            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0))))) h := by
                  dsimp [adaptSrc] at hp
                  unfold G0 vphlTopCompareBase at hp
                  have hZero : (BitVec.ofNat 64 0 : Word) = 0 := rfl
                  rw [hZero] at hp
                  simp [stackFree, frameSlotsSaved, keccakFrame, List.foldr,
                    vphlBase, vphlClaimedAddr, vphlComputedAddr] at hp ⊢
                  set_option xperm.cert false in
                    xperm_chunked hp
                -/
                have hExact :
                    (((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ vphlComputedAddr) ** (.x7 ↦ᵣ vClaim) **
                      (.x28 ↦ᵣ vComp)) **
                      ((.x20 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ outVal) **
                        bytesRegion vphlClaimedAddr claimedB ** bytesRegion vphlComputedAddr computedB ** G0)) h := by
                  change (((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ (0 : Word)) **
                    (outPtr ↦ₘ outVal) ** (.x6 ↦ᵣ vphlComputedAddr) ** (.x7 ↦ᵣ vClaim) **
                    (.x28 ↦ᵣ vComp) ** bytesRegion vphlClaimedAddr claimedB **
                    bytesRegion vphlComputedAddr computedB ** G0) h) at hp
                  xperm_chunked hp
                have hOwn := sepConj_mono
                  (top_reg4_to_regOwn v5 (BitVec.ofNat 64 GuestAddrs.vphl_computed) vClaim vComp)
                  (fun _ h => h) h hExact
                have hInnerMap : ∀ h,
                    ((.x20 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ outVal) **
                      bytesRegion vphlClaimedAddr claimedB ** bytesRegion vphlComputedAddr computedB ** G0) h →
                    ((.x20 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ outVal) **
                      bytesRegion vphlClaimedAddr claimedB ** bytesRegion vphlComputedAddr computedB ** G0Own) h := by
                  intro h hp
                  exact sepConj_mono (fun _ x => x)
                    (sepConj_mono (fun _ x => x)
                      (sepConj_mono (fun _ x => x)
                        (sepConj_mono (fun _ x => x)
                          (sepConj_mono (fun _ x => x) hG0Own)))) h hp
                have hOwn' := sepConj_mono (fun _ x => x) hInnerMap h hOwn
                simp [epiPre, G0Own, vphlTopComparePrefixOwn, vphlTopCompareSuffix, stackFree,
                  vphlBase, vphlOffsetAddr, vphlLengthAddr,
                  vphlClaimedAddr, vphlComputedAddr, sepConj_emp_right',
                  sepConj_emp_left'] at hOwn' ⊢
                xperm_chunked hOwn'
              have hEpiFor : ∀ outVal,
                  outVal = (if claimedB = computedB then (1 : Word) else (0 : Word)) →
                  cpsTripleWithin 8 (vphlBase + 288) retHdr vphlCode
                  (epiPre outVal)
                  (vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
                    parentBase childBase parentBytes childBytes claimedOld childLen
                    oldOffset oldLen os) := by
                intro outVal houtVal
                have h := vphl_epilogue_spec_within
                  spC sp0 retHdr (vphlBase + 184) (0 : Word) v11 v12
                  parentBase parentLenW childBase childLenW outPtr v21
                  cs0 cs1 cs2 cs3 cs4 outVal fo ln parentBytes childBytes
                  claimedB computedB
                  (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                    (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0))
                  hspC hret
                have h' : cpsTripleWithin 8 (vphlBase + 288) retHdr vphlCode
                    (epiPre outVal)
                    (vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
                      parentBase childBase parentBytes childBytes claimedOld childLen
                      oldOffset oldLen os) := by
                    exact cpsTripleWithin_weaken
                      (nSteps := 8) (entry := vphlBase + 288) (exit_ := retHdr)
                      (cr := vphlCode)
                      (P' := epiPre outVal)
                      (Q := vphlTopEpiPost sp0 spC retHdr (0 : Word) v11 v12
                        parentBase parentLenW childBase childLenW outPtr v21
                        cs0 cs1 cs2 cs3 cs4 outVal fo ln parentBytes childBytes
                        claimedB computedB
                        (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                          (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)))
                      (Q' := vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
                        parentBase childBase parentBytes childBytes claimedOld childLen
                        oldOffset oldLen os)
                      (fun _ hp => by
                        unfold epiPre at hp
                        simp only [vphlBase, vphlOffsetAddr, vphlLengthAddr,
                          vphlClaimedAddr, vphlComputedAddr] at hp ⊢
                        exact hp)
                          (fun h hq => by
                        simp only [vphlRetPost]
                        refine ⟨0, outVal, fo, ln, fo, ln, claimedB, computedB,
                          (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                            (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)), ?_⟩
                        refine (sepConj_pure_right _).2 ⟨?_, ?_⟩
                        · have h1 :
                            (((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12)) **
                              ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ retHdr) ** (.x8 ↦ᵣ cs0) **
                                (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) **
                                (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ v21) ** (.x10 ↦ᵣ (0 : Word)) **
                                regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x15 **
                                regOwn .x16 ** regOwn .x17 ** regOwn .x28 ** regOwn .x29 **
                                regOwn .x30 ** regOwn .x31 ** regOwn .x13 ** regOwn .x14 **
                                (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ retHdr) **
                                ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
                                ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
                                ((spC + 40) ↦ₘ cs4) ** stackFree spC 8 **
                                bytesRegion parentBase parentBytes ** bytesRegion childBase childBytes **
                                (outPtr ↦ₘ outVal) ** (vphlOffsetAddr ↦ₘ fo) **
                                (vphlLengthAddr ↦ₘ ln) ** bytesRegion vphlClaimedAddr claimedB **
                                  bytesRegion vphlComputedAddr computedB ** bytesRegion vphlZk3
                                    (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
                                      (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)))) h := by
                              simp [vphlTopEpiPost, stackFree] at hq ⊢
                              xperm_chunked hq
                          have h2 := sepConj_mono (top_regPair_to_regOwn v11 v12)
                            (fun _ x => x) h h1
                          xperm_chunked h2
                        · exact Or.inr (Or.inr
                            ⟨rfl, hsucc, hln32, rfl, rfl, rfl, rfl, houtVal⟩)
                      ) h
                exact h'
              let GmatchEq : Assertion :=
                vphlTopCompareDword claimedB computedB 3 G0
              have hEqTail : cpsTripleWithin 24 (vphlBase + 200) retHdr vphlCode
                  ((.x5 ↦ᵣ vphlClaimedAddr) ** (.x6 ↦ᵣ vphlComputedAddr) **
                    (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
                    bytesRegion vphlClaimedAddr claimedB **
                    bytesRegion vphlComputedAddr computedB ** Gcmp)
                  finalPost := by
                by_cases h0 : vphlDwordAt claimedB 0 = vphlDwordAt computedB 0
                · by_cases h1 : vphlDwordAt claimedB 1 = vphlDwordAt computedB 1
                  · by_cases h2 : vphlDwordAt claimedB 2 = vphlDwordAt computedB 2
                    · by_cases h3 : vphlDwordAt claimedB 3 = vphlDwordAt computedB 3
                      · have hEq0 := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareAllEq claimedB computedB v7 v28 hclen hcdlen h0 h1 h2 h3)
                        have hEq := cpsTripleWithin_frameR Gcmp hGcmp hEq0
                        have hMatch := vphlCompareMatchTail outPtr (0 : Word) GmatchEq
                          (by unfold GmatchEq vphlTopCompareDword; pcf)
                        have hMatchC := cpsTripleWithin_extend_code hbody_sub hMatch
                        have hEqMatch := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by
                            simp only [Gcmp, GmatchEq, G0, vphlTopCompareDword,
                              vphlTopCompareBase, vphlClaimedOwn] at hp ⊢
                            xperm_chunked hp) hEq hMatchC
                        have hEqBytes : claimedB = computedB := by
                          apply (vphl_dwords_eq_iff claimedB computedB hclen hcdlen).mp
                          intro q hq
                          interval_cases q <;> assumption
                        have hEpi := hEpiFor (1 : Word) (by simp [hEqBytes])
                        /- old explicit register permutation -/
                        /-
                        have hEqEpi := cpsTripleWithin_seq_perm_same_cr
                          (fun h hp => by
                            have h1 :
                                (((.x5 ↦ᵣ (1 : Word)) **
                                  (.x6 ↦ᵣ vphlComputedAddr) **
                                  (.x7 ↦ᵣ vphlDwordAt claimedB 3) **
                                  (.x15 ↦ᵣ v15) ** (.x16 ↦ᵣ v16) ** (.x17 ↦ᵣ v17) **
                                  (.x28 ↦ᵣ vphlDwordAt computedB 3) **
                                  (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
                                  (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) **
                                ((.x20 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) **
                                  (outPtr ↦ₘ (1 : Word)) **
                                  ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (vphlBase + 184)) **
                                    (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ parentLenW) **
                                    (.x18 ↦ᵣ childBase) ** (.x19 ↦ᵣ childLenW) **
                                    (.x21 ↦ᵣ v21) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
                                    (.x0 ↦ᵣ (0 : Word)) ** (spC ↦ₘ retHdr) **
                                    ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
                                    ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
                                    ((spC + 40) ↦ₘ cs4) ** stackFree spC 8 **
                                    bytesRegion parentBase parentBytes **
                                    bytesRegion childBase childBytes **
                                    (vphlOffsetAddr ↦ₘ fo) ** (vphlLengthAddr ↦ₘ ln) **
                                    bytesRegion vphlClaimedAddr claimedB **
                                    bytesRegion vphlComputedAddr computedB **
                                    bytesRegion vphlZk3 os))) h := by
                              simp only [GmatchEq, vphlTopCompareDword, G0,
                                vphlTopCompareBase, vphlClaimedOwn] at hp ⊢
                              xperm_chunked hp
                            have h2 := sepConj_mono
                              (top_reg12_to_regOwn (1 : Word) vphlComputedAddr
                                (vphlDwordAt claimedB 3) v15 v16 v17
                                (vphlDwordAt computedB 3) v29 v30 v31 v13 v14)
                              (fun _ h => h) h h1
                            xperm_hyp h2) hEqMatch hEpi
                        -/
                        have hEqEpi := cpsTripleWithin_seq_perm_same_cr
                          (fun h hp => by
                            simp only [GmatchEq, vphlTopCompareDword,
                              vphlClaimedOwn] at hp
                            have hp' : adaptSrc (1 : Word)
                                (vphlDwordAt claimedB 3) (vphlDwordAt computedB 3)
                                (1 : Word) h := by
                              simpa only [adaptSrc] using hp
                            exact hAdapt (1 : Word)
                              (vphlDwordAt claimedB 3) (vphlDwordAt computedB 3)
                              (1 : Word) h hp') hEqMatch hEpi
                        have hEqEpi' := cpsTripleWithin_mono_nSteps (nSteps' := 24) (by omega) hEqEpi
                        exact cpsTripleWithin_weaken
                          (fun _ hp => by
                            simp only [vphlClaimedOwn] at hp ⊢
                            xperm_chunked hp)
                          (fun _ hq => by simpa only [finalPost] using hq) hEqEpi'
                      · have h0eq := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound0Eq claimedB computedB v7 v28 hclen hcdlen h0)
                        have h0eqF := cpsTripleWithin_frameR Gcmp hGcmp h0eq
                        have h1eq := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound1Eq claimedB computedB
                            (vphlDwordAt claimedB 0) (vphlDwordAt computedB 0)
                            hclen hcdlen h1)
                        have h1eqF := cpsTripleWithin_frameR Gcmp hGcmp h1eq
                        have h01 := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h0eqF h1eqF
                        have h2eq := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound2Eq claimedB computedB
                            (vphlDwordAt claimedB 1) (vphlDwordAt computedB 1)
                            hclen hcdlen h2)
                        have h2eqF := cpsTripleWithin_frameR Gcmp hGcmp h2eq
                        have h012 := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h01 h2eqF
                        have h3ne := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound3Ne claimedB computedB
                            (vphlDwordAt claimedB 2) (vphlDwordAt computedB 2)
                            hclen hcdlen h3)
                        have h3neF := cpsTripleWithin_frameR Gcmp hGcmp h3ne
                        have h0123 := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h012 h3neF
                        let Gne3 : Assertion := vphlTopCompareDword claimedB computedB 3 G0
                        have hGne3 : Gne3.pcFree := by unfold Gne3 vphlTopCompareDword; pcf
                        have hm := vphlCompareMismatchTail outPtr (0 : Word) Gne3 hGne3
                        have hmC := cpsTripleWithin_extend_code hbody_sub hm
                        have hseq := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by
                            simp only [Gcmp, Gne3, vphlTopCompareDword, G0,
                              vphlTopCompareBase, vphlClaimedOwn] at hp ⊢
                            xperm_chunked hp) h0123 hmC
                        have hseqEpi := cpsTripleWithin_seq_perm_same_cr
                          (fun h hp => by
                            simp only [Gne3, vphlTopCompareDword] at hp
                            exact hAdapt vphlClaimedAddr
                              (vphlDwordAt claimedB 3) (vphlDwordAt computedB 3)
                              (0 : Word) h hp) hseq
                          (hEpiFor (0 : Word) (by
                            have hne : claimedB ≠ computedB := by
                              intro heq
                              have hd := (vphl_dwords_eq_iff claimedB computedB hclen hcdlen).mpr heq
                              exact h3 (hd 3 (by decide))
                            simp [hne]))
                        have hbound := cpsTripleWithin_mono_nSteps
                          (nSteps' := 24) (by omega) hseqEpi
                        exact cpsTripleWithin_weaken
                          (fun _ hp => by
                            simp only [vphlClaimedOwn] at hp ⊢
                            xperm_chunked hp)
                          (fun _ hq => by simpa only [finalPost] using hq) hbound
                    · have h0eq := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound0Eq claimedB computedB v7 v28 hclen hcdlen h0)
                      have h0eqF := cpsTripleWithin_frameR Gcmp hGcmp h0eq
                      have h1ne := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound1Eq claimedB computedB
                            (vphlDwordAt claimedB 0) (vphlDwordAt computedB 0)
                            hclen hcdlen h1)
                      have h1neF := cpsTripleWithin_frameR Gcmp hGcmp h1ne
                      have h01 := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h0eqF h1neF
                      have h2ne := cpsTripleWithin_extend_code hbody_sub
                          (vphlCompareRound2Ne claimedB computedB
                            (vphlDwordAt claimedB 1) (vphlDwordAt computedB 1)
                            hclen hcdlen h2)
                      have h2neF := cpsTripleWithin_frameR Gcmp hGcmp h2ne
                      have h012 := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by xperm_chunked hp) h01 h2neF
                      let Gne2 : Assertion := vphlTopCompareDword claimedB computedB 2 G0
                      have hGne2 : Gne2.pcFree := by unfold Gne2 vphlTopCompareDword; pcf
                      have hm := vphlCompareMismatchTail outPtr (0 : Word) Gne2 hGne2
                      have hmC := cpsTripleWithin_extend_code hbody_sub hm
                      have hseq := cpsTripleWithin_seq_perm_same_cr
                          (fun _ hp => by
                            simp only [Gcmp, Gne2, vphlTopCompareDword, G0,
                              vphlTopCompareBase, vphlClaimedOwn] at hp ⊢
                            xperm_chunked hp) h012 hmC
                      have hseqEpi := cpsTripleWithin_seq_perm_same_cr
                        (fun h hp => by
                          simp only [Gne2, vphlTopCompareDword] at hp
                          exact hAdapt vphlClaimedAddr
                            (vphlDwordAt claimedB 2) (vphlDwordAt computedB 2)
                            (0 : Word) h hp) hseq
                        (hEpiFor (0 : Word) (by
                          have hne : claimedB ≠ computedB := by
                            intro heq
                            have hd := (vphl_dwords_eq_iff claimedB computedB hclen hcdlen).mpr heq
                            exact h2 (hd 2 (by decide))
                          simp [hne]))
                      have hbound := cpsTripleWithin_mono_nSteps
                        (nSteps' := 24) (by omega) hseqEpi
                      exact cpsTripleWithin_weaken
                        (fun _ hp => by
                          simp only [vphlClaimedOwn] at hp ⊢
                          xperm_chunked hp)
                        (fun _ hq => by simpa only [finalPost] using hq) hbound
                  · have h0eq := cpsTripleWithin_extend_code hbody_sub
                        (vphlCompareRound0Eq claimedB computedB v7 v28 hclen hcdlen h0)
                    have h0eqF := cpsTripleWithin_frameR Gcmp hGcmp h0eq
                    have h1ne := cpsTripleWithin_extend_code hbody_sub
                      (vphlCompareRound1Ne claimedB computedB
                        (vphlDwordAt claimedB 0) (vphlDwordAt computedB 0)
                        hclen hcdlen h1)
                    have h1neF := cpsTripleWithin_frameR Gcmp hGcmp h1ne
                    have h01 := cpsTripleWithin_seq_perm_same_cr
                      (fun _ hp => by xperm_chunked hp) h0eqF h1neF
                    let Gne1 : Assertion := vphlTopCompareDword claimedB computedB 1 G0
                    have hGne1 : Gne1.pcFree := by unfold Gne1 vphlTopCompareDword; pcf
                    have hm := vphlCompareMismatchTail outPtr (0 : Word) Gne1 hGne1
                    have hmC := cpsTripleWithin_extend_code hbody_sub hm
                    have hseq := cpsTripleWithin_seq_perm_same_cr
                      (fun _ hp => by
                        simp only [Gcmp, Gne1, vphlTopCompareDword, G0,
                          vphlTopCompareBase, vphlClaimedOwn] at hp ⊢
                        xperm_chunked hp) h01 hmC
                    have hseqEpi := cpsTripleWithin_seq_perm_same_cr
                      (fun h hp => by
                        simp only [Gne1, vphlTopCompareDword] at hp
                        exact hAdapt vphlClaimedAddr
                          (vphlDwordAt claimedB 1) (vphlDwordAt computedB 1)
                          (0 : Word) h hp) hseq
                      (hEpiFor (0 : Word) (by
                        have hne : claimedB ≠ computedB := by
                          intro heq
                          have hd := (vphl_dwords_eq_iff claimedB computedB hclen hcdlen).mpr heq
                          exact h1 (hd 1 (by decide))
                        simp [hne]))
                    have hbound := cpsTripleWithin_mono_nSteps
                      (nSteps' := 24) (by omega) hseqEpi
                    exact cpsTripleWithin_weaken
                      (fun _ hp => by
                        simp only [vphlClaimedOwn] at hp ⊢
                        xperm_chunked hp)
                      (fun _ hq => by simpa only [finalPost] using hq) hbound
                · have h0ne := cpsTripleWithin_extend_code hbody_sub
                      (vphlCompareRound0Ne claimedB computedB v7 v28 hclen hcdlen h0)
                  have h0neF := cpsTripleWithin_frameR Gcmp hGcmp h0ne
                  let Gne0 : Assertion := vphlTopCompareDword claimedB computedB 0 G0
                  have hGne0 : Gne0.pcFree := by unfold Gne0 vphlTopCompareDword; pcf
                  have hm := vphlCompareMismatchTail outPtr (0 : Word) Gne0 hGne0
                  have hmC := cpsTripleWithin_extend_code hbody_sub hm
                  have hseq := cpsTripleWithin_seq_perm_same_cr
                    (fun _ hp => by
                      simp only [Gcmp, Gne0, vphlTopCompareDword, G0,
                        vphlTopCompareBase, vphlClaimedOwn] at hp ⊢
                      xperm_chunked hp) h0neF hmC
                  have hseqEpi := cpsTripleWithin_seq_perm_same_cr
                    (fun h hp => by
                      simp only [Gne0, vphlTopCompareDword] at hp
                      exact hAdapt vphlClaimedAddr
                        (vphlDwordAt claimedB 0) (vphlDwordAt computedB 0)
                        (0 : Word) h hp) hseq
                    (hEpiFor (0 : Word) (by
                      have hne : claimedB ≠ computedB := by
                        intro heq
                        have hd := (vphl_dwords_eq_iff claimedB computedB hclen hcdlen).mpr heq
                        exact h0 (hd 0 (by decide))
                      simp [hne]))
                  have hbound := cpsTripleWithin_mono_nSteps
                    (nSteps' := 24) (by omega) hseqEpi
                  exact cpsTripleWithin_weaken
                    (fun _ hp => by
                      simp only [vphlClaimedOwn] at hp ⊢
                      xperm_chunked hp)
                    (fun _ hq => by simpa only [finalPost] using hq) hbound
              have hAll := cpsTripleWithin_seq_perm_same_cr
                (fun _ hp => by
                  unfold g6 hashRest vphlTopHashRest at hp
                  simp only [Gcmp, G0, vphlTopCompareBase, vphlTopComparePrefix,
                    vphlTopCompareStackSaved, vphlTopCompareSuffix, frameSlotsSaved,
                    keccakFrame, List.foldr, stackFree, claimedB, computedB,
                    vphlClaimedAddr, vphlComputedAddr, sepConj_emp_right',
                    sepConj_emp_left'] at hp ⊢
                  xperm_chunked hp) h56 hEqTail
              exact hAll
            exact hVal R hR s hcr (by
              refine ⟨hOwned, hcompat, ?_⟩
              simp only [prefixVals] at hRest
              unfold pVal
              xperm_hyp hRest) hpc
          have hAll := cpsTripleWithin_seq_perm_same_cr
            (fun _ hp => by
              unfold hashPost vphlTopHashPost
              xperm_chunked hp) hpcp hTail
          have hAllBound := cpsTripleWithin_mono_nSteps
            (nSteps' := 264 + keccakBodyFuel N rem) (by omega) hAll
          exact cpsTripleWithin_weaken
            (fun _ hp => by
              simp only [p32Core, kFrameCore, vphlTopArmPre, vphlTopKFrame,
                sepConj_emp_right', sepConj_emp_left'] at hp ⊢
              xperm_chunked hp)
            (fun _ hq => hq) hAllBound
        have hOwn := vphl_of_forall_regIs_to_regOwn12
          (P := p32Core) (Q := finalPost) hWhole
        have hOwnF := cpsTripleWithin_frameR F hF hOwn
        exact cpsTripleWithin_weaken
          (fun _ hp => by
            simp only [p32, p32Core, kFrame, kFrameCore, vphlTopArmPre, vphlTopKFrame,
              sepConj_emp_right', sepConj_emp_left'] at hp ⊢
            xperm_chunked hp)
          (fun _ hq => hq) hOwnF
  have hcall := vphl_callReturn_pre (F := kFrame ** F)
    (Q := vphlRetPost sp0 spC retHdr outPtr cs0 cs1 cs2 cs3 cs4 v21
      parentBase childBase parentBytes childBytes claimedOld childLen oldOffset oldLen os ** F)
    spC childBase vphlOffsetAddr vphlLengthAddr oldOffset oldLen
    { ra := vphlBase + 84, s0 := parentBase, s1 := parentLenW,
      s2 := childBase, s3 := childLenW, s4 := outPtr, s5 := v21 }
    childBytes childLen hcont
  have hkcall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [kFrame, vphlTopKFrame, callReturnResult,
        vphlK20Frame, RlpListNthItemSAsm.savedRegTail,
        RlpListNthItemSAsm.entryRest] at hp ⊢
      xperm_chunked hp) hkF hcall
  have hpre := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hproF hkcall
  have hpreBound := cpsTripleWithin_mono_nSteps
    (nSteps' := 583 + keccakBodyFuel N rem) (by omega) hpre
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_chunked hp) (fun _ hq => hq) hpreBound

end EvmAsm.Codegen.ValidateParentHashLinkSpec
