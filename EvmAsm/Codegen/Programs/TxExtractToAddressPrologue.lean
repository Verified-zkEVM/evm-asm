/-
  Prologue for `tx_extract_to_address`: allocate 80B frame, storeSeq ra/s0–s7,
  MV ABI a0–a3 into s0–s3. Leaves PC at E+56 (pre-zero outputs).
-/

import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.TxIntrinsicStateGasSpec (nExtractStackDwords)

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
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_stackFree _ _)

theorem regsAt_extractFrame (s : ExtractSaved) :
    regsAt extractFrame (extractSavedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (Reg.x23 ↦ᵣ s.s7)) := by
  simp [extractFrame, regsAt, extractSavedVals, sepConj_emp_right']

theorem frameSlotsSaved_extractFrame (spC : Word) (s : ExtractSaved) :
    frameSlotsSaved extractFrame spC (extractSavedVals s) =
      ((spC + signExtend12 (0 : BitVec 12) ↦ₘ s.ra) **
        (spC + signExtend12 (8 : BitVec 12) ↦ₘ s.s0) **
        (spC + signExtend12 (16 : BitVec 12) ↦ₘ s.s1) **
        (spC + signExtend12 (24 : BitVec 12) ↦ₘ s.s2) **
        (spC + signExtend12 (32 : BitVec 12) ↦ₘ s.s3) **
        (spC + signExtend12 (40 : BitVec 12) ↦ₘ s.s4) **
        (spC + signExtend12 (48 : BitVec 12) ↦ₘ s.s5) **
        (spC + signExtend12 (56 : BitVec 12) ↦ₘ s.s6) **
        (spC + signExtend12 (64 : BitVec 12) ↦ₘ s.s7)) := by
  simp [extractFrame, frameSlotsSaved, extractSavedVals, sepConj_emp_right']

/-- Spare dword at offset 72 (10th free stack cell; frame uses 0..64). -/
def extractSpareSlot (spC : Word) : Assertion :=
  memOwn (spC + signExtend12 (72 : BitVec 12))

private theorem spC_eq_extract (sp0 : Word) :
    sp0 + signExtend12 (-80 : BitVec 12) = sp0 - (80 : Word) := by
  rw [show signExtend12 (-80 : BitVec 12) = (-80 : Word) from by decide]
  bv_omega

private theorem slot0e (sp : Word) : (sp - (80 : Word)) + (0 : Word) = sp - (80 : Word) := by
  bv_omega
private theorem slot8e (sp : Word) : (sp - (80 : Word)) + (8 : Word) = sp - (72 : Word) := by
  bv_omega
private theorem slot16e (sp : Word) : (sp - (80 : Word)) + (16 : Word) = sp - (64 : Word) := by
  bv_omega
private theorem slot24e (sp : Word) : (sp - (80 : Word)) + (24 : Word) = sp - (56 : Word) := by
  bv_omega
private theorem slot32e (sp : Word) : (sp - (80 : Word)) + (32 : Word) = sp - (48 : Word) := by
  bv_omega
private theorem slot40e (sp : Word) : (sp - (80 : Word)) + (40 : Word) = sp - (40 : Word) := by
  bv_omega
private theorem slot48e (sp : Word) : (sp - (80 : Word)) + (48 : Word) = sp - (32 : Word) := by
  bv_omega
private theorem slot56e (sp : Word) : (sp - (80 : Word)) + (56 : Word) = sp - (24 : Word) := by
  bv_omega
private theorem slot64e (sp : Word) : (sp - (80 : Word)) + (64 : Word) = sp - (16 : Word) := by
  bv_omega
private theorem slot72e (sp : Word) : (sp - (80 : Word)) + (72 : Word) = sp - (8 : Word) := by
  bv_omega

private theorem se12s_extract :
    signExtend12 (0 : BitVec 12) = (0 : Word) ∧
    signExtend12 (8 : BitVec 12) = (8 : Word) ∧
    signExtend12 (16 : BitVec 12) = (16 : Word) ∧
    signExtend12 (24 : BitVec 12) = (24 : Word) ∧
    signExtend12 (32 : BitVec 12) = (32 : Word) ∧
    signExtend12 (40 : BitVec 12) = (40 : Word) ∧
    signExtend12 (48 : BitVec 12) = (48 : Word) ∧
    signExtend12 (56 : BitVec 12) = (56 : Word) ∧
    signExtend12 (64 : BitVec 12) = (64 : Word) ∧
    signExtend12 (72 : BitVec 12) = (72 : Word) := by decide

private theorem mul8s_extract :
    BitVec.ofNat 64 (8 * (9 + 1)) = BitVec.ofNat 64 80 ∧
    BitVec.ofNat 64 (8 * (8 + 1)) = BitVec.ofNat 64 72 ∧
    BitVec.ofNat 64 (8 * (7 + 1)) = BitVec.ofNat 64 64 ∧
    BitVec.ofNat 64 (8 * (6 + 1)) = BitVec.ofNat 64 56 ∧
    BitVec.ofNat 64 (8 * (5 + 1)) = BitVec.ofNat 64 48 ∧
    BitVec.ofNat 64 (8 * (4 + 1)) = BitVec.ofNat 64 40 ∧
    BitVec.ofNat 64 (8 * (3 + 1)) = BitVec.ofNat 64 32 ∧
    BitVec.ofNat 64 (8 * (2 + 1)) = BitVec.ofNat 64 24 ∧
    BitVec.ofNat 64 (8 * (1 + 1)) = BitVec.ofNat 64 16 ∧
    BitVec.ofNat 64 (8 * (0 + 1)) = BitVec.ofNat 64 8 := by decide

private theorem sepConj_assoc_eq {P Q R : Assertion} :
    ((P ** Q) ** R) = (P ** (Q ** R)) := by
  funext h; exact propext (sepConj_assoc h)

/-- `stackFree sp0 10` = frame slots at spC + spare@72. -/
theorem stackFree10_eq_frameSlotsOwn (sp0 : Word)
    (spC : Word) (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12)) :
    stackFree sp0 nExtractStackDwords =
      (frameSlotsOwn extractFrame spC ** extractSpareSlot spC) := by
  subst hspC
  rw [spC_eq_extract]
  obtain ⟨e0, e8, e16, e24, e32, e40, e48, e56, e64, e72⟩ := se12s_extract
  obtain ⟨n80, n72, n64, n56, n48, n40, n32, n24, n16, n8⟩ := mul8s_extract
  simp only [nExtractStackDwords, extractFrame, extractSpareSlot, frameSlotsOwn,
    stackFree_succ, stackFree_zero, sepConj_emp_right', List.foldr_cons, List.foldr_nil,
    e0, e8, e16, e24, e32, e40, e48, e56, e64, e72,
    slot0e, slot8e, slot16e, slot24e, slot32e, slot40e, slot48e, slot56e, slot64e, slot72e,
    n80, n72, n64, n56, n48, n40, n32, n24, n16, n8]
  -- LHS right-assoc 10 atoms; RHS is (right-assoc 9) ** spare — reassociate.
  symm
  repeat rw [sepConj_assoc_eq]
  rfl

/-- Saved slots imply owned slots (memIs → memOwn). -/
private theorem frameSlotsSaved_imp_own (spC : Word) (s : ExtractSaved) :
    ∀ h, frameSlotsSaved extractFrame spC (extractSavedVals s) h →
      frameSlotsOwn extractFrame spC h := by
  intro h hp
  obtain ⟨e0, e8, e16, e24, e32, e40, e48, e56, e64, _e72⟩ := se12s_extract
  simp only [extractFrame, frameSlotsSaved, frameSlotsOwn, extractSavedVals,
    List.foldr_cons, List.foldr_nil, sepConj_emp_right',
    e0, e8, e16, e24, e32, e40, e48, e56, e64] at hp ⊢
  exact sepConj_mono memIs_implies_memOwn
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn
                  memIs_implies_memOwn))))))) h hp

/-- Post: saved frame + spare rejoin to entry `stackFree sp0 10`. -/
theorem frameSlotsSaved_imp_stackFree10 (sp0 spC : Word) (s : ExtractSaved)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12)) :
    ∀ h,
      (frameSlotsSaved extractFrame spC (extractSavedVals s) **
        extractSpareSlot spC) h →
      stackFree sp0 nExtractStackDwords h := by
  intro h hp
  have hown :=
    sepConj_mono (frameSlotsSaved_imp_own spC s) (fun _ hh => hh) h hp
  have heq := stackFree10_eq_frameSlotsOwn sp0 spC hspC
  rw [heq]
  exact hown

/-- ABI args + temps carried through the prologue. -/
def prologueAbiRest
    (txBase txLenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word) : Assertion :=
  (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) **
  (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr) **
  (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
  (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

/-- Post-prologue (PC = E+56): frame saved, ABI in s0–s3. -/
def prologuePost (spC : Word) (s : ExtractSaved)
    (txBase txLenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x1 ↦ᵣ s.ra) **
  (.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
  (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
  (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (Reg.x23 ↦ᵣ s.s7) **
  frameSlotsSaved extractFrame spC (extractSavedVals s) **
  extractSpareSlot spC **
  prologueAbiRest txBase txLenW toBuf isCreationPtr
    old5 old6 old7 old14 old15 old16

set_option maxRecDepth 8000 in
/-- Four ABI moves (instr 10-13): s0=a0, s1=a1, s2=a2, s3=a3. -/
theorem extractAbiMoves
    (txBase txLenW toBuf isCreationPtr : Word)
    (cs0 cs1 cs2 cs3 : Word) :
    cpsTripleWithin 4 (E + 40) (E + 56) extractCode
      ((.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) ** (Reg.x19 ↦ᵣ cs3) **
        (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr))
      ((.x8 ↦ᵣ txBase) ** (.x9 ↦ᵣ txLenW) **
        (.x18 ↦ᵣ toBuf) ** (.x19 ↦ᵣ isCreationPtr) **
        (.x10 ↦ᵣ txBase) ** (.x11 ↦ᵣ txLenW) **
        (.x12 ↦ᵣ toBuf) ** (.x13 ↦ᵣ isCreationPtr)) := by
  have h0 := mv_spec_gen_within .x8 .x10 txBase cs0 (E + 40) (by decide)
  have h1 := mv_spec_gen_within .x9 .x11 txLenW cs1 (E + 44) (by decide)
  have h2 := mv_spec_gen_within .x18 .x12 toBuf cs2 (E + 48) (by decide)
  have h3 := mv_spec_gen_within .x19 .x13 isCreationPtr cs3 (E + 52) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (E + 40) extractProg 10
      (.MV .x8 .x10) (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) h0
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (E + 44) extractProg 11
      (.MV .x9 .x11) (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) h1
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (E + 48) extractProg 12
      (.MV .x18 .x12) (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) h2
  have e3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (E + 52) extractProg 13
      (.MV .x19 .x13) (by bv_omega) (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) h3
  runBlock e0 e1 e2 e3

set_option maxRecDepth 8000 in
/-- Frame allocate + storeSeq (instr 0-9): 1 ADDI + 9 SD. -/
theorem extractFrameSave (sp0 spC : Word) (s : ExtractSaved)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12)) :
    cpsTripleWithin 10 E (E + 40) extractCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC)
      ((.x2 ↦ᵣ spC) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsSaved extractFrame spC (extractSavedVals s)) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 (-80 : BitVec 12) E (by decide)
  rw [← hspC] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E E extractProg 0
      (.ADDI .x2 .x2 (-80 : BitVec 12)) rfl
      (by rw [extract_length]; decide) rfl
      (by rw [extract_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt extractFrame (extractSavedVals s) ** frameSlotsOwn extractFrame spC)
    (by pcf) ha
  have hs0 := storeSeq_spec extractFrame spC (extractSavedVals s) (E + 4) (by decide)
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (E + 4) (storeProg extractFrame) a = some i →
        extractCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub E (E + 4) extractProg (storeProg extractFrame) 1
      (by bv_omega) rfl
      (by rw [extract_length]; simp [extractFrame, storeProg])
      (by rw [extract_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_storeMono hs0
  rw [show E + 4 + BitVec.ofNat 64 (4 * extractFrame.length) = E + 40 from by
    simp [extractFrame]; bv_omega] at hs
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hs

set_option maxRecDepth 8000 in
/-- Full prologue: frame save + ABI moves (instr 0-13 to E+56). -/
theorem extractPrologue (sp0 spC : Word) (s : ExtractSaved)
    (txBase txLenW toBuf isCreationPtr : Word)
    (old5 old6 old7 old14 old15 old16 : Word)
    (hspC : spC = sp0 + signExtend12 (-80 : BitVec 12)) :
    cpsTripleWithin 14 E (E + 56) extractCode
      ((.x2 ↦ᵣ sp0) ** regsAt extractFrame (extractSavedVals s) **
        frameSlotsOwn extractFrame spC ** extractSpareSlot spC **
        prologueAbiRest txBase txLenW toBuf isCreationPtr
          old5 old6 old7 old14 old15 old16)
      (prologuePost spC s txBase txLenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16) := by
  have hsave := extractFrameSave sp0 spC s hspC
  have hsaveF := cpsTripleWithin_frameR
    (extractSpareSlot spC **
      prologueAbiRest txBase txLenW toBuf isCreationPtr
        old5 old6 old7 old14 old15 old16)
    (by pcf) hsave
  have hmv := extractAbiMoves txBase txLenW toBuf isCreationPtr s.s0 s.s1 s.s2 s.s3
  have hmvF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
      (.x20 ↦ᵣ s.s4) ** (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (Reg.x23 ↦ᵣ s.s7) **
      frameSlotsSaved extractFrame spC (extractSavedVals s) **
      extractSpareSlot spC **
      (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
      (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) ** (.x16 ↦ᵣ old16) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hmv
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_extractFrame] at hp
    unfold prologueAbiRest at hp
    xperm_hyp hp) hsaveF hmvF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      unfold prologuePost prologueAbiRest
      xperm_hyp hq) h01

#print axioms extractFrameSave
#print axioms extractPrologue
#print axioms stackFree10_eq_frameSlotsOwn

end EvmAsm.Codegen.TxExtractToAddressSpec
