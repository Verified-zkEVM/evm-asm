/-
  Teer prologue: allocate 160B frame → storeSeq ra/s0–s11/a5 →
  MV ABI a0–a4 into s0–s4. Leaves PC at AfterAbiMoves (E+80).
-/

import EvmAsm.Codegen.Programs.TxEip7702TeerSpec
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure)

theorem regsAt_teerFrame (s : TeerSaved) :
    regsAt teerFrame (teerSavedVals s) =
      ((.x1 ↦ᵣ s.ra) ** (.x8 ↦ᵣ s.s0) ** (.x9 ↦ᵣ s.s1) **
        (.x18 ↦ᵣ s.s2) ** (.x19 ↦ᵣ s.s3) ** (.x20 ↦ᵣ s.s4) **
        (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
        (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
        (.x27 ↦ᵣ s.s11) ** (.x15 ↦ᵣ s.a5)) := by
  simp [teerFrame, regsAt, teerSavedVals, sepConj_emp_right']

theorem frameSlotsSaved_teerFrame (spC : Word) (s : TeerSaved) :
    frameSlotsSaved teerFrame spC (teerSavedVals s) =
      ((spC + signExtend12 (0 : BitVec 12) ↦ₘ s.ra) **
        (spC + signExtend12 (8 : BitVec 12) ↦ₘ s.s0) **
        (spC + signExtend12 (16 : BitVec 12) ↦ₘ s.s1) **
        (spC + signExtend12 (24 : BitVec 12) ↦ₘ s.s2) **
        (spC + signExtend12 (32 : BitVec 12) ↦ₘ s.s3) **
        (spC + signExtend12 (40 : BitVec 12) ↦ₘ s.s4) **
        (spC + signExtend12 (48 : BitVec 12) ↦ₘ s.s5) **
        (spC + signExtend12 (56 : BitVec 12) ↦ₘ s.s6) **
        (spC + signExtend12 (64 : BitVec 12) ↦ₘ s.s7) **
        (spC + signExtend12 (72 : BitVec 12) ↦ₘ s.s8) **
        (spC + signExtend12 (80 : BitVec 12) ↦ₘ s.s9) **
        (spC + signExtend12 (88 : BitVec 12) ↦ₘ s.s10) **
        (spC + signExtend12 (96 : BitVec 12) ↦ₘ s.s11) **
        (spC + signExtend12 (104 : BitVec 12) ↦ₘ s.a5)) := by
  simp [teerFrame, frameSlotsSaved, teerSavedVals, sepConj_emp_right']

/-- ABI a0–a4 + temps. x15 (a5/bai) rides in `teerFrame` / regsAt. -/
def prologueAbiRest
    (loadPtr lenW balPtr balLenW chainIdW : Word)
    (old5 old6 old7 old16 : Word) : Assertion :=
  (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ balPtr) **
  (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW) **
  (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
  (.x16 ↦ᵣ old16) **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  (.x0 ↦ᵣ (0 : Word))

/-- Post-prologue (PC = AfterAbiMoves): frame saved, ABI in s0–s4. -/
def prologuePost (spC : Word) (s : TeerSaved)
    (loadPtr lenW balPtr balLenW chainIdW : Word)
    (old5 old6 old7 old16 : Word) : Assertion :=
  (.x2 ↦ᵣ spC) **
  (.x1 ↦ᵣ s.ra) **
  (.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) **
  (.x18 ↦ᵣ balPtr) ** (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
  (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
  (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
  (.x27 ↦ᵣ s.s11) ** (.x15 ↦ᵣ s.a5) **
  frameSlotsSaved teerFrame spC (teerSavedVals s) **
  prologueAbiRest loadPtr lenW balPtr balLenW chainIdW
    old5 old6 old7 old16

set_option maxRecDepth 8000 in
/-- Five ABI moves (instr 15-19): s0=a0 .. s4=a4. -/
theorem teerAbiMoves
    (loadPtr lenW balPtr balLenW chainIdW : Word)
    (cs0 cs1 cs2 cs3 cs4 : Word) :
    cpsTripleWithin 5 AfterFrameSave AfterAbiMoves teerCode
      ((.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ balPtr) **
        (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW))
      ((.x8 ↦ᵣ loadPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ balPtr) **
        (.x19 ↦ᵣ balLenW) ** (.x20 ↦ᵣ chainIdW) **
        (.x10 ↦ᵣ loadPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ balPtr) **
        (.x13 ↦ᵣ balLenW) ** (.x14 ↦ᵣ chainIdW)) := by
  have h0 := mv_spec_gen_within .x8 .x10 loadPtr cs0 AfterFrameSave (by decide)
  have h1 := mv_spec_gen_within .x9 .x11 lenW cs1 (AfterFrameSave + 4) (by decide)
  have h2 := mv_spec_gen_within .x18 .x12 balPtr cs2 (AfterFrameSave + 8) (by decide)
  have h3 := mv_spec_gen_within .x19 .x13 balLenW cs3 (AfterFrameSave + 12) (by decide)
  have h4 := mv_spec_gen_within .x20 .x14 chainIdW cs4 (AfterFrameSave + 16) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E AfterFrameSave teerProg 15
      (.MV .x8 .x10) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide)) h0
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (AfterFrameSave + 4) teerProg 16
      (.MV .x9 .x11) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide)) h1
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (AfterFrameSave + 8) teerProg 17
      (.MV .x18 .x12) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide)) h2
  have e3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (AfterFrameSave + 12) teerProg 18
      (.MV .x19 .x13) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide)) h3
  have e4 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E (AfterFrameSave + 16) teerProg 19
      (.MV .x20 .x14) (by bv_omega) (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide)) h4
  runBlock e0 e1 e2 e3 e4

set_option maxRecDepth 8000 in
/-- Frame allocate + storeSeq (instr 0-14): 1 ADDI + 14 SD. -/
theorem teerFrameSave (sp0 spC : Word) (s : TeerSaved)
    (hspC : spC = sp0 + signExtend12 teerSpDelta) :
    cpsTripleWithin 15 E AfterFrameSave teerCode
      ((.x2 ↦ᵣ sp0) ** regsAt teerFrame (teerSavedVals s) **
        frameSlotsOwn teerFrame spC)
      ((.x2 ↦ᵣ spC) ** regsAt teerFrame (teerSavedVals s) **
        frameSlotsSaved teerFrame spC (teerSavedVals s)) := by
  have ha0 := addi_spec_gen_same_within .x2 sp0 teerSpDelta E (by decide)
  rw [← hspC] at ha0
  have ha := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at E E teerProg 0
      (.ADDI .x2 .x2 teerSpDelta) rfl
      (by rw [teer_length]; decide) rfl
      (by rw [teer_length]; decide)) ha0
  have haF := cpsTripleWithin_frameR
    (regsAt teerFrame (teerSavedVals s) ** frameSlotsOwn teerFrame spC) (by pcf) ha
  have hs0 := storeSeq_spec teerFrame spC (teerSavedVals s) (E + 4) (by decide)
  have h_storeMono : ∀ a i,
      CodeReq.ofProg (E + 4) (storeProg teerFrame) a = some i →
        teerCode a = some i := by
    intro a i h_mem
    exact CodeReq.ofProg_mono_sub E (E + 4) teerProg (storeProg teerFrame) 1
      (by bv_omega) rfl
      (by rw [teer_length]; simp [teerFrame, storeProg])
      (by rw [teer_length]; decide) a i h_mem
  have hs := cpsTripleWithin_extend_code h_storeMono hs0
  rw [show E + 4 + BitVec.ofNat 64 (4 * teerFrame.length) = AfterFrameSave from by
    simp [teerFrame, AfterFrameSave, E]; bv_omega] at hs
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) haF hs

set_option maxRecDepth 8000 in
/-- Full prologue through ABI moves (instr 0-19 → AfterAbiMoves). -/
theorem teerPrologue (sp0 spC : Word) (s : TeerSaved)
    (loadPtr lenW balPtr balLenW chainIdW : Word)
    (old5 old6 old7 old16 : Word)
    (hspC : spC = sp0 + signExtend12 teerSpDelta) :
    cpsTripleWithin 20 E AfterAbiMoves teerCode
      ((.x2 ↦ᵣ sp0) ** regsAt teerFrame (teerSavedVals s) **
        frameSlotsOwn teerFrame spC **
        prologueAbiRest loadPtr lenW balPtr balLenW chainIdW
          old5 old6 old7 old16)
      (prologuePost spC s loadPtr lenW balPtr balLenW chainIdW
        old5 old6 old7 old16) := by
  have hsave := teerFrameSave sp0 spC s hspC
  have hsaveF := cpsTripleWithin_frameR
    (prologueAbiRest loadPtr lenW balPtr balLenW chainIdW
      old5 old6 old7 old16)
    (by pcf) hsave
  have hmv := teerAbiMoves loadPtr lenW balPtr balLenW chainIdW
    s.s0 s.s1 s.s2 s.s3 s.s4
  have hmvF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ s.ra) **
      (.x21 ↦ᵣ s.s5) ** (.x22 ↦ᵣ s.s6) ** (.x23 ↦ᵣ s.s7) **
      (.x24 ↦ᵣ s.s8) ** (.x25 ↦ᵣ s.s9) ** (.x26 ↦ᵣ s.s10) **
      (.x27 ↦ᵣ s.s11) ** (.x15 ↦ᵣ s.a5) **
      frameSlotsSaved teerFrame spC (teerSavedVals s) **
      (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
      (.x16 ↦ᵣ old16) **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      (.x0 ↦ᵣ (0 : Word))) (by pcf) hmv
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_teerFrame] at hp
    unfold prologueAbiRest at hp
    xperm_hyp hp) hsaveF hmvF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      unfold prologuePost prologueAbiRest
      xperm_hyp hq) h01

#print axioms teerFrameSave
#print axioms teerAbiMoves
#print axioms teerPrologue

end EvmAsm.Codegen.TxEip7702TeerSpec
